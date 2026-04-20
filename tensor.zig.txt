const std = @import("std");
const mem = std.mem;
const math = std.math;
const Allocator = mem.Allocator;
const types = @import("types.zig");
const Error = types.Error;
const Fixed32_32 = types.Fixed32_32;
const memory = @import("memory.zig");

const Shape = struct {
    dims: []usize,
    strides: []usize,

    pub fn init(allocator: Allocator, shape: []const usize) !Shape {
        const n = shape.len;
        if (n == 0) return Error.InvalidShape;
        const dims = try allocator.alloc(usize, n);
        errdefer allocator.free(dims);
        const strides = try allocator.alloc(usize, n);
        errdefer allocator.free(strides);
        @memcpy(dims, shape);
        strides[n - 1] = 1;
        var i: usize = n - 1;
        while (i > 0) : (i -= 1) {
            const r = @mulWithOverflow(strides[i], dims[i]);
            if (r[1] != 0) return Error.Overflow;
            strides[i - 1] = r[0];
        }
        return .{ .dims = dims, .strides = strides };
    }

    pub fn deinit(self: *Shape, allocator: Allocator) void {
        allocator.free(self.dims);
        allocator.free(self.strides);
    }

    pub fn copy(self: *const Shape, allocator: Allocator) !Shape {
        const dims = try allocator.dupe(usize, self.dims);
        errdefer allocator.free(dims);
        const strides = try allocator.dupe(usize, self.strides);
        errdefer allocator.free(strides);
        return .{ .dims = dims, .strides = strides };
    }

    pub fn totalSize(self: *const Shape) Error!usize {
        if (self.dims.len == 0) return 1;
        var total: usize = 1;
        for (self.dims) |d| {
            const r = @mulWithOverflow(total, d);
            if (r[1] != 0) return Error.Overflow;
            total = r[0];
        }
        return total;
    }

    pub fn equals(self: *const Shape, other: *const Shape) bool {
        return mem.eql(usize, self.dims, other.dims) and mem.eql(usize, self.strides, other.strides);
    }

    pub fn broadcastCompatible(self: *const Shape, target: *const Shape) bool {
        if (target.dims.len < self.dims.len) return false;
        const offset = target.dims.len - self.dims.len;
        var i: usize = 0;
        while (i < self.dims.len) : (i += 1) {
            const self_dim = self.dims[i];
            const target_dim = target.dims[offset + i];
            if (self_dim != target_dim and self_dim != 1) {
                return false;
            }
        }
        return true;
    }

    pub fn isContiguous(self: *const Shape) bool {
        if (self.dims.len == 0) return true;
        var expected: usize = 1;
        var i: usize = self.dims.len;
        while (i > 0) : (i -= 1) {
            const idx = i - 1;
            if (self.strides[idx] != expected) return false;
            const r = @mulWithOverflow(expected, self.dims[idx]);
            if (r[1] != 0) return false;
            expected = r[0];
        }
        return true;
    }
};

pub const Tensor = struct {
    data: []f32,
    base_data: []f32,
    shape: Shape,
    allocator: Allocator,
    refcount: *usize,
    cow: *bool,
    mutex: *std.Thread.Mutex,

    pub fn init(allocator: Allocator, shape: []const usize) !Tensor {
        if (shape.len == 0) return Error.InvalidShape;
        var total_size: usize = 1;
        for (shape) |dim| {
            if (dim == 0) return Error.InvalidShape;
            const r = @mulWithOverflow(total_size, dim);
            if (r[1] != 0) return Error.Overflow;
            total_size = r[0];
        }
        const data = try allocator.alloc(f32, total_size);
        errdefer allocator.free(data);
        @memset(data, 0);
        var sh = try Shape.init(allocator, shape);
        errdefer sh.deinit(allocator);
        const refcount = try allocator.create(usize);
        errdefer allocator.destroy(refcount);
        refcount.* = 1;
        const cow = try allocator.create(bool);
        errdefer allocator.destroy(cow);
        cow.* = false;
        const mutex = try allocator.create(std.Thread.Mutex);
        errdefer allocator.destroy(mutex);
        mutex.* = .{};
        return .{ .data = data, .base_data = data, .shape = sh, .allocator = allocator, .refcount = refcount, .cow = cow, .mutex = mutex };
    }

    pub fn initWithArena(arena: *memory.ArenaAllocator, shape: []const usize) !Tensor {
        return init(arena.allocator(), shape);
    }

    pub fn initWithPool(pool: *memory.PoolAllocator, shape: []const usize) !Tensor {
        return init(pool.allocator(), shape);
    }

    pub fn initWithSlab(slab: *memory.SlabAllocator, shape: []const usize) !Tensor {
        return init(slab.allocator(), shape);
    }

    pub fn initWithBuddy(buddy: *memory.BuddyAllocator, shape: []const usize) !Tensor {
        return init(buddy.allocator(), shape);
    }

    pub fn retain(self: *Tensor) void {
        _ = @atomicRmw(usize, self.refcount, .Add, 1, .acq_rel);
        self.markShared();
    }

    pub fn release(self: *Tensor) void {
        const prev = @atomicRmw(usize, self.refcount, .Sub, 1, .acq_rel);
        if (prev == 1) {
            self.deallocate();
        } else {
            self.shape.deinit(self.allocator);
        }
    }

    fn deallocate(self: *Tensor) void {
        self.allocator.free(self.base_data);
        self.shape.deinit(self.allocator);
        self.allocator.destroy(self.refcount);
        self.allocator.destroy(self.cow);
        self.allocator.destroy(self.mutex);
    }

    pub fn deinit(self: *Tensor) void {
        self.release();
    }

    pub fn copy(self: *const Tensor, allocator: Allocator) !Tensor {
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            new_t.data[flat] = try self.get(indices);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    fn ensureWritable(self: *Tensor) !void {
        self.mutex.lock();
        var unlock_old = true;
        defer if (unlock_old) self.mutex.unlock();

        if (!self.cow.*) return;

        const total = try self.shape.totalSize();
        const new_data = try self.allocator.alloc(f32, total);
        errdefer self.allocator.free(new_data);

        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);

        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            new_data[flat] = self.data[try self.computeIndex(indices)];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }

        const new_refcount = try self.allocator.create(usize);
        errdefer self.allocator.destroy(new_refcount);
        new_refcount.* = 1;

        const new_cow = try self.allocator.create(bool);
        errdefer self.allocator.destroy(new_cow);
        new_cow.* = false;

        const new_mutex = try self.allocator.create(std.Thread.Mutex);
        errdefer self.allocator.destroy(new_mutex);
        new_mutex.* = .{};

        var new_strides = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_strides);
        var expected: usize = 1;
        var i: usize = self.shape.dims.len;
        while (i > 0) : (i -= 1) {
            new_strides[i - 1] = expected;
            expected *= self.shape.dims[i - 1];
        }

        const old_refcount = @atomicRmw(usize, self.refcount, .Sub, 1, .acq_rel);
        const was_last = (old_refcount == 1);
        const old_base_data = self.base_data;
        const old_refcount_ptr = self.refcount;
        const old_cow_ptr = self.cow;
        const old_mutex_ptr = self.mutex;
        const old_strides = self.shape.strides;

        self.data = new_data;
        self.base_data = new_data;
        self.refcount = new_refcount;
        self.cow = new_cow;
        self.mutex = new_mutex;
        self.shape.strides = new_strides;

        unlock_old = false;
        old_mutex_ptr.unlock();

        self.allocator.free(old_strides);
        if (was_last) {
            self.allocator.free(old_base_data);
            self.allocator.destroy(old_refcount_ptr);
            self.allocator.destroy(old_cow_ptr);
            self.allocator.destroy(old_mutex_ptr);
        }
    }

    fn markShared(self: *Tensor) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        self.cow.* = true;
    }

    pub fn newView(self: *Tensor, shape: Shape) !Tensor {
        const shape_size = try shape.totalSize();
        const self_size = try self.shape.totalSize();
        if (shape_size != self_size) return Error.InvalidShape;
        self.retain();
        return .{ .data = self.data, .base_data = self.base_data, .shape = shape, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn reshape(self: *Tensor, new_shape: []const usize) !void {
        if (new_shape.len == 0) return Error.InvalidShape;
        if (!self.shape.isContiguous()) return Error.InvalidShape;
        var total: usize = 1;
        for (new_shape) |dim| {
            const r = @mulWithOverflow(total, dim);
            if (r[1] != 0) return Error.Overflow;
            total = r[0];
        }
        const self_size = try self.shape.totalSize();
        if (total != self_size) return Error.InvalidShape;
        const new_sh = try Shape.init(self.allocator, new_shape);
        self.shape.deinit(self.allocator);
        self.shape = new_sh;
    }

    pub fn view(self: *Tensor, new_shape: []const usize) !Tensor {
        if (new_shape.len == 0) return Error.InvalidShape;
        var total: usize = 1;
        for (new_shape) |dim| {
            const r = @mulWithOverflow(total, dim);
            if (r[1] != 0) return Error.Overflow;
            total = r[0];
        }
        const self_size = try self.shape.totalSize();
        if (total != self_size) return Error.InvalidShape;
        const new_sh = try Shape.init(self.allocator, new_shape);
        self.retain();
        return .{ .data = self.data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn slice(self: *Tensor, starts: []const usize, ends: []const usize) !Tensor {
        if (starts.len != self.shape.dims.len or ends.len != self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_dims);
        var new_strides = try self.allocator.alloc(usize, self.shape.strides.len);
        errdefer self.allocator.free(new_strides);
        var offset: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (starts[i] > ends[i] or ends[i] > self.shape.dims[i]) return Error.OutOfBounds;
            new_dims[i] = ends[i] - starts[i];
            new_strides[i] = self.shape.strides[i];
            offset += starts[i] * self.shape.strides[i];
        }
        const new_sh = Shape{ .dims = new_dims, .strides = new_strides };
        const new_data = self.data[offset..];
        self.retain();
        return .{ .data = new_data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn transpose(self: *Tensor, axes: []const usize) !Tensor {
        if (axes.len != self.shape.dims.len) return Error.InvalidAxis;
        var seen = try self.allocator.alloc(bool, axes.len);
        defer self.allocator.free(seen);
        @memset(seen, false);
        for (axes) |a| {
            if (a >= axes.len or seen[a]) return Error.InvalidAxis;
            seen[a] = true;
        }
        var new_dims = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_dims);
        var new_strides = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_strides);
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            new_dims[i] = self.shape.dims[axes[i]];
            new_strides[i] = self.shape.strides[axes[i]];
        }
        const new_sh = Shape{ .dims = new_dims, .strides = new_strides };
        self.retain();
        return .{ .data = self.data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    fn computeIndex(self: *const Tensor, indices: []const usize) !usize {
        if (indices.len != self.shape.dims.len) return Error.InvalidAxis;
        var idx: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (indices[i] >= self.shape.dims[i]) return Error.OutOfBounds;
            idx += indices[i] * self.shape.strides[i];
        }
        return idx;
    }

    pub fn get(self: *const Tensor, indices: []const usize) !f32 {
        const idx = try computeIndex(self, indices);
        return self.data[idx];
    }

    pub fn set(self: *Tensor, indices: []const usize, value: f32) !void {
        try ensureWritable(self);
        const idx = try computeIndex(self, indices);
        self.data[idx] = value;
    }

    pub fn fill(self: *Tensor, value: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] = value;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn add(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            self.data[idx1] += other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn sub(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            self.data[idx1] -= other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn mul(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            self.data[idx1] *= other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn div(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            if (other.data[idx2] == 0.0) return Error.DivideByZero;
            self.data[idx1] /= other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn addScalar(self: *Tensor, scalar: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] += scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn subScalar(self: *Tensor, scalar: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] -= scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn mulScalar(self: *Tensor, scalar: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] *= scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn divScalar(self: *Tensor, scalar: f32) !void {
        if (scalar == 0.0) return Error.DivideByZero;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] /= scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn exp(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @exp(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn log(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            if (self.data[idx] <= 0.0) {
                self.data[idx] = -math.inf(f32);
            } else {
                self.data[idx] = @log(self.data[idx]);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn sin(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @sin(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn cos(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @cos(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn tan(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @tan(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn sqrt(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            if (self.data[idx] < 0.0) {
                self.data[idx] = math.nan(f32);
            } else {
                self.data[idx] = @sqrt(self.data[idx]);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn pow(self: *Tensor, exponent: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            if (self.data[idx] < 0.0 and @floor(exponent) != exponent) {
                self.data[idx] = math.nan(f32);
            } else if (self.data[idx] == 0.0 and exponent < 0.0) {
                self.data[idx] = math.inf(f32);
            } else {
                self.data[idx] = math.pow(f32, self.data[idx], exponent);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn abs(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @abs(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn max(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var max_val: f32 = -math.inf(f32);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (val > max_val) max_val = val;
            }
            result.data[out_idx] = max_val;
        }
        return result;
    }

    pub fn min(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var min_val: f32 = math.inf(f32);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (val < min_val) min_val = val;
            }
            result.data[out_idx] = min_val;
        }
        return result;
    }

    pub fn sum(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var total: f32 = 0.0;
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                total += try self.get(in_indices);
            }
            result.data[out_idx] = total;
        }
        return result;
    }

    pub fn mean(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        var summed = try self.sum(allocator, axis);
        if (self.shape.dims[axis] == 0) return Error.DivideByZero;
        try summed.divScalar(@as(f32, @floatFromInt(self.shape.dims[axis])));
        return summed;
    }

    pub fn matmul(a: *const Tensor, b: *const Tensor, allocator: Allocator) !Tensor {
        if (a.shape.dims.len != 2 or b.shape.dims.len != 2 or a.shape.dims[1] != b.shape.dims[0]) return Error.ShapeMismatch;
        const m = a.shape.dims[0];
        const k = a.shape.dims[1];
        const n = b.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var c = try init(allocator, &.{ m, n });
        var i: usize = 0;
        while (i < m) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                var sum_val: f32 = 0.0;
                var l: usize = 0;
                while (l < k) : (l += 1) {
                    sum_val += try a.get(&.{ i, l }) * try b.get(&.{ l, j });
                }
                try c.set(&.{ i, j }, sum_val);
            }
        }
        return c;
    }

    pub fn broadcast(self: *Tensor, target_shape: []const usize) !Tensor {
        const new_dims = try self.allocator.alloc(usize, target_shape.len);
        errdefer self.allocator.free(new_dims);
        @memcpy(new_dims, target_shape);
        
        var new_strides = try self.allocator.alloc(usize, target_shape.len);
        errdefer self.allocator.free(new_strides);
        
        const offset = target_shape.len - self.shape.dims.len;
        var i: usize = 0;
        while (i < target_shape.len) : (i += 1) {
            if (i < offset) {
                new_strides[i] = 0;
            } else {
                const self_dim = self.shape.dims[i - offset];
                if (self_dim == 1 and target_shape[i] > 1) {
                    new_strides[i] = 0;
                } else {
                    new_strides[i] = self.shape.strides[i - offset];
                }
            }
        }
        
        var new_sh = Shape{ .dims = new_dims, .strides = new_strides };
        if (!self.shape.broadcastCompatible(&new_sh)) {
            self.allocator.free(new_dims);
            self.allocator.free(new_strides);
            return Error.ShapeMismatch;
        }
        
        self.retain();
        return .{ .data = self.data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn unsqueeze(self: *Tensor, axis: usize) !Tensor {
        if (axis > self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try self.allocator.alloc(usize, self.shape.dims.len + 1);
        errdefer self.allocator.free(new_dims);
        var new_strides = try self.allocator.alloc(usize, self.shape.dims.len + 1);
        errdefer self.allocator.free(new_strides);
        
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len + 1) : (i += 1) {
            if (i == axis) {
                new_dims[i] = 1;
                new_strides[i] = if (i == self.shape.dims.len) 1 else self.shape.strides[j];
            } else {
                new_dims[i] = self.shape.dims[j];
                new_strides[i] = self.shape.strides[j];
                j += 1;
            }
        }
        const new_sh = Shape{ .dims = new_dims, .strides = new_strides };
        self.retain();
        return .{ .data = self.data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn zeros(allocator: Allocator, shape: []const usize) !Tensor {
        return init(allocator, shape);
    }

    pub fn ones(allocator: Allocator, shape: []const usize) !Tensor {
        var t = try init(allocator, shape);
        try t.fill(1.0);
        return t;
    }

    pub fn full(allocator: Allocator, shape: []const usize, value: f32) !Tensor {
        var t = try init(allocator, shape);
        try t.fill(value);
        return t;
    }

    pub fn randomUniform(allocator: Allocator, shape: []const usize, min_val: f32, max_val: f32, seed: u64) !Tensor {
        var prng = types.PRNG.init(seed);
        var t = try init(allocator, shape);
        var indices = try allocator.alloc(usize, shape.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            t.data[try t.computeIndex(indices)] = prng.float() * (max_val - min_val) + min_val;
            var i: usize = shape.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < shape[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return t;
    }

    pub fn randomNormal(allocator: Allocator, shape: []const usize, mean_val: f32, stddev_val: f32, seed: u64) !Tensor {
        var prng = types.PRNG.init(seed);
        var t = try init(allocator, shape);
        var indices = try allocator.alloc(usize, shape.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var u = prng.float();
            var v = prng.float();
            while (u <= 0.0) u = prng.float();
            while (v == 0.0) v = prng.float();
            const z = @sqrt(-2.0 * @log(u)) * @cos(2.0 * math.pi * v);
            t.data[try t.computeIndex(indices)] = mean_val + stddev_val * z;
            var i: usize = shape.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < shape[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return t;
    }

    pub fn identity(allocator: Allocator, n: usize) !Tensor {
        if (n == 0) return Error.InvalidShape;
        var t = try init(allocator, &.{ n, n });
        var i: usize = 0;
        while (i < n) : (i += 1) {
            try t.set(&.{ i, i }, 1.0);
        }
        return t;
    }

    pub fn pad(self: *const Tensor, allocator: Allocator, pads: [][2]usize) !Tensor {
        if (pads.len != self.shape.dims.len) return Error.InvalidPads;
        var new_shape = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(new_shape);
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            const r1 = @addWithOverflow(self.shape.dims[i], pads[i][0]);
            if (r1[1] != 0) return Error.Overflow;
            const r2 = @addWithOverflow(r1[0], pads[i][1]);
            if (r2[1] != 0) return Error.Overflow;
            new_shape[i] = r2[0];
            if (new_shape[i] == 0) return Error.InvalidShape;
        }
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        var src_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(src_indices);
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var is_pad = false;
            i = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                if (indices[i] < pads[i][0] or indices[i] >= pads[i][0] + self.shape.dims[i]) {
                    is_pad = true;
                } else {
                    src_indices[i] = indices[i] - pads[i][0];
                }
            }
            if (!is_pad) {
                const val = try self.get(src_indices);
                new_t.data[try new_t.computeIndex(indices)] = val;
            }
            var carry = true;
            var dim = self.shape.dims.len;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn tile(self: *const Tensor, allocator: Allocator, reps: []const usize) !Tensor {
        if (reps.len != self.shape.dims.len) return Error.InvalidReps;
        var new_shape = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(new_shape);
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (reps[i] == 0) return Error.InvalidShape;
            const r = @mulWithOverflow(self.shape.dims[i], reps[i]);
            if (r[1] != 0) return Error.Overflow;
            new_shape[i] = r[0];
        }
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        var src_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(src_indices);
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            i = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                src_indices[i] = indices[i] % self.shape.dims[i];
            }
            new_t.data[try new_t.computeIndex(indices)] = try self.get(src_indices);
            var carry = true;
            var dim = self.shape.dims.len;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn concat(allocator: Allocator, tensors: []const *const Tensor, axis: usize) !Tensor {
        if (tensors.len == 0) return Error.EmptyInput;
        const ndim = tensors[0].shape.dims.len;
        if (axis >= ndim) return Error.InvalidAxis;
        
        var total_axis: usize = 0;
        for (tensors) |ten| {
            if (ten.shape.dims.len != ndim) return Error.ShapeMismatch;
            var i: usize = 0;
            while (i < ndim) : (i += 1) {
                if (i != axis and ten.shape.dims[i] != tensors[0].shape.dims[i]) return Error.ShapeMismatch;
            }
            const r = @addWithOverflow(total_axis, ten.shape.dims[axis]);
            if (r[1] != 0) return Error.Overflow;
            total_axis = r[0];
        }
        
        var new_shape = try allocator.alloc(usize, ndim);
        defer allocator.free(new_shape);
        @memcpy(new_shape, tensors[0].shape.dims);
        new_shape[axis] = total_axis;
        
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, ndim);
        defer allocator.free(indices);
        @memset(indices, 0);
        var src_indices = try allocator.alloc(usize, ndim);
        defer allocator.free(src_indices);
        
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const axis_val = indices[axis];
            var current_offset: usize = 0;
            var t_idx: usize = 0;
            while (t_idx < tensors.len) : (t_idx += 1) {
                const ten = tensors[t_idx];
                const limit = current_offset + ten.shape.dims[axis];
                if (axis_val >= current_offset and axis_val < limit) {
                    @memcpy(src_indices, indices);
                    src_indices[axis] = axis_val - current_offset;
                    new_t.data[try new_t.computeIndex(indices)] = try ten.get(src_indices);
                    break;
                }
                current_offset = limit;
            }
            var carry = true;
            var dim = ndim;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn stack(allocator: Allocator, tensors: []const *const Tensor, axis: usize) !Tensor {
        if (tensors.len == 0) return Error.EmptyInput;
        const ndim = tensors[0].shape.dims.len;
        if (axis > ndim) return Error.InvalidAxis;
        
        for (tensors) |ten| {
            if (ten.shape.dims.len != ndim) return Error.ShapeMismatch;
            var i: usize = 0;
            while (i < ndim) : (i += 1) {
                if (ten.shape.dims[i] != tensors[0].shape.dims[i]) return Error.ShapeMismatch;
            }
        }
        
        var new_shape = try allocator.alloc(usize, ndim + 1);
        defer allocator.free(new_shape);
        new_shape[axis] = tensors.len;
        var k: usize = 0;
        var i: usize = 0;
        while (i < ndim + 1) : (i += 1) {
            if (i == axis) continue;
            new_shape[i] = tensors[0].shape.dims[k];
            k += 1;
        }
        
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, ndim + 1);
        defer allocator.free(indices);
        @memset(indices, 0);
        var src_indices = try allocator.alloc(usize, ndim);
        defer allocator.free(src_indices);
        
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const t_idx = indices[axis];
            const ten = tensors[t_idx];
            var a: usize = 0;
            var d: usize = 0;
            while (d < ndim + 1) : (d += 1) {
                if (d != axis) {
                    src_indices[a] = indices[d];
                    a += 1;
                }
            }
            new_t.data[try new_t.computeIndex(indices)] = try ten.get(src_indices);
            var carry = true;
            var dim = ndim + 1;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn argmax(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var max_val: f32 = -math.inf(f32);
            var max_idx: usize = 0;
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (k == 0 or val > max_val) {
                    max_val = val;
                    max_idx = k;
                }
            }
            result.data[out_idx] = @as(f32, @floatFromInt(max_idx));
        }
        return result;
    }

    pub fn argmin(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var min_val: f32 = math.inf(f32);
            var min_idx: usize = 0;
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (k == 0 or val < min_val) {
                    min_val = val;
                    min_idx = k;
                }
            }
            result.data[out_idx] = @as(f32, @floatFromInt(min_idx));
        }
        return result;
    }

    pub fn cumsum(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        var search_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(search_indices);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var sum_val: f32 = 0.0;
            @memcpy(search_indices, indices);
            var k: usize = 0;
            while (k <= indices[axis]) : (k += 1) {
                search_indices[axis] = k;
                sum_val += try self.get(search_indices);
            }
            new_t.data[try new_t.computeIndex(indices)] = sum_val;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    pub fn variance(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        var mean_t = try self.mean(allocator, axis);
        defer mean_t.deinit();
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            const mean_val = mean_t.data[out_idx];
            var sum_sq: f32 = 0.0;
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                const diff = val - mean_val;
                sum_sq += diff * diff;
            }
            result.data[out_idx] = sum_sq / @as(f32, @floatFromInt(self.shape.dims[axis]));
        }
        return result;
    }

    pub fn stddev(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        var var_t = try self.variance(allocator, axis);
        var i: usize = 0;
        while (i < var_t.data.len) : (i += 1) {
            if (var_t.data[i] < 0.0) {
                var_t.data[i] = 0.0;
            } else {
                var_t.data[i] = @sqrt(var_t.data[i]);
            }
        }
        return var_t;
    }

    pub fn sort(self: *const Tensor, allocator: Allocator, axis: usize, descending: bool) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_t = try self.copy(allocator);
        const Context = struct {
            pub fn lessThan(_: void, a: f32, b: f32) bool {
                if (math.isNan(a)) return false;
                if (math.isNan(b)) return true;
                return a < b;
            }
            pub fn greaterThan(_: void, a: f32, b: f32) bool {
                if (math.isNan(a)) return false;
                if (math.isNan(b)) return true;
                return a > b;
            }
        };
        var reduced_shape = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(reduced_shape);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                reduced_shape[j] = self.shape.dims[i];
                j += 1;
            }
        }
        var common_indices = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(common_indices);
        @memset(common_indices, 0);
        var temp = try allocator.alloc(f32, self.shape.dims[axis]);
        defer allocator.free(temp);
        var in_indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(in_indices);
        var flat_size: usize = 1;
        for (reduced_shape) |d| flat_size *= d;
        var flat_idx: usize = 0;
        while (flat_idx < flat_size) : (flat_idx += 1) {
            var map_idx: usize = 0;
            i = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                if (i != axis) {
                    in_indices[i] = common_indices[map_idx];
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                temp[k] = try new_t.get(in_indices);
            }
            if (descending) {
                std.mem.sort(f32, temp, {}, Context.greaterThan);
            } else {
                std.mem.sort(f32, temp, {}, Context.lessThan);
            }
            k = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                new_t.data[try new_t.computeIndex(in_indices)] = temp[k];
            }
            var carry = true;
            var dim: isize = @as(isize, @intCast(self.shape.dims.len - 1)) - 1;
            while (carry and dim >= 0) : (dim -= 1) {
                common_indices[@intCast(dim)] += 1;
                if (common_indices[@intCast(dim)] < reduced_shape[@intCast(dim)]) {
                    carry = false;
                } else {
                    common_indices[@intCast(dim)] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn unique(self: *const Tensor, allocator: Allocator) !Tensor {
        var vals = std.ArrayList(f32).init(allocator);
        defer vals.deinit();
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            var found = false;
            for (vals.items) |v| {
                if (@abs(v - val) < 1e-10) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                try vals.append(val);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        if (vals.items.len == 0) return Error.EmptyInput;
        const Context = struct {
            pub fn lessThan(_: void, a: f32, b: f32) bool {
                return a < b;
            }
        };
        std.mem.sort(f32, vals.items, {}, Context.lessThan);
        const unique_t = try init(allocator, &.{vals.items.len});
        @memcpy(unique_t.data, vals.items);
        return unique_t;
    }

    pub fn oneHot(self: *const Tensor, allocator: Allocator, num_classes: usize) !Tensor {
        if (self.shape.dims.len != 1) return Error.InvalidForOneHot;
        if (num_classes == 0) return Error.InvalidShape;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        const new_shape = &.{ n, num_classes };
        var new_t = try init(allocator, new_shape);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            const val = try self.get(&.{i});
            if (val >= 0.0) {
                const idx = @as(usize, @intFromFloat(val));
                if (idx < num_classes) {
                    try new_t.set(&.{ i, idx }, 1.0);
                }
            }
        }
        return new_t;
    }

    pub fn isClose(self: *const Tensor, other: *const Tensor, rtol: f32, atol: f32) !bool {
        if (!self.shape.equals(&other.shape)) return false;
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const a = try self.get(indices);
            const b = try other.get(indices);
            if (@abs(a - b) > atol + rtol * @abs(b)) return false;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return true;
    }

    pub fn toInt(self: *const Tensor, allocator: Allocator) !Tensor {
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            new_t.data[try new_t.computeIndex(indices)] = @floor(val);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    pub fn spectralNorm(self: *const Tensor, allocator: Allocator, max_iter: u32, tol: f32) !f32 {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const m = self.shape.dims[0];
        const n = self.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var v = try init(allocator, &.{n});
        defer v.deinit();
        var i: usize = 0;
        while (i < n) : (i += 1) {
            try v.set(&.{i}, 1.0 / @as(f32, @floatFromInt(n)));
        }
        var last_radius: f32 = 0.0;
        var iter: usize = 0;
        while (iter < max_iter) : (iter += 1) {
            var av = try init(allocator, &.{m});
            defer av.deinit();
            var j: usize = 0;
            while (j < m) : (j += 1) {
                var sum_val: f32 = 0.0;
                var k: usize = 0;
                while (k < n) : (k += 1) {
                    sum_val += try self.get(&.{ j, k }) * try v.get(&.{k});
                }
                try av.set(&.{j}, sum_val);
            }
            var atav = try init(allocator, &.{n});
            defer atav.deinit();
            j = 0;
            while (j < n) : (j += 1) {
                var sum_val: f32 = 0.0;
                var k: usize = 0;
                while (k < m) : (k += 1) {
                    sum_val += try self.get(&.{ k, j }) * try av.get(&.{k});
                }
                try atav.set(&.{j}, sum_val);
            }
            var norm_atav: f32 = 0.0;
            j = 0;
            while (j < n) : (j += 1) {
                const val = try atav.get(&.{j});
                norm_atav += val * val;
            }
            norm_atav = @sqrt(norm_atav);
            if (norm_atav >= 1e-12) {
                j = 0;
                while (j < n) : (j += 1) {
                    try v.set(&.{j}, try atav.get(&.{j}) / norm_atav);
                }
            }
            var new_av = try init(allocator, &.{m});
            defer new_av.deinit();
            j = 0;
            while (j < m) : (j += 1) {
                var sum_val: f32 = 0.0;
                var k: usize = 0;
                while (k < n) : (k += 1) {
                    sum_val += try self.get(&.{ j, k }) * try v.get(&.{k});
                }
                try new_av.set(&.{j}, sum_val);
            }
            var radius_sq: f32 = 0.0;
            j = 0;
            while (j < m) : (j += 1) {
                const val = try new_av.get(&.{j});
                radius_sq += val * val;
            }
            const radius = @sqrt(radius_sq);
            if (@abs(radius - last_radius) < tol) return @abs(radius);
            last_radius = radius;
        }
        return @abs(last_radius);
    }

    pub fn normL2(self: *const Tensor) !f32 {
        var sum_sq: f32 = 0.0;
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            sum_sq += val * val;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return @sqrt(sum_sq);
    }

    pub fn dot(self: *const Tensor, other: *const Tensor) !f32 {
        if (self.shape.dims.len != 1 or other.shape.dims.len != 1) return Error.ShapeMismatch;
        if (self.shape.dims[0] != other.shape.dims[0]) return Error.ShapeMismatch;
        var sum_result: f32 = 0.0;
        var i: usize = 0;
        while (i < self.shape.dims[0]) : (i += 1) {
            sum_result += try self.get(&.{i}) * try other.get(&.{i});
        }
        return sum_result;
    }

    pub fn outer(allocator: Allocator, a: *const Tensor, b: *const Tensor) !Tensor {
        if (a.shape.dims.len != 1 or b.shape.dims.len != 1) return Error.ShapeMismatch;
        const m = a.shape.dims[0];
        const n = b.shape.dims[0];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var result = try init(allocator, &.{ m, n });
        var i: usize = 0;
        while (i < m) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                try result.set(&.{ i, j }, try a.get(&.{i}) * try b.get(&.{j}));
            }
        }
        return result;
    }

    pub fn trace(self: *const Tensor) !f32 {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        var sum_result: f32 = 0.0;
        const n = self.shape.dims[0];
        var i: usize = 0;
        while (i < n) : (i += 1) {
            sum_result += try self.get(&.{ i, i });
        }
        return sum_result;
    }

    pub fn norm(self: *const Tensor, order: f32) !f32 {
        if (order <= 0.0) return Error.InvalidShape;
        var total: f32 = 0.0;
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const len = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < len) : (flat += 1) {
            const val = try self.get(indices);
            total += math.pow(f32, @abs(val), order);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return math.pow(f32, total, 1.0 / order);
    }

    pub fn inverse(self: *const Tensor, allocator: Allocator) !Tensor {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        var aug = try init(allocator, &.{ n, 2 * n });
        defer aug.deinit();
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                try aug.set(&.{ i, j }, try self.get(&.{ i, j }));
            }
            try aug.set(&.{ i, i + n }, 1.0);
        }
        i = 0;
        while (i < n) : (i += 1) {
            var pivot_row = i;
            var max_val = @abs(try aug.get(&.{ i, i }));
            var r: usize = i + 1;
            while (r < n) : (r += 1) {
                const val = @abs(try aug.get(&.{ r, i }));
                if (val > max_val) {
                    max_val = val;
                    pivot_row = r;
                }
            }
            if (max_val == 0.0) return Error.SingularMatrix;
            if (pivot_row != i) {
                var j: usize = 0;
                while (j < 2 * n) : (j += 1) {
                    const temp = try aug.get(&.{ i, j });
                    try aug.set(&.{ i, j }, try aug.get(&.{ pivot_row, j }));
                    try aug.set(&.{ pivot_row, j }, temp);
                }
            }
            
            const pivotVal = try aug.get(&.{ i, i });
            var j: usize = 0;
            while (j < 2 * n) : (j += 1) {
                try aug.set(&.{ i, j }, try aug.get(&.{ i, j }) / pivotVal);
            }
            var row: usize = 0;
            while (row < n) : (row += 1) {
                if (row == i) continue;
                const factor = try aug.get(&.{ row, i });
                j = 0;
                while (j < 2 * n) : (j += 1) {
                    try aug.set(&.{ row, j }, try aug.get(&.{ row, j }) - factor * try aug.get(&.{ i, j }));
                }
            }
        }
        var inv = try init(allocator, &.{ n, n });
        i = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                try inv.set(&.{ i, j }, try aug.get(&.{ i, j + n }));
            }
        }
        return inv;
    }

    pub fn det(self: *const Tensor, allocator: Allocator) !f32 {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return 1.0;
        var mat = try self.copy(allocator);
        defer mat.deinit();
        var det_val: f32 = 1.0;
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var pivot_row = i;
            var max_val = @abs(try mat.get(&.{ i, i }));
            var r: usize = i + 1;
            while (r < n) : (r += 1) {
                const val = @abs(try mat.get(&.{ r, i }));
                if (val > max_val) {
                    max_val = val;
                    pivot_row = r;
                }
            }
            if (max_val == 0.0) return 0.0;
            if (pivot_row != i) {
                var j: usize = 0;
                while (j < n) : (j += 1) {
                    const temp = try mat.get(&.{ i, j });
                    try mat.set(&.{ i, j }, try mat.get(&.{ pivot_row, j }));
                    try mat.set(&.{ pivot_row, j }, temp);
                }
                det_val = -det_val;
            }
            
            const pivotVal = try mat.get(&.{ i, i });
            var row: usize = i + 1;
            while (row < n) : (row += 1) {
                const factor = try mat.get(&.{ row, i }) / pivotVal;
                var j: usize = i;
                while (j < n) : (j += 1) {
                    try mat.set(&.{ row, j }, try mat.get(&.{ row, j }) - factor * try mat.get(&.{ i, j }));
                }
            }
            det_val *= pivotVal;
        }
        return det_val;
    }

    pub fn lu(self: *const Tensor, allocator: Allocator) !struct { p: Tensor, l: Tensor, u: Tensor } {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        var p = try identity(allocator, n);
        var l = try identity(allocator, n);
        var u = try self.copy(allocator);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var pivot_row = i;
            var max_val = @abs(try u.get(&.{ i, i }));
            var r: usize = i + 1;
            while (r < n) : (r += 1) {
                const val = @abs(try u.get(&.{ r, i }));
                if (val > max_val) {
                    max_val = val;
                    pivot_row = r;
                }
            }
            if (max_val == 0.0) continue;
            if (pivot_row != i) {
                var j: usize = 0;
                while (j < n) : (j += 1) {
                    const temp_u = try u.get(&.{ i, j });
                    try u.set(&.{ i, j }, try u.get(&.{ pivot_row, j }));
                    try u.set(&.{ pivot_row, j }, temp_u);
                    
                    const temp_p = try p.get(&.{ i, j });
                    try p.set(&.{ i, j }, try p.get(&.{ pivot_row, j }));
                    try p.set(&.{ pivot_row, j }, temp_p);
                }
                j = 0;
                while (j < i) : (j += 1) {
                    const temp_l = try l.get(&.{ i, j });
                    try l.set(&.{ i, j }, try l.get(&.{ pivot_row, j }));
                    try l.set(&.{ pivot_row, j }, temp_l);
                }
            }
            
            const pivot = try u.get(&.{ i, i });
            var j: usize = i + 1;
            while (j < n) : (j += 1) {
                const factor = try u.get(&.{ j, i }) / pivot;
                try l.set(&.{ j, i }, factor);
                var k: usize = i;
                while (k < n) : (k += 1) {
                    try u.set(&.{ j, k }, try u.get(&.{ j, k }) - factor * try u.get(&.{ i, k }));
                }
            }
        }
        return .{ .p = p, .l = l, .u = u };
    }

    pub fn qr(self: *const Tensor, allocator: Allocator) !struct { q: Tensor, r: Tensor } {
        if (self.shape.dims.len != 2) return Error.MustBeSquare;
        const m = self.shape.dims[0];
        const n = self.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var q = try identity(allocator, m);
        var r = try self.copy(allocator);
        const k_limit = @min(m, n);
        var j: usize = 0;
        while (j < k_limit) : (j += 1) {
            var norm_sq: f32 = 0.0;
            var i: usize = j;
            while (i < m) : (i += 1) {
                const val = try r.get(&.{ i, j });
                norm_sq += val * val;
            }
            const norm_val = @sqrt(norm_sq);
            if (norm_val < 1e-12) continue;
            const sign: f32 = if (try r.get(&.{ j, j }) < 0.0) -1.0 else 1.0;
            const alpha = -(sign * norm_val);
            var vArr = try allocator.alloc(f32, m);
            defer allocator.free(vArr);
            i = 0;
            while (i < m) : (i += 1) {
                if (i < j) {
                    vArr[i] = 0.0;
                } else if (i == j) {
                    vArr[i] = try r.get(&.{ i, j }) - alpha;
                } else {
                    vArr[i] = try r.get(&.{ i, j });
                }
            }
            var v_norm_sq: f32 = 0.0;
            for (vArr) |v| v_norm_sq += v * v;
            if (v_norm_sq < 1e-24) continue;
            const tau = 2.0 / v_norm_sq;
            var c: usize = 0;
            while (c < n) : (c += 1) {
                var dot_v_col: f32 = 0.0;
                i = 0;
                while (i < m) : (i += 1) dot_v_col += vArr[i] * try r.get(&.{ i, c });
                i = 0;
                while (i < m) : (i += 1) try r.set(&.{ i, c }, try r.get(&.{ i, c }) - tau * vArr[i] * dot_v_col);
            }
            var row: usize = 0;
            while (row < m) : (row += 1) {
                var dot_q_v: f32 = 0.0;
                i = 0;
                while (i < m) : (i += 1) dot_q_v += try q.get(&.{ row, i }) * vArr[i];
                i = 0;
                while (i < m) : (i += 1) try q.set(&.{ row, i }, try q.get(&.{ row, i }) - tau * dot_q_v * vArr[i]);
            }
        }
        return .{ .q = q, .r = r };
    }

    pub fn svd(self: *const Tensor, allocator: Allocator) !struct { u: Tensor, s: Tensor, v: Tensor } {
        if (self.shape.dims.len != 2) return Error.MustBeSquare;
        const m = self.shape.dims[0];
        const n = self.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        
        var a = try self.copy(allocator);
        defer a.deinit();
        var v = try identity(allocator, n);
        
        const max_iter = 100;
        const tol = 1e-6;
        var iter: usize = 0;
        while (iter < max_iter) : (iter += 1) {
            var changed = false;
            var i: usize = 0;
            while (i < n - 1) : (i += 1) {
                var j: usize = i + 1;
                while (j < n) : (j += 1) {
                    var a_ii: f32 = 0.0;
                    var a_jj: f32 = 0.0;
                    var a_ij: f32 = 0.0;
                    var k: usize = 0;
                    while (k < m) : (k += 1) {
                        const aki = try a.get(&.{ k, i });
                        const akj = try a.get(&.{ k, j });
                        a_ii += aki * aki;
                        a_jj += akj * akj;
                        a_ij += aki * akj;
                    }
                    if (@abs(a_ij) > tol) {
                        changed = true;
                        const tau = (a_jj - a_ii) / (2.0 * a_ij);
                        const t = if (tau >= 0.0) 1.0 / (tau + @sqrt(1.0 + tau * tau)) else -1.0 / (-tau + @sqrt(1.0 + tau * tau));
                        const c = 1.0 / @sqrt(1.0 + t * t);
                        const s_val = t * c;
                        
                        k = 0;
                        while (k < m) : (k += 1) {
                            const aki = try a.get(&.{ k, i });
                            const akj = try a.get(&.{ k, j });
                            try a.set(&.{ k, i }, c * aki - s_val * akj);
                            try a.set(&.{ k, j }, s_val * aki + c * akj);
                        }
                        k = 0;
                        while (k < n) : (k += 1) {
                            const vki = try v.get(&.{ k, i });
                            const vkj = try v.get(&.{ k, j });
                            try v.set(&.{ k, i }, c * vki - s_val * vkj);
                            try v.set(&.{ k, j }, s_val * vki + c * vkj);
                        }
                    }
                }
            }
            if (!changed) break;
        }
        
        const k_dim = @min(m, n);
        var s = try init(allocator, &.{k_dim});
        var u = try init(allocator, &.{ m, k_dim });
        
        var i: usize = 0;
        while (i < k_dim) : (i += 1) {
            var norm_sq: f32 = 0.0;
            var k: usize = 0;
            while (k < m) : (k += 1) {
                const val = try a.get(&.{ k, i });
                norm_sq += val * val;
            }
            const sigma = @sqrt(norm_sq);
            try s.set(&.{i}, sigma);
            
            k = 0;
            while (k < m) : (k += 1) {
                if (sigma > 1e-10) {
                    try u.set(&.{ k, i }, try a.get(&.{ k, i }) / sigma);
                } else {
                    try u.set(&.{ k, i }, 0.0);
                }
            }
        }
        
        return .{ .u = u, .s = s, .v = v };
    }

    pub fn eig(self: *const Tensor, allocator: Allocator) !struct { vals: Tensor, vecs: Tensor } {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        
        var a = try self.copy(allocator);
        defer a.deinit();
        var vecs = try identity(allocator, n);
        
        const max_iter = 100;
        const tol = 1e-6;
        var iter: usize = 0;
        while (iter < max_iter) : (iter += 1) {
            var changed = false;
            var i: usize = 0;
            while (i < n - 1) : (i += 1) {
                var j: usize = i + 1;
                while (j < n) : (j += 1) {
                    const a_ij = try a.get(&.{ i, j });
                    if (@abs(a_ij) > tol) {
                        changed = true;
                        const a_ii = try a.get(&.{ i, i });
                        const a_jj = try a.get(&.{ j, j });
                        const tau = (a_jj - a_ii) / (2.0 * a_ij);
                        const t = if (tau >= 0.0) 1.0 / (tau + @sqrt(1.0 + tau * tau)) else -1.0 / (-tau + @sqrt(1.0 + tau * tau));
                        const c = 1.0 / @sqrt(1.0 + t * t);
                        const s_val = t * c;
                        
                        var k: usize = 0;
                        while (k < n) : (k += 1) {
                            if (k != i and k != j) {
                                const aki = try a.get(&.{ k, i });
                                const akj = try a.get(&.{ k, j });
                                try a.set(&.{ k, i }, c * aki - s_val * akj);
                                try a.set(&.{ i, k }, c * aki - s_val * akj);
                                try a.set(&.{ k, j }, s_val * aki + c * akj);
                                try a.set(&.{ j, k }, s_val * aki + c * akj);
                            }
                        }
                        try a.set(&.{ i, i }, a_ii - t * a_ij);
                        try a.set(&.{ j, j }, a_jj + t * a_ij);
                        try a.set(&.{ i, j }, 0.0);
                        try a.set(&.{ j, i }, 0.0);
                        
                        k = 0;
                        while (k < n) : (k += 1) {
                            const vki = try vecs.get(&.{ k, i });
                            const vkj = try vecs.get(&.{ k, j });
                            try vecs.set(&.{ k, i }, c * vki - s_val * vkj);
                            try vecs.set(&.{ k, j }, s_val * vki + c * vkj);
                        }
                    }
                }
            }
            if (!changed) break;
        }
        
        var vals = try init(allocator, &.{n});
        var i: usize = 0;
        while (i < n) : (i += 1) {
            try vals.set(&.{i}, try a.get(&.{ i, i }));
        }
        
        return .{ .vals = vals, .vecs = vecs };
    }

    pub fn cholesky(self: *const Tensor, allocator: Allocator) !Tensor {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        var l = try init(allocator, self.shape.dims);
        try l.fill(0.0);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < i + 1) : (j += 1) {
                var sum_result: f32 = 0.0;
                var k: usize = 0;
                while (k < j) : (k += 1) {
                    sum_result += try l.get(&.{ i, k }) * try l.get(&.{ j, k });
                }
                if (i == j) {
                    const diff = try self.get(&.{ i, j }) - sum_result;
                    if (diff <= 0.0) return Error.SingularMatrix;
                    try l.set(&.{ i, j }, @sqrt(diff));
                } else {
                    const diagJ = try l.get(&.{ j, j });
                    if (diagJ == 0.0) return Error.SingularMatrix;
                    try l.set(&.{ i, j }, (try self.get(&.{ i, j }) - sum_result) / diagJ);
                }
            }
        }
        return l;
    }

    pub fn solve(self: *const Tensor, b: *const Tensor, allocator: Allocator) !Tensor {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (b.shape.dims.len != 1 or b.shape.dims[0] != n) return Error.ShapeMismatch;
        if (n == 0) return Error.InvalidShape;
        const lu_result = try self.lu(allocator);
        defer lu_result.p.deinit();
        defer lu_result.l.deinit();
        defer lu_result.u.deinit();
        
        var pb = try init(allocator, &.{n});
        defer pb.deinit();
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var sum_val: f32 = 0.0;
            var j: usize = 0;
            while (j < n) : (j += 1) {
                sum_val += try lu_result.p.get(&.{ i, j }) * try b.get(&.{j});
            }
            try pb.set(&.{i}, sum_val);
        }
        
        var y = try init(allocator, &.{n});
        defer y.deinit();
        i = 0;
        while (i < n) : (i += 1) {
            var sum_val: f32 = 0.0;
            var j: usize = 0;
            while (j < i) : (j += 1) {
                sum_val += try lu_result.l.get(&.{ i, j }) * try y.get(&.{j});
            }
            try y.set(&.{i}, try pb.get(&.{i}) - sum_val);
        }
        
        var x = try init(allocator, &.{n});
        var ri: isize = @as(isize, @intCast(n)) - 1;
        while (ri >= 0) : (ri -= 1) {
            const ui = @as(usize, @intCast(ri));
            var sum_val: f32 = 0.0;
            var j: usize = ui + 1;
            while (j < n) : (j += 1) {
                sum_val += try lu_result.u.get(&.{ ui, j }) * try x.get(&.{j});
            }
            const diag = try lu_result.u.get(&.{ ui, ui });
            if (diag == 0.0) return Error.SingularMatrix;
            try x.set(&.{ui}, (try y.get(&.{ui}) - sum_val) / diag);
        }
        return x;
    }

    pub fn clip(self: *Tensor, min_val: f32, max_val: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = math.clamp(self.data[idx], min_val, max_val);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn toFixed(self: *const Tensor, allocator: Allocator) !Tensor {
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            new_t.data[try new_t.computeIndex(indices)] = @floor(val * 4294967296.0) / 4294967296.0;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    pub fn arange(allocator: Allocator, start: f32, end: f32, step: f32) !Tensor {
        if (step == 0.0) return Error.InvalidShape;
        const size = @as(usize, @intFromFloat(@ceil(@abs((end - start) / step))));
        if (size == 0) return Error.InvalidShape;
        var t = try init(allocator, &.{size});
        var i: usize = 0;
        while (i < size) : (i += 1) {
            try t.set(&.{i}, start + @as(f32, @floatFromInt(i)) * step);
        }
        return t;
    }

    pub fn linspace(allocator: Allocator, start: f32, end: f32, num: usize) !Tensor {
        if (num == 0) return Error.InvalidShape;
        var t = try init(allocator, &.{num});
        var i: usize = 0;
        while (i < num) : (i += 1) {
            if (num == 1) {
                try t.set(&.{i}, start);
            } else {
                const fraction = @as(f32, @floatFromInt(i)) / @as(f32, @floatFromInt(num - 1));
                try t.set(&.{i}, start + fraction * (end - start));
            }
        }
        return t;
    }
};

test "Tensor init and basic operations" {
    const allocator = std.testing.allocator;
    
    var t = try Tensor.init(allocator, &.{ 2, 3 });
    defer t.deinit();
    
    try std.testing.expectEqual(@as(usize, 2), t.shape.dims[0]);
    try std.testing.expectEqual(@as(usize, 3), t.shape.dims[1]);
    
    try t.set(&.{ 0, 0 }, 1.0);
    try t.set(&.{ 0, 1 }, 2.0);
    try t.set(&.{ 0, 2 }, 3.0);
    try t.set(&.{ 1, 0 }, 4.0);
    try t.set(&.{ 1, 1 }, 5.0);
    try t.set(&.{ 1, 2 }, 6.0);
    
    try std.testing.expectApproxEqAbs(@as(f32, 1.0), try t.get(&.{ 0, 0 }), 1e-6);
    try std.testing.expectApproxEqAbs(@as(f32, 6.0), try t.get(&.{ 1, 2 }), 1e-6);
}

test "Tensor operations" {
    const allocator = std.testing.allocator;
    
    var a = try Tensor.init(allocator, &.{ 2, 2 });
    defer a.deinit();
    
    try a.fill(2.0);
    try std.testing.expectApproxEqAbs(@as(f32, 2.0), try a.get(&.{ 0, 0 }), 1e-6);
    
    try a.addScalar(3.0);
    try std.testing.expectApproxEqAbs(@as(f32, 5.0), try a.get(&.{ 0, 0 }), 1e-6);
    
    try a.mulScalar(2.0);
    try std.testing.expectApproxEqAbs(@as(f32, 10.0), try a.get(&.{ 0, 0 }), 1e-6);
}

test "Tensor view and reshape" {
    const allocator = std.testing.allocator;
    
    var t = try Tensor.init(allocator, &.{ 2, 3 });
    defer t.deinit();
    
    var i: usize = 0;
    while (i < 6) : (i += 1) {
        try t.set(&.{ i / 3, i % 3 }, @floatFromInt(i));
    }
    
    var v = try t.view(&.{ 3, 2 });
    defer v.deinit();
    
    try std.testing.expectApproxEqAbs(@as(f32, 0.0), try v.get(&.{ 0, 0 }), 1e-6);
    try std.testing.expectApproxEqAbs(@as(f32, 5.0), try v.get(&.{ 2, 1 }), 1e-6);
}

test "Tensor matmul" {
    const allocator = std.testing.allocator;
    
    var a = try Tensor.init(allocator, &.{ 2, 3 });
    defer a.deinit();
    
    try a.set(&.{ 0, 0 }, 1.0);
    try a.set(&.{ 0, 1 }, 2.0);
    try a.set(&.{ 0, 2 }, 3.0);
    try a.set(&.{ 1, 0 }, 4.0);
    try a.set(&.{ 1, 1 }, 5.0);
    try a.set(&.{ 1, 2 }, 6.0);
    
    var b = try Tensor.init(allocator, &.{ 3, 2 });
    defer b.deinit();
    
    try b.set(&.{ 0, 0 }, 7.0);
    try b.set(&.{ 0, 1 }, 8.0);
    try b.set(&.{ 1, 0 }, 9.0);
    try b.set(&.{ 1, 1 }, 10.0);
    try b.set(&.{ 2, 0 }, 11.0);
    try b.set(&.{ 2, 1 }, 12.0);
    
    var c = try Tensor.matmul(&a, &b, allocator);
    defer c.deinit();
    
    try std.testing.expectApproxEqAbs(@as(f32, 58.0), try c.get(&.{ 0, 0 }), 1e-5);
    try std.testing.expectApproxEqAbs(@as(f32, 64.0), try c.get(&.{ 0, 1 }), 1e-5);
    try std.testing.expectApproxEqAbs(@as(f32, 139.0), try c.get(&.{ 1, 0 }), 1e-5);
    try std.testing.expectApproxEqAbs(@as(f32, 154.0), try c.get(&.{ 1, 1 }), 1e-5);
}

test "Tensor inverse and det" {
    const allocator = std.testing.allocator;
    
    var t = try Tensor.init(allocator, &.{ 2, 2 });
    defer t.deinit();
    
    try t.set(&.{ 0, 0 }, 4.0);
    try t.set(&.{ 0, 1 }, 7.0);
    try t.set(&.{ 1, 0 }, 2.0);
    try t.set(&.{ 1, 1 }, 6.0);
    
    const det_val = try t.det(allocator);
    try std.testing.expectApproxEqAbs(@as(f32, 10.0), det_val, 1e-5);
    
    var inv = try t.inverse(allocator);
    defer inv.deinit();
    
    try std.testing.expectApproxEqAbs(@as(f32, 0.6), try inv.get(&.{ 0, 0 }), 1e-5);
    try std.testing.expectApproxEqAbs(@as(f32, -0.7), try inv.get(&.{ 0, 1 }), 1e-5);
    try std.testing.expectApproxEqAbs(@as(f32, -0.2), try inv.get(&.{ 1, 0 }), 1e-5);
    try std.testing.expectApproxEqAbs(@as(f32, 0.4), try inv.get(&.{ 1, 1 }), 1e-5);
}
