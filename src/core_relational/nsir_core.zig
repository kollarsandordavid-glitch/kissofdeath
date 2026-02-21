const std = @import("std");

const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;
const StringHashMap = std.StringHashMap;
const Sha256 = std.crypto.hash.sha2.Sha256;
const Complex = std.math.Complex;
const core_types = @import("../core/types.zig");
const core_tensor = @import("../core/tensor.zig");
const core_memory = @import("../core/memory.zig");

pub const EdgeQuality = enum(u8) {
    superposition = 0,
    entangled = 1,
    coherent = 2,
    collapsed = 3,
    fractal = 4,

    pub fn toString(self: EdgeQuality) []const u8 {
        return switch (self) {
            .superposition => "superposition",
            .entangled => "entangled",
            .coherent => "coherent",
            .collapsed => "collapsed",
            .fractal => "fractal",
        };
    }

    pub fn fromString(s: []const u8) ?EdgeQuality {
        if (std.mem.eql(u8, s, "superposition")) return .superposition;
        if (std.mem.eql(u8, s, "entangled")) return .entangled;
        if (std.mem.eql(u8, s, "coherent")) return .coherent;
        if (std.mem.eql(u8, s, "collapsed")) return .collapsed;
        if (std.mem.eql(u8, s, "fractal")) return .fractal;
        return null;
    }
};

fn dupeBytes(allocator: Allocator, b: []const u8) ![]u8 {
    return try allocator.dupe(u8, b);
}

fn freeMapStringBytes(map: *StringHashMap([]u8), allocator: Allocator) void {
    var it = map.iterator();
    while (it.next()) |e| {
        allocator.free(e.key_ptr.*);
        allocator.free(e.value_ptr.*);
    }
    map.deinit();
}

fn putOwnedStringBytes(map: *StringHashMap([]u8), allocator: Allocator, key: []const u8, value: []const u8) !void {
    if (map.fetchRemove(key)) |removed| {
        allocator.free(removed.key);
        allocator.free(removed.value);
    }
    const k = try allocator.dupe(u8, key);
    errdefer allocator.free(k);
    const v = try allocator.dupe(u8, value);
    errdefer allocator.free(v);
    map.put(k, v) catch |err| {
        allocator.free(k);
        allocator.free(v);
        return err;
    };
}

pub const Qubit = struct {
    a: Complex(f64),
    b: Complex(f64),

    pub fn init(a: Complex(f64), b: Complex(f64)) Qubit {
        var q = Qubit{ .a = a, .b = b };
        q.normalizeInPlace();
        return q;
    }

    pub fn initBasis0() Qubit {
        return Qubit{ .a = Complex(f64).init(1.0, 0.0), .b = Complex(f64).init(0.0, 0.0) };
    }

    pub fn initBasis1() Qubit {
        return Qubit{ .a = Complex(f64).init(0.0, 0.0), .b = Complex(f64).init(1.0, 0.0) };
    }

    pub fn normSquared(self: Qubit) f64 {
        return (self.a.re * self.a.re + self.a.im * self.a.im) + (self.b.re * self.b.re + self.b.im * self.b.im);
    }

    pub fn normalizeInPlace(self: *Qubit) void {
        const ns = self.normSquared();
        if (!(ns > 0.0) or std.math.isNan(ns) or std.math.isInf(ns)) {
            self.* = Qubit.initBasis0();
            return;
        }
        const inv = 1.0 / std.math.sqrt(ns);
        const s = Complex(f64).init(inv, 0.0);
        self.a = self.a.mul(s);
        self.b = self.b.mul(s);
    }

    pub fn prob0(self: Qubit) f64 {
        return std.math.clamp(self.a.re * self.a.re + self.a.im * self.a.im, 0.0, 1.0);
    }

    pub fn prob1(self: Qubit) f64 {
        return std.math.clamp(self.b.re * self.b.re + self.b.im * self.b.im, 0.0, 1.0);
    }
};

pub const Node = struct {
    id: []u8,
    data: []u8,
    qubit: Qubit,
    phase: f64,
    metadata: StringHashMap([]u8),
    allocator: Allocator,

    pub fn init(allocator: Allocator, id: []const u8, data: []const u8, qubit: Qubit, phase: f64) !Node {
        return Node{
            .id = try dupeBytes(allocator, id),
            .data = try dupeBytes(allocator, data),
            .qubit = qubit,
            .phase = phase,
            .metadata = StringHashMap([]u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Node) void {
        self.allocator.free(self.id);
        self.allocator.free(self.data);
        freeMapStringBytes(&self.metadata, self.allocator);
    }

    pub fn clone(self: *const Node, allocator: Allocator) !Node {
        var n = Node{
            .id = try dupeBytes(allocator, self.id),
            .data = try dupeBytes(allocator, self.data),
            .qubit = self.qubit,
            .phase = self.phase,
            .metadata = StringHashMap([]u8).init(allocator),
            .allocator = allocator,
        };
        errdefer {
            allocator.free(n.id);
            allocator.free(n.data);
            freeMapStringBytes(&n.metadata, allocator);
        }

        var it = self.metadata.iterator();
        while (it.next()) |e| {
            const k = try dupeBytes(allocator, e.key_ptr.*);
            const v = try dupeBytes(allocator, e.value_ptr.*);
            n.metadata.put(k, v) catch |err| {
                allocator.free(k);
                allocator.free(v);
                return err;
            };
        }

        return n;
    }

    pub fn setMetadata(self: *Node, key: []const u8, value: []const u8) !void {
        try putOwnedStringBytes(&self.metadata, self.allocator, key, value);
    }

    pub fn getMetadata(self: *const Node, key: []const u8) ?[]const u8 {
        return self.metadata.get(key);
    }
};

pub const Edge = struct {
    source: []const u8,
    target: []const u8,
    quality: EdgeQuality,
    weight: f64,
    quantum_correlation: Complex(f64),
    fractal_dimension: f64,
    metadata: StringHashMap([]u8),
    allocator: Allocator,

    pub fn init(
        allocator: Allocator,
        source: []const u8,
        target: []const u8,
        quality: EdgeQuality,
        weight: f64,
        quantum_correlation: Complex(f64),
        fractal_dimension: f64,
    ) Edge {
        return Edge{
            .source = source,
            .target = target,
            .quality = quality,
            .weight = weight,
            .quantum_correlation = quantum_correlation,
            .fractal_dimension = fractal_dimension,
            .metadata = StringHashMap([]u8).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Edge) void {
        freeMapStringBytes(&self.metadata, self.allocator);
    }

    pub fn clone(self: *const Edge, allocator: Allocator) !Edge {
        var e = Edge{
            .source = self.source,
            .target = self.target,
            .quality = self.quality,
            .weight = self.weight,
            .quantum_correlation = self.quantum_correlation,
            .fractal_dimension = self.fractal_dimension,
            .metadata = StringHashMap([]u8).init(allocator),
            .allocator = allocator,
        };
        errdefer freeMapStringBytes(&e.metadata, allocator);

        var it = self.metadata.iterator();
        while (it.next()) |entry| {
            const k = try dupeBytes(allocator, entry.key_ptr.*);
            const v = try dupeBytes(allocator, entry.value_ptr.*);
            e.metadata.put(k, v) catch |err| {
                allocator.free(k);
                allocator.free(v);
                return err;
            };
        }

        return e;
    }

    pub fn setMetadata(self: *Edge, key: []const u8, value: []const u8) !void {
        try putOwnedStringBytes(&self.metadata, self.allocator, key, value);
    }

    pub fn getMetadata(self: *const Edge, key: []const u8) ?[]const u8 {
        return self.metadata.get(key);
    }

    pub fn correlationMagnitude(self: *const Edge) f64 {
        const qc = self.quantum_correlation;
        return @sqrt(qc.re * qc.re + qc.im * qc.im);
    }
};

pub const EdgeKey = struct {
    source: []const u8,
    target: []const u8,
};

fn hashSlice(h: *std.hash.Wyhash, s: []const u8) void {
    var len_buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &len_buf, @as(u64, @intCast(s.len)), .Little);
    h.update(&len_buf);
    h.update(s);
}

pub const EdgeKeyContext = struct {
    pub fn hash(_: @This(), k: EdgeKey) u64 {
        var h = std.hash.Wyhash.init(0);
        hashSlice(&h, k.source);
        hashSlice(&h, k.target);
        return h.final();
    }

    pub fn eql(_: @This(), a: EdgeKey, b: EdgeKey) bool {
        return std.mem.eql(u8, a.source, b.source) and std.mem.eql(u8, a.target, b.target);
    }
};

pub const PairKey = struct {
    a: []const u8,
    b: []const u8,
};

pub const PairKeyContext = struct {
    pub fn hash(_: @This(), k: PairKey) u64 {
        var h = std.hash.Wyhash.init(1);
        hashSlice(&h, k.a);
        hashSlice(&h, k.b);
        return h.final();
    }

    pub fn eql(_: @This(), x: PairKey, y: PairKey) bool {
        return std.mem.eql(u8, x.a, y.a) and std.mem.eql(u8, x.b, y.b);
    }
};

pub const TwoQubit = struct {
    amps: [4]Complex(f64),

    pub fn initBellPhiPlus() TwoQubit {
        const inv_sqrt2 = 1.0 / std.math.sqrt(2.0);
        return TwoQubit{
            .amps = .{
                Complex(f64).init(inv_sqrt2, 0.0),
                Complex(f64).init(0.0, 0.0),
                Complex(f64).init(0.0, 0.0),
                Complex(f64).init(inv_sqrt2, 0.0),
            },
        };
    }
};

pub const Gate = *const fn (q: Qubit) Qubit;

pub fn hadamardGate(q: Qubit) Qubit {
    const inv_sqrt2 = 1.0 / std.math.sqrt(2.0);
    const s = Complex(f64).init(inv_sqrt2, 0.0);
    const a = q.a.add(q.b).mul(s);
    const b = q.a.sub(q.b).mul(s);
    return Qubit.init(a, b);
}

pub fn pauliXGate(q: Qubit) Qubit {
    return Qubit.init(q.b, q.a);
}

pub fn pauliYGate(q: Qubit) Qubit {
    const i = Complex(f64).init(0.0, 1.0);
    const minus_i = Complex(f64).init(0.0, -1.0);
    return Qubit.init(minus_i.mul(q.b), i.mul(q.a));
}

pub fn pauliZGate(q: Qubit) Qubit {
    return Qubit.init(q.a, q.b.mul(Complex(f64).init(-1.0, 0.0)));
}

pub fn identityGate(q: Qubit) Qubit {
    return q;
}

pub fn phaseGate(comptime phase: f64) Gate {
    const S = struct {
        const c_val = std.math.cos(phase);
        const s_val = std.math.sin(phase);
        fn apply(q: Qubit) Qubit {
            const factor = Complex(f64).init(c_val, s_val);
            return Qubit.init(q.a, q.b.mul(factor));
        }
    };
    return &S.apply;
}

fn floatBits(v: f64) u64 {
    return @as(u64, @bitCast(v));
}

const EdgeMap = std.HashMap(EdgeKey, ArrayList(Edge), EdgeKeyContext, std.hash_map.default_max_load_percentage);
const EntMap = std.HashMap(PairKey, TwoQubit, PairKeyContext, std.hash_map.default_max_load_percentage);

pub const SelfSimilarRelationalGraph = struct {
    allocator: Allocator,
    nodes: StringHashMap(Node),
    edges: EdgeMap,
    entanglements: EntMap,
    quantum_register: StringHashMap(Qubit),
    topology_hash: [65]u8,
    rng: std.rand.DefaultPrng,

    pub fn init(allocator: Allocator) !SelfSimilarRelationalGraph {
        const ts = std.time.nanoTimestamp();
        const seed: u64 = std.hash.Wyhash.hash(0, std.mem.asBytes(&ts));
        var g = SelfSimilarRelationalGraph{
            .allocator = allocator,
            .nodes = StringHashMap(Node).init(allocator),
            .edges = EdgeMap.init(allocator),
            .entanglements = EntMap.init(allocator),
            .quantum_register = StringHashMap(Qubit).init(allocator),
            .topology_hash = [_]u8{0} ** 65,
            .rng = std.rand.DefaultPrng.init(seed),
        };
        try g.updateTopologyHash();
        return g;
    }

    pub fn initWithArena(arena: *core_memory.ArenaAllocator) !SelfSimilarRelationalGraph {
        return init(arena.allocator());
    }

    pub fn initWithPool(pool: *core_memory.PoolAllocator) !SelfSimilarRelationalGraph {
        return init(pool.allocator());
    }

    pub fn initWithBuddy(buddy: *core_memory.BuddyAllocator) !SelfSimilarRelationalGraph {
        return init(buddy.allocator());
    }

    pub fn deinit(self: *SelfSimilarRelationalGraph) void {
        var n_it = self.nodes.iterator();
        while (n_it.next()) |e| e.value_ptr.deinit();
        self.nodes.deinit();

        var ed_it = self.edges.iterator();
        while (ed_it.next()) |e| {
            for (e.value_ptr.items) |*edge| edge.deinit();
            e.value_ptr.deinit();
        }
        self.edges.deinit();

        self.entanglements.deinit();

        var qr_it = self.quantum_register.iterator();
        while (qr_it.next()) |e| self.allocator.free(e.key_ptr.*);
        self.quantum_register.deinit();
    }

    fn canonicalIdPtr(self: *SelfSimilarRelationalGraph, id: []const u8) ?[]const u8 {
        if (self.nodes.getPtr(id)) |n| return n.id;
        return null;
    }

    pub fn addNode(self: *SelfSimilarRelationalGraph, node_in: Node) !void {
        var node = node_in;
        const incoming_id = node.id;

        if (self.nodes.getPtr(incoming_id)) |existing| {
            self.allocator.free(existing.data);
            existing.data = try dupeBytes(self.allocator, node.data);
            existing.qubit = node.qubit;
            existing.phase = node.phase;

            freeMapStringBytes(&existing.metadata, self.allocator);
            existing.metadata = StringHashMap([]u8).init(self.allocator);

            var it = node.metadata.iterator();
            while (it.next()) |m| {
                const k = try dupeBytes(self.allocator, m.key_ptr.*);
                const v = try dupeBytes(self.allocator, m.value_ptr.*);
                existing.metadata.put(k, v) catch |err| {
                    self.allocator.free(k);
                    self.allocator.free(v);
                    return err;
                };
            }

            node.deinit();
        } else {
            try self.nodes.put(node.id, node);
        }

        if (self.quantum_register.fetchRemove(incoming_id)) |removed| self.allocator.free(removed.key);
        const qr_key = try dupeBytes(self.allocator, incoming_id);
        errdefer self.allocator.free(qr_key);
        const q = self.nodes.get(incoming_id).?.qubit;
        try self.quantum_register.put(qr_key, q);

        try self.updateTopologyHash();
    }

    pub fn addEdge(self: *SelfSimilarRelationalGraph, source: []const u8, target: []const u8, edge_in: Edge) !void {
        const s = self.canonicalIdPtr(source) orelse return error.SourceNodeNotFound;
        const t = self.canonicalIdPtr(target) orelse return error.TargetNodeNotFound;

        var edge = edge_in;
        defer edge.deinit();

        var stored = try edge.clone(self.allocator);
        stored.source = s;
        stored.target = t;

        const key = EdgeKey{ .source = s, .target = t };
        var gop = try self.edges.getOrPut(key);
        if (!gop.found_existing) gop.value_ptr.* = ArrayList(Edge).init(self.allocator);

        gop.value_ptr.append(stored) catch |err| {
            stored.deinit();
            if (!gop.found_existing and gop.value_ptr.items.len == 0) {
                gop.value_ptr.deinit();
                _ = self.edges.remove(key);
            }
            return err;
        };

        try self.updateTopologyHash();
    }

    pub fn getNode(self: *SelfSimilarRelationalGraph, node_id: []const u8) ?*Node {
        return self.nodes.getPtr(node_id);
    }

    pub fn getNodeConst(self: *const SelfSimilarRelationalGraph, node_id: []const u8) ?*const Node {
        return self.nodes.getPtr(node_id);
    }

    pub fn getEdgesConst(self: *const SelfSimilarRelationalGraph, source: []const u8, target: []const u8) ?[]const Edge {
        const key = EdgeKey{ .source = source, .target = target };
        if (self.edges.getPtr(key)) |list| return list.items;
        return null;
    }

    pub fn clear(self: *SelfSimilarRelationalGraph) !void {
        var n_it = self.nodes.iterator();
        while (n_it.next()) |e| e.value_ptr.deinit();
        self.nodes.clearRetainingCapacity();

        var ed_it = self.edges.iterator();
        while (ed_it.next()) |e| {
            for (e.value_ptr.items) |*edge| edge.deinit();
            e.value_ptr.deinit();
        }
        self.edges.clearRetainingCapacity();

        self.entanglements.clearRetainingCapacity();

        var qr_it = self.quantum_register.iterator();
        while (qr_it.next()) |e| self.allocator.free(e.key_ptr.*);
        self.quantum_register.clearRetainingCapacity();

        try self.updateTopologyHash();
    }

    pub fn setQuantumState(self: *SelfSimilarRelationalGraph, node_id: []const u8, q: Qubit) !void {
        const n = self.nodes.getPtr(node_id) orelse return error.NodeNotFound;
        n.qubit = q;

        if (self.quantum_register.getPtr(node_id)) |qptr| {
            qptr.* = q;
        } else {
            const k = try dupeBytes(self.allocator, node_id);
            errdefer self.allocator.free(k);
            try self.quantum_register.put(k, q);
        }

        try self.updateTopologyHash();
    }

    pub fn getQuantumState(self: *const SelfSimilarRelationalGraph, node_id: []const u8) ?Qubit {
        return self.quantum_register.get(node_id);
    }

    pub fn applyQuantumGate(self: *SelfSimilarRelationalGraph, node_id: []const u8, gate: Gate) !void {
        const n = self.nodes.getPtr(node_id) orelse return error.NodeNotFound;
        n.qubit = gate(n.qubit);
        if (self.quantum_register.getPtr(node_id)) |qptr| qptr.* = n.qubit;
        try self.updateTopologyHash();
    }

    pub fn entangleNodes(self: *SelfSimilarRelationalGraph, a_id: []const u8, b_id: []const u8) !void {
        const a = self.canonicalIdPtr(a_id) orelse return error.NodeNotFound;
        const b = self.canonicalIdPtr(b_id) orelse return error.NodeNotFound;

        const pk = if (std.mem.lessThan(u8, a, b)) PairKey{ .a = a, .b = b } else PairKey{ .a = b, .b = a };
        try self.entanglements.put(pk, TwoQubit.initBellPhiPlus());

        const edge_ab = Edge.init(self.allocator, a, b, .entangled, 1.0, Complex(f64).init(1.0, 0.0), 0.0);
        const edge_ba = Edge.init(self.allocator, b, a, .entangled, 1.0, Complex(f64).init(1.0, 0.0), 0.0);
        try self.addEdge(a, b, edge_ab);
        try self.addEdge(b, a, edge_ba);
    }

    pub fn measure(self: *SelfSimilarRelationalGraph, node_id: []const u8) !u1 {
        _ = self.canonicalIdPtr(node_id) orelse return error.NodeNotFound;

        var hit_key: ?PairKey = null;
        var hit_val: ?TwoQubit = null;

        var it = self.entanglements.iterator();
        while (it.next()) |e| {
            if (std.mem.eql(u8, e.key_ptr.*.a, node_id) or std.mem.eql(u8, e.key_ptr.*.b, node_id)) {
                hit_key = e.key_ptr.*;
                hit_val = e.value_ptr.*;
                break;
            }
        }

        if (hit_key) |pk| {
            const state = hit_val.?;
            const r = self.rng.random().float(f64);
            var cum: f64 = 0.0;
            var outcome: usize = 0;
            var amp_idx: usize = 0;
            while (amp_idx < state.amps.len) : (amp_idx += 1) {
                const amp = state.amps[amp_idx];
                cum += amp.re * amp.re + amp.im * amp.im;
                if (r <= cum) {
                    outcome = amp_idx;
                    break;
                }
            }

            const a_id = pk.a;
            const b_id = pk.b;

            const a_ptr = self.nodes.getPtr(a_id).?;
            const b_ptr = self.nodes.getPtr(b_id).?;

            switch (outcome) {
                0 => { a_ptr.qubit = Qubit.initBasis0(); b_ptr.qubit = Qubit.initBasis0(); },
                1 => { a_ptr.qubit = Qubit.initBasis0(); b_ptr.qubit = Qubit.initBasis1(); },
                2 => { a_ptr.qubit = Qubit.initBasis1(); b_ptr.qubit = Qubit.initBasis0(); },
                else => { a_ptr.qubit = Qubit.initBasis1(); b_ptr.qubit = Qubit.initBasis1(); },
            }

            if (self.quantum_register.getPtr(a_id)) |qa| qa.* = a_ptr.qubit;
            if (self.quantum_register.getPtr(b_id)) |qb| qb.* = b_ptr.qubit;

            _ = self.entanglements.remove(pk);

            const bit: u1 = if (std.mem.eql(u8, node_id, a_id))
                @as(u1, @intCast((outcome >> 1) & 1))
            else
                @as(u1, @intCast(outcome & 1));

            if (self.edges.getPtr(EdgeKey{ .source = a_id, .target = b_id })) |lst| {
                if (lst.items.len > 0) {
                    lst.items[0].quality = .collapsed;
                }
            }
            if (self.edges.getPtr(EdgeKey{ .source = b_id, .target = a_id })) |lst2| {
                if (lst2.items.len > 0) {
                    lst2.items[0].quality = .collapsed;
                }
            }

            try self.updateTopologyHash();
            return bit;
        }

        const n = self.nodes.getPtr(node_id).?;
        const p0 = n.qubit.prob0();
        const r0 = self.rng.random().float(f64);
        const bit: u1 = if (r0 <= p0) 0 else 1;

        n.qubit = if (bit == 0) Qubit.initBasis0() else Qubit.initBasis1();
        if (self.quantum_register.getPtr(node_id)) |qp| qp.* = n.qubit;

        try self.updateTopologyHash();
        return bit;
    }

    pub fn nodeCount(self: *const SelfSimilarRelationalGraph) usize {
        return self.nodes.count();
    }

    pub fn edgeCount(self: *const SelfSimilarRelationalGraph) usize {
        var c: usize = 0;
        var it = self.edges.iterator();
        while (it.next()) |e| c += e.value_ptr.items.len;
        return c;
    }

    pub fn getAllNodeIds(self: *const SelfSimilarRelationalGraph, allocator: Allocator) !ArrayList([]u8) {
        var out = ArrayList([]u8).init(allocator);
        errdefer {
            for (out.items) |id| allocator.free(id);
            out.deinit();
        }
        var it = self.nodes.iterator();
        while (it.next()) |e| {
            const copy = try allocator.dupe(u8, e.value_ptr.id);
            errdefer allocator.free(copy);
            try out.append(copy);
        }
        std.mem.sort([]u8, out.items, {}, struct {
            fn lessThan(_: void, a: []u8, b: []u8) bool {
                return std.mem.lessThan(u8, a, b);
            }
        }.lessThan);
        return out;
    }

    fn shaUpdateU64(h: *Sha256, v: u64) void {
        var b: [8]u8 = undefined;
        std.mem.writeInt(u64, &b, v, .Little);
        h.update(&b);
    }

    fn shaUpdateBytes(h: *Sha256, b: []const u8) void {
        shaUpdateU64(h, @as(u64, @intCast(b.len)));
        h.update(b);
    }

    fn shaUpdateF64(h: *Sha256, v: f64) void {
        shaUpdateU64(h, floatBits(v));
    }

    fn xorDigest(acc: *[Sha256.digest_length]u8, d: *const [Sha256.digest_length]u8) void {
        var i: usize = 0;
        while (i < Sha256.digest_length) : (i += 1) {
            acc[i] ^= d[i];
        }
    }

    fn updateTopologyHash(self: *SelfSimilarRelationalGraph) !void {
        var acc_nodes: [Sha256.digest_length]u8 = [_]u8{0} ** Sha256.digest_length;
        var acc_edges: [Sha256.digest_length]u8 = [_]u8{0} ** Sha256.digest_length;
        var acc_ent: [Sha256.digest_length]u8 = [_]u8{0} ** Sha256.digest_length;

        var node_count: u64 = 0;
        var edgekey_count: u64 = 0;
        var total_edge_count: u64 = 0;
        var ent_count: u64 = 0;

        var n_it = self.nodes.iterator();
        while (n_it.next()) |e| {
            node_count += 1;

            var meta_acc: [Sha256.digest_length]u8 = [_]u8{0} ** Sha256.digest_length;
            var meta_count: u64 = 0;

            var mit = e.value_ptr.metadata.iterator();
            while (mit.next()) |me| {
                meta_count += 1;
                var mh = Sha256.init(.{});
                shaUpdateBytes(&mh, me.key_ptr.*);
                shaUpdateBytes(&mh, me.value_ptr.*);
                var md: [Sha256.digest_length]u8 = undefined;
                mh.final(&md);
                xorDigest(&meta_acc, &md);
            }

            var h = Sha256.init(.{});
            shaUpdateBytes(&h, e.value_ptr.id);
            shaUpdateBytes(&h, e.value_ptr.data);
            shaUpdateF64(&h, e.value_ptr.phase);
            shaUpdateF64(&h, e.value_ptr.qubit.a.re);
            shaUpdateF64(&h, e.value_ptr.qubit.a.im);
            shaUpdateF64(&h, e.value_ptr.qubit.b.re);
            shaUpdateF64(&h, e.value_ptr.qubit.b.im);
            h.update(&meta_acc);
            shaUpdateU64(&h, meta_count);

            var d: [Sha256.digest_length]u8 = undefined;
            h.final(&d);
            xorDigest(&acc_nodes, &d);
        }

        var e_it = self.edges.iterator();
        while (e_it.next()) |kv| {
            edgekey_count += 1;

            var edges_acc: [Sha256.digest_length]u8 = [_]u8{0} ** Sha256.digest_length;
            var edges_count: u64 = 0;

            for (kv.value_ptr.items) |*edge| {
                edges_count += 1;
                total_edge_count += 1;

                var emeta_acc: [Sha256.digest_length]u8 = [_]u8{0} ** Sha256.digest_length;
                var emeta_count: u64 = 0;

                var emi = edge.metadata.iterator();
                while (emi.next()) |me| {
                    emeta_count += 1;
                    var mh = Sha256.init(.{});
                    shaUpdateBytes(&mh, me.key_ptr.*);
                    shaUpdateBytes(&mh, me.value_ptr.*);
                    var md: [Sha256.digest_length]u8 = undefined;
                    mh.final(&md);
                    xorDigest(&emeta_acc, &md);
                }

                var eh = Sha256.init(.{});
                shaUpdateBytes(&eh, edge.quality.toString());
                shaUpdateF64(&eh, edge.weight);
                shaUpdateF64(&eh, edge.fractal_dimension);
                shaUpdateF64(&eh, edge.quantum_correlation.re);
                shaUpdateF64(&eh, edge.quantum_correlation.im);
                eh.update(&emeta_acc);
                shaUpdateU64(&eh, emeta_count);

                var ed: [Sha256.digest_length]u8 = undefined;
                eh.final(&ed);
                xorDigest(&edges_acc, &ed);
            }

            var kh = Sha256.init(.{});
            shaUpdateBytes(&kh, kv.key_ptr.source);
            shaUpdateBytes(&kh, kv.key_ptr.target);
            kh.update(&edges_acc);
            shaUpdateU64(&kh, edges_count);

            var kd: [Sha256.digest_length]u8 = undefined;
            kh.final(&kd);
            xorDigest(&acc_edges, &kd);
        }

        var en_it = self.entanglements.iterator();
        while (en_it.next()) |kv| {
            ent_count += 1;

            var h = Sha256.init(.{});
            shaUpdateBytes(&h, kv.key_ptr.a);
            shaUpdateBytes(&h, kv.key_ptr.b);
            for (kv.value_ptr.amps) |c| {
                shaUpdateF64(&h, c.re);
                shaUpdateF64(&h, c.im);
            }

            var d: [Sha256.digest_length]u8 = undefined;
            h.final(&d);
            xorDigest(&acc_ent, &d);
        }

        var final = Sha256.init(.{});
        final.update(&acc_nodes);
        shaUpdateU64(&final, node_count);
        final.update(&acc_edges);
        shaUpdateU64(&final, edgekey_count);
        shaUpdateU64(&final, total_edge_count);
        final.update(&acc_ent);
        shaUpdateU64(&final, ent_count);

        var digest: [Sha256.digest_length]u8 = undefined;
        final.final(&digest);

        var out: [65]u8 = undefined;
        _ = try std.fmt.bufPrint(&out, "{s}", .{std.fmt.fmtSliceHexLower(&digest)});
        out[64] = 0;
        self.topology_hash = out;
    }

    pub fn getTopologyHashHex(self: *const SelfSimilarRelationalGraph) []const u8 {
        return self.topology_hash[0..64];
    }

    pub fn encodeInformation(self: *SelfSimilarRelationalGraph, data: []const u8) ![]u8 {
        var hash: [Sha256.digest_length]u8 = undefined;
        Sha256.hash(data, &hash, .{});

        var id_buf: [16]u8 = undefined;
        _ = try std.fmt.bufPrint(&id_buf, "{s}", .{std.fmt.fmtSliceHexLower(hash[0..8])});

        const node_id = try self.allocator.dupe(u8, id_buf[0..16]);
        errdefer self.allocator.free(node_id);

        var added_node = false;
        var added_edges = ArrayList(EdgeKey).init(self.allocator);
        defer added_edges.deinit();

        errdefer {
            for (added_edges.items) |k| {
                if (self.edges.fetchRemove(k)) |removed| {
                    var lst = removed.value;
                    for (lst.items) |*e| e.deinit();
                    lst.deinit();
                }
            }
            if (added_node) {
                if (self.nodes.fetchRemove(node_id)) |removed| {
                    var v = removed.value;
                    v.deinit();
                }
            }
            self.updateTopologyHash() catch {};
        }

        var node = try Node.init(self.allocator, node_id, data, Qubit.initBasis0(), 0.0);
        const ts_str = try std.fmt.allocPrint(self.allocator, "{d}", .{std.time.timestamp()});
        defer self.allocator.free(ts_str);
        try node.setMetadata("encoding_time", ts_str);

        try self.addNode(node);
        added_node = true;

        var ids = try self.getAllNodeIds(self.allocator);
        defer {
            for (ids.items) |id| self.allocator.free(id);
            ids.deinit();
        }

        if (ids.items.len > 1) {
            const max_links: usize = if (ids.items.len - 1 < 3) ids.items.len - 1 else 3;
            var linked: usize = 0;
            var i: usize = ids.items.len;
            while (i > 0 and linked < max_links) : (i -= 1) {
                const prev = ids.items[i - 1];
                if (std.mem.eql(u8, prev, node_id)) continue;
                const src = self.canonicalIdPtr(node_id).?;
                const dst = self.canonicalIdPtr(prev).?;
                const e = Edge.init(self.allocator, src, dst, .coherent, 0.5, Complex(f64).init(0.0, 0.0), 0.0);
                try self.addEdge(src, dst, e);
                try added_edges.append(EdgeKey{ .source = src, .target = dst });
                linked += 1;
            }
        }

        try self.updateTopologyHash();
        return node_id;
    }

    pub fn decodeInformation(self: *const SelfSimilarRelationalGraph, node_id: []const u8) ?[]const u8 {
        if (self.nodes.getPtr(node_id)) |n| return n.data;
        return null;
    }

    pub fn exportNodeEmbeddings(self: *SelfSimilarRelationalGraph, allocator: Allocator) !core_tensor.Tensor {
        const node_count = self.nodes.count();
        if (node_count == 0) return core_tensor.Tensor.init(allocator, &[_]usize{1, 4});
        const shape = [_]usize{ node_count, 4 };
        var tensor = try core_tensor.Tensor.init(allocator, &shape);
        var idx: usize = 0;
        var it = self.nodes.iterator();
        while (it.next()) |entry| {
            const node = entry.value_ptr;
            tensor.data[idx * 4 + 0] = @floatCast(node.qubit.a.re);
            tensor.data[idx * 4 + 1] = @floatCast(node.qubit.a.im);
            tensor.data[idx * 4 + 2] = @floatCast(node.qubit.b.re);
            tensor.data[idx * 4 + 3] = @floatCast(node.qubit.b.im);
            idx += 1;
        }
        return tensor;
    }

    pub fn importNodeEmbeddings(self: *SelfSimilarRelationalGraph, tensor: *const core_tensor.Tensor) !void {
        if (tensor.shape.dims.len != 2 or tensor.shape.dims[1] != 4) return;
        var idx: usize = 0;
        var it = self.nodes.iterator();
        while (it.next()) |entry| {
            if (idx >= tensor.shape.dims[0]) break;
            const node = entry.value_ptr;
            node.qubit.a.re = @floatCast(tensor.data[idx * 4 + 0]);
            node.qubit.a.im = @floatCast(tensor.data[idx * 4 + 1]);
            node.qubit.b.re = @floatCast(tensor.data[idx * 4 + 2]);
            node.qubit.b.im = @floatCast(tensor.data[idx * 4 + 3]);
            idx += 1;
        }
    }

    pub fn exportAdjacencyMatrix(self: *SelfSimilarRelationalGraph, node_ids: []const []const u8, allocator: Allocator) !core_tensor.Tensor {
        const n = node_ids.len;
        if (n == 0) return core_tensor.Tensor.init(allocator, &[_]usize{1, 1});
        const shape = [_]usize{ n, n };
        var tensor = try core_tensor.Tensor.init(allocator, &shape);
        @memset(tensor.data, 0);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                const key = EdgeKey{ .source = node_ids[i], .target = node_ids[j] };
                if (self.edges.get(key)) |edge_list| {
                    tensor.data[i * n + j] = @floatCast(@as(f32, @floatFromInt(edge_list.items.len)));
                }
            }
        }
        return tensor;
    }
};

test "quantum gates basics" {
    const testing = std.testing;
    var q = Qubit.initBasis0();
    q = hadamardGate(q);
    try testing.expectApproxEqAbs(q.prob0(), 0.5, 1e-9);
    try testing.expectApproxEqAbs(q.prob1(), 0.5, 1e-9);

    var qx = Qubit.initBasis0();
    qx = pauliXGate(qx);
    try testing.expectApproxEqAbs(qx.prob0(), 0.0, 1e-9);
    try testing.expectApproxEqAbs(qx.prob1(), 1.0, 1e-9);

    var qz = Qubit.init(Complex(f64).init(0.0, 0.0), Complex(f64).init(1.0, 0.0));
    qz = pauliZGate(qz);
    try testing.expectApproxEqAbs(qz.b.re, -1.0, 1e-9);
}

test "graph basic operations" {
    const testing = std.testing;
    var g = try SelfSimilarRelationalGraph.init(testing.allocator);
    defer g.deinit();

    var n1 = try Node.init(testing.allocator, "a", "data_a", Qubit.initBasis0(), 0.0);
    var n2 = try Node.init(testing.allocator, "b", "data_b", Qubit.initBasis1(), 0.0);
    try g.addNode(n1);
    try g.addNode(n2);

    const e = Edge.init(testing.allocator, "a", "b", .coherent, 1.0, Complex(f64).init(0.0, 0.0), 0.0);
    try g.addEdge("a", "b", e);

    try testing.expectEqual(@as(usize, 2), g.nodeCount());
    try testing.expectEqual(@as(usize, 1), g.edgeCount());
    try testing.expect(g.getEdgesConst("a", "b") != null);

    _ = try g.measure("a");
    _ = g.getTopologyHashHex();
}