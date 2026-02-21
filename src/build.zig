const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const main_exe = b.addExecutable(.{
        .name = "jaide",
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(main_exe);

    const run_cmd = b.addRunArtifact(main_exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the JAIDE main executable");
    run_step.dependOn(&run_cmd.step);

    const inference_exe = b.addExecutable(.{
        .name = "jaide-server",
        .root_source_file = .{ .path = "src/inference_server_main.zig" },
        .target = target,
        .optimize = optimize,
    });
    b.installArtifact(inference_exe);

    const run_server_cmd = b.addRunArtifact(inference_exe);
    run_server_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_server_cmd.addArgs(args);
    }

    const run_server_step = b.step("run-server", "Run the JAIDE inference server");
    run_server_step.dependOn(&run_server_cmd.step);

    const main_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });
    const run_main_tests = b.addRunArtifact(main_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_main_tests.step);

    const tensor_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/core/tensor.zig" },
        .target = target,
        .optimize = optimize,
    });
    const run_tensor_tests = b.addRunArtifact(tensor_tests);
    const tensor_test_step = b.step("test-tensor", "Run tensor tests");
    tensor_test_step.dependOn(&run_tensor_tests.step);

    const memory_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/core/memory.zig" },
        .target = target,
        .optimize = optimize,
    });
    const run_memory_tests = b.addRunArtifact(memory_tests);
    const memory_test_step = b.step("test-memory", "Run memory tests");
    memory_test_step.dependOn(&run_memory_tests.step);
}
