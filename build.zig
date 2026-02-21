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
    main_exe.linkLibC();
    b.installArtifact(main_exe);

    const distributed_exe = b.addExecutable(.{
        .name = "jaide-distributed",
        .root_source_file = .{ .path = "src/main_distributed.zig" },
        .target = target,
        .optimize = optimize,
    });
    distributed_exe.linkLibC();
    b.installArtifact(distributed_exe);

    const distributed_futhark_exe = b.addExecutable(.{
        .name = "jaide-distributed-futhark",
        .root_source_file = .{ .path = "src/main_distributed_futhark.zig" },
        .target = target,
        .optimize = optimize,
    });
    distributed_futhark_exe.linkLibC();
    b.installArtifact(distributed_futhark_exe);

    const gpu_exe = b.addExecutable(.{
        .name = "jaide-gpu",
        .root_source_file = .{ .path = "src/main_gpu.zig" },
        .target = target,
        .optimize = optimize,
    });
    gpu_exe.linkLibC();
    b.installArtifact(gpu_exe);

    const inference_server_exe = b.addExecutable(.{
        .name = "jaide-inference-server",
        .root_source_file = .{ .path = "src/api/inference_server.zig" },
        .target = target,
        .optimize = optimize,
    });
    inference_server_exe.linkLibC();
    b.installArtifact(inference_server_exe);

    const run_cmd = b.addRunArtifact(main_exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the JAIDE main executable");
    run_step.dependOn(&run_cmd.step);

    const run_distributed_cmd = b.addRunArtifact(distributed_exe);
    run_distributed_cmd.step.dependOn(b.getInstallStep());
    const run_distributed_step = b.step("run-distributed", "Run the distributed trainer");
    run_distributed_step.dependOn(&run_distributed_cmd.step);

    const main_tests = b.addTest(.{
        .root_source_file = .{ .path = "src/main.zig" },
        .target = target,
        .optimize = optimize,
    });
    main_tests.linkLibC();
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
