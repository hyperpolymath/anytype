// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// anytype FFI: the Zig side of the seam.
//
// Exports `anytype_check`, the C symbol declared in src/interface/Abi/
// Foreign.idr. The MVP transport is a spawned `anytype-check` process
// (see README.adoc); in-process linkage of the Idris2 kernel is future
// work. Wire structs are comptime-asserted against the layouts proven
// CABICompliant in src/interface/Abi/Layout.idr — if either side edits
// a layout, one of the two gates fails.

const std = @import("std");

/// Verdict codes — must match Abi.Types.verdictCode (proven injective
/// on the Idris side).
pub const VERDICT_ACCEPTED: u8 = 0;
pub const VERDICT_REJECTED: u8 = 1;
pub const VERDICT_ILLFORMED: u8 = 2;

/// Mirrors Abi.Layout.requestLayout: size 16, align 8,
/// discipline@0, term_len@4, term_utf8@8.
pub const anytype_request_t = extern struct {
    discipline: u8,
    term_len: u32,
    term_utf8: [*:0]const u8,
};

/// Mirrors Abi.Layout.responseLayout: size 16, align 8,
/// verdict@0, msg_len@4, msg_utf8@8.
pub const anytype_response_t = extern struct {
    verdict: u8,
    msg_len: u32,
    msg_utf8: [*:0]const u8,
};

comptime {
    // These numbers are the ones proven in Abi.Layout; a drift on either
    // side breaks the corresponding gate.
    std.debug.assert(@sizeOf(anytype_request_t) == 16);
    std.debug.assert(@alignOf(anytype_request_t) == 8);
    std.debug.assert(@offsetOf(anytype_request_t, "discipline") == 0);
    std.debug.assert(@offsetOf(anytype_request_t, "term_len") == 4);
    std.debug.assert(@offsetOf(anytype_request_t, "term_utf8") == 8);
    std.debug.assert(@sizeOf(anytype_response_t) == 16);
    std.debug.assert(@alignOf(anytype_response_t) == 8);
    std.debug.assert(@offsetOf(anytype_response_t, "verdict") == 0);
    std.debug.assert(@offsetOf(anytype_response_t, "msg_len") == 4);
    std.debug.assert(@offsetOf(anytype_response_t, "msg_utf8") == 8);
}

fn disciplineName(code: u8) ?[]const u8 {
    // Must match Abi.Types.disciplineCode.
    return switch (code) {
        0 => "affine",
        1 => "exact",
        else => null,
    };
}

/// Run one kernel check by spawning `bin` and speaking the seam
/// protocol: term on stdin, verdict as exit code (= verdictCode).
pub fn checkWith(
    io: std.Io,
    bin: []const u8,
    discipline: u8,
    term: []const u8,
) u8 {
    const disc = disciplineName(discipline) orelse return VERDICT_ILLFORMED;

    var child = std.process.spawn(io, .{
        .argv = &.{ bin, "--discipline", disc },
        .stdin = .pipe,
        .stdout = .ignore,
        .stderr = .ignore,
    }) catch return VERDICT_ILLFORMED;

    if (child.stdin) |stdin| {
        stdin.writeStreamingAll(io, term) catch {};
        stdin.writeStreamingAll(io, "\n") catch {};
        stdin.close(io);
        child.stdin = null;
    }
    const result = child.wait(io) catch return VERDICT_ILLFORMED;
    return switch (result) {
        .exited => |code| switch (code) {
            VERDICT_ACCEPTED, VERDICT_REJECTED, VERDICT_ILLFORMED => code,
            else => VERDICT_ILLFORMED,
        },
        else => VERDICT_ILLFORMED,
    };
}

/// C entry point. The kernel binary is found via $ANYTYPE_CHECK_BIN,
/// falling back to `anytype-check` on PATH. A missing binary reports
/// VERDICT_ILLFORMED — the seam never invents an acceptance.
export fn anytype_check(discipline: u8, term: [*:0]const u8) u8 {
    var threaded: std.Io.Threaded = .init(std.heap.page_allocator, .{});
    defer threaded.deinit();
    const bin: []const u8 = if (std.c.getenv("ANYTYPE_CHECK_BIN")) |v|
        std.mem.span(@as([*:0]const u8, v))
    else
        "anytype-check";
    return checkWith(threaded.io(), bin, discipline, std.mem.span(term));
}

// ---------------------------------------------------------------------------
// Tests (zig build test). The round-trip tests need the kernel binary at
// ../../../build/exec/anytype-check (built by `just test`); they fail if
// it is absent, because a seam test that cannot run must not pass.
// ---------------------------------------------------------------------------

const KERNEL_BIN = "../../../build/exec/anytype-check";

test "unknown discipline is ill-formed without spawning" {
    try std.testing.expectEqual(
        VERDICT_ILLFORMED,
        checkWith(std.testing.io, KERNEL_BIN, 9, "tt"),
    );
}

test "round trip: affine accepts drop" {
    try std.testing.expectEqual(
        VERDICT_ACCEPTED,
        checkWith(std.testing.io, KERNEL_BIN, 0, "(lam 1 bool tt)"),
    );
}

test "round trip: exact rejects drop (the discipline split)" {
    try std.testing.expectEqual(
        VERDICT_REJECTED,
        checkWith(std.testing.io, KERNEL_BIN, 1, "(lam 1 bool tt)"),
    );
}

test "round trip: ill-formed input" {
    try std.testing.expectEqual(
        VERDICT_ILLFORMED,
        checkWith(std.testing.io, KERNEL_BIN, 0, "garbage(("),
    );
}
