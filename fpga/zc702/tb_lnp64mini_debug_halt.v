`timescale 1ns/1ps
`default_nettype none

// Behavioral seam test for the generated debug map. This deliberately uses a
// tiny source module rather than the complete SoC: it checks first-event halt
// persistence, per-core selection, reset, and the generated named bindings.
module debug_sources (
    input  wire run0, halt0, run1, halt1,
    output wire        o_c0_running, o_c0_halted,
    output wire        o_c1_running, o_c1_halted,
    output wire [63:0] o_c0_trace_rd_pc, o_c1_trace_rd_pc,
    output wire [63:0] o_c0_trace_rd_wb, o_c1_trace_rd_wb,
    output wire [63:0] o_c0_fault_pc, o_c1_fault_pc,
    output wire [7:0]  o_c0_fault_cause, o_c1_fault_cause,
    output wire [4:0]  o_c0_fault_cur, o_c1_fault_cur
);
    assign o_c0_running = run0;
    assign o_c0_halted = halt0;
    assign o_c1_running = run1;
    assign o_c1_halted = halt1;
    assign o_c0_trace_rd_pc = 0; assign o_c1_trace_rd_pc = 0;
    assign o_c0_trace_rd_wb = 0; assign o_c1_trace_rd_wb = 0;
    assign o_c0_fault_pc = 0; assign o_c1_fault_pc = 0;
    assign o_c0_fault_cause = 0; assign o_c1_fault_cause = 0;
    assign o_c0_fault_cur = 0; assign o_c1_fault_cur = 0;
endmodule

module tb_lnp64mini_debug_halt;
    reg sysclk = 0, drck = 0, rst = 1;
    reg run0 = 0, halt0 = 0, run1 = 0, halt1 = 0;
    reg w_core = 0;
    wire o_c0_running, o_c0_halted, o_c1_running, o_c1_halted;

    always #5 sysclk = ~sysclk;
    always #3 drck = ~drck;

`include "lnp64mini_debug_map.vh"

    debug_sources u_sources (
        .run0(run0), .halt0(halt0), .run1(run1), .halt1(halt1),
        .o_c0_running(o_c0_running), .o_c0_halted(o_c0_halted),
        .o_c1_running(o_c1_running), .o_c1_halted(o_c1_halted)
`define LOOM_DEBUG_PORTS
`include "lnp64mini_debug_map.vh"
`undef LOOM_DEBUG_PORTS
    );

    task tick;
        begin @(posedge sysclk); #1; end
    endtask

    initial begin
        tick; tick;
        rst = 0;
        tick;
        if (loom_debug_halt_request_c0 !== 1'b0 ||
            loom_debug_halt_request_c1 !== 1'b0) begin
            $display("debug halt: FAIL reset state"); $finish(1);
        end

        run0 = 1; halt0 = 1;
        tick;
        if (loom_debug_halt_request_c0 !== 1'b1 ||
            loom_debug_halt_request_c1 !== 1'b0) begin
            $display("debug halt: FAIL core0 trigger"); $finish(1);
        end
        run0 = 0; halt0 = 0;
        tick;
        if (loom_debug_halt_request_c0 !== 1'b1) begin
            $display("debug halt: FAIL core0 persistence"); $finish(1);
        end

        run1 = 1; halt1 = 1;
        tick;
        if (loom_debug_halt_request_c0 !== 1'b1 ||
            loom_debug_halt_request_c1 !== 1'b1) begin
            $display("debug halt: FAIL core1 trigger"); $finish(1);
        end

        rst = 1;
        tick;
        if (loom_debug_halt_request_c0 !== 1'b0 ||
            loom_debug_halt_request_c1 !== 1'b0) begin
            $display("debug halt: FAIL reset clear"); $finish(1);
        end
        $display("debug halt: OK (per-core trigger + persistence + reset)");
        $finish;
    end
endmodule

`default_nettype wire
