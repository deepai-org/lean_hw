`timescale 1ns/1ps
`default_nettype none

// Board transport only. Channel/checker behavior remains in Loom-emitted RTL.
module surface_matrix_bscan (
    input wire tck, input wire sel, input wire capture, input wire shift,
    input wire update, input wire tdi, output wire tdo,
    input wire clocks_ready, input wire system_reset,
    input wire [31:0] source_heartbeat, sink_heartbeat,
    input wire [255:0] accepted, delivered, expected_sequence, digest, supply_gaps,
    input wire [255:0] source_backpressure, sink_backpressure, sink_ticks,
    input wire [7:0] data_errors, gap_errors,
    input wire [1:0] recovery_status,
    output wire command_epoch,
    output wire [7:0] control,
    output wire [31:0] run_limit
);
    localparam [31:0] ID_MAGIC = 32'h534d_4154; // "SMAT"
`ifdef SURFACE_MATRIX_RTL_SHA_PREFIX
    localparam [31:0] RTL_SHA_PREFIX = `SURFACE_MATRIX_RTL_SHA_PREFIX;
`else
    localparam [31:0] RTL_SHA_PREFIX = 32'h0000_0000;
`endif

    reg [7:0] control_reg = 8'd0;
    reg [31:0] run_limit_reg = 32'd4096;
    reg command_epoch_reg = 1'b0;
    reg [31:0] rd_reg = 32'd0;
    // XSDB `drshift -integer 42` shifts the least-significant bit first.  Bit
    // 41 is reserved padding; bits 40:0 retain the established board map.
    reg [41:0] dr = 42'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] accepted_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] accepted_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] delivered_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] delivered_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] expected_sequence_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] expected_sequence_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] digest_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] digest_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] supply_gaps_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] supply_gaps_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] source_backpressure_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] source_backpressure_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] sink_backpressure_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] sink_backpressure_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] sink_ticks_sync0 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [255:0] sink_ticks_sync1 = 256'd0;
    (* ASYNC_REG = "TRUE" *) reg [31:0] source_heartbeat_sync0 = 32'd0;
    (* ASYNC_REG = "TRUE" *) reg [31:0] source_heartbeat_sync1 = 32'd0;
    (* ASYNC_REG = "TRUE" *) reg [31:0] sink_heartbeat_sync0 = 32'd0;
    (* ASYNC_REG = "TRUE" *) reg [31:0] sink_heartbeat_sync1 = 32'd0;
    (* ASYNC_REG = "TRUE" *) reg [7:0] data_errors_sync0 = 8'd0;
    (* ASYNC_REG = "TRUE" *) reg [7:0] data_errors_sync1 = 8'd0;
    (* ASYNC_REG = "TRUE" *) reg [7:0] gap_errors_sync0 = 8'd0;
    (* ASYNC_REG = "TRUE" *) reg [7:0] gap_errors_sync1 = 8'd0;
    (* ASYNC_REG = "TRUE" *) reg [1:0] recovery_status_sync0 = 2'd0;
    (* ASYNC_REG = "TRUE" *) reg [1:0] recovery_status_sync1 = 2'd0;
    (* ASYNC_REG = "TRUE" *) reg [1:0] status_sync0 = 2'd0;
    (* ASYNC_REG = "TRUE" *) reg [1:0] status_sync1 = 2'd0;
    integer lane;

    always @(posedge tck) begin
        accepted_sync0 <= accepted;
        accepted_sync1 <= accepted_sync0;
        delivered_sync0 <= delivered;
        delivered_sync1 <= delivered_sync0;
        expected_sequence_sync0 <= expected_sequence;
        expected_sequence_sync1 <= expected_sequence_sync0;
        digest_sync0 <= digest;
        digest_sync1 <= digest_sync0;
        supply_gaps_sync0 <= supply_gaps;
        supply_gaps_sync1 <= supply_gaps_sync0;
        source_backpressure_sync0 <= source_backpressure;
        source_backpressure_sync1 <= source_backpressure_sync0;
        sink_backpressure_sync0 <= sink_backpressure;
        sink_backpressure_sync1 <= sink_backpressure_sync0;
        sink_ticks_sync0 <= sink_ticks;
        sink_ticks_sync1 <= sink_ticks_sync0;
        source_heartbeat_sync0 <= source_heartbeat;
        source_heartbeat_sync1 <= source_heartbeat_sync0;
        sink_heartbeat_sync0 <= sink_heartbeat;
        sink_heartbeat_sync1 <= sink_heartbeat_sync0;
        data_errors_sync0 <= data_errors;
        data_errors_sync1 <= data_errors_sync0;
        gap_errors_sync0 <= gap_errors;
        gap_errors_sync1 <= gap_errors_sync0;
        recovery_status_sync0 <= recovery_status;
        recovery_status_sync1 <= recovery_status_sync0;
        status_sync0 <= {system_reset, clocks_ready};
        status_sync1 <= status_sync0;
        if (sel) begin
            if (capture) dr <= {10'd0, rd_reg};
            else if (shift) dr <= {tdi, dr[41:1]};
        end
    end
    assign tdo = dr[0];

    wire write_enable = dr[40];
    wire [6:0] index = dr[38:32];
    always @(posedge tck) begin
        if (sel && update) begin
            if (write_enable && index == 7'd1) control_reg <= dr[7:0];
            if (write_enable && index == 7'd2) run_limit_reg <= dr[31:0];
            if (write_enable && (index == 7'd1 || index == 7'd2))
                command_epoch_reg <= ~command_epoch_reg;
            if (index >= 7'd16 && index < 7'd24) begin
                lane = index - 16;
                rd_reg <= accepted_sync1[lane*32 +: 32];
            end else if (index >= 7'd24 && index < 7'd32) begin
                lane = index - 24;
                rd_reg <= delivered_sync1[lane*32 +: 32];
            end else if (index >= 7'd32 && index < 7'd40) begin
                lane = index - 32;
                rd_reg <= digest_sync1[lane*32 +: 32];
            end else if (index >= 7'd48 && index < 7'd56) begin
                lane = index - 48;
                rd_reg <= supply_gaps_sync1[lane*32 +: 32];
            end else if (index >= 7'd56 && index < 7'd64) begin
                lane = index - 56;
                rd_reg <= source_backpressure_sync1[lane*32 +: 32];
            end else if (index >= 7'd64 && index < 7'd72) begin
                lane = index - 64;
                rd_reg <= sink_backpressure_sync1[lane*32 +: 32];
            end else if (index >= 7'd72 && index < 7'd80) begin
                lane = index - 72;
                rd_reg <= sink_ticks_sync1[lane*32 +: 32];
            end else if (index >= 7'd80 && index < 7'd88) begin
                lane = index - 80;
                rd_reg <= expected_sequence_sync1[lane*32 +: 32];
            end else begin
                case (index)
                    7'd0: rd_reg <= ID_MAGIC;
                    7'd1: rd_reg <= {24'd0, control_reg};
                    7'd2: rd_reg <= run_limit_reg;
                    7'd3: rd_reg <= RTL_SHA_PREFIX;
                    7'd4: rd_reg <= {28'd0, status_sync1,
                                      control_reg[1], control_reg[0]};
                    7'd5: rd_reg <= source_heartbeat_sync1;
                    7'd6: rd_reg <= sink_heartbeat_sync1;
                    7'd40: rd_reg <= {24'd0, data_errors_sync1};
                    7'd41: rd_reg <= {24'd0, gap_errors_sync1};
                    7'd42: rd_reg <= {30'd0, recovery_status_sync1};
                    default: rd_reg <= 32'hdead_0000 | index;
                endcase
            end
        end
    end

    assign control = control_reg;
    assign run_limit = run_limit_reg;
    assign command_epoch = command_epoch_reg;
endmodule

`default_nettype wire
