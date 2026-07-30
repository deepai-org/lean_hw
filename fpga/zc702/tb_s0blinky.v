`timescale 1ns/1ps
module tb;
  reg clk=0, rst=1;
  wire [27:0] o_cnt;
  s0blinky dut(.clk(clk), .rst(rst), .o_cnt(o_cnt));
  always #2.5 clk = ~clk;
  initial begin
    @(negedge clk); rst = 0;
    repeat (1000) @(negedge clk);
    if (o_cnt !== 28'd1000) $display("BLINKY MISMATCH exp=1000 got=%0d", o_cnt);
    else $display("BLINKY OK cnt=%0d", o_cnt);
    $finish;
  end
endmodule
