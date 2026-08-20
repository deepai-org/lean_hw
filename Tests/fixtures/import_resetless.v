module import_resetless(
  input wire clk,
  input wire d,
  output wire q
);
  reg state;
  always @(posedge clk) state <= d;
  assign q = state;
endmodule
