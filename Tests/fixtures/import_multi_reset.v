module import_multi_reset(
  input wire clk,
  input wire rst_a,
  input wire rst_bn,
  input wire en,
  input wire d,
  output wire qa,
  output wire qb
);
  reg state_a;
  reg state_b;
  always @(posedge clk) begin
    if (rst_a) state_a <= 1'b0;
    else state_a <= d;
    if (en) begin
      if (!rst_bn) state_b <= 1'b1;
      else state_b <= state_a;
    end
  end
  assign qa = state_a;
  assign qb = state_b;
endmodule
