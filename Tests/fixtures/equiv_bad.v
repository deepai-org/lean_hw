module fixture_bad(
  input wire clk,
  input wire rst,
  input wire [7:0] d,
  output wire [7:0] q
);
  reg [7:0] state;
  always @(posedge clk) begin
    if (rst) state <= 8'd0;
    else state <= d + 8'd1;
  end
  assign q = state;
endmodule
