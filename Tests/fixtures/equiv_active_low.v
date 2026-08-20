module fixture_active_low(
  input wire clock_i,
  input wire reset_ni,
  input wire [7:0] d,
  output wire [7:0] q
);
  reg [7:0] state;
  always @(negedge clock_i) begin
    if (!reset_ni) state <= 8'd0;
    else state <= d;
  end
  assign q = state;
endmodule
