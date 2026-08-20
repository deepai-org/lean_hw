module import_stateless(
  input wire [7:0] a,
  input wire [7:0] b,
  input wire [3:0] amount,
  input wire signed [3:0] displacement,
  input wire select,
  output wire [7:0] q,
  output wire [7:0] arithmetic_q,
  output wire [7:0] directional_q
);
  assign q = select ? (a + b) : (a ^ b);
  assign arithmetic_q = $signed(a) >>> amount;
  assign directional_q = a >> displacement;
endmodule
