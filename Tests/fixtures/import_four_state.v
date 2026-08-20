module import_four_state (
  input  wire [7:0] a,
  output wire [7:0] q
);
  assign q = {a[7:1], 1'bx};
endmodule
