module import_shiftx (
  input wire [7:0] a,
  input wire [3:0] index,
  output wire q
);
  assign q = a[index];
endmodule
