module import_hierarchy_child (
  input  wire [7:0] a,
  output wire [7:0] q
);
  assign q = {a[6:0], a[7]};
endmodule

module import_hierarchy (
  input  wire [7:0] a,
  output wire [7:0] q
);
  wire [7:0] child_q;
  import_hierarchy_child u_child (
    .a(a ^ 8'h5a),
    .q(child_q)
  );
  assign q = child_q + 8'd1;
endmodule
