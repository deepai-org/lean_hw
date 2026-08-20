module import_hierarchy_seq_child (
  input  wire       clk,
  input  wire       rst,
  input  wire [7:0] d,
  output wire [7:0] q
);
  reg [7:0] state;
  always @(posedge clk) begin
    if (rst)
      state <= 8'd0;
    else
      state <= d;
  end
  assign q = state;
endmodule

module import_hierarchy_seq (
  input  wire       clk,
  input  wire       rst,
  input  wire [7:0] a,
  output wire [7:0] q
);
  import_hierarchy_seq_child u_child (
    .clk(clk),
    .rst(rst),
    .d(a ^ 8'h5a),
    .q(q)
  );
endmodule
