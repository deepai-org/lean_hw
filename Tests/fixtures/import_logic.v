module import_logic(
  input wire clk,
  input wire rst,
  input wire [7:0] a,
  input wire [7:0] b,
  input wire [2:0] select,
  output wire [7:0] q
);
  reg [7:0] state;
  wire predicate = (a && b) || !select || (&a) || (|b);
  wire relation = (a != b) ^ (a >= b) ^ (a <= b);
  reg [7:0] selected;
  always @* begin
    case (select)
      3'd0: selected = a;
      3'd1: selected = b;
      3'd2: selected = a + b;
      default: selected = a ^ b;
    endcase
  end
  always @(posedge clk) begin
    if (rst) state <= 8'd0;
    else state <= (predicate ^ relation) ? selected : (a - b);
  end
  assign q = state;
endmodule
