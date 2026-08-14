module soc_fabric_cpu(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_cpu_request_src_ready,
  input wire [0:0] __loom_chan_cpu_request_src_accepted,
  input wire [0:0] __loom_chan_cpu_response_dst_valid,
  input wire [37:0] __loom_chan_cpu_response_dst_payload,
  input wire [0:0] hold_issue,
  input wire [0:0] hold_response,
  input wire [31:0] transaction_limit,
  output wire [0:0] o___loom_chan_cpu_request_src_valid,
  output wire [49:0] o___loom_chan_cpu_request_src_payload,
  output wire [0:0] o___loom_chan_cpu_response_dst_pop,
  output wire [31:0] o_sequence,
  output wire [0:0] o_active,
  output wire [3:0] o_active_tag,
  output wire [31:0] o_requests_staged,
  output wire [31:0] o_requests_accepted,
  output wire [31:0] o_responses_received,
  output wire [31:0] o_response_digest,
  output wire [31:0] o_request_stalls,
  output wire [0:0] o_sticky_error,
  output wire [1:0] o_progress
);
  reg [0:0] __loom_chan_cpu_request_src_valid;
  reg [49:0] __loom_chan_cpu_request_src_payload;
  reg [0:0] __loom_chan_cpu_response_dst_pop;
  reg [31:0] sequence;
  reg [0:0] active;
  reg [3:0] active_tag;
  reg [31:0] requests_staged;
  reg [31:0] requests_accepted;
  reg [31:0] responses_received;
  reg [31:0] response_digest;
  reg [31:0] request_stalls;
  reg [0:0] sticky_error;
  reg [1:0] progress;
  wire [0:0] n0 = ~hold_issue;
  wire [0:0] n1 = ~active;
  wire [0:0] n2 = sequence < transaction_limit;
  wire [0:0] n3 = n1 & n2;
  wire [0:0] n4 = n0 & n3;
  wire [0:0] n5 = ~__loom_chan_cpu_request_src_valid;
  wire [0:0] n6 = n5 | __loom_chan_cpu_request_src_accepted;
  wire [0:0] n7 = n6 & __loom_chan_cpu_request_src_ready;
  wire [0:0] n8 = 1'd1;
  wire [0:0] n9 = 1'd0;
  wire [0:0] n10 = __loom_chan_cpu_request_src_accepted ? n9 : __loom_chan_cpu_request_src_valid;
  wire [0:0] n11 = n7 ? n8 : n10;
  wire [0:0] n12 = n7 ? n11 : n10;
  wire [0:0] n13 = n4 ? n12 : n10;
  wire [49:0] n14 = n9;
  wire [49:0] n15 = 50'd49;
  wire [49:0] n16 = n14 << n15;
  wire [3:0] n17 = sequence[3:0];
  wire [48:0] n18 = n17;
  wire [48:0] n19 = 49'd45;
  wire [48:0] n20 = n18 << n19;
  wire [0:0] n21 = sequence[4:4];
  wire [44:0] n22 = n21;
  wire [44:0] n23 = 45'd44;
  wire [44:0] n24 = n22 << n23;
  wire [7:0] n25 = sequence[7:0];
  wire [43:0] n26 = n25;
  wire [43:0] n27 = 44'd36;
  wire [43:0] n28 = n26 << n27;
  wire [31:0] n29 = 32'd324508639;
  wire [31:0] n30 = sequence ^ n29;
  wire [35:0] n31 = n30;
  wire [35:0] n32 = 36'd4;
  wire [35:0] n33 = n31 << n32;
  wire [35:0] n34 = n17;
  wire [35:0] n35 = n33 | n34;
  wire [43:0] n36 = n35;
  wire [43:0] n37 = n28 | n36;
  wire [44:0] n38 = n37;
  wire [44:0] n39 = n24 | n38;
  wire [48:0] n40 = n39;
  wire [48:0] n41 = n20 | n40;
  wire [49:0] n42 = n41;
  wire [49:0] n43 = n16 | n42;
  wire [49:0] n44 = n7 ? n43 : __loom_chan_cpu_request_src_payload;
  wire [49:0] n45 = n7 ? n44 : __loom_chan_cpu_request_src_payload;
  wire [49:0] n46 = n4 ? n45 : __loom_chan_cpu_request_src_payload;
  wire [0:0] n47 = ~hold_response;
  wire [0:0] n48 = ~__loom_chan_cpu_response_dst_pop;
  wire [0:0] n49 = __loom_chan_cpu_response_dst_valid & n48;
  wire [0:0] n50 = active & n49;
  wire [0:0] n51 = n47 & n50;
  wire [0:0] n52 = n49 ? n8 : n9;
  wire [0:0] n53 = n51 ? n52 : n9;
  wire [31:0] n54 = 32'd1;
  wire [31:0] n55 = sequence + n54;
  wire [31:0] n56 = n7 ? n55 : sequence;
  wire [31:0] n57 = n4 ? n56 : sequence;
  wire [0:0] n58 = n51 ? n9 : active;
  wire [0:0] n59 = n7 ? n8 : n58;
  wire [0:0] n60 = n4 ? n59 : n58;
  wire [3:0] n61 = n7 ? n17 : active_tag;
  wire [3:0] n62 = n4 ? n61 : active_tag;
  wire [31:0] n63 = requests_staged + n54;
  wire [31:0] n64 = n7 ? n63 : requests_staged;
  wire [31:0] n65 = n4 ? n64 : requests_staged;
  wire [31:0] n66 = requests_accepted + n54;
  wire [31:0] n67 = __loom_chan_cpu_request_src_accepted ? n66 : requests_accepted;
  wire [31:0] n68 = responses_received + n54;
  wire [31:0] n69 = n51 ? n68 : responses_received;
  wire [31:0] n70 = __loom_chan_cpu_response_dst_payload[32:1];
  wire [31:0] n71 = response_digest ^ n70;
  wire [31:0] n72 = n51 ? n71 : response_digest;
  wire [31:0] n73 = request_stalls + n54;
  wire [31:0] n74 = n7 ? request_stalls : n73;
  wire [31:0] n75 = n4 ? n74 : request_stalls;
  wire [0:0] n76 = __loom_chan_cpu_response_dst_payload[37:37];
  wire [0:0] n77 = n76 == n9;
  wire [0:0] n78 = ~n77;
  wire [3:0] n79 = __loom_chan_cpu_response_dst_payload[36:33];
  wire [0:0] n80 = n79 == active_tag;
  wire [0:0] n81 = ~n80;
  wire [0:0] n82 = __loom_chan_cpu_response_dst_payload[0:0];
  wire [0:0] n83 = n81 | n82;
  wire [0:0] n84 = n78 | n83;
  wire [0:0] n85 = n84 ? n8 : sticky_error;
  wire [0:0] n86 = n51 ? n85 : sticky_error;
  wire [1:0] n87 = 2'd1;
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_cpu_request_src_valid <= 1'd0;
      __loom_chan_cpu_request_src_payload <= 50'd0;
      __loom_chan_cpu_response_dst_pop <= 1'd0;
      sequence <= 32'd0;
      active <= 1'd0;
      active_tag <= 4'd0;
      requests_staged <= 32'd0;
      requests_accepted <= 32'd0;
      responses_received <= 32'd0;
      response_digest <= 32'd0;
      request_stalls <= 32'd0;
      sticky_error <= 1'd0;
      progress <= 2'd0;
    end else begin
      __loom_chan_cpu_request_src_valid <= n13;
      __loom_chan_cpu_request_src_payload <= n46;
      __loom_chan_cpu_response_dst_pop <= n53;
      sequence <= n57;
      active <= n60;
      active_tag <= n62;
      requests_staged <= n65;
      requests_accepted <= n67;
      responses_received <= n69;
      response_digest <= n72;
      request_stalls <= n75;
      sticky_error <= n86;
      progress <= n87;
    end
  end
  assign o___loom_chan_cpu_request_src_valid = __loom_chan_cpu_request_src_valid;
  assign o___loom_chan_cpu_request_src_payload = __loom_chan_cpu_request_src_payload;
  assign o___loom_chan_cpu_response_dst_pop = __loom_chan_cpu_response_dst_pop;
  assign o_sequence = sequence;
  assign o_active = active;
  assign o_active_tag = active_tag;
  assign o_requests_staged = requests_staged;
  assign o_requests_accepted = requests_accepted;
  assign o_responses_received = responses_received;
  assign o_response_digest = response_digest;
  assign o_request_stalls = request_stalls;
  assign o_sticky_error = sticky_error;
  assign o_progress = progress;
endmodule

module soc_fabric_dma(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_dma_request_src_ready,
  input wire [0:0] __loom_chan_dma_request_src_accepted,
  input wire [0:0] __loom_chan_dma_response_dst_valid,
  input wire [37:0] __loom_chan_dma_response_dst_payload,
  input wire [0:0] hold_issue,
  input wire [0:0] hold_response,
  input wire [31:0] transaction_limit,
  output wire [0:0] o___loom_chan_dma_request_src_valid,
  output wire [49:0] o___loom_chan_dma_request_src_payload,
  output wire [0:0] o___loom_chan_dma_response_dst_pop,
  output wire [31:0] o_sequence,
  output wire [0:0] o_active,
  output wire [3:0] o_active_tag,
  output wire [31:0] o_requests_staged,
  output wire [31:0] o_requests_accepted,
  output wire [31:0] o_responses_received,
  output wire [31:0] o_response_digest,
  output wire [31:0] o_request_stalls,
  output wire [0:0] o_sticky_error,
  output wire [1:0] o_progress
);
  reg [0:0] __loom_chan_dma_request_src_valid;
  reg [49:0] __loom_chan_dma_request_src_payload;
  reg [0:0] __loom_chan_dma_response_dst_pop;
  reg [31:0] sequence;
  reg [0:0] active;
  reg [3:0] active_tag;
  reg [31:0] requests_staged;
  reg [31:0] requests_accepted;
  reg [31:0] responses_received;
  reg [31:0] response_digest;
  reg [31:0] request_stalls;
  reg [0:0] sticky_error;
  reg [1:0] progress;
  wire [0:0] n0 = ~hold_issue;
  wire [0:0] n1 = ~active;
  wire [0:0] n2 = sequence < transaction_limit;
  wire [0:0] n3 = n1 & n2;
  wire [0:0] n4 = n0 & n3;
  wire [0:0] n5 = ~__loom_chan_dma_request_src_valid;
  wire [0:0] n6 = n5 | __loom_chan_dma_request_src_accepted;
  wire [0:0] n7 = n6 & __loom_chan_dma_request_src_ready;
  wire [0:0] n8 = 1'd1;
  wire [0:0] n9 = 1'd0;
  wire [0:0] n10 = __loom_chan_dma_request_src_accepted ? n9 : __loom_chan_dma_request_src_valid;
  wire [0:0] n11 = n7 ? n8 : n10;
  wire [0:0] n12 = n7 ? n11 : n10;
  wire [0:0] n13 = n4 ? n12 : n10;
  wire [49:0] n14 = n8;
  wire [49:0] n15 = 50'd49;
  wire [49:0] n16 = n14 << n15;
  wire [3:0] n17 = sequence[3:0];
  wire [48:0] n18 = n17;
  wire [48:0] n19 = 49'd45;
  wire [48:0] n20 = n18 << n19;
  wire [0:0] n21 = sequence[4:4];
  wire [44:0] n22 = n21;
  wire [44:0] n23 = 45'd44;
  wire [44:0] n24 = n22 << n23;
  wire [7:0] n25 = sequence[7:0];
  wire [43:0] n26 = n25;
  wire [43:0] n27 = 44'd36;
  wire [43:0] n28 = n26 << n27;
  wire [31:0] n29 = 32'd610839776;
  wire [31:0] n30 = sequence ^ n29;
  wire [35:0] n31 = n30;
  wire [35:0] n32 = 36'd4;
  wire [35:0] n33 = n31 << n32;
  wire [35:0] n34 = n17;
  wire [35:0] n35 = n33 | n34;
  wire [43:0] n36 = n35;
  wire [43:0] n37 = n28 | n36;
  wire [44:0] n38 = n37;
  wire [44:0] n39 = n24 | n38;
  wire [48:0] n40 = n39;
  wire [48:0] n41 = n20 | n40;
  wire [49:0] n42 = n41;
  wire [49:0] n43 = n16 | n42;
  wire [49:0] n44 = n7 ? n43 : __loom_chan_dma_request_src_payload;
  wire [49:0] n45 = n7 ? n44 : __loom_chan_dma_request_src_payload;
  wire [49:0] n46 = n4 ? n45 : __loom_chan_dma_request_src_payload;
  wire [0:0] n47 = ~hold_response;
  wire [0:0] n48 = ~__loom_chan_dma_response_dst_pop;
  wire [0:0] n49 = __loom_chan_dma_response_dst_valid & n48;
  wire [0:0] n50 = active & n49;
  wire [0:0] n51 = n47 & n50;
  wire [0:0] n52 = n49 ? n8 : n9;
  wire [0:0] n53 = n51 ? n52 : n9;
  wire [31:0] n54 = 32'd1;
  wire [31:0] n55 = sequence + n54;
  wire [31:0] n56 = n7 ? n55 : sequence;
  wire [31:0] n57 = n4 ? n56 : sequence;
  wire [0:0] n58 = n51 ? n9 : active;
  wire [0:0] n59 = n7 ? n8 : n58;
  wire [0:0] n60 = n4 ? n59 : n58;
  wire [3:0] n61 = n7 ? n17 : active_tag;
  wire [3:0] n62 = n4 ? n61 : active_tag;
  wire [31:0] n63 = requests_staged + n54;
  wire [31:0] n64 = n7 ? n63 : requests_staged;
  wire [31:0] n65 = n4 ? n64 : requests_staged;
  wire [31:0] n66 = requests_accepted + n54;
  wire [31:0] n67 = __loom_chan_dma_request_src_accepted ? n66 : requests_accepted;
  wire [31:0] n68 = responses_received + n54;
  wire [31:0] n69 = n51 ? n68 : responses_received;
  wire [31:0] n70 = __loom_chan_dma_response_dst_payload[32:1];
  wire [31:0] n71 = response_digest ^ n70;
  wire [31:0] n72 = n51 ? n71 : response_digest;
  wire [31:0] n73 = request_stalls + n54;
  wire [31:0] n74 = n7 ? request_stalls : n73;
  wire [31:0] n75 = n4 ? n74 : request_stalls;
  wire [0:0] n76 = __loom_chan_dma_response_dst_payload[37:37];
  wire [0:0] n77 = n76 == n8;
  wire [0:0] n78 = ~n77;
  wire [3:0] n79 = __loom_chan_dma_response_dst_payload[36:33];
  wire [0:0] n80 = n79 == active_tag;
  wire [0:0] n81 = ~n80;
  wire [0:0] n82 = __loom_chan_dma_response_dst_payload[0:0];
  wire [0:0] n83 = n81 | n82;
  wire [0:0] n84 = n78 | n83;
  wire [0:0] n85 = n84 ? n8 : sticky_error;
  wire [0:0] n86 = n51 ? n85 : sticky_error;
  wire [1:0] n87 = 2'd1;
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_dma_request_src_valid <= 1'd0;
      __loom_chan_dma_request_src_payload <= 50'd0;
      __loom_chan_dma_response_dst_pop <= 1'd0;
      sequence <= 32'd0;
      active <= 1'd0;
      active_tag <= 4'd0;
      requests_staged <= 32'd0;
      requests_accepted <= 32'd0;
      responses_received <= 32'd0;
      response_digest <= 32'd0;
      request_stalls <= 32'd0;
      sticky_error <= 1'd0;
      progress <= 2'd0;
    end else begin
      __loom_chan_dma_request_src_valid <= n13;
      __loom_chan_dma_request_src_payload <= n46;
      __loom_chan_dma_response_dst_pop <= n53;
      sequence <= n57;
      active <= n60;
      active_tag <= n62;
      requests_staged <= n65;
      requests_accepted <= n67;
      responses_received <= n69;
      response_digest <= n72;
      request_stalls <= n75;
      sticky_error <= n86;
      progress <= n87;
    end
  end
  assign o___loom_chan_dma_request_src_valid = __loom_chan_dma_request_src_valid;
  assign o___loom_chan_dma_request_src_payload = __loom_chan_dma_request_src_payload;
  assign o___loom_chan_dma_response_dst_pop = __loom_chan_dma_response_dst_pop;
  assign o_sequence = sequence;
  assign o_active = active;
  assign o_active_tag = active_tag;
  assign o_requests_staged = requests_staged;
  assign o_requests_accepted = requests_accepted;
  assign o_responses_received = responses_received;
  assign o_response_digest = response_digest;
  assign o_request_stalls = request_stalls;
  assign o_sticky_error = sticky_error;
  assign o_progress = progress;
endmodule

module soc_fabric_arbiter(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_target_request_src_ready,
  input wire [0:0] __loom_chan_target_request_src_accepted,
  input wire [0:0] __loom_chan_target_response_dst_valid,
  input wire [37:0] __loom_chan_target_response_dst_payload,
  input wire [0:0] __loom_chan_cpu_request_dst_valid,
  input wire [49:0] __loom_chan_cpu_request_dst_payload,
  input wire [0:0] __loom_chan_dma_request_dst_valid,
  input wire [49:0] __loom_chan_dma_request_dst_payload,
  input wire [0:0] __loom_chan_cpu_response_src_ready,
  input wire [0:0] __loom_chan_cpu_response_src_accepted,
  input wire [0:0] __loom_chan_dma_response_src_ready,
  input wire [0:0] __loom_chan_dma_response_src_accepted,
  input wire [0:0] hold_arbitration,
  output wire [0:0] o___loom_chan_target_request_src_valid,
  output wire [49:0] o___loom_chan_target_request_src_payload,
  output wire [0:0] o___loom_chan_target_response_dst_pop,
  output wire [0:0] o___loom_chan_cpu_request_dst_pop,
  output wire [0:0] o___loom_chan_dma_request_dst_pop,
  output wire [0:0] o___loom_chan_cpu_response_src_valid,
  output wire [37:0] o___loom_chan_cpu_response_src_payload,
  output wire [0:0] o___loom_chan_dma_response_src_valid,
  output wire [37:0] o___loom_chan_dma_response_src_payload,
  output wire [0:0] o_round_robin,
  output wire [0:0] o_outstanding,
  output wire [0:0] o_route,
  output wire [31:0] o_cpu_grants,
  output wire [31:0] o_dma_grants,
  output wire [31:0] o_total_grants,
  output wire [31:0] o_responses_routed,
  output wire [31:0] o_contention_ticks,
  output wire [31:0] o_target_stalls,
  output wire [31:0] o_response_stalls,
  output wire [0:0] o_double_grant_error,
  output wire [1:0] o_progress
);
  reg [0:0] __loom_chan_target_request_src_valid;
  reg [49:0] __loom_chan_target_request_src_payload;
  reg [0:0] __loom_chan_target_response_dst_pop;
  reg [0:0] __loom_chan_cpu_request_dst_pop;
  reg [0:0] __loom_chan_dma_request_dst_pop;
  reg [0:0] __loom_chan_cpu_response_src_valid;
  reg [37:0] __loom_chan_cpu_response_src_payload;
  reg [0:0] __loom_chan_dma_response_src_valid;
  reg [37:0] __loom_chan_dma_response_src_payload;
  reg [0:0] round_robin;
  reg [0:0] outstanding;
  reg [0:0] route;
  reg [31:0] cpu_grants;
  reg [31:0] dma_grants;
  reg [31:0] total_grants;
  reg [31:0] responses_routed;
  reg [31:0] contention_ticks;
  reg [31:0] target_stalls;
  reg [31:0] response_stalls;
  reg [0:0] double_grant_error;
  reg [1:0] progress;
  wire [0:0] n0 = ~hold_arbitration;
  wire [0:0] n1 = ~outstanding;
  wire [0:0] n2 = n0 & n1;
  wire [0:0] n3 = ~__loom_chan_target_request_src_valid;
  wire [0:0] n4 = n3 | __loom_chan_target_request_src_accepted;
  wire [0:0] n5 = n4 & __loom_chan_target_request_src_ready;
  wire [0:0] n6 = ~__loom_chan_cpu_request_dst_pop;
  wire [0:0] n7 = __loom_chan_cpu_request_dst_valid & n6;
  wire [0:0] n8 = ~__loom_chan_dma_request_dst_pop;
  wire [0:0] n9 = __loom_chan_dma_request_dst_valid & n8;
  wire [0:0] n10 = n7 & n9;
  wire [0:0] n11 = 1'd0;
  wire [0:0] n12 = round_robin == n11;
  wire [0:0] n13 = 1'd1;
  wire [0:0] n14 = __loom_chan_target_request_src_accepted ? n11 : __loom_chan_target_request_src_valid;
  wire [0:0] n15 = n5 ? n13 : n14;
  wire [0:0] n16 = n12 ? n15 : n15;
  wire [0:0] n17 = n9 ? n15 : n14;
  wire [0:0] n18 = n7 ? n15 : n17;
  wire [0:0] n19 = n10 ? n16 : n18;
  wire [0:0] n20 = n5 ? n19 : n14;
  wire [0:0] n21 = n2 ? n20 : n14;
  wire [49:0] n22 = n5 ? __loom_chan_cpu_request_dst_payload : __loom_chan_target_request_src_payload;
  wire [49:0] n23 = n5 ? __loom_chan_dma_request_dst_payload : __loom_chan_target_request_src_payload;
  wire [49:0] n24 = n12 ? n22 : n23;
  wire [49:0] n25 = n9 ? n23 : __loom_chan_target_request_src_payload;
  wire [49:0] n26 = n7 ? n22 : n25;
  wire [49:0] n27 = n10 ? n24 : n26;
  wire [49:0] n28 = n5 ? n27 : __loom_chan_target_request_src_payload;
  wire [49:0] n29 = n2 ? n28 : __loom_chan_target_request_src_payload;
  wire [0:0] n30 = ~__loom_chan_target_response_dst_pop;
  wire [0:0] n31 = __loom_chan_target_response_dst_valid & n30;
  wire [0:0] n32 = outstanding & n31;
  wire [0:0] n33 = route == n11;
  wire [0:0] n34 = ~__loom_chan_cpu_response_src_valid;
  wire [0:0] n35 = n34 | __loom_chan_cpu_response_src_accepted;
  wire [0:0] n36 = n35 & __loom_chan_cpu_response_src_ready;
  wire [0:0] n37 = n31 ? n13 : n11;
  wire [0:0] n38 = n36 ? n37 : n11;
  wire [0:0] n39 = ~__loom_chan_dma_response_src_valid;
  wire [0:0] n40 = n39 | __loom_chan_dma_response_src_accepted;
  wire [0:0] n41 = n40 & __loom_chan_dma_response_src_ready;
  wire [0:0] n42 = n41 ? n37 : n11;
  wire [0:0] n43 = n33 ? n38 : n42;
  wire [0:0] n44 = n32 ? n43 : n11;
  wire [0:0] n45 = n7 ? n13 : n11;
  wire [0:0] n46 = n12 ? n45 : n11;
  wire [0:0] n47 = n7 ? n45 : n11;
  wire [0:0] n48 = n10 ? n46 : n47;
  wire [0:0] n49 = n5 ? n48 : n11;
  wire [0:0] n50 = n2 ? n49 : n11;
  wire [0:0] n51 = n9 ? n13 : n11;
  wire [0:0] n52 = n12 ? n11 : n51;
  wire [0:0] n53 = n9 ? n51 : n11;
  wire [0:0] n54 = n7 ? n11 : n53;
  wire [0:0] n55 = n10 ? n52 : n54;
  wire [0:0] n56 = n5 ? n55 : n11;
  wire [0:0] n57 = n2 ? n56 : n11;
  wire [0:0] n58 = __loom_chan_cpu_response_src_accepted ? n11 : __loom_chan_cpu_response_src_valid;
  wire [0:0] n59 = n36 ? n13 : n58;
  wire [0:0] n60 = n36 ? n59 : n58;
  wire [0:0] n61 = n33 ? n60 : n58;
  wire [0:0] n62 = n32 ? n61 : n58;
  wire [37:0] n63 = n36 ? __loom_chan_target_response_dst_payload : __loom_chan_cpu_response_src_payload;
  wire [37:0] n64 = n36 ? n63 : __loom_chan_cpu_response_src_payload;
  wire [37:0] n65 = n33 ? n64 : __loom_chan_cpu_response_src_payload;
  wire [37:0] n66 = n32 ? n65 : __loom_chan_cpu_response_src_payload;
  wire [0:0] n67 = __loom_chan_dma_response_src_accepted ? n11 : __loom_chan_dma_response_src_valid;
  wire [0:0] n68 = n41 ? n13 : n67;
  wire [0:0] n69 = n41 ? n68 : n67;
  wire [0:0] n70 = n33 ? n67 : n69;
  wire [0:0] n71 = n32 ? n70 : n67;
  wire [37:0] n72 = n41 ? __loom_chan_target_response_dst_payload : __loom_chan_dma_response_src_payload;
  wire [37:0] n73 = n41 ? n72 : __loom_chan_dma_response_src_payload;
  wire [37:0] n74 = n33 ? __loom_chan_dma_response_src_payload : n73;
  wire [37:0] n75 = n32 ? n74 : __loom_chan_dma_response_src_payload;
  wire [0:0] n76 = n12 ? n13 : n11;
  wire [0:0] n77 = n9 ? n11 : round_robin;
  wire [0:0] n78 = n7 ? n13 : n77;
  wire [0:0] n79 = n10 ? n76 : n78;
  wire [0:0] n80 = n5 ? n79 : round_robin;
  wire [0:0] n81 = n2 ? n80 : round_robin;
  wire [0:0] n82 = n12 ? n13 : n13;
  wire [0:0] n83 = n36 ? n11 : outstanding;
  wire [0:0] n84 = n41 ? n11 : outstanding;
  wire [0:0] n85 = n33 ? n83 : n84;
  wire [0:0] n86 = n32 ? n85 : outstanding;
  wire [0:0] n87 = n9 ? n13 : n86;
  wire [0:0] n88 = n7 ? n13 : n87;
  wire [0:0] n89 = n10 ? n82 : n88;
  wire [0:0] n90 = n5 ? n89 : n86;
  wire [0:0] n91 = n2 ? n90 : n86;
  wire [0:0] n92 = n12 ? n11 : n13;
  wire [0:0] n93 = n9 ? n13 : route;
  wire [0:0] n94 = n7 ? n11 : n93;
  wire [0:0] n95 = n10 ? n92 : n94;
  wire [0:0] n96 = n5 ? n95 : route;
  wire [0:0] n97 = n2 ? n96 : route;
  wire [31:0] n98 = 32'd1;
  wire [31:0] n99 = cpu_grants + n98;
  wire [31:0] n100 = n12 ? n99 : cpu_grants;
  wire [31:0] n101 = n7 ? n99 : cpu_grants;
  wire [31:0] n102 = n10 ? n100 : n101;
  wire [31:0] n103 = n5 ? n102 : cpu_grants;
  wire [31:0] n104 = n2 ? n103 : cpu_grants;
  wire [31:0] n105 = dma_grants + n98;
  wire [31:0] n106 = n12 ? dma_grants : n105;
  wire [31:0] n107 = n9 ? n105 : dma_grants;
  wire [31:0] n108 = n7 ? dma_grants : n107;
  wire [31:0] n109 = n10 ? n106 : n108;
  wire [31:0] n110 = n5 ? n109 : dma_grants;
  wire [31:0] n111 = n2 ? n110 : dma_grants;
  wire [31:0] n112 = total_grants + n98;
  wire [31:0] n113 = n12 ? n112 : n112;
  wire [31:0] n114 = n9 ? n112 : total_grants;
  wire [31:0] n115 = n7 ? n112 : n114;
  wire [31:0] n116 = n10 ? n113 : n115;
  wire [31:0] n117 = n5 ? n116 : total_grants;
  wire [31:0] n118 = n2 ? n117 : total_grants;
  wire [31:0] n119 = responses_routed + n98;
  wire [31:0] n120 = n36 ? n119 : responses_routed;
  wire [31:0] n121 = n41 ? n119 : responses_routed;
  wire [31:0] n122 = n33 ? n120 : n121;
  wire [31:0] n123 = n32 ? n122 : responses_routed;
  wire [31:0] n124 = contention_ticks + n98;
  wire [31:0] n125 = n10 ? n124 : contention_ticks;
  wire [0:0] n126 = n7 | n9;
  wire [31:0] n127 = target_stalls + n98;
  wire [31:0] n128 = n126 ? n127 : target_stalls;
  wire [31:0] n129 = n5 ? target_stalls : n128;
  wire [31:0] n130 = n2 ? n129 : target_stalls;
  wire [31:0] n131 = response_stalls + n98;
  wire [31:0] n132 = n36 ? response_stalls : n131;
  wire [31:0] n133 = n41 ? response_stalls : n131;
  wire [31:0] n134 = n33 ? n132 : n133;
  wire [31:0] n135 = n32 ? n134 : response_stalls;
  wire [1:0] n136 = 2'd1;
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_target_request_src_valid <= 1'd0;
      __loom_chan_target_request_src_payload <= 50'd0;
      __loom_chan_target_response_dst_pop <= 1'd0;
      __loom_chan_cpu_request_dst_pop <= 1'd0;
      __loom_chan_dma_request_dst_pop <= 1'd0;
      __loom_chan_cpu_response_src_valid <= 1'd0;
      __loom_chan_cpu_response_src_payload <= 38'd0;
      __loom_chan_dma_response_src_valid <= 1'd0;
      __loom_chan_dma_response_src_payload <= 38'd0;
      round_robin <= 1'd0;
      outstanding <= 1'd0;
      route <= 1'd0;
      cpu_grants <= 32'd0;
      dma_grants <= 32'd0;
      total_grants <= 32'd0;
      responses_routed <= 32'd0;
      contention_ticks <= 32'd0;
      target_stalls <= 32'd0;
      response_stalls <= 32'd0;
      double_grant_error <= 1'd0;
      progress <= 2'd0;
    end else begin
      __loom_chan_target_request_src_valid <= n21;
      __loom_chan_target_request_src_payload <= n29;
      __loom_chan_target_response_dst_pop <= n44;
      __loom_chan_cpu_request_dst_pop <= n50;
      __loom_chan_dma_request_dst_pop <= n57;
      __loom_chan_cpu_response_src_valid <= n62;
      __loom_chan_cpu_response_src_payload <= n66;
      __loom_chan_dma_response_src_valid <= n71;
      __loom_chan_dma_response_src_payload <= n75;
      round_robin <= n81;
      outstanding <= n91;
      route <= n97;
      cpu_grants <= n104;
      dma_grants <= n111;
      total_grants <= n118;
      responses_routed <= n123;
      contention_ticks <= n125;
      target_stalls <= n130;
      response_stalls <= n135;
      double_grant_error <= double_grant_error;
      progress <= n136;
    end
  end
  assign o___loom_chan_target_request_src_valid = __loom_chan_target_request_src_valid;
  assign o___loom_chan_target_request_src_payload = __loom_chan_target_request_src_payload;
  assign o___loom_chan_target_response_dst_pop = __loom_chan_target_response_dst_pop;
  assign o___loom_chan_cpu_request_dst_pop = __loom_chan_cpu_request_dst_pop;
  assign o___loom_chan_dma_request_dst_pop = __loom_chan_dma_request_dst_pop;
  assign o___loom_chan_cpu_response_src_valid = __loom_chan_cpu_response_src_valid;
  assign o___loom_chan_cpu_response_src_payload = __loom_chan_cpu_response_src_payload;
  assign o___loom_chan_dma_response_src_valid = __loom_chan_dma_response_src_valid;
  assign o___loom_chan_dma_response_src_payload = __loom_chan_dma_response_src_payload;
  assign o_round_robin = round_robin;
  assign o_outstanding = outstanding;
  assign o_route = route;
  assign o_cpu_grants = cpu_grants;
  assign o_dma_grants = dma_grants;
  assign o_total_grants = total_grants;
  assign o_responses_routed = responses_routed;
  assign o_contention_ticks = contention_ticks;
  assign o_target_stalls = target_stalls;
  assign o_response_stalls = response_stalls;
  assign o_double_grant_error = double_grant_error;
  assign o_progress = progress;
endmodule

module soc_fabric_register_service(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_target_request_dst_valid,
  input wire [49:0] __loom_chan_target_request_dst_payload,
  input wire [0:0] __loom_chan_target_response_src_ready,
  input wire [0:0] __loom_chan_target_response_src_accepted,
  input wire [0:0] __loom_chan_audit_src_ready,
  input wire [0:0] __loom_chan_audit_src_accepted,
  output wire [0:0] o___loom_chan_target_request_dst_pop,
  output wire [0:0] o___loom_chan_target_response_src_valid,
  output wire [37:0] o___loom_chan_target_response_src_payload,
  output wire [0:0] o___loom_chan_audit_src_valid,
  output wire [45:0] o___loom_chan_audit_src_payload,
  output wire [31:0] o_commits,
  output wire [31:0] o_request_stalls,
  output wire [31:0] o_response_stalls,
  output wire [31:0] o_audit_stalls,
  output wire [1:0] o_progress
);
  reg [0:0] __loom_chan_target_request_dst_pop;
  reg [0:0] __loom_chan_target_response_src_valid;
  reg [37:0] __loom_chan_target_response_src_payload;
  reg [0:0] __loom_chan_audit_src_valid;
  reg [45:0] __loom_chan_audit_src_payload;
  reg [31:0] commits;
  reg [31:0] request_stalls;
  reg [31:0] response_stalls;
  reg [31:0] audit_stalls;
  reg [1:0] progress;
  reg [31:0] register_file [0:255];
  initial begin
    register_file[0] = 32'd0;
    register_file[1] = 32'd0;
    register_file[2] = 32'd0;
    register_file[3] = 32'd0;
    register_file[4] = 32'd0;
    register_file[5] = 32'd0;
    register_file[6] = 32'd0;
    register_file[7] = 32'd0;
    register_file[8] = 32'd0;
    register_file[9] = 32'd0;
    register_file[10] = 32'd0;
    register_file[11] = 32'd0;
    register_file[12] = 32'd0;
    register_file[13] = 32'd0;
    register_file[14] = 32'd0;
    register_file[15] = 32'd0;
    register_file[16] = 32'd0;
    register_file[17] = 32'd0;
    register_file[18] = 32'd0;
    register_file[19] = 32'd0;
    register_file[20] = 32'd0;
    register_file[21] = 32'd0;
    register_file[22] = 32'd0;
    register_file[23] = 32'd0;
    register_file[24] = 32'd0;
    register_file[25] = 32'd0;
    register_file[26] = 32'd0;
    register_file[27] = 32'd0;
    register_file[28] = 32'd0;
    register_file[29] = 32'd0;
    register_file[30] = 32'd0;
    register_file[31] = 32'd0;
    register_file[32] = 32'd0;
    register_file[33] = 32'd0;
    register_file[34] = 32'd0;
    register_file[35] = 32'd0;
    register_file[36] = 32'd0;
    register_file[37] = 32'd0;
    register_file[38] = 32'd0;
    register_file[39] = 32'd0;
    register_file[40] = 32'd0;
    register_file[41] = 32'd0;
    register_file[42] = 32'd0;
    register_file[43] = 32'd0;
    register_file[44] = 32'd0;
    register_file[45] = 32'd0;
    register_file[46] = 32'd0;
    register_file[47] = 32'd0;
    register_file[48] = 32'd0;
    register_file[49] = 32'd0;
    register_file[50] = 32'd0;
    register_file[51] = 32'd0;
    register_file[52] = 32'd0;
    register_file[53] = 32'd0;
    register_file[54] = 32'd0;
    register_file[55] = 32'd0;
    register_file[56] = 32'd0;
    register_file[57] = 32'd0;
    register_file[58] = 32'd0;
    register_file[59] = 32'd0;
    register_file[60] = 32'd0;
    register_file[61] = 32'd0;
    register_file[62] = 32'd0;
    register_file[63] = 32'd0;
    register_file[64] = 32'd0;
    register_file[65] = 32'd0;
    register_file[66] = 32'd0;
    register_file[67] = 32'd0;
    register_file[68] = 32'd0;
    register_file[69] = 32'd0;
    register_file[70] = 32'd0;
    register_file[71] = 32'd0;
    register_file[72] = 32'd0;
    register_file[73] = 32'd0;
    register_file[74] = 32'd0;
    register_file[75] = 32'd0;
    register_file[76] = 32'd0;
    register_file[77] = 32'd0;
    register_file[78] = 32'd0;
    register_file[79] = 32'd0;
    register_file[80] = 32'd0;
    register_file[81] = 32'd0;
    register_file[82] = 32'd0;
    register_file[83] = 32'd0;
    register_file[84] = 32'd0;
    register_file[85] = 32'd0;
    register_file[86] = 32'd0;
    register_file[87] = 32'd0;
    register_file[88] = 32'd0;
    register_file[89] = 32'd0;
    register_file[90] = 32'd0;
    register_file[91] = 32'd0;
    register_file[92] = 32'd0;
    register_file[93] = 32'd0;
    register_file[94] = 32'd0;
    register_file[95] = 32'd0;
    register_file[96] = 32'd0;
    register_file[97] = 32'd0;
    register_file[98] = 32'd0;
    register_file[99] = 32'd0;
    register_file[100] = 32'd0;
    register_file[101] = 32'd0;
    register_file[102] = 32'd0;
    register_file[103] = 32'd0;
    register_file[104] = 32'd0;
    register_file[105] = 32'd0;
    register_file[106] = 32'd0;
    register_file[107] = 32'd0;
    register_file[108] = 32'd0;
    register_file[109] = 32'd0;
    register_file[110] = 32'd0;
    register_file[111] = 32'd0;
    register_file[112] = 32'd0;
    register_file[113] = 32'd0;
    register_file[114] = 32'd0;
    register_file[115] = 32'd0;
    register_file[116] = 32'd0;
    register_file[117] = 32'd0;
    register_file[118] = 32'd0;
    register_file[119] = 32'd0;
    register_file[120] = 32'd0;
    register_file[121] = 32'd0;
    register_file[122] = 32'd0;
    register_file[123] = 32'd0;
    register_file[124] = 32'd0;
    register_file[125] = 32'd0;
    register_file[126] = 32'd0;
    register_file[127] = 32'd0;
    register_file[128] = 32'd0;
    register_file[129] = 32'd0;
    register_file[130] = 32'd0;
    register_file[131] = 32'd0;
    register_file[132] = 32'd0;
    register_file[133] = 32'd0;
    register_file[134] = 32'd0;
    register_file[135] = 32'd0;
    register_file[136] = 32'd0;
    register_file[137] = 32'd0;
    register_file[138] = 32'd0;
    register_file[139] = 32'd0;
    register_file[140] = 32'd0;
    register_file[141] = 32'd0;
    register_file[142] = 32'd0;
    register_file[143] = 32'd0;
    register_file[144] = 32'd0;
    register_file[145] = 32'd0;
    register_file[146] = 32'd0;
    register_file[147] = 32'd0;
    register_file[148] = 32'd0;
    register_file[149] = 32'd0;
    register_file[150] = 32'd0;
    register_file[151] = 32'd0;
    register_file[152] = 32'd0;
    register_file[153] = 32'd0;
    register_file[154] = 32'd0;
    register_file[155] = 32'd0;
    register_file[156] = 32'd0;
    register_file[157] = 32'd0;
    register_file[158] = 32'd0;
    register_file[159] = 32'd0;
    register_file[160] = 32'd0;
    register_file[161] = 32'd0;
    register_file[162] = 32'd0;
    register_file[163] = 32'd0;
    register_file[164] = 32'd0;
    register_file[165] = 32'd0;
    register_file[166] = 32'd0;
    register_file[167] = 32'd0;
    register_file[168] = 32'd0;
    register_file[169] = 32'd0;
    register_file[170] = 32'd0;
    register_file[171] = 32'd0;
    register_file[172] = 32'd0;
    register_file[173] = 32'd0;
    register_file[174] = 32'd0;
    register_file[175] = 32'd0;
    register_file[176] = 32'd0;
    register_file[177] = 32'd0;
    register_file[178] = 32'd0;
    register_file[179] = 32'd0;
    register_file[180] = 32'd0;
    register_file[181] = 32'd0;
    register_file[182] = 32'd0;
    register_file[183] = 32'd0;
    register_file[184] = 32'd0;
    register_file[185] = 32'd0;
    register_file[186] = 32'd0;
    register_file[187] = 32'd0;
    register_file[188] = 32'd0;
    register_file[189] = 32'd0;
    register_file[190] = 32'd0;
    register_file[191] = 32'd0;
    register_file[192] = 32'd0;
    register_file[193] = 32'd0;
    register_file[194] = 32'd0;
    register_file[195] = 32'd0;
    register_file[196] = 32'd0;
    register_file[197] = 32'd0;
    register_file[198] = 32'd0;
    register_file[199] = 32'd0;
    register_file[200] = 32'd0;
    register_file[201] = 32'd0;
    register_file[202] = 32'd0;
    register_file[203] = 32'd0;
    register_file[204] = 32'd0;
    register_file[205] = 32'd0;
    register_file[206] = 32'd0;
    register_file[207] = 32'd0;
    register_file[208] = 32'd0;
    register_file[209] = 32'd0;
    register_file[210] = 32'd0;
    register_file[211] = 32'd0;
    register_file[212] = 32'd0;
    register_file[213] = 32'd0;
    register_file[214] = 32'd0;
    register_file[215] = 32'd0;
    register_file[216] = 32'd0;
    register_file[217] = 32'd0;
    register_file[218] = 32'd0;
    register_file[219] = 32'd0;
    register_file[220] = 32'd0;
    register_file[221] = 32'd0;
    register_file[222] = 32'd0;
    register_file[223] = 32'd0;
    register_file[224] = 32'd0;
    register_file[225] = 32'd0;
    register_file[226] = 32'd0;
    register_file[227] = 32'd0;
    register_file[228] = 32'd0;
    register_file[229] = 32'd0;
    register_file[230] = 32'd0;
    register_file[231] = 32'd0;
    register_file[232] = 32'd0;
    register_file[233] = 32'd0;
    register_file[234] = 32'd0;
    register_file[235] = 32'd0;
    register_file[236] = 32'd0;
    register_file[237] = 32'd0;
    register_file[238] = 32'd0;
    register_file[239] = 32'd0;
    register_file[240] = 32'd0;
    register_file[241] = 32'd0;
    register_file[242] = 32'd0;
    register_file[243] = 32'd0;
    register_file[244] = 32'd0;
    register_file[245] = 32'd0;
    register_file[246] = 32'd0;
    register_file[247] = 32'd0;
    register_file[248] = 32'd0;
    register_file[249] = 32'd0;
    register_file[250] = 32'd0;
    register_file[251] = 32'd0;
    register_file[252] = 32'd0;
    register_file[253] = 32'd0;
    register_file[254] = 32'd0;
    register_file[255] = 32'd0;
  end
  wire [0:0] n0 = ~__loom_chan_target_request_dst_pop;
  wire [0:0] n1 = __loom_chan_target_request_dst_valid & n0;
  wire [0:0] n2 = ~__loom_chan_target_response_src_valid;
  wire [0:0] n3 = n2 | __loom_chan_target_response_src_accepted;
  wire [0:0] n4 = n3 & __loom_chan_target_response_src_ready;
  wire [0:0] n5 = ~__loom_chan_audit_src_valid;
  wire [0:0] n6 = n5 | __loom_chan_audit_src_accepted;
  wire [0:0] n7 = n6 & __loom_chan_audit_src_ready;
  wire [0:0] n8 = 1'd1;
  wire [0:0] n9 = 1'd0;
  wire [0:0] n10 = n1 ? n8 : n9;
  wire [0:0] n11 = n7 ? n10 : n9;
  wire [0:0] n12 = n4 ? n11 : n9;
  wire [0:0] n13 = n1 ? n12 : n9;
  wire [0:0] n14 = __loom_chan_target_response_src_accepted ? n9 : __loom_chan_target_response_src_valid;
  wire [0:0] n15 = n4 ? n8 : n14;
  wire [0:0] n16 = n7 ? n15 : n14;
  wire [0:0] n17 = n4 ? n16 : n14;
  wire [0:0] n18 = n1 ? n17 : n14;
  wire [0:0] n19 = __loom_chan_target_request_dst_payload[49:49];
  wire [37:0] n20 = n19;
  wire [37:0] n21 = 38'd37;
  wire [37:0] n22 = n20 << n21;
  wire [3:0] n23 = __loom_chan_target_request_dst_payload[48:45];
  wire [36:0] n24 = n23;
  wire [36:0] n25 = 37'd33;
  wire [36:0] n26 = n24 << n25;
  wire [0:0] n27 = __loom_chan_target_request_dst_payload[44:44];
  wire [3:0] n28 = __loom_chan_target_request_dst_payload[3:0];
  wire [0:0] n29 = n28[3:3];
  wire [31:0] n30 = __loom_chan_target_request_dst_payload[35:4];
  wire [7:0] n31 = n30[31:24];
  wire [7:0] n32 = __loom_chan_target_request_dst_payload[43:36];
  wire [31:0] n33 = register_file[n32];
  wire [7:0] n34 = n33[31:24];
  wire [7:0] n35 = n29 ? n31 : n34;
  wire [31:0] n36 = n35;
  wire [31:0] n37 = 32'd24;
  wire [31:0] n38 = n36 << n37;
  wire [0:0] n39 = n28[2:2];
  wire [7:0] n40 = n30[23:16];
  wire [7:0] n41 = n33[23:16];
  wire [7:0] n42 = n39 ? n40 : n41;
  wire [23:0] n43 = n42;
  wire [23:0] n44 = 24'd16;
  wire [23:0] n45 = n43 << n44;
  wire [0:0] n46 = n28[1:1];
  wire [7:0] n47 = n30[15:8];
  wire [7:0] n48 = n33[15:8];
  wire [7:0] n49 = n46 ? n47 : n48;
  wire [15:0] n50 = n49;
  wire [15:0] n51 = 16'd8;
  wire [15:0] n52 = n50 << n51;
  wire [0:0] n53 = n28[0:0];
  wire [7:0] n54 = n30[7:0];
  wire [7:0] n55 = n33[7:0];
  wire [7:0] n56 = n53 ? n54 : n55;
  wire [15:0] n57 = n56;
  wire [15:0] n58 = n52 | n57;
  wire [23:0] n59 = n58;
  wire [23:0] n60 = n45 | n59;
  wire [31:0] n61 = n60;
  wire [31:0] n62 = n38 | n61;
  wire [31:0] n63 = n27 ? n62 : n33;
  wire [32:0] n64 = n63;
  wire [32:0] n65 = 33'd1;
  wire [32:0] n66 = n64 << n65;
  wire [32:0] n67 = n9;
  wire [32:0] n68 = n66 | n67;
  wire [36:0] n69 = n68;
  wire [36:0] n70 = n26 | n69;
  wire [37:0] n71 = n70;
  wire [37:0] n72 = n22 | n71;
  wire [37:0] n73 = n4 ? n72 : __loom_chan_target_response_src_payload;
  wire [37:0] n74 = n7 ? n73 : __loom_chan_target_response_src_payload;
  wire [37:0] n75 = n4 ? n74 : __loom_chan_target_response_src_payload;
  wire [37:0] n76 = n1 ? n75 : __loom_chan_target_response_src_payload;
  wire [0:0] n77 = __loom_chan_audit_src_accepted ? n9 : __loom_chan_audit_src_valid;
  wire [0:0] n78 = n7 ? n8 : n77;
  wire [0:0] n79 = n7 ? n78 : n77;
  wire [0:0] n80 = n4 ? n79 : n77;
  wire [0:0] n81 = n1 ? n80 : n77;
  wire [45:0] n82 = n19;
  wire [45:0] n83 = 46'd45;
  wire [45:0] n84 = n82 << n83;
  wire [44:0] n85 = n23;
  wire [44:0] n86 = 45'd41;
  wire [44:0] n87 = n85 << n86;
  wire [40:0] n88 = n32;
  wire [40:0] n89 = 41'd33;
  wire [40:0] n90 = n88 << n89;
  wire [32:0] n91 = n27;
  wire [32:0] n92 = 33'd32;
  wire [32:0] n93 = n91 << n92;
  wire [32:0] n94 = n93 | n64;
  wire [40:0] n95 = n94;
  wire [40:0] n96 = n90 | n95;
  wire [44:0] n97 = n96;
  wire [44:0] n98 = n87 | n97;
  wire [45:0] n99 = n98;
  wire [45:0] n100 = n84 | n99;
  wire [45:0] n101 = n7 ? n100 : __loom_chan_audit_src_payload;
  wire [45:0] n102 = n7 ? n101 : __loom_chan_audit_src_payload;
  wire [45:0] n103 = n4 ? n102 : __loom_chan_audit_src_payload;
  wire [45:0] n104 = n1 ? n103 : __loom_chan_audit_src_payload;
  wire [31:0] n105 = 32'd1;
  wire [31:0] n106 = commits + n105;
  wire [31:0] n107 = n7 ? n106 : commits;
  wire [31:0] n108 = n4 ? n107 : commits;
  wire [31:0] n109 = n1 ? n108 : commits;
  wire [31:0] n110 = request_stalls + n105;
  wire [31:0] n111 = n1 ? request_stalls : n110;
  wire [31:0] n112 = response_stalls + n105;
  wire [31:0] n113 = n4 ? response_stalls : n112;
  wire [31:0] n114 = n1 ? n113 : response_stalls;
  wire [31:0] n115 = audit_stalls + n105;
  wire [31:0] n116 = n7 ? audit_stalls : n115;
  wire [31:0] n117 = n4 ? n116 : audit_stalls;
  wire [31:0] n118 = n1 ? n117 : audit_stalls;
  wire [1:0] n119 = 2'd1;
  wire [0:0] n120 = n27 ? n8 : n9;
  wire [0:0] n121 = n7 ? n120 : n9;
  wire [0:0] n122 = n4 ? n121 : n9;
  wire [0:0] n123 = n1 ? n122 : n9;
  wire [7:0] n124 = 8'd0;
  wire [7:0] n125 = n27 ? n32 : n124;
  wire [7:0] n126 = n7 ? n125 : n124;
  wire [7:0] n127 = n4 ? n126 : n124;
  wire [7:0] n128 = n1 ? n127 : n124;
  wire [31:0] n129 = 32'd0;
  wire [31:0] n130 = n27 ? n63 : n129;
  wire [31:0] n131 = n7 ? n130 : n129;
  wire [31:0] n132 = n4 ? n131 : n129;
  wire [31:0] n133 = n1 ? n132 : n129;
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_target_request_dst_pop <= 1'd0;
      __loom_chan_target_response_src_valid <= 1'd0;
      __loom_chan_target_response_src_payload <= 38'd0;
      __loom_chan_audit_src_valid <= 1'd0;
      __loom_chan_audit_src_payload <= 46'd0;
      commits <= 32'd0;
      request_stalls <= 32'd0;
      response_stalls <= 32'd0;
      audit_stalls <= 32'd0;
      progress <= 2'd0;
    end else begin
      __loom_chan_target_request_dst_pop <= n13;
      __loom_chan_target_response_src_valid <= n18;
      __loom_chan_target_response_src_payload <= n76;
      __loom_chan_audit_src_valid <= n81;
      __loom_chan_audit_src_payload <= n104;
      commits <= n109;
      request_stalls <= n111;
      response_stalls <= n114;
      audit_stalls <= n118;
      progress <= n119;
      if (n123) register_file[n128] <= n133;
    end
  end
  assign o___loom_chan_target_request_dst_pop = __loom_chan_target_request_dst_pop;
  assign o___loom_chan_target_response_src_valid = __loom_chan_target_response_src_valid;
  assign o___loom_chan_target_response_src_payload = __loom_chan_target_response_src_payload;
  assign o___loom_chan_audit_src_valid = __loom_chan_audit_src_valid;
  assign o___loom_chan_audit_src_payload = __loom_chan_audit_src_payload;
  assign o_commits = commits;
  assign o_request_stalls = request_stalls;
  assign o_response_stalls = response_stalls;
  assign o_audit_stalls = audit_stalls;
  assign o_progress = progress;
endmodule

module soc_fabric_audit_monitor(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_audit_dst_valid,
  input wire [45:0] __loom_chan_audit_dst_payload,
  output wire [0:0] o___loom_chan_audit_dst_pop,
  output wire [31:0] o_records,
  output wire [31:0] o_audit_digest,
  output wire [31:0] o_expected_digest,
  output wire [31:0] o_cpu_expected_sequence,
  output wire [31:0] o_dma_expected_sequence,
  output wire [0:0] o_sticky_error,
  output wire [1:0] o_progress
);
  reg [0:0] __loom_chan_audit_dst_pop;
  reg [31:0] records;
  reg [31:0] audit_digest;
  reg [31:0] expected_digest;
  reg [31:0] cpu_expected_sequence;
  reg [31:0] dma_expected_sequence;
  reg [0:0] sticky_error;
  reg [1:0] progress;
  reg [31:0] monitor_memory [0:255];
  initial begin
    monitor_memory[0] = 32'd0;
    monitor_memory[1] = 32'd0;
    monitor_memory[2] = 32'd0;
    monitor_memory[3] = 32'd0;
    monitor_memory[4] = 32'd0;
    monitor_memory[5] = 32'd0;
    monitor_memory[6] = 32'd0;
    monitor_memory[7] = 32'd0;
    monitor_memory[8] = 32'd0;
    monitor_memory[9] = 32'd0;
    monitor_memory[10] = 32'd0;
    monitor_memory[11] = 32'd0;
    monitor_memory[12] = 32'd0;
    monitor_memory[13] = 32'd0;
    monitor_memory[14] = 32'd0;
    monitor_memory[15] = 32'd0;
    monitor_memory[16] = 32'd0;
    monitor_memory[17] = 32'd0;
    monitor_memory[18] = 32'd0;
    monitor_memory[19] = 32'd0;
    monitor_memory[20] = 32'd0;
    monitor_memory[21] = 32'd0;
    monitor_memory[22] = 32'd0;
    monitor_memory[23] = 32'd0;
    monitor_memory[24] = 32'd0;
    monitor_memory[25] = 32'd0;
    monitor_memory[26] = 32'd0;
    monitor_memory[27] = 32'd0;
    monitor_memory[28] = 32'd0;
    monitor_memory[29] = 32'd0;
    monitor_memory[30] = 32'd0;
    monitor_memory[31] = 32'd0;
    monitor_memory[32] = 32'd0;
    monitor_memory[33] = 32'd0;
    monitor_memory[34] = 32'd0;
    monitor_memory[35] = 32'd0;
    monitor_memory[36] = 32'd0;
    monitor_memory[37] = 32'd0;
    monitor_memory[38] = 32'd0;
    monitor_memory[39] = 32'd0;
    monitor_memory[40] = 32'd0;
    monitor_memory[41] = 32'd0;
    monitor_memory[42] = 32'd0;
    monitor_memory[43] = 32'd0;
    monitor_memory[44] = 32'd0;
    monitor_memory[45] = 32'd0;
    monitor_memory[46] = 32'd0;
    monitor_memory[47] = 32'd0;
    monitor_memory[48] = 32'd0;
    monitor_memory[49] = 32'd0;
    monitor_memory[50] = 32'd0;
    monitor_memory[51] = 32'd0;
    monitor_memory[52] = 32'd0;
    monitor_memory[53] = 32'd0;
    monitor_memory[54] = 32'd0;
    monitor_memory[55] = 32'd0;
    monitor_memory[56] = 32'd0;
    monitor_memory[57] = 32'd0;
    monitor_memory[58] = 32'd0;
    monitor_memory[59] = 32'd0;
    monitor_memory[60] = 32'd0;
    monitor_memory[61] = 32'd0;
    monitor_memory[62] = 32'd0;
    monitor_memory[63] = 32'd0;
    monitor_memory[64] = 32'd0;
    monitor_memory[65] = 32'd0;
    monitor_memory[66] = 32'd0;
    monitor_memory[67] = 32'd0;
    monitor_memory[68] = 32'd0;
    monitor_memory[69] = 32'd0;
    monitor_memory[70] = 32'd0;
    monitor_memory[71] = 32'd0;
    monitor_memory[72] = 32'd0;
    monitor_memory[73] = 32'd0;
    monitor_memory[74] = 32'd0;
    monitor_memory[75] = 32'd0;
    monitor_memory[76] = 32'd0;
    monitor_memory[77] = 32'd0;
    monitor_memory[78] = 32'd0;
    monitor_memory[79] = 32'd0;
    monitor_memory[80] = 32'd0;
    monitor_memory[81] = 32'd0;
    monitor_memory[82] = 32'd0;
    monitor_memory[83] = 32'd0;
    monitor_memory[84] = 32'd0;
    monitor_memory[85] = 32'd0;
    monitor_memory[86] = 32'd0;
    monitor_memory[87] = 32'd0;
    monitor_memory[88] = 32'd0;
    monitor_memory[89] = 32'd0;
    monitor_memory[90] = 32'd0;
    monitor_memory[91] = 32'd0;
    monitor_memory[92] = 32'd0;
    monitor_memory[93] = 32'd0;
    monitor_memory[94] = 32'd0;
    monitor_memory[95] = 32'd0;
    monitor_memory[96] = 32'd0;
    monitor_memory[97] = 32'd0;
    monitor_memory[98] = 32'd0;
    monitor_memory[99] = 32'd0;
    monitor_memory[100] = 32'd0;
    monitor_memory[101] = 32'd0;
    monitor_memory[102] = 32'd0;
    monitor_memory[103] = 32'd0;
    monitor_memory[104] = 32'd0;
    monitor_memory[105] = 32'd0;
    monitor_memory[106] = 32'd0;
    monitor_memory[107] = 32'd0;
    monitor_memory[108] = 32'd0;
    monitor_memory[109] = 32'd0;
    monitor_memory[110] = 32'd0;
    monitor_memory[111] = 32'd0;
    monitor_memory[112] = 32'd0;
    monitor_memory[113] = 32'd0;
    monitor_memory[114] = 32'd0;
    monitor_memory[115] = 32'd0;
    monitor_memory[116] = 32'd0;
    monitor_memory[117] = 32'd0;
    monitor_memory[118] = 32'd0;
    monitor_memory[119] = 32'd0;
    monitor_memory[120] = 32'd0;
    monitor_memory[121] = 32'd0;
    monitor_memory[122] = 32'd0;
    monitor_memory[123] = 32'd0;
    monitor_memory[124] = 32'd0;
    monitor_memory[125] = 32'd0;
    monitor_memory[126] = 32'd0;
    monitor_memory[127] = 32'd0;
    monitor_memory[128] = 32'd0;
    monitor_memory[129] = 32'd0;
    monitor_memory[130] = 32'd0;
    monitor_memory[131] = 32'd0;
    monitor_memory[132] = 32'd0;
    monitor_memory[133] = 32'd0;
    monitor_memory[134] = 32'd0;
    monitor_memory[135] = 32'd0;
    monitor_memory[136] = 32'd0;
    monitor_memory[137] = 32'd0;
    monitor_memory[138] = 32'd0;
    monitor_memory[139] = 32'd0;
    monitor_memory[140] = 32'd0;
    monitor_memory[141] = 32'd0;
    monitor_memory[142] = 32'd0;
    monitor_memory[143] = 32'd0;
    monitor_memory[144] = 32'd0;
    monitor_memory[145] = 32'd0;
    monitor_memory[146] = 32'd0;
    monitor_memory[147] = 32'd0;
    monitor_memory[148] = 32'd0;
    monitor_memory[149] = 32'd0;
    monitor_memory[150] = 32'd0;
    monitor_memory[151] = 32'd0;
    monitor_memory[152] = 32'd0;
    monitor_memory[153] = 32'd0;
    monitor_memory[154] = 32'd0;
    monitor_memory[155] = 32'd0;
    monitor_memory[156] = 32'd0;
    monitor_memory[157] = 32'd0;
    monitor_memory[158] = 32'd0;
    monitor_memory[159] = 32'd0;
    monitor_memory[160] = 32'd0;
    monitor_memory[161] = 32'd0;
    monitor_memory[162] = 32'd0;
    monitor_memory[163] = 32'd0;
    monitor_memory[164] = 32'd0;
    monitor_memory[165] = 32'd0;
    monitor_memory[166] = 32'd0;
    monitor_memory[167] = 32'd0;
    monitor_memory[168] = 32'd0;
    monitor_memory[169] = 32'd0;
    monitor_memory[170] = 32'd0;
    monitor_memory[171] = 32'd0;
    monitor_memory[172] = 32'd0;
    monitor_memory[173] = 32'd0;
    monitor_memory[174] = 32'd0;
    monitor_memory[175] = 32'd0;
    monitor_memory[176] = 32'd0;
    monitor_memory[177] = 32'd0;
    monitor_memory[178] = 32'd0;
    monitor_memory[179] = 32'd0;
    monitor_memory[180] = 32'd0;
    monitor_memory[181] = 32'd0;
    monitor_memory[182] = 32'd0;
    monitor_memory[183] = 32'd0;
    monitor_memory[184] = 32'd0;
    monitor_memory[185] = 32'd0;
    monitor_memory[186] = 32'd0;
    monitor_memory[187] = 32'd0;
    monitor_memory[188] = 32'd0;
    monitor_memory[189] = 32'd0;
    monitor_memory[190] = 32'd0;
    monitor_memory[191] = 32'd0;
    monitor_memory[192] = 32'd0;
    monitor_memory[193] = 32'd0;
    monitor_memory[194] = 32'd0;
    monitor_memory[195] = 32'd0;
    monitor_memory[196] = 32'd0;
    monitor_memory[197] = 32'd0;
    monitor_memory[198] = 32'd0;
    monitor_memory[199] = 32'd0;
    monitor_memory[200] = 32'd0;
    monitor_memory[201] = 32'd0;
    monitor_memory[202] = 32'd0;
    monitor_memory[203] = 32'd0;
    monitor_memory[204] = 32'd0;
    monitor_memory[205] = 32'd0;
    monitor_memory[206] = 32'd0;
    monitor_memory[207] = 32'd0;
    monitor_memory[208] = 32'd0;
    monitor_memory[209] = 32'd0;
    monitor_memory[210] = 32'd0;
    monitor_memory[211] = 32'd0;
    monitor_memory[212] = 32'd0;
    monitor_memory[213] = 32'd0;
    monitor_memory[214] = 32'd0;
    monitor_memory[215] = 32'd0;
    monitor_memory[216] = 32'd0;
    monitor_memory[217] = 32'd0;
    monitor_memory[218] = 32'd0;
    monitor_memory[219] = 32'd0;
    monitor_memory[220] = 32'd0;
    monitor_memory[221] = 32'd0;
    monitor_memory[222] = 32'd0;
    monitor_memory[223] = 32'd0;
    monitor_memory[224] = 32'd0;
    monitor_memory[225] = 32'd0;
    monitor_memory[226] = 32'd0;
    monitor_memory[227] = 32'd0;
    monitor_memory[228] = 32'd0;
    monitor_memory[229] = 32'd0;
    monitor_memory[230] = 32'd0;
    monitor_memory[231] = 32'd0;
    monitor_memory[232] = 32'd0;
    monitor_memory[233] = 32'd0;
    monitor_memory[234] = 32'd0;
    monitor_memory[235] = 32'd0;
    monitor_memory[236] = 32'd0;
    monitor_memory[237] = 32'd0;
    monitor_memory[238] = 32'd0;
    monitor_memory[239] = 32'd0;
    monitor_memory[240] = 32'd0;
    monitor_memory[241] = 32'd0;
    monitor_memory[242] = 32'd0;
    monitor_memory[243] = 32'd0;
    monitor_memory[244] = 32'd0;
    monitor_memory[245] = 32'd0;
    monitor_memory[246] = 32'd0;
    monitor_memory[247] = 32'd0;
    monitor_memory[248] = 32'd0;
    monitor_memory[249] = 32'd0;
    monitor_memory[250] = 32'd0;
    monitor_memory[251] = 32'd0;
    monitor_memory[252] = 32'd0;
    monitor_memory[253] = 32'd0;
    monitor_memory[254] = 32'd0;
    monitor_memory[255] = 32'd0;
  end
  wire [0:0] n0 = ~__loom_chan_audit_dst_pop;
  wire [0:0] n1 = __loom_chan_audit_dst_valid & n0;
  wire [0:0] n2 = 1'd1;
  wire [0:0] n3 = 1'd0;
  wire [0:0] n4 = n1 ? n2 : n3;
  wire [0:0] n5 = n1 ? n4 : n3;
  wire [31:0] n6 = 32'd1;
  wire [31:0] n7 = records + n6;
  wire [31:0] n8 = n1 ? n7 : records;
  wire [31:0] n9 = __loom_chan_audit_dst_payload[31:0];
  wire [31:0] n10 = audit_digest ^ n9;
  wire [31:0] n11 = n1 ? n10 : audit_digest;
  wire [0:0] n12 = __loom_chan_audit_dst_payload[45:45];
  wire [31:0] n13 = n12 ? dma_expected_sequence : cpu_expected_sequence;
  wire [0:0] n14 = n13[4:4];
  wire [3:0] n15 = n13[3:0];
  wire [0:0] n16 = n15[3:3];
  wire [31:0] n17 = 32'd610839776;
  wire [31:0] n18 = 32'd324508639;
  wire [31:0] n19 = n12 ? n17 : n18;
  wire [31:0] n20 = n13 ^ n19;
  wire [7:0] n21 = n20[31:24];
  wire [7:0] n22 = __loom_chan_audit_dst_payload[40:33];
  wire [31:0] n23 = monitor_memory[n22];
  wire [7:0] n24 = n23[31:24];
  wire [7:0] n25 = n16 ? n21 : n24;
  wire [31:0] n26 = n25;
  wire [31:0] n27 = 32'd24;
  wire [31:0] n28 = n26 << n27;
  wire [0:0] n29 = n15[2:2];
  wire [7:0] n30 = n20[23:16];
  wire [7:0] n31 = n23[23:16];
  wire [7:0] n32 = n29 ? n30 : n31;
  wire [23:0] n33 = n32;
  wire [23:0] n34 = 24'd16;
  wire [23:0] n35 = n33 << n34;
  wire [0:0] n36 = n15[1:1];
  wire [7:0] n37 = n20[15:8];
  wire [7:0] n38 = n23[15:8];
  wire [7:0] n39 = n36 ? n37 : n38;
  wire [15:0] n40 = n39;
  wire [15:0] n41 = 16'd8;
  wire [15:0] n42 = n40 << n41;
  wire [0:0] n43 = n15[0:0];
  wire [7:0] n44 = n20[7:0];
  wire [7:0] n45 = n23[7:0];
  wire [7:0] n46 = n43 ? n44 : n45;
  wire [15:0] n47 = n46;
  wire [15:0] n48 = n42 | n47;
  wire [23:0] n49 = n48;
  wire [23:0] n50 = n35 | n49;
  wire [31:0] n51 = n50;
  wire [31:0] n52 = n28 | n51;
  wire [31:0] n53 = n14 ? n52 : n23;
  wire [31:0] n54 = expected_digest ^ n53;
  wire [31:0] n55 = n1 ? n54 : expected_digest;
  wire [31:0] n56 = cpu_expected_sequence + n6;
  wire [31:0] n57 = n12 ? cpu_expected_sequence : n56;
  wire [31:0] n58 = n1 ? n57 : cpu_expected_sequence;
  wire [31:0] n59 = dma_expected_sequence + n6;
  wire [31:0] n60 = n12 ? n59 : dma_expected_sequence;
  wire [31:0] n61 = n1 ? n60 : dma_expected_sequence;
  wire [3:0] n62 = __loom_chan_audit_dst_payload[44:41];
  wire [0:0] n63 = n62 == n15;
  wire [0:0] n64 = ~n63;
  wire [7:0] n65 = n13[7:0];
  wire [0:0] n66 = n22 == n65;
  wire [0:0] n67 = ~n66;
  wire [0:0] n68 = __loom_chan_audit_dst_payload[32:32];
  wire [0:0] n69 = n68 == n14;
  wire [0:0] n70 = ~n69;
  wire [0:0] n71 = n9 == n53;
  wire [0:0] n72 = ~n71;
  wire [0:0] n73 = n70 | n72;
  wire [0:0] n74 = n67 | n73;
  wire [0:0] n75 = n64 | n74;
  wire [0:0] n76 = n75 ? n2 : sticky_error;
  wire [0:0] n77 = n1 ? n76 : sticky_error;
  wire [1:0] n78 = 2'd1;
  wire [0:0] n79 = n14 ? n2 : n3;
  wire [0:0] n80 = n1 ? n79 : n3;
  wire [7:0] n81 = 8'd0;
  wire [7:0] n82 = n14 ? n22 : n81;
  wire [7:0] n83 = n1 ? n82 : n81;
  wire [31:0] n84 = 32'd0;
  wire [31:0] n85 = n14 ? n53 : n84;
  wire [31:0] n86 = n1 ? n85 : n84;
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_audit_dst_pop <= 1'd0;
      records <= 32'd0;
      audit_digest <= 32'd0;
      expected_digest <= 32'd0;
      cpu_expected_sequence <= 32'd0;
      dma_expected_sequence <= 32'd0;
      sticky_error <= 1'd0;
      progress <= 2'd0;
    end else begin
      __loom_chan_audit_dst_pop <= n5;
      records <= n8;
      audit_digest <= n11;
      expected_digest <= n55;
      cpu_expected_sequence <= n58;
      dma_expected_sequence <= n61;
      sticky_error <= n77;
      progress <= n78;
      if (n80) monitor_memory[n83] <= n86;
    end
  end
  assign o___loom_chan_audit_dst_pop = __loom_chan_audit_dst_pop;
  assign o_records = records;
  assign o_audit_digest = audit_digest;
  assign o_expected_digest = expected_digest;
  assign o_cpu_expected_sequence = cpu_expected_sequence;
  assign o_dma_expected_sequence = dma_expected_sequence;
  assign o_sticky_error = sticky_error;
  assign o_progress = progress;
endmodule

module __loom_chan_cpu_request_sync_adapter(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_cpu_request_push,
  input wire [49:0] __loom_chan_cpu_request_push_payload,
  input wire [0:0] __loom_chan_cpu_request_pop,
  output wire [0:0] source_ready,
  output wire [0:0] sink_valid,
  output wire [49:0] sink_payload
);
  reg [1:0] __loom_chan_cpu_request_count;
  reg [0:0] __loom_chan_cpu_request_head;
  reg [0:0] __loom_chan_cpu_request_tail;
  reg [0:0] __loom_chan_cpu_request_accepted;
  reg [0:0] __loom_chan_cpu_request_delivered;
  reg [49:0] __loom_chan_cpu_request_storage [0:1];
  initial begin
    __loom_chan_cpu_request_storage[0] = 50'd0;
    __loom_chan_cpu_request_storage[1] = 50'd0;
  end
  wire [1:0] n0 = 2'd2;
  wire [0:0] n1 = __loom_chan_cpu_request_count < n0;
  wire [1:0] n2 = 2'd0;
  wire [0:0] n3 = __loom_chan_cpu_request_count == n2;
  wire [0:0] n4 = ~n3;
  wire [0:0] n5 = __loom_chan_cpu_request_pop & n4;
  wire [0:0] n6 = n1 | n5;
  wire [0:0] n7 = __loom_chan_cpu_request_push & n6;
  wire [1:0] n8 = 2'd1;
  wire [1:0] n9 = __loom_chan_cpu_request_count + n8;
  wire [1:0] n10 = n5 ? __loom_chan_cpu_request_count : n9;
  wire [1:0] n11 = __loom_chan_cpu_request_count - n8;
  wire [1:0] n12 = n5 ? n11 : __loom_chan_cpu_request_count;
  wire [1:0] n13 = n7 ? n10 : n12;
  wire [0:0] n14 = 1'd0;
  wire [0:0] n15 = n14 == n14;
  wire [0:0] n16 = 1'd1;
  wire [0:0] n17 = __loom_chan_cpu_request_head + n16;
  wire [0:0] n18 = n17 % n14;
  wire [0:0] n19 = n15 ? n17 : n18;
  wire [0:0] n20 = n5 ? n19 : __loom_chan_cpu_request_head;
  wire [0:0] n21 = __loom_chan_cpu_request_tail + n16;
  wire [0:0] n22 = n21 % n14;
  wire [0:0] n23 = n15 ? n21 : n22;
  wire [0:0] n24 = n7 ? n23 : __loom_chan_cpu_request_tail;
  wire [0:0] n25 = n7 ? n16 : n14;
  wire [0:0] n26 = n5 ? n16 : n14;
  wire [0:0] n27 = n7 ? __loom_chan_cpu_request_tail : n14;
  wire [49:0] n28 = 50'd0;
  wire [49:0] n29 = n7 ? __loom_chan_cpu_request_push_payload : n28;
  wire [49:0] n30 = __loom_chan_cpu_request_storage[__loom_chan_cpu_request_head];
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_cpu_request_count <= 2'd0;
      __loom_chan_cpu_request_head <= 1'd0;
      __loom_chan_cpu_request_tail <= 1'd0;
      __loom_chan_cpu_request_accepted <= 1'd0;
      __loom_chan_cpu_request_delivered <= 1'd0;
    end else begin
      __loom_chan_cpu_request_count <= n13;
      __loom_chan_cpu_request_head <= n20;
      __loom_chan_cpu_request_tail <= n24;
      __loom_chan_cpu_request_accepted <= n25;
      __loom_chan_cpu_request_delivered <= n26;
      if (n25) __loom_chan_cpu_request_storage[n27] <= n29;
    end
  end
  assign source_ready = n6;
  assign sink_valid = n4;
  assign sink_payload = n30;
endmodule

module __loom_chan_cpu_response_sync_adapter(
  input wire clk,
  input wire rst,
  input wire [0:0] __loom_chan_cpu_response_push,
  input wire [37:0] __loom_chan_cpu_response_push_payload,
  input wire [0:0] __loom_chan_cpu_response_pop,
  output wire [0:0] source_ready,
  output wire [0:0] sink_valid,
  output wire [37:0] sink_payload
);
  reg [1:0] __loom_chan_cpu_response_count;
  reg [0:0] __loom_chan_cpu_response_head;
  reg [0:0] __loom_chan_cpu_response_tail;
  reg [0:0] __loom_chan_cpu_response_accepted;
  reg [0:0] __loom_chan_cpu_response_delivered;
  reg [37:0] __loom_chan_cpu_response_storage [0:1];
  initial begin
    __loom_chan_cpu_response_storage[0] = 38'd0;
    __loom_chan_cpu_response_storage[1] = 38'd0;
  end
  wire [1:0] n0 = 2'd2;
  wire [0:0] n1 = __loom_chan_cpu_response_count < n0;
  wire [1:0] n2 = 2'd0;
  wire [0:0] n3 = __loom_chan_cpu_response_count == n2;
  wire [0:0] n4 = ~n3;
  wire [0:0] n5 = __loom_chan_cpu_response_pop & n4;
  wire [0:0] n6 = n1 | n5;
  wire [0:0] n7 = __loom_chan_cpu_response_push & n6;
  wire [1:0] n8 = 2'd1;
  wire [1:0] n9 = __loom_chan_cpu_response_count + n8;
  wire [1:0] n10 = n5 ? __loom_chan_cpu_response_count : n9;
  wire [1:0] n11 = __loom_chan_cpu_response_count - n8;
  wire [1:0] n12 = n5 ? n11 : __loom_chan_cpu_response_count;
  wire [1:0] n13 = n7 ? n10 : n12;
  wire [0:0] n14 = 1'd0;
  wire [0:0] n15 = n14 == n14;
  wire [0:0] n16 = 1'd1;
  wire [0:0] n17 = __loom_chan_cpu_response_head + n16;
  wire [0:0] n18 = n17 % n14;
  wire [0:0] n19 = n15 ? n17 : n18;
  wire [0:0] n20 = n5 ? n19 : __loom_chan_cpu_response_head;
  wire [0:0] n21 = __loom_chan_cpu_response_tail + n16;
  wire [0:0] n22 = n21 % n14;
  wire [0:0] n23 = n15 ? n21 : n22;
  wire [0:0] n24 = n7 ? n23 : __loom_chan_cpu_response_tail;
  wire [0:0] n25 = n7 ? n16 : n14;
  wire [0:0] n26 = n5 ? n16 : n14;
  wire [0:0] n27 = n7 ? __loom_chan_cpu_response_tail : n14;
  wire [37:0] n28 = 38'd0;
  wire [37:0] n29 = n7 ? __loom_chan_cpu_response_push_payload : n28;
  wire [37:0] n30 = __loom_chan_cpu_response_storage[__loom_chan_cpu_response_head];
  always @(posedge clk) begin
    if (rst) begin
      __loom_chan_cpu_response_count <= 2'd0;
      __loom_chan_cpu_response_head <= 1'd0;
      __loom_chan_cpu_response_tail <= 1'd0;
      __loom_chan_cpu_response_accepted <= 1'd0;
      __loom_chan_cpu_response_delivered <= 1'd0;
    end else begin
      __loom_chan_cpu_response_count <= n13;
      __loom_chan_cpu_response_head <= n20;
      __loom_chan_cpu_response_tail <= n24;
      __loom_chan_cpu_response_accepted <= n25;
      __loom_chan_cpu_response_delivered <= n26;
      if (n25) __loom_chan_cpu_response_storage[n27] <= n29;
    end
  end
  assign source_ready = n6;
  assign sink_valid = n4;
  assign sink_payload = n30;
endmodule

module async_fifo_source_control_w50_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] source_valid,
  input wire [49:0] source_payload,
  input wire [2:0] raw_read_gray,
  output wire [2:0] o_write_binary,
  output wire [2:0] o_write_gray,
  output wire [2:0] o_read_gray_sync0,
  output wire [2:0] o_read_gray_sync1,
  output wire [0:0] source_ready,
  output wire [0:0] write_take,
  output wire [1:0] write_address,
  output wire [49:0] write_data
);
  reg [2:0] write_binary;
  reg [2:0] write_gray;
  reg [2:0] read_gray_sync0;
  reg [2:0] read_gray_sync1;
  wire [2:0] n0 = 3'd1;
  wire [2:0] n1 = read_gray_sync1 >> n0;
  wire [2:0] n2 = read_gray_sync1 ^ n1;
  wire [2:0] n3 = 3'd2;
  wire [2:0] n4 = read_gray_sync1 >> n3;
  wire [2:0] n5 = n2 ^ n4;
  wire [2:0] n6 = 3'd4;
  wire [2:0] n7 = n5 + n6;
  wire [0:0] n8 = write_binary == n7;
  wire [0:0] n9 = ~n8;
  wire [0:0] n10 = source_valid & n9;
  wire [2:0] n11 = n10;
  wire [2:0] n12 = write_binary + n11;
  wire [2:0] n13 = n12 >> n0;
  wire [2:0] n14 = n12 ^ n13;
  wire [1:0] n15 = write_binary[1:0];
  always @(posedge clk) begin
    if (rst) begin
      write_binary <= 3'd0;
      write_gray <= 3'd0;
      read_gray_sync0 <= 3'd0;
      read_gray_sync1 <= 3'd0;
    end else begin
      write_binary <= n12;
      write_gray <= n14;
      read_gray_sync0 <= raw_read_gray;
      read_gray_sync1 <= read_gray_sync0;
    end
  end
  assign o_write_binary = write_binary;
  assign o_write_gray = write_gray;
  assign o_read_gray_sync0 = read_gray_sync0;
  assign o_read_gray_sync1 = read_gray_sync1;
  assign source_ready = n9;
  assign write_take = n10;
  assign write_address = n15;
  assign write_data = source_payload;
endmodule

module async_fifo_sink_control_w50_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] sink_pop,
  input wire [2:0] raw_write_gray,
  output wire [2:0] o_read_binary,
  output wire [2:0] o_read_gray,
  output wire [2:0] o_write_gray_sync0,
  output wire [2:0] o_write_gray_sync1,
  output wire [0:0] sink_valid,
  output wire [0:0] read_take,
  output wire [1:0] read_address
);
  reg [2:0] read_binary;
  reg [2:0] read_gray;
  reg [2:0] write_gray_sync0;
  reg [2:0] write_gray_sync1;
  wire [2:0] n0 = 3'd1;
  wire [2:0] n1 = write_gray_sync1 >> n0;
  wire [2:0] n2 = write_gray_sync1 ^ n1;
  wire [2:0] n3 = 3'd2;
  wire [2:0] n4 = write_gray_sync1 >> n3;
  wire [2:0] n5 = n2 ^ n4;
  wire [0:0] n6 = read_binary == n5;
  wire [0:0] n7 = ~n6;
  wire [0:0] n8 = sink_pop & n7;
  wire [2:0] n9 = n8;
  wire [2:0] n10 = read_binary + n9;
  wire [2:0] n11 = n10 >> n0;
  wire [2:0] n12 = n10 ^ n11;
  wire [1:0] n13 = read_binary[1:0];
  always @(posedge clk) begin
    if (rst) begin
      read_binary <= 3'd0;
      read_gray <= 3'd0;
      write_gray_sync0 <= 3'd0;
      write_gray_sync1 <= 3'd0;
    end else begin
      read_binary <= n10;
      read_gray <= n12;
      write_gray_sync0 <= raw_write_gray;
      write_gray_sync1 <= write_gray_sync0;
    end
  end
  assign o_read_binary = read_binary;
  assign o_read_gray = read_gray;
  assign o_write_gray_sync0 = write_gray_sync0;
  assign o_write_gray_sync1 = write_gray_sync1;
  assign sink_valid = n7;
  assign read_take = n8;
  assign read_address = n13;
endmodule

module async_queue_portable_writer_w50_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] sssss,
  input wire [1:0] ssssss,
  input wire [49:0] sssssss,
  output wire [49:0] o_s,
  output wire [49:0] o_ss,
  output wire [49:0] o_sss,
  output wire [49:0] o_ssss
);
  reg [49:0] s;
  reg [49:0] ss;
  reg [49:0] sss;
  reg [49:0] ssss;
  wire [1:0] n0 = 2'd0;
  wire [0:0] n1 = ssssss == n0;
  wire [49:0] n2 = n1 ? sssssss : s;
  wire [49:0] n3 = sssss ? n2 : s;
  wire [1:0] n4 = 2'd1;
  wire [0:0] n5 = ssssss == n4;
  wire [49:0] n6 = n5 ? sssssss : ss;
  wire [49:0] n7 = sssss ? n6 : ss;
  wire [1:0] n8 = 2'd2;
  wire [0:0] n9 = ssssss == n8;
  wire [49:0] n10 = n9 ? sssssss : sss;
  wire [49:0] n11 = sssss ? n10 : sss;
  wire [1:0] n12 = 2'd3;
  wire [0:0] n13 = ssssss == n12;
  wire [49:0] n14 = n13 ? sssssss : ssss;
  wire [49:0] n15 = sssss ? n14 : ssss;
  always @(posedge clk) begin
    if (rst) begin
      s <= 50'd0;
      ss <= 50'd0;
      sss <= 50'd0;
      ssss <= 50'd0;
    end else begin
      s <= n3;
      ss <= n7;
      sss <= n11;
      ssss <= n15;
    end
  end
  assign o_s = s;
  assign o_ss = ss;
  assign o_sss = sss;
  assign o_ssss = ssss;
endmodule

module async_queue_portable_fwft_reader_w50_d4(
  input wire clk,
  input wire rst,
  input wire [49:0] s,
  input wire [49:0] ss,
  input wire [49:0] sss,
  input wire [49:0] ssss,
  input wire [0:0] ssssssss,
  input wire [1:0] sssssssss,
  output wire [49:0] read_sample
);
  wire [1:0] n0 = 2'd3;
  wire [0:0] n1 = sssssssss == n0;
  wire [1:0] n2 = 2'd2;
  wire [0:0] n3 = sssssssss == n2;
  wire [1:0] n4 = 2'd1;
  wire [0:0] n5 = sssssssss == n4;
  wire [1:0] n6 = 2'd0;
  wire [0:0] n7 = sssssssss == n6;
  wire [49:0] n8 = 50'd0;
  wire [49:0] n9 = n7 ? s : n8;
  wire [49:0] n10 = n5 ? ss : n9;
  wire [49:0] n11 = n3 ? sss : n10;
  wire [49:0] n12 = n1 ? ssss : n11;
  always @(posedge clk) begin
    if (rst) begin
    end else begin
    end
  end
  assign read_sample = n12;
endmodule

module async_fifo_source_control_w38_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] source_valid,
  input wire [37:0] source_payload,
  input wire [2:0] raw_read_gray,
  output wire [2:0] o_write_binary,
  output wire [2:0] o_write_gray,
  output wire [2:0] o_read_gray_sync0,
  output wire [2:0] o_read_gray_sync1,
  output wire [0:0] source_ready,
  output wire [0:0] write_take,
  output wire [1:0] write_address,
  output wire [37:0] write_data
);
  reg [2:0] write_binary;
  reg [2:0] write_gray;
  reg [2:0] read_gray_sync0;
  reg [2:0] read_gray_sync1;
  wire [2:0] n0 = 3'd1;
  wire [2:0] n1 = read_gray_sync1 >> n0;
  wire [2:0] n2 = read_gray_sync1 ^ n1;
  wire [2:0] n3 = 3'd2;
  wire [2:0] n4 = read_gray_sync1 >> n3;
  wire [2:0] n5 = n2 ^ n4;
  wire [2:0] n6 = 3'd4;
  wire [2:0] n7 = n5 + n6;
  wire [0:0] n8 = write_binary == n7;
  wire [0:0] n9 = ~n8;
  wire [0:0] n10 = source_valid & n9;
  wire [2:0] n11 = n10;
  wire [2:0] n12 = write_binary + n11;
  wire [2:0] n13 = n12 >> n0;
  wire [2:0] n14 = n12 ^ n13;
  wire [1:0] n15 = write_binary[1:0];
  always @(posedge clk) begin
    if (rst) begin
      write_binary <= 3'd0;
      write_gray <= 3'd0;
      read_gray_sync0 <= 3'd0;
      read_gray_sync1 <= 3'd0;
    end else begin
      write_binary <= n12;
      write_gray <= n14;
      read_gray_sync0 <= raw_read_gray;
      read_gray_sync1 <= read_gray_sync0;
    end
  end
  assign o_write_binary = write_binary;
  assign o_write_gray = write_gray;
  assign o_read_gray_sync0 = read_gray_sync0;
  assign o_read_gray_sync1 = read_gray_sync1;
  assign source_ready = n9;
  assign write_take = n10;
  assign write_address = n15;
  assign write_data = source_payload;
endmodule

module async_fifo_sink_control_w38_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] sink_pop,
  input wire [2:0] raw_write_gray,
  output wire [2:0] o_read_binary,
  output wire [2:0] o_read_gray,
  output wire [2:0] o_write_gray_sync0,
  output wire [2:0] o_write_gray_sync1,
  output wire [0:0] sink_valid,
  output wire [0:0] read_take,
  output wire [1:0] read_address
);
  reg [2:0] read_binary;
  reg [2:0] read_gray;
  reg [2:0] write_gray_sync0;
  reg [2:0] write_gray_sync1;
  wire [2:0] n0 = 3'd1;
  wire [2:0] n1 = write_gray_sync1 >> n0;
  wire [2:0] n2 = write_gray_sync1 ^ n1;
  wire [2:0] n3 = 3'd2;
  wire [2:0] n4 = write_gray_sync1 >> n3;
  wire [2:0] n5 = n2 ^ n4;
  wire [0:0] n6 = read_binary == n5;
  wire [0:0] n7 = ~n6;
  wire [0:0] n8 = sink_pop & n7;
  wire [2:0] n9 = n8;
  wire [2:0] n10 = read_binary + n9;
  wire [2:0] n11 = n10 >> n0;
  wire [2:0] n12 = n10 ^ n11;
  wire [1:0] n13 = read_binary[1:0];
  always @(posedge clk) begin
    if (rst) begin
      read_binary <= 3'd0;
      read_gray <= 3'd0;
      write_gray_sync0 <= 3'd0;
      write_gray_sync1 <= 3'd0;
    end else begin
      read_binary <= n10;
      read_gray <= n12;
      write_gray_sync0 <= raw_write_gray;
      write_gray_sync1 <= write_gray_sync0;
    end
  end
  assign o_read_binary = read_binary;
  assign o_read_gray = read_gray;
  assign o_write_gray_sync0 = write_gray_sync0;
  assign o_write_gray_sync1 = write_gray_sync1;
  assign sink_valid = n7;
  assign read_take = n8;
  assign read_address = n13;
endmodule

module async_queue_portable_writer_w38_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] sssss,
  input wire [1:0] ssssss,
  input wire [37:0] sssssss,
  output wire [37:0] o_s,
  output wire [37:0] o_ss,
  output wire [37:0] o_sss,
  output wire [37:0] o_ssss
);
  reg [37:0] s;
  reg [37:0] ss;
  reg [37:0] sss;
  reg [37:0] ssss;
  wire [1:0] n0 = 2'd0;
  wire [0:0] n1 = ssssss == n0;
  wire [37:0] n2 = n1 ? sssssss : s;
  wire [37:0] n3 = sssss ? n2 : s;
  wire [1:0] n4 = 2'd1;
  wire [0:0] n5 = ssssss == n4;
  wire [37:0] n6 = n5 ? sssssss : ss;
  wire [37:0] n7 = sssss ? n6 : ss;
  wire [1:0] n8 = 2'd2;
  wire [0:0] n9 = ssssss == n8;
  wire [37:0] n10 = n9 ? sssssss : sss;
  wire [37:0] n11 = sssss ? n10 : sss;
  wire [1:0] n12 = 2'd3;
  wire [0:0] n13 = ssssss == n12;
  wire [37:0] n14 = n13 ? sssssss : ssss;
  wire [37:0] n15 = sssss ? n14 : ssss;
  always @(posedge clk) begin
    if (rst) begin
      s <= 38'd0;
      ss <= 38'd0;
      sss <= 38'd0;
      ssss <= 38'd0;
    end else begin
      s <= n3;
      ss <= n7;
      sss <= n11;
      ssss <= n15;
    end
  end
  assign o_s = s;
  assign o_ss = ss;
  assign o_sss = sss;
  assign o_ssss = ssss;
endmodule

module async_queue_portable_fwft_reader_w38_d4(
  input wire clk,
  input wire rst,
  input wire [37:0] s,
  input wire [37:0] ss,
  input wire [37:0] sss,
  input wire [37:0] ssss,
  input wire [0:0] ssssssss,
  input wire [1:0] sssssssss,
  output wire [37:0] read_sample
);
  wire [1:0] n0 = 2'd3;
  wire [0:0] n1 = sssssssss == n0;
  wire [1:0] n2 = 2'd2;
  wire [0:0] n3 = sssssssss == n2;
  wire [1:0] n4 = 2'd1;
  wire [0:0] n5 = sssssssss == n4;
  wire [1:0] n6 = 2'd0;
  wire [0:0] n7 = sssssssss == n6;
  wire [37:0] n8 = 38'd0;
  wire [37:0] n9 = n7 ? s : n8;
  wire [37:0] n10 = n5 ? ss : n9;
  wire [37:0] n11 = n3 ? sss : n10;
  wire [37:0] n12 = n1 ? ssss : n11;
  always @(posedge clk) begin
    if (rst) begin
    end else begin
    end
  end
  assign read_sample = n12;
endmodule

module async_fifo_source_control_w46_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] source_valid,
  input wire [45:0] source_payload,
  input wire [2:0] raw_read_gray,
  output wire [2:0] o_write_binary,
  output wire [2:0] o_write_gray,
  output wire [2:0] o_read_gray_sync0,
  output wire [2:0] o_read_gray_sync1,
  output wire [0:0] source_ready,
  output wire [0:0] write_take,
  output wire [1:0] write_address,
  output wire [45:0] write_data
);
  reg [2:0] write_binary;
  reg [2:0] write_gray;
  reg [2:0] read_gray_sync0;
  reg [2:0] read_gray_sync1;
  wire [2:0] n0 = 3'd1;
  wire [2:0] n1 = read_gray_sync1 >> n0;
  wire [2:0] n2 = read_gray_sync1 ^ n1;
  wire [2:0] n3 = 3'd2;
  wire [2:0] n4 = read_gray_sync1 >> n3;
  wire [2:0] n5 = n2 ^ n4;
  wire [2:0] n6 = 3'd4;
  wire [2:0] n7 = n5 + n6;
  wire [0:0] n8 = write_binary == n7;
  wire [0:0] n9 = ~n8;
  wire [0:0] n10 = source_valid & n9;
  wire [2:0] n11 = n10;
  wire [2:0] n12 = write_binary + n11;
  wire [2:0] n13 = n12 >> n0;
  wire [2:0] n14 = n12 ^ n13;
  wire [1:0] n15 = write_binary[1:0];
  always @(posedge clk) begin
    if (rst) begin
      write_binary <= 3'd0;
      write_gray <= 3'd0;
      read_gray_sync0 <= 3'd0;
      read_gray_sync1 <= 3'd0;
    end else begin
      write_binary <= n12;
      write_gray <= n14;
      read_gray_sync0 <= raw_read_gray;
      read_gray_sync1 <= read_gray_sync0;
    end
  end
  assign o_write_binary = write_binary;
  assign o_write_gray = write_gray;
  assign o_read_gray_sync0 = read_gray_sync0;
  assign o_read_gray_sync1 = read_gray_sync1;
  assign source_ready = n9;
  assign write_take = n10;
  assign write_address = n15;
  assign write_data = source_payload;
endmodule

module async_fifo_sink_control_w46_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] sink_pop,
  input wire [2:0] raw_write_gray,
  output wire [2:0] o_read_binary,
  output wire [2:0] o_read_gray,
  output wire [2:0] o_write_gray_sync0,
  output wire [2:0] o_write_gray_sync1,
  output wire [0:0] sink_valid,
  output wire [0:0] read_take,
  output wire [1:0] read_address
);
  reg [2:0] read_binary;
  reg [2:0] read_gray;
  reg [2:0] write_gray_sync0;
  reg [2:0] write_gray_sync1;
  wire [2:0] n0 = 3'd1;
  wire [2:0] n1 = write_gray_sync1 >> n0;
  wire [2:0] n2 = write_gray_sync1 ^ n1;
  wire [2:0] n3 = 3'd2;
  wire [2:0] n4 = write_gray_sync1 >> n3;
  wire [2:0] n5 = n2 ^ n4;
  wire [0:0] n6 = read_binary == n5;
  wire [0:0] n7 = ~n6;
  wire [0:0] n8 = sink_pop & n7;
  wire [2:0] n9 = n8;
  wire [2:0] n10 = read_binary + n9;
  wire [2:0] n11 = n10 >> n0;
  wire [2:0] n12 = n10 ^ n11;
  wire [1:0] n13 = read_binary[1:0];
  always @(posedge clk) begin
    if (rst) begin
      read_binary <= 3'd0;
      read_gray <= 3'd0;
      write_gray_sync0 <= 3'd0;
      write_gray_sync1 <= 3'd0;
    end else begin
      read_binary <= n10;
      read_gray <= n12;
      write_gray_sync0 <= raw_write_gray;
      write_gray_sync1 <= write_gray_sync0;
    end
  end
  assign o_read_binary = read_binary;
  assign o_read_gray = read_gray;
  assign o_write_gray_sync0 = write_gray_sync0;
  assign o_write_gray_sync1 = write_gray_sync1;
  assign sink_valid = n7;
  assign read_take = n8;
  assign read_address = n13;
endmodule

module async_queue_portable_writer_w46_d4(
  input wire clk,
  input wire rst,
  input wire [0:0] sssss,
  input wire [1:0] ssssss,
  input wire [45:0] sssssss,
  output wire [45:0] o_s,
  output wire [45:0] o_ss,
  output wire [45:0] o_sss,
  output wire [45:0] o_ssss
);
  reg [45:0] s;
  reg [45:0] ss;
  reg [45:0] sss;
  reg [45:0] ssss;
  wire [1:0] n0 = 2'd0;
  wire [0:0] n1 = ssssss == n0;
  wire [45:0] n2 = n1 ? sssssss : s;
  wire [45:0] n3 = sssss ? n2 : s;
  wire [1:0] n4 = 2'd1;
  wire [0:0] n5 = ssssss == n4;
  wire [45:0] n6 = n5 ? sssssss : ss;
  wire [45:0] n7 = sssss ? n6 : ss;
  wire [1:0] n8 = 2'd2;
  wire [0:0] n9 = ssssss == n8;
  wire [45:0] n10 = n9 ? sssssss : sss;
  wire [45:0] n11 = sssss ? n10 : sss;
  wire [1:0] n12 = 2'd3;
  wire [0:0] n13 = ssssss == n12;
  wire [45:0] n14 = n13 ? sssssss : ssss;
  wire [45:0] n15 = sssss ? n14 : ssss;
  always @(posedge clk) begin
    if (rst) begin
      s <= 46'd0;
      ss <= 46'd0;
      sss <= 46'd0;
      ssss <= 46'd0;
    end else begin
      s <= n3;
      ss <= n7;
      sss <= n11;
      ssss <= n15;
    end
  end
  assign o_s = s;
  assign o_ss = ss;
  assign o_sss = sss;
  assign o_ssss = ssss;
endmodule

module async_queue_portable_fwft_reader_w46_d4(
  input wire clk,
  input wire rst,
  input wire [45:0] s,
  input wire [45:0] ss,
  input wire [45:0] sss,
  input wire [45:0] ssss,
  input wire [0:0] ssssssss,
  input wire [1:0] sssssssss,
  output wire [45:0] read_sample
);
  wire [1:0] n0 = 2'd3;
  wire [0:0] n1 = sssssssss == n0;
  wire [1:0] n2 = 2'd2;
  wire [0:0] n3 = sssssssss == n2;
  wire [1:0] n4 = 2'd1;
  wire [0:0] n5 = sssssssss == n4;
  wire [1:0] n6 = 2'd0;
  wire [0:0] n7 = sssssssss == n6;
  wire [45:0] n8 = 46'd0;
  wire [45:0] n9 = n7 ? s : n8;
  wire [45:0] n10 = n5 ? ss : n9;
  wire [45:0] n11 = n3 ? sss : n10;
  wire [45:0] n12 = n1 ? ssss : n11;
  always @(posedge clk) begin
    if (rst) begin
    end else begin
    end
  end
  assign read_sample = n12;
endmodule

module loom_compiled_sync_fifo_cpu_request(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [49:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [49:0] dst_payload, input wire dst_pop
);
__loom_chan_cpu_request_sync_adapter u_sync_fifo (
  .clk(src_clk), .rst(rst),
  .__loom_chan_cpu_request_push(src_valid),
  .__loom_chan_cpu_request_push_payload(src_payload),
  .__loom_chan_cpu_request_pop(dst_pop),
  .source_ready(src_ready), .sink_valid(dst_valid),
  .sink_payload(dst_payload));
endmodule

module loom_compiled_sync_fifo_cpu_response(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [37:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [37:0] dst_payload, input wire dst_pop
);
__loom_chan_cpu_response_sync_adapter u_sync_fifo (
  .clk(src_clk), .rst(rst),
  .__loom_chan_cpu_response_push(src_valid),
  .__loom_chan_cpu_response_push_payload(src_payload),
  .__loom_chan_cpu_response_pop(dst_pop),
  .source_ready(src_ready), .sink_valid(dst_valid),
  .sink_payload(dst_payload));
endmodule

module loom_compiled_async_fifo_dma_request(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [49:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [49:0] dst_payload, input wire dst_pop
);
wire [2:0] write_binary, write_gray, read_gray_sync0, read_gray_sync1;
wire [2:0] read_binary, read_gray, write_gray_sync0, write_gray_sync1;
wire write_take, read_take, sink_valid;
wire [1:0] write_address, read_address;
wire [49:0] write_data, read_sample;
wire [49:0] slot_0, slot_1, slot_2, slot_3;
async_fifo_source_control_w50_d4 u_source_control (
  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),
  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),
  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),
  .source_ready(src_ready), .write_take(write_take),
  .write_address(write_address), .write_data(write_data));
async_fifo_sink_control_w50_d4 u_sink_control (
  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),
  .o_read_binary(read_binary), .o_read_gray(read_gray),
  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),
  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));
async_queue_portable_writer_w50_d4 u_storage_writer (
  .clk(src_clk), .rst(rst),
  .o_s(slot_0),
  .o_ss(slot_1),
  .o_sss(slot_2),
  .o_ssss(slot_3),
  .sssss(write_take),
  .ssssss(write_address),
  .sssssss(write_data));
async_queue_portable_fwft_reader_w50_d4 u_storage_reader (
  .clk(dst_clk), .rst(rst),
  .s(slot_0),
  .ss(slot_1),
  .sss(slot_2),
  .ssss(slot_3),
  .ssssssss(read_take),
  .sssssssss(read_address),
  .read_sample(read_sample));
assign dst_valid = sink_valid;
assign dst_payload = read_sample;
endmodule

module loom_compiled_async_fifo_dma_response(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [37:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [37:0] dst_payload, input wire dst_pop
);
wire [2:0] write_binary, write_gray, read_gray_sync0, read_gray_sync1;
wire [2:0] read_binary, read_gray, write_gray_sync0, write_gray_sync1;
wire write_take, read_take, sink_valid;
wire [1:0] write_address, read_address;
wire [37:0] write_data, read_sample;
wire [37:0] slot_0, slot_1, slot_2, slot_3;
async_fifo_source_control_w38_d4 u_source_control (
  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),
  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),
  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),
  .source_ready(src_ready), .write_take(write_take),
  .write_address(write_address), .write_data(write_data));
async_fifo_sink_control_w38_d4 u_sink_control (
  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),
  .o_read_binary(read_binary), .o_read_gray(read_gray),
  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),
  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));
async_queue_portable_writer_w38_d4 u_storage_writer (
  .clk(src_clk), .rst(rst),
  .o_s(slot_0),
  .o_ss(slot_1),
  .o_sss(slot_2),
  .o_ssss(slot_3),
  .sssss(write_take),
  .ssssss(write_address),
  .sssssss(write_data));
async_queue_portable_fwft_reader_w38_d4 u_storage_reader (
  .clk(dst_clk), .rst(rst),
  .s(slot_0),
  .ss(slot_1),
  .sss(slot_2),
  .ssss(slot_3),
  .ssssssss(read_take),
  .sssssssss(read_address),
  .read_sample(read_sample));
assign dst_valid = sink_valid;
assign dst_payload = read_sample;
endmodule

module loom_compiled_async_fifo_target_request(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [49:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [49:0] dst_payload, input wire dst_pop
);
wire [2:0] write_binary, write_gray, read_gray_sync0, read_gray_sync1;
wire [2:0] read_binary, read_gray, write_gray_sync0, write_gray_sync1;
wire write_take, read_take, sink_valid;
wire [1:0] write_address, read_address;
wire [49:0] write_data, read_sample;
wire [49:0] slot_0, slot_1, slot_2, slot_3;
async_fifo_source_control_w50_d4 u_source_control (
  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),
  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),
  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),
  .source_ready(src_ready), .write_take(write_take),
  .write_address(write_address), .write_data(write_data));
async_fifo_sink_control_w50_d4 u_sink_control (
  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),
  .o_read_binary(read_binary), .o_read_gray(read_gray),
  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),
  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));
async_queue_portable_writer_w50_d4 u_storage_writer (
  .clk(src_clk), .rst(rst),
  .o_s(slot_0),
  .o_ss(slot_1),
  .o_sss(slot_2),
  .o_ssss(slot_3),
  .sssss(write_take),
  .ssssss(write_address),
  .sssssss(write_data));
async_queue_portable_fwft_reader_w50_d4 u_storage_reader (
  .clk(dst_clk), .rst(rst),
  .s(slot_0),
  .ss(slot_1),
  .sss(slot_2),
  .ssss(slot_3),
  .ssssssss(read_take),
  .sssssssss(read_address),
  .read_sample(read_sample));
assign dst_valid = sink_valid;
assign dst_payload = read_sample;
endmodule

module loom_compiled_async_fifo_target_response(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [37:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [37:0] dst_payload, input wire dst_pop
);
wire [2:0] write_binary, write_gray, read_gray_sync0, read_gray_sync1;
wire [2:0] read_binary, read_gray, write_gray_sync0, write_gray_sync1;
wire write_take, read_take, sink_valid;
wire [1:0] write_address, read_address;
wire [37:0] write_data, read_sample;
wire [37:0] slot_0, slot_1, slot_2, slot_3;
async_fifo_source_control_w38_d4 u_source_control (
  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),
  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),
  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),
  .source_ready(src_ready), .write_take(write_take),
  .write_address(write_address), .write_data(write_data));
async_fifo_sink_control_w38_d4 u_sink_control (
  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),
  .o_read_binary(read_binary), .o_read_gray(read_gray),
  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),
  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));
async_queue_portable_writer_w38_d4 u_storage_writer (
  .clk(src_clk), .rst(rst),
  .o_s(slot_0),
  .o_ss(slot_1),
  .o_sss(slot_2),
  .o_ssss(slot_3),
  .sssss(write_take),
  .ssssss(write_address),
  .sssssss(write_data));
async_queue_portable_fwft_reader_w38_d4 u_storage_reader (
  .clk(dst_clk), .rst(rst),
  .s(slot_0),
  .ss(slot_1),
  .sss(slot_2),
  .ssss(slot_3),
  .ssssssss(read_take),
  .sssssssss(read_address),
  .read_sample(read_sample));
assign dst_valid = sink_valid;
assign dst_payload = read_sample;
endmodule

module loom_compiled_async_fifo_audit(
  input wire src_clk, input wire dst_clk, input wire rst,
  input wire src_valid, input wire [45:0] src_payload,
  output wire src_ready,
  output wire dst_valid,
  output wire [45:0] dst_payload, input wire dst_pop
);
wire [2:0] write_binary, write_gray, read_gray_sync0, read_gray_sync1;
wire [2:0] read_binary, read_gray, write_gray_sync0, write_gray_sync1;
wire write_take, read_take, sink_valid;
wire [1:0] write_address, read_address;
wire [45:0] write_data, read_sample;
wire [45:0] slot_0, slot_1, slot_2, slot_3;
async_fifo_source_control_w46_d4 u_source_control (
  .clk(src_clk), .rst(rst), .source_valid(src_valid), .source_payload(src_payload),
  .raw_read_gray(read_gray), .o_write_binary(write_binary), .o_write_gray(write_gray),
  .o_read_gray_sync0(read_gray_sync0), .o_read_gray_sync1(read_gray_sync1),
  .source_ready(src_ready), .write_take(write_take),
  .write_address(write_address), .write_data(write_data));
async_fifo_sink_control_w46_d4 u_sink_control (
  .clk(dst_clk), .rst(rst), .sink_pop(dst_pop), .raw_write_gray(write_gray),
  .o_read_binary(read_binary), .o_read_gray(read_gray),
  .o_write_gray_sync0(write_gray_sync0), .o_write_gray_sync1(write_gray_sync1),
  .sink_valid(sink_valid), .read_take(read_take), .read_address(read_address));
async_queue_portable_writer_w46_d4 u_storage_writer (
  .clk(src_clk), .rst(rst),
  .o_s(slot_0),
  .o_ss(slot_1),
  .o_sss(slot_2),
  .o_ssss(slot_3),
  .sssss(write_take),
  .ssssss(write_address),
  .sssssss(write_data));
async_queue_portable_fwft_reader_w46_d4 u_storage_reader (
  .clk(dst_clk), .rst(rst),
  .s(slot_0),
  .ss(slot_1),
  .sss(slot_2),
  .ssss(slot_3),
  .ssssssss(read_take),
  .sssssssss(read_address),
  .read_sample(read_sample));
assign dst_valid = sink_valid;
assign dst_payload = read_sample;
endmodule

module loom_system(
  input wire cpu_fabric_clk,
  input wire dma_clk,
  input wire mem_clk,
  input wire mon_clk,
  input wire rst,
  input wire cpu__hold_issue,
  input wire cpu__hold_response,
  input wire [31:0] cpu__transaction_limit,
  output wire [31:0] cpu__o_sequence,
  output wire cpu__o_active,
  output wire [3:0] cpu__o_active_tag,
  output wire [31:0] cpu__o_requests_staged,
  output wire [31:0] cpu__o_requests_accepted,
  output wire [31:0] cpu__o_responses_received,
  output wire [31:0] cpu__o_response_digest,
  output wire [31:0] cpu__o_request_stalls,
  output wire cpu__o_sticky_error,
  output wire [1:0] cpu__o_progress,
  input wire dma__hold_issue,
  input wire dma__hold_response,
  input wire [31:0] dma__transaction_limit,
  output wire [31:0] dma__o_sequence,
  output wire dma__o_active,
  output wire [3:0] dma__o_active_tag,
  output wire [31:0] dma__o_requests_staged,
  output wire [31:0] dma__o_requests_accepted,
  output wire [31:0] dma__o_responses_received,
  output wire [31:0] dma__o_response_digest,
  output wire [31:0] dma__o_request_stalls,
  output wire dma__o_sticky_error,
  output wire [1:0] dma__o_progress,
  input wire fabric__hold_arbitration,
  output wire fabric__o_round_robin,
  output wire fabric__o_outstanding,
  output wire fabric__o_route,
  output wire [31:0] fabric__o_cpu_grants,
  output wire [31:0] fabric__o_dma_grants,
  output wire [31:0] fabric__o_total_grants,
  output wire [31:0] fabric__o_responses_routed,
  output wire [31:0] fabric__o_contention_ticks,
  output wire [31:0] fabric__o_target_stalls,
  output wire [31:0] fabric__o_response_stalls,
  output wire fabric__o_double_grant_error,
  output wire [1:0] fabric__o_progress,
  output wire [31:0] service__o_commits,
  output wire [31:0] service__o_request_stalls,
  output wire [31:0] service__o_response_stalls,
  output wire [31:0] service__o_audit_stalls,
  output wire [1:0] service__o_progress,
  output wire [31:0] monitor__o_records,
  output wire [31:0] monitor__o_audit_digest,
  output wire [31:0] monitor__o_expected_digest,
  output wire [31:0] monitor__o_cpu_expected_sequence,
  output wire [31:0] monitor__o_dma_expected_sequence,
  output wire monitor__o_sticky_error,
  output wire [1:0] monitor__o_progress
);
wire cpu____loom_chan_cpu_request_src_ready;
wire cpu____loom_chan_cpu_request_src_accepted;
wire cpu____loom_chan_cpu_response_dst_valid;
wire [37:0] cpu____loom_chan_cpu_response_dst_payload;
wire cpu__o___loom_chan_cpu_request_src_valid;
wire [49:0] cpu__o___loom_chan_cpu_request_src_payload;
wire cpu__o___loom_chan_cpu_response_dst_pop;
wire dma____loom_chan_dma_request_src_ready;
wire dma____loom_chan_dma_request_src_accepted;
wire dma____loom_chan_dma_response_dst_valid;
wire [37:0] dma____loom_chan_dma_response_dst_payload;
wire dma__o___loom_chan_dma_request_src_valid;
wire [49:0] dma__o___loom_chan_dma_request_src_payload;
wire dma__o___loom_chan_dma_response_dst_pop;
wire fabric____loom_chan_target_request_src_ready;
wire fabric____loom_chan_target_request_src_accepted;
wire fabric____loom_chan_target_response_dst_valid;
wire [37:0] fabric____loom_chan_target_response_dst_payload;
wire fabric____loom_chan_cpu_request_dst_valid;
wire [49:0] fabric____loom_chan_cpu_request_dst_payload;
wire fabric____loom_chan_dma_request_dst_valid;
wire [49:0] fabric____loom_chan_dma_request_dst_payload;
wire fabric____loom_chan_cpu_response_src_ready;
wire fabric____loom_chan_cpu_response_src_accepted;
wire fabric____loom_chan_dma_response_src_ready;
wire fabric____loom_chan_dma_response_src_accepted;
wire fabric__o___loom_chan_target_request_src_valid;
wire [49:0] fabric__o___loom_chan_target_request_src_payload;
wire fabric__o___loom_chan_target_response_dst_pop;
wire fabric__o___loom_chan_cpu_request_dst_pop;
wire fabric__o___loom_chan_dma_request_dst_pop;
wire fabric__o___loom_chan_cpu_response_src_valid;
wire [37:0] fabric__o___loom_chan_cpu_response_src_payload;
wire fabric__o___loom_chan_dma_response_src_valid;
wire [37:0] fabric__o___loom_chan_dma_response_src_payload;
wire service____loom_chan_target_request_dst_valid;
wire [49:0] service____loom_chan_target_request_dst_payload;
wire service____loom_chan_target_response_src_ready;
wire service____loom_chan_target_response_src_accepted;
wire service____loom_chan_audit_src_ready;
wire service____loom_chan_audit_src_accepted;
wire service__o___loom_chan_target_request_dst_pop;
wire service__o___loom_chan_target_response_src_valid;
wire [37:0] service__o___loom_chan_target_response_src_payload;
wire service__o___loom_chan_audit_src_valid;
wire [45:0] service__o___loom_chan_audit_src_payload;
wire monitor____loom_chan_audit_dst_valid;
wire [45:0] monitor____loom_chan_audit_dst_payload;
wire monitor__o___loom_chan_audit_dst_pop;
soc_fabric_cpu u_island_cpu (.clk(cpu_fabric_clk), .rst(rst), .__loom_chan_cpu_request_src_ready(cpu____loom_chan_cpu_request_src_ready), .__loom_chan_cpu_request_src_accepted(cpu____loom_chan_cpu_request_src_accepted), .__loom_chan_cpu_response_dst_valid(cpu____loom_chan_cpu_response_dst_valid), .__loom_chan_cpu_response_dst_payload(cpu____loom_chan_cpu_response_dst_payload), .hold_issue(cpu__hold_issue), .hold_response(cpu__hold_response), .transaction_limit(cpu__transaction_limit), .o___loom_chan_cpu_request_src_valid(cpu__o___loom_chan_cpu_request_src_valid), .o___loom_chan_cpu_request_src_payload(cpu__o___loom_chan_cpu_request_src_payload), .o___loom_chan_cpu_response_dst_pop(cpu__o___loom_chan_cpu_response_dst_pop), .o_sequence(cpu__o_sequence), .o_active(cpu__o_active), .o_active_tag(cpu__o_active_tag), .o_requests_staged(cpu__o_requests_staged), .o_requests_accepted(cpu__o_requests_accepted), .o_responses_received(cpu__o_responses_received), .o_response_digest(cpu__o_response_digest), .o_request_stalls(cpu__o_request_stalls), .o_sticky_error(cpu__o_sticky_error), .o_progress(cpu__o_progress));
soc_fabric_dma u_island_dma (.clk(dma_clk), .rst(rst), .__loom_chan_dma_request_src_ready(dma____loom_chan_dma_request_src_ready), .__loom_chan_dma_request_src_accepted(dma____loom_chan_dma_request_src_accepted), .__loom_chan_dma_response_dst_valid(dma____loom_chan_dma_response_dst_valid), .__loom_chan_dma_response_dst_payload(dma____loom_chan_dma_response_dst_payload), .hold_issue(dma__hold_issue), .hold_response(dma__hold_response), .transaction_limit(dma__transaction_limit), .o___loom_chan_dma_request_src_valid(dma__o___loom_chan_dma_request_src_valid), .o___loom_chan_dma_request_src_payload(dma__o___loom_chan_dma_request_src_payload), .o___loom_chan_dma_response_dst_pop(dma__o___loom_chan_dma_response_dst_pop), .o_sequence(dma__o_sequence), .o_active(dma__o_active), .o_active_tag(dma__o_active_tag), .o_requests_staged(dma__o_requests_staged), .o_requests_accepted(dma__o_requests_accepted), .o_responses_received(dma__o_responses_received), .o_response_digest(dma__o_response_digest), .o_request_stalls(dma__o_request_stalls), .o_sticky_error(dma__o_sticky_error), .o_progress(dma__o_progress));
soc_fabric_arbiter u_island_fabric (.clk(cpu_fabric_clk), .rst(rst), .__loom_chan_target_request_src_ready(fabric____loom_chan_target_request_src_ready), .__loom_chan_target_request_src_accepted(fabric____loom_chan_target_request_src_accepted), .__loom_chan_target_response_dst_valid(fabric____loom_chan_target_response_dst_valid), .__loom_chan_target_response_dst_payload(fabric____loom_chan_target_response_dst_payload), .__loom_chan_cpu_request_dst_valid(fabric____loom_chan_cpu_request_dst_valid), .__loom_chan_cpu_request_dst_payload(fabric____loom_chan_cpu_request_dst_payload), .__loom_chan_dma_request_dst_valid(fabric____loom_chan_dma_request_dst_valid), .__loom_chan_dma_request_dst_payload(fabric____loom_chan_dma_request_dst_payload), .__loom_chan_cpu_response_src_ready(fabric____loom_chan_cpu_response_src_ready), .__loom_chan_cpu_response_src_accepted(fabric____loom_chan_cpu_response_src_accepted), .__loom_chan_dma_response_src_ready(fabric____loom_chan_dma_response_src_ready), .__loom_chan_dma_response_src_accepted(fabric____loom_chan_dma_response_src_accepted), .hold_arbitration(fabric__hold_arbitration), .o___loom_chan_target_request_src_valid(fabric__o___loom_chan_target_request_src_valid), .o___loom_chan_target_request_src_payload(fabric__o___loom_chan_target_request_src_payload), .o___loom_chan_target_response_dst_pop(fabric__o___loom_chan_target_response_dst_pop), .o___loom_chan_cpu_request_dst_pop(fabric__o___loom_chan_cpu_request_dst_pop), .o___loom_chan_dma_request_dst_pop(fabric__o___loom_chan_dma_request_dst_pop), .o___loom_chan_cpu_response_src_valid(fabric__o___loom_chan_cpu_response_src_valid), .o___loom_chan_cpu_response_src_payload(fabric__o___loom_chan_cpu_response_src_payload), .o___loom_chan_dma_response_src_valid(fabric__o___loom_chan_dma_response_src_valid), .o___loom_chan_dma_response_src_payload(fabric__o___loom_chan_dma_response_src_payload), .o_round_robin(fabric__o_round_robin), .o_outstanding(fabric__o_outstanding), .o_route(fabric__o_route), .o_cpu_grants(fabric__o_cpu_grants), .o_dma_grants(fabric__o_dma_grants), .o_total_grants(fabric__o_total_grants), .o_responses_routed(fabric__o_responses_routed), .o_contention_ticks(fabric__o_contention_ticks), .o_target_stalls(fabric__o_target_stalls), .o_response_stalls(fabric__o_response_stalls), .o_double_grant_error(fabric__o_double_grant_error), .o_progress(fabric__o_progress));
soc_fabric_register_service u_island_service (.clk(mem_clk), .rst(rst), .__loom_chan_target_request_dst_valid(service____loom_chan_target_request_dst_valid), .__loom_chan_target_request_dst_payload(service____loom_chan_target_request_dst_payload), .__loom_chan_target_response_src_ready(service____loom_chan_target_response_src_ready), .__loom_chan_target_response_src_accepted(service____loom_chan_target_response_src_accepted), .__loom_chan_audit_src_ready(service____loom_chan_audit_src_ready), .__loom_chan_audit_src_accepted(service____loom_chan_audit_src_accepted), .o___loom_chan_target_request_dst_pop(service__o___loom_chan_target_request_dst_pop), .o___loom_chan_target_response_src_valid(service__o___loom_chan_target_response_src_valid), .o___loom_chan_target_response_src_payload(service__o___loom_chan_target_response_src_payload), .o___loom_chan_audit_src_valid(service__o___loom_chan_audit_src_valid), .o___loom_chan_audit_src_payload(service__o___loom_chan_audit_src_payload), .o_commits(service__o_commits), .o_request_stalls(service__o_request_stalls), .o_response_stalls(service__o_response_stalls), .o_audit_stalls(service__o_audit_stalls), .o_progress(service__o_progress));
soc_fabric_audit_monitor u_island_monitor (.clk(mon_clk), .rst(rst), .__loom_chan_audit_dst_valid(monitor____loom_chan_audit_dst_valid), .__loom_chan_audit_dst_payload(monitor____loom_chan_audit_dst_payload), .o___loom_chan_audit_dst_pop(monitor__o___loom_chan_audit_dst_pop), .o_records(monitor__o_records), .o_audit_digest(monitor__o_audit_digest), .o_expected_digest(monitor__o_expected_digest), .o_cpu_expected_sequence(monitor__o_cpu_expected_sequence), .o_dma_expected_sequence(monitor__o_dma_expected_sequence), .o_sticky_error(monitor__o_sticky_error), .o_progress(monitor__o_progress));
loom_compiled_sync_fifo_cpu_request u_cpu_request (
  .src_clk(cpu_fabric_clk), .dst_clk(cpu_fabric_clk), .rst(rst),
  .src_valid(cpu__o___loom_chan_cpu_request_src_valid), .src_payload(cpu__o___loom_chan_cpu_request_src_payload), .src_ready(cpu____loom_chan_cpu_request_src_ready),
  .dst_valid(fabric____loom_chan_cpu_request_dst_valid), .dst_payload(fabric____loom_chan_cpu_request_dst_payload), .dst_pop(fabric__o___loom_chan_cpu_request_dst_pop));
assign cpu____loom_chan_cpu_request_src_accepted = cpu__o___loom_chan_cpu_request_src_valid && cpu____loom_chan_cpu_request_src_ready;

loom_compiled_sync_fifo_cpu_response u_cpu_response (
  .src_clk(cpu_fabric_clk), .dst_clk(cpu_fabric_clk), .rst(rst),
  .src_valid(fabric__o___loom_chan_cpu_response_src_valid), .src_payload(fabric__o___loom_chan_cpu_response_src_payload), .src_ready(fabric____loom_chan_cpu_response_src_ready),
  .dst_valid(cpu____loom_chan_cpu_response_dst_valid), .dst_payload(cpu____loom_chan_cpu_response_dst_payload), .dst_pop(cpu__o___loom_chan_cpu_response_dst_pop));
assign fabric____loom_chan_cpu_response_src_accepted = fabric__o___loom_chan_cpu_response_src_valid && fabric____loom_chan_cpu_response_src_ready;

loom_compiled_async_fifo_dma_request u_dma_request (
  .src_clk(dma_clk), .dst_clk(cpu_fabric_clk), .rst(rst),
  .src_valid(dma__o___loom_chan_dma_request_src_valid), .src_payload(dma__o___loom_chan_dma_request_src_payload), .src_ready(dma____loom_chan_dma_request_src_ready),
  .dst_valid(fabric____loom_chan_dma_request_dst_valid), .dst_payload(fabric____loom_chan_dma_request_dst_payload), .dst_pop(fabric__o___loom_chan_dma_request_dst_pop));
assign dma____loom_chan_dma_request_src_accepted = dma__o___loom_chan_dma_request_src_valid && dma____loom_chan_dma_request_src_ready;

loom_compiled_async_fifo_dma_response u_dma_response (
  .src_clk(cpu_fabric_clk), .dst_clk(dma_clk), .rst(rst),
  .src_valid(fabric__o___loom_chan_dma_response_src_valid), .src_payload(fabric__o___loom_chan_dma_response_src_payload), .src_ready(fabric____loom_chan_dma_response_src_ready),
  .dst_valid(dma____loom_chan_dma_response_dst_valid), .dst_payload(dma____loom_chan_dma_response_dst_payload), .dst_pop(dma__o___loom_chan_dma_response_dst_pop));
assign fabric____loom_chan_dma_response_src_accepted = fabric__o___loom_chan_dma_response_src_valid && fabric____loom_chan_dma_response_src_ready;

loom_compiled_async_fifo_target_request u_target_request (
  .src_clk(cpu_fabric_clk), .dst_clk(mem_clk), .rst(rst),
  .src_valid(fabric__o___loom_chan_target_request_src_valid), .src_payload(fabric__o___loom_chan_target_request_src_payload), .src_ready(fabric____loom_chan_target_request_src_ready),
  .dst_valid(service____loom_chan_target_request_dst_valid), .dst_payload(service____loom_chan_target_request_dst_payload), .dst_pop(service__o___loom_chan_target_request_dst_pop));
assign fabric____loom_chan_target_request_src_accepted = fabric__o___loom_chan_target_request_src_valid && fabric____loom_chan_target_request_src_ready;

loom_compiled_async_fifo_target_response u_target_response (
  .src_clk(mem_clk), .dst_clk(cpu_fabric_clk), .rst(rst),
  .src_valid(service__o___loom_chan_target_response_src_valid), .src_payload(service__o___loom_chan_target_response_src_payload), .src_ready(service____loom_chan_target_response_src_ready),
  .dst_valid(fabric____loom_chan_target_response_dst_valid), .dst_payload(fabric____loom_chan_target_response_dst_payload), .dst_pop(fabric__o___loom_chan_target_response_dst_pop));
assign service____loom_chan_target_response_src_accepted = service__o___loom_chan_target_response_src_valid && service____loom_chan_target_response_src_ready;

loom_compiled_async_fifo_audit u_audit (
  .src_clk(mem_clk), .dst_clk(mon_clk), .rst(rst),
  .src_valid(service__o___loom_chan_audit_src_valid), .src_payload(service__o___loom_chan_audit_src_payload), .src_ready(service____loom_chan_audit_src_ready),
  .dst_valid(monitor____loom_chan_audit_dst_valid), .dst_payload(monitor____loom_chan_audit_dst_payload), .dst_pop(monitor__o___loom_chan_audit_dst_pop));
assign service____loom_chan_audit_src_accepted = service__o___loom_chan_audit_src_valid && service____loom_chan_audit_src_ready;

endmodule