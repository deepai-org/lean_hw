# Clock-crossing constraint intent

This technology-neutral review report is derived from the checked System.
A selected FPGA or ASIC backend may translate it into tool-specific constraints.

## Channel `cpu_request`

No external clock constraint is required by this realization.

## Channel `cpu_response`

No external clock constraint is required by this realization.

## Channel `dma_request`

- Treat `dma_clk` and `cpu_fabric_clk` as asynchronous clocks.
- Preserve and identify the ordered synchronizer chain `u_dma_request/u_sink_control/write_gray_sync0` -> `u_dma_request/u_sink_control/write_gray_sync1` in destination clock `cpu_fabric_clk`.
- Constrain the 3-bit coherent CDC bus `u_dma_request/u_source_control/write_gray` -> `u_dma_request/u_sink_control/write_gray_sync0` (`dma_clk` to `cpu_fabric_clk`): maximum bus skew 1/1 of the faster endpoint clock (`dma_clk` or `cpu_fabric_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`dma_clk` or `cpu_fabric_clk`) period.
- Preserve and identify the ordered synchronizer chain `u_dma_request/u_source_control/read_gray_sync0` -> `u_dma_request/u_source_control/read_gray_sync1` in destination clock `dma_clk`.
- Constrain the 3-bit coherent CDC bus `u_dma_request/u_sink_control/read_gray` -> `u_dma_request/u_source_control/read_gray_sync0` (`cpu_fabric_clk` to `dma_clk`): maximum bus skew 1/1 of the faster endpoint clock (`dma_clk` or `cpu_fabric_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`dma_clk` or `cpu_fabric_clk`) period.

## Channel `dma_response`

- Treat `cpu_fabric_clk` and `dma_clk` as asynchronous clocks.
- Preserve and identify the ordered synchronizer chain `u_dma_response/u_sink_control/write_gray_sync0` -> `u_dma_response/u_sink_control/write_gray_sync1` in destination clock `dma_clk`.
- Constrain the 3-bit coherent CDC bus `u_dma_response/u_source_control/write_gray` -> `u_dma_response/u_sink_control/write_gray_sync0` (`cpu_fabric_clk` to `dma_clk`): maximum bus skew 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `dma_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `dma_clk`) period.
- Preserve and identify the ordered synchronizer chain `u_dma_response/u_source_control/read_gray_sync0` -> `u_dma_response/u_source_control/read_gray_sync1` in destination clock `cpu_fabric_clk`.
- Constrain the 3-bit coherent CDC bus `u_dma_response/u_sink_control/read_gray` -> `u_dma_response/u_source_control/read_gray_sync0` (`dma_clk` to `cpu_fabric_clk`): maximum bus skew 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `dma_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `dma_clk`) period.

## Channel `target_request`

- Treat `cpu_fabric_clk` and `mem_clk` as asynchronous clocks.
- Preserve and identify the ordered synchronizer chain `u_target_request/u_sink_control/write_gray_sync0` -> `u_target_request/u_sink_control/write_gray_sync1` in destination clock `mem_clk`.
- Constrain the 3-bit coherent CDC bus `u_target_request/u_source_control/write_gray` -> `u_target_request/u_sink_control/write_gray_sync0` (`cpu_fabric_clk` to `mem_clk`): maximum bus skew 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `mem_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `mem_clk`) period.
- Preserve and identify the ordered synchronizer chain `u_target_request/u_source_control/read_gray_sync0` -> `u_target_request/u_source_control/read_gray_sync1` in destination clock `cpu_fabric_clk`.
- Constrain the 3-bit coherent CDC bus `u_target_request/u_sink_control/read_gray` -> `u_target_request/u_source_control/read_gray_sync0` (`mem_clk` to `cpu_fabric_clk`): maximum bus skew 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `mem_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`cpu_fabric_clk` or `mem_clk`) period.

## Channel `target_response`

- Treat `mem_clk` and `cpu_fabric_clk` as asynchronous clocks.
- Preserve and identify the ordered synchronizer chain `u_target_response/u_sink_control/write_gray_sync0` -> `u_target_response/u_sink_control/write_gray_sync1` in destination clock `cpu_fabric_clk`.
- Constrain the 3-bit coherent CDC bus `u_target_response/u_source_control/write_gray` -> `u_target_response/u_sink_control/write_gray_sync0` (`mem_clk` to `cpu_fabric_clk`): maximum bus skew 1/1 of the faster endpoint clock (`mem_clk` or `cpu_fabric_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`mem_clk` or `cpu_fabric_clk`) period.
- Preserve and identify the ordered synchronizer chain `u_target_response/u_source_control/read_gray_sync0` -> `u_target_response/u_source_control/read_gray_sync1` in destination clock `mem_clk`.
- Constrain the 3-bit coherent CDC bus `u_target_response/u_sink_control/read_gray` -> `u_target_response/u_source_control/read_gray_sync0` (`cpu_fabric_clk` to `mem_clk`): maximum bus skew 1/1 of the faster endpoint clock (`mem_clk` or `cpu_fabric_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`mem_clk` or `cpu_fabric_clk`) period.

## Channel `audit`

- Treat `mem_clk` and `mon_clk` as asynchronous clocks.
- Preserve and identify the ordered synchronizer chain `u_audit/u_sink_control/write_gray_sync0` -> `u_audit/u_sink_control/write_gray_sync1` in destination clock `mon_clk`.
- Constrain the 3-bit coherent CDC bus `u_audit/u_source_control/write_gray` -> `u_audit/u_sink_control/write_gray_sync0` (`mem_clk` to `mon_clk`): maximum bus skew 1/1 of the faster endpoint clock (`mem_clk` or `mon_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`mem_clk` or `mon_clk`) period.
- Preserve and identify the ordered synchronizer chain `u_audit/u_source_control/read_gray_sync0` -> `u_audit/u_source_control/read_gray_sync1` in destination clock `mem_clk`.
- Constrain the 3-bit coherent CDC bus `u_audit/u_sink_control/read_gray` -> `u_audit/u_source_control/read_gray_sync0` (`mon_clk` to `mem_clk`): maximum bus skew 1/1 of the faster endpoint clock (`mem_clk` or `mon_clk`) period and maximum datapath delay 1/1 of the faster endpoint clock (`mem_clk` or `mon_clk`) period.

# Reset delivery intent

This describes generated RTL behavior, not a physical reset tree.
- Clock `cpu_fabric_clk`: `rst` is active high and sampled synchronously; release is sampled independently by this domain; no reset synchronizer is implied. This clock must tick while reset is asserted.
- Clock `dma_clk`: `rst` is active high and sampled synchronously; release is sampled independently by this domain; no reset synchronizer is implied. This clock must tick while reset is asserted.
- Clock `mem_clk`: `rst` is active high and sampled synchronously; release is sampled independently by this domain; no reset synchronizer is implied. This clock must tick while reset is asserted.
- Clock `mon_clk`: `rst` is active high and sampled synchronously; release is sampled independently by this domain; no reset synchronizer is implied. This clock must tick while reset is asserted.
