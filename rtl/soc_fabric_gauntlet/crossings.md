# Clock-crossing inventory

This human-readable report is derived from the checked System declaration.

Channel | Width | Depth | Co-tick policy | Source | Source clock | Sink | Sink clock
--- | ---: | ---: | --- | --- | --- | --- | ---
`cpu_request` | 50 | 2 | exchange | `cpu` | `cpu_fabric_clk` | `fabric` | `cpu_fabric_clk`
`cpu_response` | 38 | 2 | exchange | `fabric` | `cpu_fabric_clk` | `cpu` | `cpu_fabric_clk`
`dma_request` | 50 | 4 | exchange | `dma` | `dma_clk` | `fabric` | `cpu_fabric_clk`
`dma_response` | 38 | 4 | exchange | `fabric` | `cpu_fabric_clk` | `dma` | `dma_clk`
`target_request` | 50 | 4 | exchange | `fabric` | `cpu_fabric_clk` | `service` | `mem_clk`
`target_response` | 38 | 4 | exchange | `service` | `mem_clk` | `fabric` | `cpu_fabric_clk`
`audit` | 46 | 4 | exchange | `service` | `mem_clk` | `monitor` | `mon_clk`
