# SoC Fabric Gauntlet timing contracts

- cpu_request: compiled synchronous FIFO; aligned cpu_fabric_clk endpoints
- cpu_response: compiled synchronous FIFO; aligned cpu_fabric_clk endpoints
- dma_request: portable Gray FIFO; dma_clk -> cpu_fabric_clk
- dma_response: portable Gray FIFO; cpu_fabric_clk -> dma_clk
- target_request: portable Gray FIFO; cpu_fabric_clk -> mem_clk
- target_response: portable Gray FIFO; mem_clk -> cpu_fabric_clk
- audit: portable Gray FIFO; mem_clk -> mon_clk

Portable asynchronous routes have two forward and two reverse synchronizer stages.
Delivery bounds remain schedule-dependent on explicit continued-ticking/consumption premises.
