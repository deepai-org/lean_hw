# Neutral import coverage

This report executes the fail-closed Yosys-to-neutral-IR translator over
every module in one exact elaborated artifact. Acceptance means neutral IR
translation only; it does not imply emitted RTL equivalence or signoff.

- Modules: 74
- Accepted neutral imports: 18
- Blocked neutral imports: 56
- Elaborated JSON SHA-256: `8898eac9eba9975b617b9741cfd96210790f63cf694bcb07cb87f01641dad0f9`

## Blocker classes

- `four_state_constant`: 28 module(s)
- `instance_output_binding`: 30 module(s)
- `memory_cell`: 6 module(s)
- `multiple_clock_domains`: 1 module(s)
- `multiple_reset_domains`: 8 module(s)
- `resetless_state`: 4 module(s)
- `yosys_cell`: 21 module(s)

## Per-module status

| Module | Status | Blocker classes |
|---|---|---|
| `$paramod$07648fe22cda1c5887fba6b98d56d491849e8d4b\sdram_cfg_if` | BLOCKED | `multiple_reset_domains` |
| `$paramod$24edb32283c2798b1a9de01e5e8a5775f3de8d6d\spi_if` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod$2c2a78eaab39f077d28c359da24eea1bb3ee72ca\sysinfo_if` | ACCEPTED | — |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | BLOCKED | `memory_cell`, `yosys_cell` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | BLOCKED | `four_state_constant`, `multiple_clock_domains`, `yosys_cell` |
| `$paramod$530c0f32123495a95a65ef2dee5adb9a30a708f6\spi_if` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | BLOCKED | `four_state_constant`, `instance_output_binding`, `yosys_cell` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | BLOCKED | `memory_cell` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_D$` | BLOCKED | `four_state_constant`, `instance_output_binding`, `yosys_cell` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | BLOCKED | `four_state_constant`, `instance_output_binding`, `yosys_cell` |
| `$paramod$7639c2062dbcb83ce6fca4673452b1d6f11c5802\dff_kianV` | ACCEPTED | — |
| `$paramod$80b52c6771af61c058960d8e594f8fa1878424bc\div_if` | ACCEPTED | — |
| `$paramod$97c33ce1f197c7d09a6065d46e5aec5f4fa18127\Word_Reducer` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | BLOCKED | `four_state_constant`, `memory_cell` |
| `$paramod$9e9c3eac67bdfcffcee59edb9321066a49ebd9bc\gpio_if` | BLOCKED | `instance_output_binding` |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | BLOCKED | `four_state_constant`, `instance_output_binding`, `yosys_cell` |
| `$paramod$a39b4da5cbc02a0ba8e2c33f3a070905ed9e4012\kianv_harris_mc_edition` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod$b21d8177f76650034fcf5c651716b86b29dd0174\spi_nor_if` | BLOCKED | `instance_output_binding` |
| `$paramod$e0de9e5afae9227897f68c4fd4bf06762d640101\Bit_Reducer` | ACCEPTED | — |
| `$paramod$e990c30bcd7893b07a35da62716c79724dd6c561\dff_kianV` | ACCEPTED | — |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | BLOCKED | `four_state_constant`, `instance_output_binding`, `multiple_reset_domains` |
| `$paramod\Bitmask_Isolate_Rightmost_1_Bit\WORD_WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\Logarithm_of_Powers_of_Two\WORD_WIDTH=s32'00000000000000000000000000100000` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod\Priority_Encoder\WORD_WIDTH=s32'00000000000000000000000000100000` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod\cache\BYPASS_CACHES=1'0` | BLOCKED | `instance_output_binding` |
| `$paramod\clint_if\BASE_HI=8'00000010` | BLOCKED | `instance_output_binding` |
| `$paramod\counter\WIDTH=s32'00000000000000000000000001000000` | ACCEPTED | — |
| `$paramod\datapath_unit\RESET_ADDR=32'00100000000100000000000000000000` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `$paramod\dff_kianV\WIDTH=s32'00000000000000000000000000000001` | ACCEPTED | — |
| `$paramod\dff_kianV\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\dlatch_kianV\WIDTH=s32'00000000000000000000000000000010` | BLOCKED | `resetless_state` |
| `$paramod\dlatch_kianV\WIDTH=s32'00000000000000000000000000100000` | BLOCKED | `resetless_state` |
| `$paramod\mux2\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\mux4\WIDTH=s32'00000000000000000000000000100000` | BLOCKED | `instance_output_binding` |
| `$paramod\mux5\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\mux6\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\plic_if\BASE_HI=8'00001100` | BLOCKED | `instance_output_binding` |
| `$paramod\spi\CPOL=1'0` | BLOCKED | `multiple_reset_domains` |
| `alu` | ACCEPTED | — |
| `alu_decoder` | BLOCKED | `four_state_constant`, `memory_cell` |
| `chip_core` | BLOCKED | `instance_output_binding` |
| `clint` | ACCEPTED | — |
| `control_unit` | BLOCKED | `instance_output_binding` |
| `csr_decoder` | ACCEPTED | — |
| `csr_exception_handler` | BLOCKED | `instance_output_binding` |
| `csr_unit` | BLOCKED | `four_state_constant`, `instance_output_binding`, `yosys_cell` |
| `dcache` | BLOCKED | `four_state_constant`, `instance_output_binding`, `multiple_reset_domains`, `yosys_cell` |
| `divider` | BLOCKED | `four_state_constant`, `yosys_cell` |
| `divider_decoder` | BLOCKED | `four_state_constant` |
| `extend` | ACCEPTED | — |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | BLOCKED | `four_state_constant`, `memory_cell`, `resetless_state` |
| `gpio` | BLOCKED | `four_state_constant` |
| `icache` | BLOCKED | `four_state_constant`, `instance_output_binding`, `multiple_reset_domains`, `yosys_cell` |
| `interrupt_controller` | ACCEPTED | — |
| `load_alignment` | BLOCKED | `four_state_constant` |
| `load_decoder` | BLOCKED | `four_state_constant` |
| `main_fsm` | BLOCKED | `four_state_constant` |
| `mtime_source` | BLOCKED | `four_state_constant` |
| `multiplier` | BLOCKED | `four_state_constant`, `multiple_reset_domains` |
| `multiplier_decoder` | BLOCKED | `four_state_constant` |
| `multiplier_extension_decoder` | BLOCKED | `instance_output_binding` |
| `mux2` | ACCEPTED | — |
| `plic` | BLOCKED | `instance_output_binding`, `yosys_cell` |
| `register_file` | BLOCKED | `memory_cell` |
| `rx_uart` | BLOCKED | `four_state_constant`, `instance_output_binding`, `yosys_cell` |
| `soc` | BLOCKED | `instance_output_binding`, `multiple_reset_domains`, `yosys_cell` |
| `spi_nor_flash` | BLOCKED | `four_state_constant` |
| `sram_sp_gf180_512x56` | BLOCKED | `instance_output_binding` |
| `store_alignment` | BLOCKED | `four_state_constant` |
| `store_decoder` | BLOCKED | `four_state_constant` |
| `sv32_translate_data_to_physical` | BLOCKED | `four_state_constant` |
| `sv32_translate_instruction_to_physical` | BLOCKED | `four_state_constant` |
| `sync_2ff` | BLOCKED | `resetless_state` |
| `tx_uart` | BLOCKED | `four_state_constant`, `instance_output_binding`, `multiple_reset_domains`, `yosys_cell` |
