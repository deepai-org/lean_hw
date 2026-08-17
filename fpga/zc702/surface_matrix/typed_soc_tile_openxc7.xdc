# openXC7-compatible placement view.  The authoritative physical intent is
# typed_soc_tile.xdc; this backend cannot resolve PS7/BUFG/BSCAN get_pins or
# generated-clock commands, so route evidence from this file is explicitly
# incomplete for timing/CDC signoff.
set_property PACKAGE_PIN D18 [get_ports sys_clk_p]
set_property PACKAGE_PIN C19 [get_ports sys_clk_n]
set_property IOSTANDARD LVDS_25 [get_ports sys_clk_p]
set_property IOSTANDARD LVDS_25 [get_ports sys_clk_n]
create_clock -name board_clk_200mhz -period 5.000 [get_ports sys_clk_p]

set_property PACKAGE_PIN Y9 [get_ports usr_clk_p]
set_property PACKAGE_PIN Y8 [get_ports usr_clk_n]
set_property IOSTANDARD LVDS_25 [get_ports usr_clk_p]
set_property IOSTANDARD LVDS_25 [get_ports usr_clk_n]
create_clock -name tile_core_root_156mhz -period 6.400 [get_ports usr_clk_p]

set_property PACKAGE_PIN P17 [get_ports {leds[0]}]
set_property PACKAGE_PIN P18 [get_ports {leds[1]}]
set_property PACKAGE_PIN W10 [get_ports {leds[2]}]
set_property PACKAGE_PIN V7  [get_ports {leds[3]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[0]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[1]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[2]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[3]}]
