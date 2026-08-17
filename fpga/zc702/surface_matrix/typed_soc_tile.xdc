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

create_generated_clock -name tile_core_clk -source [get_ports sys_clk_p] \
  -divide_by 4 [get_pins u_core_gate/O]
create_clock -name ps_fclk0 -period 10.000 [get_pins {u_ps7/FCLKCLK[0]}]
create_generated_clock -name tile_memory_clk -source [get_pins {u_ps7/FCLKCLK[0]}] \
  -divide_by 1 [get_pins u_memory_gate/O]
create_clock -name tile_bscan_tck -period 10.000 [get_pins u_bscan/TCK]

# Exact CDC attributes and Gray-bus constraints are derived from the emitted
# crossing inventory during signoff.  openXC7 currently consumes only the pin
# and primary-clock subset; that limitation remains explicit in its report.
