set_property PACKAGE_PIN D18 [get_ports sys_clk_p]
set_property PACKAGE_PIN C19 [get_ports sys_clk_n]
set_property IOSTANDARD LVDS_25 [get_ports sys_clk_p]
set_property IOSTANDARD LVDS_25 [get_ports sys_clk_n]
create_clock -name board_clk_200mhz -period 5.000 [get_ports sys_clk_p]

set_property PACKAGE_PIN Y9 [get_ports usr_clk_p]
set_property PACKAGE_PIN Y8 [get_ports usr_clk_n]
set_property IOSTANDARD LVDS_25 [get_ports usr_clk_p]
set_property IOSTANDARD LVDS_25 [get_ports usr_clk_n]
create_clock -name user_clk_156mhz -period 6.400 [get_ports usr_clk_p]

set_property PACKAGE_PIN P17 [get_ports {leds[0]}]
set_property PACKAGE_PIN P18 [get_ports {leds[1]}]
set_property PACKAGE_PIN W10 [get_ports {leds[2]}]
set_property PACKAGE_PIN V7  [get_ports {leds[3]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[0]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[1]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[2]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[3]}]

create_generated_clock -name surface_source_clk -source [get_ports usr_clk_p] \
  -divide_by 1 [get_pins u_source_gate/O]
create_clock -name ps_fclk0 -period 10.000 [get_pins {u_ps7/FCLKCLK[0]}]
create_generated_clock -name surface_sink_clk -source [get_pins {u_ps7/FCLKCLK[0]}] \
  -divide_by 1 [get_pins u_sink_gate/O]
create_clock -name surface_bscan_tck -period 10.000 [get_pins u_bscan/TCK]

# CDC cell attributes and path constraints are applied after synthesis by
# surface_matrix_cdc.tcl.  A clock-group exception is intentionally absent:
# Vivado gives it priority over the required Gray-bus max-delay constraints.
