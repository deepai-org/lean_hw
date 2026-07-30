# ZC702 constraints for the Loom s0blinky first-light build (openXC7 flow).
# 200 MHz system differential clock
set_property PACKAGE_PIN D18 [get_ports sys_clk_p]
set_property PACKAGE_PIN C19 [get_ports sys_clk_n]
set_property IOSTANDARD LVDS_25 [get_ports sys_clk_p]
set_property IOSTANDARD LVDS_25 [get_ports sys_clk_n]
create_clock -period 5.000 [get_ports sys_clk_p]

# User LEDs (LVCMOS25)
set_property PACKAGE_PIN P17 [get_ports {leds[0]}]
set_property PACKAGE_PIN P18 [get_ports {leds[1]}]
set_property PACKAGE_PIN W10 [get_ports {leds[2]}]
set_property PACKAGE_PIN V7  [get_ports {leds[3]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[0]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[1]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[2]}]
set_property IOSTANDARD LVCMOS25 [get_ports {leds[3]}]
