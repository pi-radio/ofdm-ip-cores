# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  ipgui::add_param $IPINST -name "C_S_AXI_ADDR_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "C_S_AXI_DATA_WIDTH" -parent ${Page_0}


}

proc update_PARAM_VALUE.C_S_AXIS_DATA_WIDTH { PARAM_VALUE.C_S_AXIS_DATA_WIDTH } {
	# Procedure called to update C_S_AXIS_DATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_S_AXIS_DATA_WIDTH { PARAM_VALUE.C_S_AXIS_DATA_WIDTH } {
	# Procedure called to validate C_S_AXIS_DATA_WIDTH
	return true
}

proc update_PARAM_VALUE.C_S_AXI_ADDR_WIDTH { PARAM_VALUE.C_S_AXI_ADDR_WIDTH } {
	# Procedure called to update C_S_AXI_ADDR_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_S_AXI_ADDR_WIDTH { PARAM_VALUE.C_S_AXI_ADDR_WIDTH } {
	# Procedure called to validate C_S_AXI_ADDR_WIDTH
	return true
}

proc update_PARAM_VALUE.C_S_AXI_DATA_WIDTH { PARAM_VALUE.C_S_AXI_DATA_WIDTH } {
	# Procedure called to update C_S_AXI_DATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_S_AXI_DATA_WIDTH { PARAM_VALUE.C_S_AXI_DATA_WIDTH } {
	# Procedure called to validate C_S_AXI_DATA_WIDTH
	return true
}

proc update_PARAM_VALUE.INTEGRATION_LENGTH { PARAM_VALUE.INTEGRATION_LENGTH } {
	# Procedure called to update INTEGRATION_LENGTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.INTEGRATION_LENGTH { PARAM_VALUE.INTEGRATION_LENGTH } {
	# Procedure called to validate INTEGRATION_LENGTH
	return true
}

proc update_PARAM_VALUE.INTEGRATION_TIME { PARAM_VALUE.INTEGRATION_TIME } {
	# Procedure called to update INTEGRATION_TIME when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.INTEGRATION_TIME { PARAM_VALUE.INTEGRATION_TIME } {
	# Procedure called to validate INTEGRATION_TIME
	return true
}

proc update_PARAM_VALUE.SAMPLE_WIDTH { PARAM_VALUE.SAMPLE_WIDTH } {
	# Procedure called to update SAMPLE_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SAMPLE_WIDTH { PARAM_VALUE.SAMPLE_WIDTH } {
	# Procedure called to validate SAMPLE_WIDTH
	return true
}

proc update_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to update SSR when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to validate SSR
	return true
}


proc update_MODELPARAM_VALUE.C_S_AXI_DATA_WIDTH { MODELPARAM_VALUE.C_S_AXI_DATA_WIDTH PARAM_VALUE.C_S_AXI_DATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_S_AXI_DATA_WIDTH}] ${MODELPARAM_VALUE.C_S_AXI_DATA_WIDTH}
}

proc update_MODELPARAM_VALUE.C_S_AXI_ADDR_WIDTH { MODELPARAM_VALUE.C_S_AXI_ADDR_WIDTH PARAM_VALUE.C_S_AXI_ADDR_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_S_AXI_ADDR_WIDTH}] ${MODELPARAM_VALUE.C_S_AXI_ADDR_WIDTH}
}

proc update_MODELPARAM_VALUE.C_S_AXIS_DATA_WIDTH { MODELPARAM_VALUE.C_S_AXIS_DATA_WIDTH PARAM_VALUE.C_S_AXIS_DATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_S_AXIS_DATA_WIDTH}] ${MODELPARAM_VALUE.C_S_AXIS_DATA_WIDTH}
}

proc update_MODELPARAM_VALUE.INTEGRATION_LENGTH { MODELPARAM_VALUE.INTEGRATION_LENGTH PARAM_VALUE.INTEGRATION_LENGTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.INTEGRATION_LENGTH}] ${MODELPARAM_VALUE.INTEGRATION_LENGTH}
}

proc update_MODELPARAM_VALUE.SSR { MODELPARAM_VALUE.SSR PARAM_VALUE.SSR } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SSR}] ${MODELPARAM_VALUE.SSR}
}

proc update_MODELPARAM_VALUE.SAMPLE_WIDTH { MODELPARAM_VALUE.SAMPLE_WIDTH PARAM_VALUE.SAMPLE_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SAMPLE_WIDTH}] ${MODELPARAM_VALUE.SAMPLE_WIDTH}
}

proc update_MODELPARAM_VALUE.INTEGRATION_TIME { MODELPARAM_VALUE.INTEGRATION_TIME PARAM_VALUE.INTEGRATION_TIME } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.INTEGRATION_TIME}] ${MODELPARAM_VALUE.INTEGRATION_TIME}
}

