# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  ipgui::add_param $IPINST -name "COMPLEX_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "CP_LENGTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "OFDM_SYMBOL_SIZE" -parent ${Page_0}
  ipgui::add_param $IPINST -name "SSR" -parent ${Page_0}
  ipgui::add_param $IPINST -name "S_AXIS_TDATA_WIDTH" -parent ${Page_0}


}

proc update_PARAM_VALUE.COMPLEX_WIDTH { PARAM_VALUE.COMPLEX_WIDTH } {
	# Procedure called to update COMPLEX_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.COMPLEX_WIDTH { PARAM_VALUE.COMPLEX_WIDTH } {
	# Procedure called to validate COMPLEX_WIDTH
	return true
}

proc update_PARAM_VALUE.CP_LENGTH { PARAM_VALUE.CP_LENGTH } {
	# Procedure called to update CP_LENGTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.CP_LENGTH { PARAM_VALUE.CP_LENGTH } {
	# Procedure called to validate CP_LENGTH
	return true
}

proc update_PARAM_VALUE.OFDM_SYMBOL_SIZE { PARAM_VALUE.OFDM_SYMBOL_SIZE } {
	# Procedure called to update OFDM_SYMBOL_SIZE when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.OFDM_SYMBOL_SIZE { PARAM_VALUE.OFDM_SYMBOL_SIZE } {
	# Procedure called to validate OFDM_SYMBOL_SIZE
	return true
}

proc update_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to update SSR when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to validate SSR
	return true
}

proc update_PARAM_VALUE.S_AXIS_TDATA_WIDTH { PARAM_VALUE.S_AXIS_TDATA_WIDTH } {
	# Procedure called to update S_AXIS_TDATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.S_AXIS_TDATA_WIDTH { PARAM_VALUE.S_AXIS_TDATA_WIDTH } {
	# Procedure called to validate S_AXIS_TDATA_WIDTH
	return true
}


proc update_MODELPARAM_VALUE.S_AXIS_TDATA_WIDTH { MODELPARAM_VALUE.S_AXIS_TDATA_WIDTH PARAM_VALUE.S_AXIS_TDATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.S_AXIS_TDATA_WIDTH}] ${MODELPARAM_VALUE.S_AXIS_TDATA_WIDTH}
}

proc update_MODELPARAM_VALUE.OFDM_SYMBOL_SIZE { MODELPARAM_VALUE.OFDM_SYMBOL_SIZE PARAM_VALUE.OFDM_SYMBOL_SIZE } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.OFDM_SYMBOL_SIZE}] ${MODELPARAM_VALUE.OFDM_SYMBOL_SIZE}
}

proc update_MODELPARAM_VALUE.CP_LENGTH { MODELPARAM_VALUE.CP_LENGTH PARAM_VALUE.CP_LENGTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.CP_LENGTH}] ${MODELPARAM_VALUE.CP_LENGTH}
}

proc update_MODELPARAM_VALUE.SSR { MODELPARAM_VALUE.SSR PARAM_VALUE.SSR } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SSR}] ${MODELPARAM_VALUE.SSR}
}

proc update_MODELPARAM_VALUE.COMPLEX_WIDTH { MODELPARAM_VALUE.COMPLEX_WIDTH PARAM_VALUE.COMPLEX_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.COMPLEX_WIDTH}] ${MODELPARAM_VALUE.COMPLEX_WIDTH}
}

