# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  ipgui::add_page $IPINST -name "Page 0"

  ipgui::add_param $IPINST -name "CORR_DATA_WIDTH"
  ipgui::add_param $IPINST -name "DATA_WIDTH"
  ipgui::add_param $IPINST -name "cp_rm_enable" -widget comboBox
  ipgui::add_param $IPINST -name "NUM_DATA_SYMBOLS"

}

proc update_PARAM_VALUE.CORR_DATA_WIDTH { PARAM_VALUE.CORR_DATA_WIDTH } {
	# Procedure called to update CORR_DATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.CORR_DATA_WIDTH { PARAM_VALUE.CORR_DATA_WIDTH } {
	# Procedure called to validate CORR_DATA_WIDTH
	return true
}

proc update_PARAM_VALUE.DATA_WIDTH { PARAM_VALUE.DATA_WIDTH } {
	# Procedure called to update DATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.DATA_WIDTH { PARAM_VALUE.DATA_WIDTH } {
	# Procedure called to validate DATA_WIDTH
	return true
}

proc update_PARAM_VALUE.NUM_DATA_SYMBOLS { PARAM_VALUE.NUM_DATA_SYMBOLS } {
	# Procedure called to update NUM_DATA_SYMBOLS when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.NUM_DATA_SYMBOLS { PARAM_VALUE.NUM_DATA_SYMBOLS } {
	# Procedure called to validate NUM_DATA_SYMBOLS
	return true
}

proc update_PARAM_VALUE.cp_rm_enable { PARAM_VALUE.cp_rm_enable } {
	# Procedure called to update cp_rm_enable when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.cp_rm_enable { PARAM_VALUE.cp_rm_enable } {
	# Procedure called to validate cp_rm_enable
	return true
}


proc update_MODELPARAM_VALUE.CORR_DATA_WIDTH { MODELPARAM_VALUE.CORR_DATA_WIDTH PARAM_VALUE.CORR_DATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.CORR_DATA_WIDTH}] ${MODELPARAM_VALUE.CORR_DATA_WIDTH}
}

proc update_MODELPARAM_VALUE.DATA_WIDTH { MODELPARAM_VALUE.DATA_WIDTH PARAM_VALUE.DATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.DATA_WIDTH}] ${MODELPARAM_VALUE.DATA_WIDTH}
}

proc update_MODELPARAM_VALUE.cp_rm_enable { MODELPARAM_VALUE.cp_rm_enable PARAM_VALUE.cp_rm_enable } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.cp_rm_enable}] ${MODELPARAM_VALUE.cp_rm_enable}
}

proc update_MODELPARAM_VALUE.NUM_DATA_SYMBOLS { MODELPARAM_VALUE.NUM_DATA_SYMBOLS PARAM_VALUE.NUM_DATA_SYMBOLS } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.NUM_DATA_SYMBOLS}] ${MODELPARAM_VALUE.NUM_DATA_SYMBOLS}
}

