# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  ipgui::add_param $IPINST -name "C_M_AXIS_DATA_TDATA_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "C_S_AXIS_DATA_TDATA_WIDTH" -parent ${Page_0}

  ipgui::add_param $IPINST -name "SAMPS_PER_FRAME"

}

proc update_PARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH { PARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH } {
	# Procedure called to update C_M_AXIS_DATA_TDATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH { PARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH } {
	# Procedure called to validate C_M_AXIS_DATA_TDATA_WIDTH
	return true
}

proc update_PARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH { PARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH } {
	# Procedure called to update C_S_AXIS_DATA_TDATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH { PARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH } {
	# Procedure called to validate C_S_AXIS_DATA_TDATA_WIDTH
	return true
}

proc update_PARAM_VALUE.SAMPS_PER_FRAME { PARAM_VALUE.SAMPS_PER_FRAME } {
	# Procedure called to update SAMPS_PER_FRAME when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SAMPS_PER_FRAME { PARAM_VALUE.SAMPS_PER_FRAME } {
	# Procedure called to validate SAMPS_PER_FRAME
	return true
}


proc update_MODELPARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH { MODELPARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH PARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH}] ${MODELPARAM_VALUE.C_S_AXIS_DATA_TDATA_WIDTH}
}

proc update_MODELPARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH { MODELPARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH PARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH}] ${MODELPARAM_VALUE.C_M_AXIS_DATA_TDATA_WIDTH}
}

proc update_MODELPARAM_VALUE.SAMPS_PER_FRAME { MODELPARAM_VALUE.SAMPS_PER_FRAME PARAM_VALUE.SAMPS_PER_FRAME } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SAMPS_PER_FRAME}] ${MODELPARAM_VALUE.SAMPS_PER_FRAME}
}

