# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  ipgui::add_param $IPINST -name "C_M00_AXIS_TDATA_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "C_S00_AXIS_TDATA_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "scaled" -parent ${Page_0}

  ipgui::add_param $IPINST -name "SSR"
  ipgui::add_param $IPINST -name "FFT_SHIFT"

}

proc update_PARAM_VALUE.C_M00_AXIS_TDATA_WIDTH { PARAM_VALUE.C_M00_AXIS_TDATA_WIDTH } {
	# Procedure called to update C_M00_AXIS_TDATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_M00_AXIS_TDATA_WIDTH { PARAM_VALUE.C_M00_AXIS_TDATA_WIDTH } {
	# Procedure called to validate C_M00_AXIS_TDATA_WIDTH
	return true
}

proc update_PARAM_VALUE.C_S00_AXIS_TDATA_WIDTH { PARAM_VALUE.C_S00_AXIS_TDATA_WIDTH } {
	# Procedure called to update C_S00_AXIS_TDATA_WIDTH when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.C_S00_AXIS_TDATA_WIDTH { PARAM_VALUE.C_S00_AXIS_TDATA_WIDTH } {
	# Procedure called to validate C_S00_AXIS_TDATA_WIDTH
	return true
}

proc update_PARAM_VALUE.FFT_SHIFT { PARAM_VALUE.FFT_SHIFT } {
	# Procedure called to update FFT_SHIFT when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.FFT_SHIFT { PARAM_VALUE.FFT_SHIFT } {
	# Procedure called to validate FFT_SHIFT
	return true
}

proc update_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to update SSR when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to validate SSR
	return true
}

proc update_PARAM_VALUE.scaled { PARAM_VALUE.scaled } {
	# Procedure called to update scaled when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.scaled { PARAM_VALUE.scaled } {
	# Procedure called to validate scaled
	return true
}


proc update_MODELPARAM_VALUE.C_S00_AXIS_TDATA_WIDTH { MODELPARAM_VALUE.C_S00_AXIS_TDATA_WIDTH PARAM_VALUE.C_S00_AXIS_TDATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_S00_AXIS_TDATA_WIDTH}] ${MODELPARAM_VALUE.C_S00_AXIS_TDATA_WIDTH}
}

proc update_MODELPARAM_VALUE.C_M00_AXIS_TDATA_WIDTH { MODELPARAM_VALUE.C_M00_AXIS_TDATA_WIDTH PARAM_VALUE.C_M00_AXIS_TDATA_WIDTH } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.C_M00_AXIS_TDATA_WIDTH}] ${MODELPARAM_VALUE.C_M00_AXIS_TDATA_WIDTH}
}

proc update_MODELPARAM_VALUE.scaled { MODELPARAM_VALUE.scaled PARAM_VALUE.scaled } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.scaled}] ${MODELPARAM_VALUE.scaled}
}

proc update_MODELPARAM_VALUE.SSR { MODELPARAM_VALUE.SSR PARAM_VALUE.SSR } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SSR}] ${MODELPARAM_VALUE.SSR}
}

proc update_MODELPARAM_VALUE.FFT_SHIFT { MODELPARAM_VALUE.FFT_SHIFT PARAM_VALUE.FFT_SHIFT } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.FFT_SHIFT}] ${MODELPARAM_VALUE.FFT_SHIFT}
}

