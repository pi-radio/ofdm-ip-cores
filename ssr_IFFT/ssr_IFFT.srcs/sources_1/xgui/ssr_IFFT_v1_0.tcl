# Definitional proc to organize widgets for parameters.
proc init_gui { IPINST } {
  ipgui::add_param $IPINST -name "Component_Name"
  #Adding Page
  set Page_0 [ipgui::add_page $IPINST -name "Page 0"]
  ipgui::add_param $IPINST -name "C_M00_AXIS_TDATA_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "C_S00_AXIS_TDATA_WIDTH" -parent ${Page_0}
  ipgui::add_param $IPINST -name "insert_cp" -parent ${Page_0}
  ipgui::add_param $IPINST -name "scaled" -parent ${Page_0}

  ipgui::add_param $IPINST -name "SSR"
  ipgui::add_param $IPINST -name "FFT_SIZE"
  ipgui::add_param $IPINST -name "CP_DURATION"
  ipgui::add_param $IPINST -name "fft_shift"

}

proc update_PARAM_VALUE.CP_DURATION { PARAM_VALUE.CP_DURATION } {
	# Procedure called to update CP_DURATION when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.CP_DURATION { PARAM_VALUE.CP_DURATION } {
	# Procedure called to validate CP_DURATION
	return true
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

proc update_PARAM_VALUE.FFT_SIZE { PARAM_VALUE.FFT_SIZE } {
	# Procedure called to update FFT_SIZE when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.FFT_SIZE { PARAM_VALUE.FFT_SIZE } {
	# Procedure called to validate FFT_SIZE
	return true
}

proc update_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to update SSR when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.SSR { PARAM_VALUE.SSR } {
	# Procedure called to validate SSR
	return true
}

proc update_PARAM_VALUE.fft_shift { PARAM_VALUE.fft_shift } {
	# Procedure called to update fft_shift when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.fft_shift { PARAM_VALUE.fft_shift } {
	# Procedure called to validate fft_shift
	return true
}

proc update_PARAM_VALUE.insert_cp { PARAM_VALUE.insert_cp } {
	# Procedure called to update insert_cp when any of the dependent parameters in the arguments change
}

proc validate_PARAM_VALUE.insert_cp { PARAM_VALUE.insert_cp } {
	# Procedure called to validate insert_cp
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

proc update_MODELPARAM_VALUE.insert_cp { MODELPARAM_VALUE.insert_cp PARAM_VALUE.insert_cp } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.insert_cp}] ${MODELPARAM_VALUE.insert_cp}
}

proc update_MODELPARAM_VALUE.scaled { MODELPARAM_VALUE.scaled PARAM_VALUE.scaled } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.scaled}] ${MODELPARAM_VALUE.scaled}
}

proc update_MODELPARAM_VALUE.SSR { MODELPARAM_VALUE.SSR PARAM_VALUE.SSR } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.SSR}] ${MODELPARAM_VALUE.SSR}
}

proc update_MODELPARAM_VALUE.FFT_SIZE { MODELPARAM_VALUE.FFT_SIZE PARAM_VALUE.FFT_SIZE } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.FFT_SIZE}] ${MODELPARAM_VALUE.FFT_SIZE}
}

proc update_MODELPARAM_VALUE.CP_DURATION { MODELPARAM_VALUE.CP_DURATION PARAM_VALUE.CP_DURATION } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.CP_DURATION}] ${MODELPARAM_VALUE.CP_DURATION}
}

proc update_MODELPARAM_VALUE.fft_shift { MODELPARAM_VALUE.fft_shift PARAM_VALUE.fft_shift } {
	# Procedure called to set VHDL generic/Verilog parameter value(s) based on TCL parameter value
	set_property value [get_property value ${PARAM_VALUE.fft_shift}] ${MODELPARAM_VALUE.fft_shift}
}

