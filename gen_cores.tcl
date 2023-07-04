proc checkRequiredFiles { origin_dir} {
  set status true
  set files [list \
 "[file normalize "$origin_dir/delay/project.tcl"]"\
 "[file normalize "$origin_dir/cfo_estimator/project.tcl"]"\
 "[file normalize "$origin_dir/fec_controller/project.tcl"]"\
 "[file normalize "$origin_dir/medium_emulator/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_correlator/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_demodulator/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_Framer/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_synchronizer/project.tcl"]"\
 "[file normalize "$origin_dir/ssr_FFT/fft_project.tcl"]"\
 "[file normalize "$origin_dir/ssr_IFFT/project.tcl"]"\
 "[file normalize "$origin_dir/tlast_generator/project.tcl"]"\
 "[file normalize "$origin_dir/signal_detect/project.tcl"]"\
 "[file normalize "$origin_dir/iq_interleaver_gain/project.tcl"]"\
 "[file normalize "$origin_dir/zf_equalizer/project.tcl"]"\
  ]
  foreach ifile $files {
    if { ![file isfile $ifile] } {
      puts " Could not find local file $ifile "
      set status false
    }
  }

  return $status
}
# Set the reference directory for source file relative paths (by default the value is script directory path)
set origin_dir "."

set validate_required 0
if { $validate_required } {
  if { [checkRequiredFiles $origin_dir] } {
    puts "Tcl file $script_file is valid. All files required for project creation is accesable. "
  } else {
    puts "Tcl file $script_file is not valid. Not all files required for project creation is accesable. "
    return
  }
}
file delete -force $origin_dir/signal_detect/signal_detect
file delete -force $origin_dir/tlast_generator/tlast_generator
file delete -force $origin_dir/iq_interleaver_gain/iq_interleaver_gain
file delete -force $origin_dir/fec_controller/fec_controller
file delete -force $origin_dir/zf_equalizer/zf_equalizer
file delete -force $origin_dir/cfo_estimator/cfo_estimator
file delete -force $origin_dir/delay/delay
file delete -force $origin_dir/medium_emulator/medium_emulator
file delete -force $origin_dir/OFDM_correlator/OFDM_correlator
file delete -force $origin_dir/OFDM_demodulator/OFDM_demodulator
file delete -force $origin_dir/OFDM_Framer/OFDM_Framer
file delete -force $origin_dir/ssr_FFT/ssr_FFT
file delete -force $origin_dir/ssr_IFFT/ssr_IFFT
file delete -force $origin_dir/OFDM_synchronizer/OFDM_synchronizer

cd signal_detect
source project.tcl
cd ../tlast_generator
source project.tcl
cd ../iq_interleaver_gain
source project.tcl
cd ../fec_controller
source project.tcl
cd ../zf_equalizer
source project.tcl
cd ../cfo_estimator
source project.tcl
cd ../delay
source project.tcl
cd ../medium_emulator
source project.tcl
cd ../OFDM_correlator
source project.tcl
cd ../OFDM_demodulator
source project.tcl
cd ../OFDM_Framer
source project.tcl
cd ../OFDM_synchronizer
source project.tcl
cd ../ssr_FFT
source project.tcl
cd ../ssr_IFFT
source project.tcl
cd ..
