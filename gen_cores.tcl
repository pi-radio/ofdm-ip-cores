proc checkRequiredFiles { origin_dir} {
  set status true
  set files [list \
 "[file normalize "$origin_dir/delay/project.tcl"]"\
 "[file normalize "$origin_dir/medium_emulator/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_correlator/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_demodulator/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_Framer/project.tcl"]"\
 "[file normalize "$origin_dir/OFDM_synchronizer/project.tcl"]"\
 "[file normalize "$origin_dir/pilot_zero_remover/project.tcl"]"\
 "[file normalize "$origin_dir/ssr_FFT/fft_project.tcl"]"\
 "[file normalize "$origin_dir/ssr_IFFT/project.tcl"]"\
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

cd $origin_dir/delay
source project.tcl
cd ../$origin_dir/medium_emulator
source project.tcl
cd ../$origin_dir/OFDM_correlator
source project.tcl
cd ../$origin_dir/OFDM_demodulator
source project.tcl
cd ../$origin_dir/OFDM_Framer
source project.tcl
cd ../$origin_dir/OFDM_synchronizer
source project.tcl
cd ../$origin_dir/pilot_zero_remover
source project.tcl
cd ../$origin_dir/ssr_FFT
source fft_project.tcl
cd ../$origin_dir/ssr_IFFT
source project.tcl
cd ..
