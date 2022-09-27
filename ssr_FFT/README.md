## Super Sample Rate FFT core

This is wrapper around a system generator SSR FFT core of FFT size 1024, and SSR 4.

### Project Recreation

The project can be generated using the provided "fft_project.tcl" script. 

Using Vivado TCL mode:

1. Clone the piradio OFDM ip cores repo
2. Open Vivado
3. From the tcl command line, navigate to the ssr_FFT folder
4. source the fft_project.tcl script
5. After project creation is completed, add the sysgenssrfft folder to the Repositories of the project
from the project settings.

Using Vivado batch mode
1. Clone the piradio OFDM ip cores repo
2. From the command line, navigate to the folder you want to generate the project
3. Execute the command "vivado -mode batch -source $origin_dir/fft_project.tcl -tclargs --origin_dir $origin_dir"

, where $origin_dir the path to the ssr_FFT/ folder of the cloned repo
4. After project creation is completed, add the sysgenssrfft folder to the Repositories of the project
from the project settings.

### Limitations

Due to a limitation of the system generated FFT core, the TVALID input to the ssrFFT core must be asserted every time for
multiples of 256 cycles. This is because the core expects a full frame at the input, without interruption by the flow
control mechanism, otherwise the output is corrupted.
