interface axis_iface
    #(parameter DATA_WIDTH = 32);
        logic [DATA_WIDTH - 1 : 0 ] tdata;
        logic tvalid;
        logic tready;
        logic tlast;
        
        modport master(output tdata, output tvalid,
                output tlast, input tready);
        modport slave(input tdata, input tvalid,
                input tlast, output tready); 
endinterface

interface bram2corr_iface
    #(parameter DATA_WIDTH = 128,
      parameter BRAM_LATENCY = 2,
      parameter FFT_SIZE = 1024);
        logic [DATA_WIDTH - 1 : 0 ] tdata;
        logic bram_en;
        logic bram_valid;
        logic config_done;
        
        modport master(output tdata, output bram_valid,
                output config_done, input bram_en);
        modport slave(input tdata, input bram_valid,
                input config_done, output bram_en); 
endinterface

interface datain2corr_iface;

        logic out_ready;
        logic out_valid;
        logic signed [16 : 0] conj_real[0 : 3];
        logic signed [16 : 0] conj_imag[0 : 3];
    
        modport master(input out_ready, output conj_real, output conj_imag, output out_valid);
        modport slave(output out_ready, input conj_real, input conj_imag, input out_valid); 
endinterface
