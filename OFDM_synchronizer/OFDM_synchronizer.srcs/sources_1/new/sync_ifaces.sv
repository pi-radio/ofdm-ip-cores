interface axis_iface
    #(parameter DATA_WIDTH = 256);
        logic [DATA_WIDTH - 1 : 0 ] tdata;
        logic tvalid;
        logic tready;
        logic tlast;
        
        modport master(output tdata, output tvalid,
                output tlast, input tready);
        modport slave(input tdata, input tvalid,
                input tlast, output tready); 
endinterface

interface mag_sq2max_cmpt_iface
    #(parameter CORR_SAMPLE_WIDTH = 26,
      parameter MAG_SQ_SAMPLE_WIDTH = 28,
      parameter CORR_COMPLEX_SIZE = 64,
      parameter SSR = 4
      );
      logic [MAG_SQ_SAMPLE_WIDTH - 1 : 0] mag_sq[0 : SSR - 1];
      logic mag_sq_valid;
      logic mag_sq_last;
      
      modport master(output mag_sq, output mag_sq_valid, output mag_sq_last);
      modport slave(input mag_sq, input mag_sq_valid, input mag_sq_last);
endinterface

interface max_cmpt2peak_det_iface
    #(parameter SAMPLE_WIDTH = 27,
      parameter SSR = 4
    );
    logic [SAMPLE_WIDTH - 1 : 0] max_mag;
    logic [$clog2(SSR) - 1 : 0] max_idx;
    logic max_valid;
    logic max_last;
    
    modport master(output max_mag, output max_idx, output max_valid, output max_last);
    modport slave(input max_mag, input max_idx, input max_valid, input max_last);
    
endinterface

interface peak_det2frame_det_iface
    #(parameter SSR = 4);
    logic [10 : 0] max_idx;
    logic [$clog2(SSR) - 1 : 0] ssr_idx;
    logic idx_valid;
    logic samples_valid;
    logic symbol_last;
    
    modport master(output max_idx, output ssr_idx, output idx_valid, output symbol_last, output samples_valid);
    modport slave(input max_idx, input ssr_idx, input idx_valid, input symbol_last, input samples_valid);
endinterface

interface frame_det2corr_arbiter_iface ();
    logic samples_valid;
    logic start_idx_valid;
    logic [10 : 0] start_idx;
    logic [1 : 0] ssr_idx;
    
    modport master(output samples_valid, output start_idx_valid, output start_idx, output ssr_idx);
    modport slave(input samples_valid, input start_idx_valid, input start_idx, input ssr_idx);
endinterface

interface corr_arbiter2sample_buff_iface ();
    logic samples_valid;
    logic start_idx_valid;
    logic [10 : 0] start_idx;
    logic [1 : 0] ssr_idx;
    logic src_ready;
    logic [1 : 0] correlator_idx;
    
    modport master(output samples_valid, output start_idx_valid, output start_idx, output ssr_idx, output correlator_idx, input src_ready);
    modport slave(input samples_valid, input start_idx_valid, input start_idx, input ssr_idx, input correlator_idx, output src_ready);
endinterface

interface sample_buff2cp_rm_iface #(
        parameter SSR_SYMBOL_SAMPLE_LEN = 256,
        parameter CP_LEN = 64,
        parameter BUFFER_LEN = 512,
        parameter SAMPLE_WIDTH = 128,
        parameter NUM_DATA_SYMBOLS = 9,
        parameter TOTAL_SYMBOL_LEN = 320,
        parameter BRAM_LATENCY = 2
    );
    
    logic [SAMPLE_WIDTH - 1 : 0] samples_out;
    logic samples_valid;
    logic samples_last;
    
    modport master(output samples_out, output samples_valid, output samples_last);
    modport slave(input samples_out, input samples_valid, input samples_last);

endinterface
    
interface cp_rm2out_iface #(
    parameter SAMPLE_WIDTH = 128
    );
    logic [SAMPLE_WIDTH - 1 : 0] samples_out;
    logic samples_valid;
    logic samples_last;
    
    modport master(output samples_out, output samples_valid, output samples_last);
    modport slave(input samples_out, input samples_valid, input samples_last);
    
endinterface
