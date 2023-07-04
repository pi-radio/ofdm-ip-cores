import piradio_ofdm::mod_t;
import piradio_ofdm::ofdm_sample_t;
interface ctrl_in_iface
    #(parameter WIDTH = 32);
    logic [WIDTH - 1 : 0] ctrl_data;
    logic ctrl_valid;
    logic ctrl_ready;
    logic ctrl_tlast;
    
    modport master(output ctrl_data, output ctrl_valid, input ctrl_ready, input ctrl_tlast);
    modport slave(input ctrl_data, input ctrl_valid, output ctrl_ready, output ctrl_tlast);
endinterface

interface bram_fifo_in_iface 
    #(parameter WIDTH = 128,
      parameter BRAM_DEPTH = 512,
      parameter BRAM_LATENCY = 2,
      parameter BRAM_ADDR_WIDTH = 8,
      parameter N_BEFORE_LAST = 3);
        logic [BRAM_ADDR_WIDTH-1:0] bram_addr;
        logic [WIDTH-1:0] bram_data;
        logic bram_rd_en;
        logic fifo_restart;
        
        modport master(output bram_addr,
            input bram_data, output bram_rd_en, output fifo_restart);
        modport slave(input bram_addr,
            output bram_data, input bram_rd_en, input fifo_restart);
endinterface

interface bram_fifo_out_iface
        #(parameter WIDTH = 128);
        logic [WIDTH-1:0] fifo_data;
        logic fifo_valid;
        logic fifo_last;
        logic fifo_rdy;
        logic fifo_restart;
        
        modport master(output fifo_data, output fifo_valid, output fifo_last, input fifo_rdy, output fifo_restart);
        modport slave(input fifo_data, input fifo_valid, input fifo_last, output fifo_rdy, input fifo_restart);
endinterface

interface frame_parser_in_iface #(
        parameter DATA_WIDTH=32,
        parameter SAMPS_PER_FRAME=180
    );
        logic                   src_valid;
        logic                   src_rdy;
        logic [DATA_WIDTH-1:0]  src_data;
        logic                   structs_rdy;
     
        modport master(input src_valid, input src_data, output src_rdy, input structs_rdy);   
endinterface

interface parser_to_mod_iface #(
        parameter DATA_WIDTH=32,
        parameter SAMPS_PER_FRAME=180
    )
    (input clk, input rstn); 
        logic                   dst_valid;
        logic                   dst_rdy;
        logic [DATA_WIDTH-1:0]  dst_data;
        logic                   dst_last;
        mod_t                   modulation;
        
        modport master(input rstn, input clk, output dst_valid, input dst_rdy, output dst_data,
                        output dst_last, output modulation);
        modport slave(input rstn, input clk, input dst_valid, output dst_rdy, input dst_data,
                        input dst_last, input modulation);
          
endinterface

interface
piradio_framer_data_modulator_out_iface
    #(
        parameter SRC_DATA_WIDTH=128,
        parameter DST_DATA_WIDTH=128,
        parameter MAX_SYMBOLS=4
    );
        logic [2:0]                 samples_rdy;
        logic [2:0]	                samples_valid;
        logic                       samples_last;
        ofdm_sample_t               samples[0:MAX_SYMBOLS-1];
        
        modport master (input samples_rdy, output samples_valid,
                         output samples_last, output samples);
        modport slave (output samples_rdy, input samples_valid,
                         input samples_last, input samples);
endinterface
