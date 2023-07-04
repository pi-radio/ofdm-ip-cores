interface bram_ctrl_iface #(
        parameter DATA_WIDTH = 128);
        wire clk;
        wire aresetn;
        logic [15 : 0] read_addr;
        logic [15 : 0] write_addr;
        logic read_enable;
        logic write_enable;
        logic [DATA_WIDTH - 1 : 0] read_data;
        logic [DATA_WIDTH - 1 : 0] write_data;
        
        modport master(output read_addr, output write_addr, output read_enable, output write_enable,
                            input read_data, output write_data);
        modport slave(input read_addr, input write_addr, input read_enable, input write_enable,
                            output read_data, input write_data);
endinterface

interface bram_ctrl2corr_iface#(
        parameter DATA_WIDTH = 128,
        parameter COMPLEX_SIZE = 32);
    logic [DATA_WIDTH - 1 : 0] prefix_data;
    logic [DATA_WIDTH - 1 : 0] suffix_data;
    logic tvalid;
    logic symbol_last;
    
    modport master(output tvalid, 
                    output symbol_last, output prefix_data, output suffix_data);
    modport slave(input tvalid, 
                    input symbol_last, input prefix_data, input suffix_data);
endinterface

interface corr2adder_iface#(
        parameter DATA_WIDTH = 128,
        parameter COMPLEX_SIZE = 32,
        parameter SSR = 4);
    logic signed [COMPLEX_SIZE : 0] corr_data_real[0 : SSR - 1];
    logic signed[COMPLEX_SIZE : 0] corr_data_imag[0 : SSR - 1];
    logic tvalid;
    logic symbol_last;
    
    modport master(output tvalid, output symbol_last,output corr_data_real, output corr_data_imag);
    modport slave(input tvalid, input symbol_last, input corr_data_real, input corr_data_imag);
endinterface

interface adder2correction_iface#(
        parameter DATA_WIDTH = 128,
        parameter COMPLEX_SIZE = 32,
        parameter SSR = 4);
    logic [COMPLEX_SIZE * 2 - 1 : 0] angle;
    logic tvalid;
    
    modport master(output tvalid, output angle);
    modport slave(input tvalid, input angle);
endinterface

interface correction2mult_iface#(
        parameter DATA_WIDTH = 128,
        parameter COMPLEX_SIZE = 32,
        parameter SSR = 4);
    logic [COMPLEX_SIZE - 1 : 0] sine;
    logic tvalid;
    logic tready;
    
    modport master(output tvalid, output sine, input tready);
    modport slave(input tvalid, input sine, output tready);
endinterface

interface bram_ctrl2mult_iface#(
        parameter DATA_WIDTH = 128,
        parameter COMPLEX_SIZE = 32,
        parameter SSR = 4);
    logic [DATA_WIDTH - 1 : 0] symbol_data;
    logic symbol_tvalid;
    logic mult_ready;
    
    modport master(output symbol_tvalid, output symbol_data, input mult_ready);
    modport slave(input symbol_tvalid, input symbol_data, output mult_ready);
endinterface

interface mult2out_iface#(
        parameter DATA_WIDTH = 128,
        parameter COMPLEX_SIZE = 32,
        parameter SSR = 4);
    logic [DATA_WIDTH - 1 : 0] symbol_data;
    logic symbol_tvalid;
    
    modport master(output symbol_tvalid, output symbol_data);
    modport slave(input symbol_tvalid, input symbol_data);
endinterface