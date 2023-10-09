`timescale 1ns / 1ps

/*

Author: George Vardakis

This core calculates the CFO of a OFDM symbol
The symbol is assumed to have a cyclic prefix. The CFO is calculated
through a crosscorrelation of the cyclic prefix with the cyclic suffix
of the symbol. The prefix is multiplied with the complex conjugate of
the suffix. The outputs of the multiplication are added, and the
arctangend of the summation output is calculated. Then, the result
is devided by the FFT size and this is used as the phase increment for
the generation of the complex sine wave that will undo the carrier 
frequency offset present in the symbol.

*/
module cfo_estimator 
    #(
    parameter integer S_AXIS_TDATA_WIDTH = 128,
    parameter integer OFDM_SYMBOL_SIZE = 1024,
    parameter integer CP_LENGTH = 256,
    parameter integer SSR = 4,
    parameter integer COMPLEX_WIDTH = 32
    )
    (
    input wire clk,
    input wire clk_fast,
    input wire aresetn,
    input logic [S_AXIS_TDATA_WIDTH - 1 : 0] s_axis_tdata,
    input logic s_axis_tvalid,
    
    output logic [S_AXIS_TDATA_WIDTH - 1 : 0] m_axis_tdata,
    output logic m_axis_tvalid
    );
    bram_ctrl_iface#(.DATA_WIDTH(S_AXIS_TDATA_WIDTH)) bram_ctrl();
    bram_ctrl_iface#(.DATA_WIDTH(S_AXIS_TDATA_WIDTH)) bram_cp_ctrl();
    adder2correction_iface adder2correction();
    bram_ctrl2mult_iface bram_ctrl2mult();
    mult2out_iface mult2out();
    
    assign m_axis_tdata = mult2out.symbol_data;
    assign m_axis_tvalid = mult2out.symbol_tvalid;

    cfo_compensation cfo_compensation_inst(
        .clk(clk),
        .aresetn(aresetn),
        .adder2correction(adder2correction),
        .mult2out(mult2out),
        .bram_ctrl2mult(bram_ctrl2mult)
    );
    
    estimator estimator_inst(
        .clk(clk),
        .aresetn(aresetn),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .bram_ctrl(bram_ctrl),
        .bram_cp_ctrl(bram_cp_ctrl),
        .adder2correction(adder2correction),
        .bram_ctrl2mult(bram_ctrl2mult)
    );
    


xpm_memory_sdpram #(
   .ADDR_WIDTH_A(16),               // DECIMAL
   .ADDR_WIDTH_B(16),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(S_AXIS_TDATA_WIDTH),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(2 * (OFDM_SYMBOL_SIZE + CP_LENGTH) * COMPLEX_WIDTH), // 2 time domain OFDM symbols
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(S_AXIS_TDATA_WIDTH),  // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(S_AXIS_TDATA_WIDTH),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
symbol_ram_inst (                                
   .doutb(bram_ctrl.read_data),
   .addra(bram_ctrl.write_addr),
   .addrb(bram_ctrl.read_addr),
   .clka(clk),
   .clkb(clk),
   .dina(bram_ctrl.write_data),
   .ena(bram_ctrl.write_enable),
   .enb(bram_ctrl.read_enable),
   .regceb(1),                        
   .wea(1)
);    

xpm_memory_sdpram #(
   .ADDR_WIDTH_A(16),               // DECIMAL
   .ADDR_WIDTH_B(16),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(S_AXIS_TDATA_WIDTH),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(2 * CP_LENGTH * COMPLEX_WIDTH), // 2 time domain OFDM symbols
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(S_AXIS_TDATA_WIDTH),  // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(S_AXIS_TDATA_WIDTH),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
cp_ram_inst (                                
   .doutb(bram_cp_ctrl.read_data),
   .addra(bram_cp_ctrl.write_addr),
   .addrb(bram_cp_ctrl.read_addr),
   .clka(clk),
   .clkb(clk),
   .dina(bram_cp_ctrl.write_data),
   .ena(bram_cp_ctrl.write_enable),
   .enb(bram_cp_ctrl.read_enable),
   .regceb(1),                        
   .wea(1)
);  
endmodule
