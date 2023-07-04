`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/25/2023 10:55:04 AM
// Design Name: 
// Module Name: cfo_compensation
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module cfo_compensation(
    input wire clk,
    input wire aresetn,
    bram_ctrl2mult_iface.slave bram_ctrl2mult,
    adder2correction_iface.slave adder2correction,
    mult2out_iface.master mult2out
    );
    
    logic [31 : 0] term = 32'h3bc90fdb;
    logic [15 : 0] angle;
    logic angle_valid;
    logic [31 : 0] mult_out;
    logic mult_out_valid;
    logic [31 : 0] out;
    logic out_valid;
    logic term_valid;
    logic m_axis_result_tvalid;
    logic [31 : 0] m_axis_result_tdata;
    logic sine_wave_tvalid;
    logic [31 : 0] sine_wave_data;
    logic [31 : 0] m_fifo_in;
    logic fifo_in_rdy,fifo_in_valid, fifo_out_rdy;
    logic [127 : 0] width_conv_out;
    logic width_conv_valid;
    logic width_conv_in_rdy;
    logic cfo_ready;
    logic [23 : 0] cfo_readysr;
    
    
    always@(posedge clk) begin
        if(~aresetn)
            cfo_readysr <= 4'b0;
        else
            cfo_readysr <= {cfo_readysr[23 : 0], m_axis_result_tvalid};
    end
    assign cfo_ready = cfo_readysr[23];
    
    assign term_valid = out_valid;
    correction2mult_iface correction2mult();
    
    atan_cordic atan_cordic_inst (
      .aclk(clk),                                        // input wire aclk
      .s_axis_cartesian_tvalid(adder2correction.tvalid),  // input wire s_axis_cartesian_tvalid
      .s_axis_cartesian_tdata(adder2correction.angle),    // input wire [31 : 0] s_axis_cartesian_tdata
      .m_axis_dout_tvalid(angle_valid),            // output wire m_axis_dout_tvalid
      .m_axis_dout_tdata(angle)              // output wire [15 : 0] m_axis_dout_tdata
    );
    
    
    fixed_to_float fixed_to_float_inst (
      .aclk(clk),                                  // input wire aclk
      .s_axis_a_tvalid(angle_valid),            // input wire s_axis_a_tvalid
      .s_axis_a_tdata(angle),              // input wire [15 : 0] s_axis_a_tdata
      .m_axis_result_tvalid(out_valid),  // output wire m_axis_result_tvalid
      .m_axis_result_tdata(out)    // output wire [31 : 0] m_axis_result_tdata
    );
    
    multiply multiply_inst (
      .aclk(clk),                                  // input wire aclk
      .s_axis_a_tvalid(out_valid),            // input wire s_axis_a_tvalid
      .s_axis_a_tdata(out),              // input wire [31 : 0] s_axis_a_tdata
      .s_axis_b_tvalid(out_valid),            // input wire s_axis_b_tvalid
      .s_axis_b_tdata(term),              // input wire [31 : 0] s_axis_b_tdata
      .m_axis_result_tvalid(mult_out_valid),  // output wire m_axis_result_tvalid
      .m_axis_result_tdata(mult_out)    // output wire [31 : 0] m_axis_result_tdata
    );
    
    float_to_fixed float_to_fixed_inst (
      .aclk(clk),                                  // input wire aclk
      .s_axis_a_tvalid(mult_out_valid),            // input wire s_axis_a_tvalid
      .s_axis_a_tdata(mult_out),              // input wire [31 : 0] s_axis_a_tdata
      .m_axis_result_tvalid(m_axis_result_tvalid),  // output wire m_axis_result_tvalid
      .m_axis_result_tdata(m_axis_result_tdata)    // output wire [31 : 0] m_axis_result_tdata
    );
//    xpm_fifo_axis #(
//     .CDC_SYNC_STAGES(2), // DECIMAL
//     .CLOCKING_MODE("independent_clock"), // String
//     .ECC_MODE("no_ecc"), // String
//     .FIFO_DEPTH(256), // DECIMAL
//     .FIFO_MEMORY_TYPE("auto"), // String
//     .PACKET_FIFO("false"), // String
//     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
//     .RELATED_CLOCKS(0), // DECIMAL
//     .SIM_ASSERT_CHK(0), // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
//     .TDATA_WIDTH(16), // DECIMAL
//     .TDEST_WIDTH(1), // DECIMAL
//     .TID_WIDTH(1), // DECIMAL
//     .TUSER_WIDTH(1), // DECIMAL
//     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
//    )
//    fifo_in (
//     .m_axis_tdata(m_fifo_in),
//     .m_axis_tvalid(fifo_in_valid),
//     .s_axis_tready(fifo_in_rdy),
//     .m_aclk(clk_fast),
//     .m_axis_tready(1),
//     .s_aclk(clk_slow),
//     .s_aresetn(aresetn_slow),
//     .s_axis_tdata(m_axis_result_tdata),
//     .s_axis_tvalid(m_axis_result_tvalid)
//    );
    sine_wave_gen sine_wave_gen_inst(
        .clk(clk),
        .aresetn(aresetn),
        .phase_increment(m_axis_result_tdata),
        .phase_in_valid(m_axis_result_tvalid),
        .sine_out(sine_wave_data),
        .sine_out_valid(sine_wave_tvalid)
    );
    
//    sine_wave sine_wave_inst (
//      .aclk(clk_fast),                                  // input wire aclk
//      .s_axis_config_tvalid(fifo_in_valid),  // input wire s_axis_config_tvalid
//      .s_axis_config_tdata(m_fifo_in),    // input wire [31 : 0] s_axis_config_tdata
//      .m_axis_data_tvalid(m_axis_data_tvalid),      // output wire m_axis_data_tvalid
//      .m_axis_data_tdata(m_axis_data_tdata)        // output wire [15 : 0] m_axis_data_tdata
//    );
    
    xpm_fifo_axis #(
     .CDC_SYNC_STAGES(2), // DECIMAL
     .CLOCKING_MODE("common_clock"), // String
     .ECC_MODE("no_ecc"), // String
     .FIFO_DEPTH(256), // DECIMAL
     .FIFO_MEMORY_TYPE("auto"), // String
     .PACKET_FIFO("false"), // String
     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
     .RELATED_CLOCKS(0), // DECIMAL
     .SIM_ASSERT_CHK(0), // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
     .TDATA_WIDTH(32), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    fifo_out (
     .m_axis_tdata(correction2mult.sine),
     .m_axis_tvalid(correction2mult.tvalid),
     .s_axis_tready(fifo_out_rdy),
     .m_aclk(clk),
     .m_axis_tready(correction2mult.tready),
     .s_aclk(clk),
     .s_aresetn(aresetn),
     .s_axis_tdata(sine_wave_data),
     .s_axis_tvalid(sine_wave_tvalid)
    );
    
    correction correction_inst(
        .clk(clk),
        .aresetn(aresetn),
        .cfo_ready(cfo_ready),
        .bram_ctrl2mult(bram_ctrl2mult),
        .correction2mult(correction2mult),
        .mult2out(mult2out)
    );
    
endmodule

module sine_wave_gen
(
    input wire clk,
    input wire aresetn,
    input logic [15 : 0] phase_increment,
    input logic phase_in_valid,
    output logic [31 : 0] sine_out,
    output logic sine_out_valid
);
    logic signed [15 : 0] high_end = 16'h6488;
    logic signed [15 : 0] low_end = 16'h9B78;
    localparam fft_width_ssr = 256;
    logic [15 : 0] phase_increment_reg;
    logic signed [15 : 0] next_inc;
    
    logic [31 : 0] sample_cnt;
    logic signed [15 : 0] phase = 0;
    logic start = 0;
    logic [31 : 0] sine_out_reg;
    logic [15 : 0] sine_out_reg_real;
    logic [15 : 0] sine_out_reg_imag;
    
    
    assign next_inc = phase + phase_increment_reg;
    
    always@(posedge clk) begin
        if(!aresetn) begin
            start <= 0;
            phase_increment_reg <= 0;
        end
        else begin
            if(phase_in_valid) begin
                start <= 1;
                phase_increment_reg <= phase_increment;
            end
            if(start && sample_cnt == fft_width_ssr - 1)
                start <= 0;
        end
    end
    
    always @(posedge clk) begin
        if(!aresetn) begin
            phase <= 0;
            sample_cnt <= 0;
        end
        else begin 
            if(start) begin
                if((next_inc > high_end) && ~phase[15]) begin  
                    phase <= (next_inc - (high_end + 1)) + low_end;
                    sample_cnt <= sample_cnt + 1;
                end
                else if((next_inc < low_end) && phase[15]) begin  
                    phase <= high_end + (low_end - phase);
                    sample_cnt <= sample_cnt + 1;
                end
                else begin
                    phase <= next_inc;
                    sample_cnt <= sample_cnt + 1;
                end
            end
            else begin 
                sample_cnt <= 0;
                phase <= 0;
            end
        end
    end

    sine_gen sine_inst (
      .aclk(clk),                                // input wire aclk
      .s_axis_phase_tvalid(start),  // input wire s_axis_phase_tvalid
      .s_axis_phase_tdata(phase),    // input wire [15 : 0] s_axis_phase_tdata
      .m_axis_dout_tvalid(sine_out_valid),    // output wire m_axis_dout_tvalid
      .m_axis_dout_tdata(sine_out)      // output wire [31 : 0] m_axis_dout_tdata
    );
    
    assert property (@(posedge clk)                 // No new phase should be introduced to the input if the
      (phase_in_valid) |-> !start);                 // previous sine wave hasn't finished generating.
	   
endmodule

module correction(
    input wire clk,
    input wire aresetn,
    input wire cfo_ready,
    bram_ctrl2mult_iface.slave bram_ctrl2mult,
    correction2mult_iface.slave correction2mult,
    mult2out_iface.master mult2out
    );
    
    assign bram_ctrl2mult.mult_ready = cfo_ready;
    assign correction2mult.tready = bram_ctrl2mult.symbol_tvalid;
    logic signed [bram_ctrl2mult.COMPLEX_SIZE/2 - 1 : 0] symbol_reals[0 : 3];
    logic signed [bram_ctrl2mult.COMPLEX_SIZE/2 - 1 : 0] symbol_imags[0 : 3];
    logic signed [bram_ctrl2mult.COMPLEX_SIZE/2 - 1 : 0] sine_real;
    logic signed [bram_ctrl2mult.COMPLEX_SIZE/2 - 1 : 0] sine_imag;
    logic [bram_ctrl2mult.COMPLEX_SIZE -1 : 0] results_real[0 : bram_ctrl2mult.SSR - 1];
    logic [bram_ctrl2mult.COMPLEX_SIZE -1 : 0] results_imag[0 : bram_ctrl2mult.SSR - 1];
    
    genvar i,l;
    generate
        for(l = 0; l < bram_ctrl2mult.SSR ; l = l + 1) begin
            assign mult2out.symbol_data[l * bram_ctrl2mult.COMPLEX_SIZE +: bram_ctrl2mult.COMPLEX_SIZE] =
                                    {results_imag[l][bram_ctrl2mult.COMPLEX_SIZE/2 - 1 +: bram_ctrl2mult.COMPLEX_SIZE/2],
                                     results_real[l][bram_ctrl2mult.COMPLEX_SIZE/2 - 1 +: bram_ctrl2mult.COMPLEX_SIZE/2]};
        end
    endgenerate
    
    logic [3 : 0] k;
    assign sine_real = correction2mult.sine[0 +: bram_ctrl2mult.COMPLEX_SIZE/2];
    assign sine_imag = correction2mult.sine[bram_ctrl2mult.COMPLEX_SIZE/2 +: bram_ctrl2mult.COMPLEX_SIZE/2];
//    assign sine_real = {correction2mult.sine[0 +: bram_ctrl2mult.COMPLEX_SIZE/2  -1 ], 1'b0};
//    assign sine_imag = {correction2mult.sine[bram_ctrl2mult.COMPLEX_SIZE/2 +: bram_ctrl2mult.COMPLEX_SIZE/2], 1'b0};
    generate
        for(i = 0; i < bram_ctrl2mult.SSR ; i = i + 1) begin
            assign symbol_reals[i] = bram_ctrl2mult.symbol_data[i * bram_ctrl2mult.COMPLEX_SIZE +: bram_ctrl2mult.COMPLEX_SIZE/2];
            assign symbol_imags[i] = bram_ctrl2mult.symbol_data[i * bram_ctrl2mult.COMPLEX_SIZE + bram_ctrl2mult.COMPLEX_SIZE/2 
                                                                                +: bram_ctrl2mult.COMPLEX_SIZE/2];
        end
    endgenerate
    
    always@(posedge clk) begin
        if(~aresetn) begin
            for(k = 0; k < bram_ctrl2mult.SSR; k = k + 1) begin
                results_real[k] <= 0;
                results_imag[k] <= 0;
            end
        end 
        else begin
            if(bram_ctrl2mult.symbol_tvalid) begin
                mult2out.symbol_tvalid <= 1;
                for(k = 0; k < bram_ctrl2mult.SSR; k = k + 1) begin
                    results_real[k] <= ((symbol_reals[k] * sine_real * 2) - (symbol_imags[k] * sine_imag * 2));
                    results_imag[k] <= ((symbol_reals[k] * sine_imag * 2) + (symbol_imags[k] * sine_real * 2));
                end
            end
            else
                mult2out.symbol_tvalid <= 0;
        end
    end

endmodule
