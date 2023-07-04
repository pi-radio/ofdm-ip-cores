`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/23/2023 11:44:51 AM
// Design Name: 
// Module Name: cfo_estimator_tb
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


module cfo_estimator_tb(

    );
    logic clk = 0;
    logic clk_fast = 0;
    logic aresetn = 0;
    logic [31 : 0] data_in[0 : 6 * 1280];
    logic [127 : 0] s_axis_tdata;
    logic s_axis_tvalid;
    logic [127 : 0] m_axis_tdata;
    logic m_axis_tvalid;
    int i,k;
    logic [31 : 0] counter = 0;
    localparam num_symbols = 1;
    
    assign s_axis_tdata = {data_in[counter + 3],
                           data_in[counter + 2],
                           data_in[counter + 1],
                           data_in[counter]};
    
    initial begin
        $readmemh("/home/george/sync_output.txt", data_in, 0, 6*1280);
    end
    
    initial begin
        forever #5 clk = ~clk;
    end
    initial begin
        forever #1.25 clk_fast = ~clk_fast;
    end   
    initial begin
        #2000
        @(posedge clk);
        aresetn <= 1;
        s_axis_tvalid <= 1;
        for(k = 0; k < num_symbols; k++) begin
            for(i = 0; i < 6*1280/4 ; i++) begin
            @(posedge clk);
            counter <= counter + 4;
            end
            repeat(320)@(posedge clk);
            counter <= 0;
        end
        s_axis_tvalid <= 0;
    end
    
    cfo_estimator DUT(
        .clk(clk),
        .aresetn(aresetn),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid)
     );
    logic [31 : 0] corr_input_prefix [0 : 6 * 256 - 1];
    logic [31 : 0] corr_input_suffix [0 : 6 * 256 - 1];
    logic [31 : 0] cnt_corr_in = 0;
    
    always@(posedge clk) begin
        if(DUT.estimator_inst.correlator_inst.bram_ctrl2corr.tvalid) begin
            corr_input_prefix[cnt_corr_in] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.prefix_data[0 +: 32];
            corr_input_prefix[cnt_corr_in + 1] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.prefix_data[32 +: 32];
            corr_input_prefix[cnt_corr_in + 2] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.prefix_data[64 +: 32];
            corr_input_prefix[cnt_corr_in + 3] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.prefix_data[96 +: 32];  
            
            corr_input_suffix[cnt_corr_in] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.suffix_data[0 +: 32];
            corr_input_suffix[cnt_corr_in + 1] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.suffix_data[32 +: 32];
            corr_input_suffix[cnt_corr_in + 2] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.suffix_data[64 +: 32];
            corr_input_suffix[cnt_corr_in + 3] <= DUT.estimator_inst.correlator_inst.bram_ctrl2corr.suffix_data[96 +: 32]; 
            cnt_corr_in <= cnt_corr_in + 4;                                                                             
        end
        if(cnt_corr_in == 6 * 256) begin
            $writememh("/home/george/corr_input_prefix.txt", corr_input_prefix, 0, 6 * 256 - 1);
            $writememh("/home/george/corr_input_suffix.txt", corr_input_suffix, 0, 6 * 256 - 1);
           
        end
    end 

    logic [31 : 0] corr_output_re [0 : 6 * 256 - 1];
    logic [31 : 0] corr_output_im [0 : 6 * 256 - 1];
    logic [31 : 0] output_data [0 : 5 * 1024 - 1];
    logic [31 : 0] cnt_corr = 0;
    logic [31 : 0] cnt_out = 0;
    logic [31 : 0] sine_wave [0 : 5000];
    logic [31 : 0] symb [0 : 5000];
    logic [31 : 0] cnt_sine = 0;
    always@(posedge clk) begin
        if(DUT.cfo_compensation_inst.correction_inst.bram_ctrl2mult.symbol_tvalid) begin
            sine_wave[cnt_sine / 4] <= DUT.cfo_compensation_inst.correction_inst.correction2mult.sine; 
            
            symb[cnt_sine] <= DUT.cfo_compensation_inst.correction_inst.bram_ctrl2mult.symbol_data[0 +: 32]; 
            symb[cnt_sine + 1] <= DUT.cfo_compensation_inst.correction_inst.bram_ctrl2mult.symbol_data[32 +: 32];
            symb[cnt_sine + 2] <= DUT.cfo_compensation_inst.correction_inst.bram_ctrl2mult.symbol_data[64 +: 32];
            symb[cnt_sine + 3] <= DUT.cfo_compensation_inst.correction_inst.bram_ctrl2mult.symbol_data[96 +: 32];
            cnt_sine <= cnt_sine + 4;                                                                             
        end
        if(cnt_sine == 4000) begin
            $writememh("/home/george/sine.txt", sine_wave, 0, 1400);
            $writememh("/home/george/symb.txt", symb, 0, 3999);
            
        end
    end 
    
    always@(posedge clk) begin
        if(DUT.estimator_inst.correlator_inst.corr2adder.tvalid) begin
            corr_output_re[cnt_corr] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_imag[0];
            corr_output_im[cnt_corr] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_real[0];
            corr_output_re[cnt_corr + 1] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_imag[1];
            corr_output_im[cnt_corr + 1] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_real[1];
            corr_output_re[cnt_corr + 2] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_imag[2];
            corr_output_im[cnt_corr + 2] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_real[2];
            corr_output_re[cnt_corr + 3] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_imag[3];
            corr_output_im[cnt_corr + 3] <= DUT.estimator_inst.correlator_inst.corr2adder.corr_data_real[3]; 
            cnt_corr <= cnt_corr + 4;                                                                             
        end
        if(cnt_corr == 6 * 256) begin
            $writememh("/home/george/corr_output_re.txt", corr_output_re, 0, 6 * 256 - 1);
            $writememh("/home/george/corr_output_im.txt", corr_output_im, 0, 6 * 256 - 1);
        end
    end 
    
    always@(posedge clk) begin
        if(m_axis_tvalid) begin
            output_data[cnt_out] <= m_axis_tdata[0 +: 32];
            output_data[cnt_out + 1] <= m_axis_tdata[32 +: 32];
            output_data[cnt_out + 2] <= m_axis_tdata[64 +: 32];
            output_data[cnt_out + 3] <= m_axis_tdata[96 +: 32];
            cnt_out <= cnt_out + 4;                                                                             
        end
        if(cnt_out == 5 * 1024) begin
            $writememh("/home/george/cfo_est_output.txt", output_data, 0, 5 * 1024 - 1);
             $finish;
        end
    end 
endmodule
