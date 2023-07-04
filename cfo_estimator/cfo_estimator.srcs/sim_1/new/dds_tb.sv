`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/25/2023 12:13:02 PM
// Design Name: 
// Module Name: dds_tb
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


module dds_tb(

    );
    logic clk = 0;
    logic aresetn;
    logic [31 : 0] data_in;
    logic data_in_valid;
    logic [15 : 0] data_out;
    logic data_out_valid;
    
    initial begin
        forever #5 clk = ~clk;
    end
    
    initial begin
        repeat(31000)@(posedge clk);
        data_in <= 28'h027e;
        data_in_valid <= 1;
        @(posedge clk);
        data_in_valid <= 0;
        repeat(33000)@(posedge clk);
        data_in <= 28'h127e;
        data_in_valid <= 1;
        @(posedge clk);
        data_in_valid <= 0;
    end
    
    sine_wave sine_wave_inst (
      .aclk(clk),                                  // input wire aclk
      .s_axis_config_tvalid(data_in_valid),  // input wire s_axis_config_tvalid
      .s_axis_config_tdata(data_in),    // input wire [31 : 0] s_axis_config_tdata
      .m_axis_data_tvalid(data_out_valid),      // output wire m_axis_data_tvalid
      .m_axis_data_tdata(data_out)        // output wire [15 : 0] m_axis_data_tdata
    );
endmodule
