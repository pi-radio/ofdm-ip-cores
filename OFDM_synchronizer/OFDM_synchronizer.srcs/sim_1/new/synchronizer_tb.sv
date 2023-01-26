`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 01/17/2023 08:28:31 AM
// Design Name: 
// Module Name: synchronizer_tb
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


module synchronizer_tb(

    );
    
    logic clk = 0;
    
    initial begin
        forever #5 clk = ~clk;
    end
    
     logic resetn = 0;
     logic [256 - 1 : 0] s_axis_corr_1_tdata;
     logic s_axis_corr_1_tvalid = 0;
     logic s_axis_corr_1_tready;
     logic s_axis_corr_1_tlast;
     logic [256  -1 : 0] s_axis_corr_2_tdata;
     logic s_axis_corr_2_tvalid = 0;
     logic s_axis_corr_2_tready;
     logic s_axis_corr_2_tlast;
     logic [128 - 1 : 0] s_axis_tdata;
     logic s_axis_tvalid = 0;
     logic s_axis_tready;
     logic s_axis_tlast;
     logic [128 - 1 : 0] m_axis_tdata;
     logic m_axis_tvalid;
     logic m_axis_tready;
     logic m_axis_tlast;
     
    synchronizer synchronizer_inst 
    (
      .*
    );
    
    int i;
    initial begin
        #1000
        @(posedge clk)
        resetn <= 1;
        s_axis_corr_1_tlast <= 0;
        wait(s_axis_tready);
        for(i = 0 ; i < 4096; i++) begin
            @(posedge clk)
            s_axis_tvalid <= 1;
            s_axis_corr_2_tvalid <= 1;
            s_axis_corr_1_tvalid <= 1;
            if(i % 256 == 255)
                s_axis_corr_1_tlast <= 1;
            else
                s_axis_corr_1_tlast <= 0;
            if(i == 100 || i == 356) begin
                s_axis_corr_1_tdata <= {64'h0, 64'h0, {2{32'hdeadbeef}}, 64'h0};
                s_axis_tdata <= i;
            end
            else begin
                s_axis_corr_1_tdata <= 256'h0;
                s_axis_tdata <= i;
            end
        end
    end
endmodule
