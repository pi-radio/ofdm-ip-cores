`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/12/2023 02:42:03 PM
// Design Name: 
// Module Name: fft_tb
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


module fft_tb(

    );
    logic axis_aclk = 0;
	logic  axis_aresetn = 0;
	logic  s00_axis_tready;
	logic [127 : 0] s00_axis_tdata;
	logic  s00_axis_tlast;
	logic  s00_axis_tvalid;

	logic  m00_axis_tvalid;
	logic [127 : 0] m00_axis_tdata;
	logic  m00_axis_tlast;
	logic  m00_axis_tready;
    
    initial begin
        forever #5 axis_aclk = ~axis_aclk;
    end
    logic [31 : 0] data_in[0 : 10000];
    logic [31 : 0] data_in_cnt = 0;
    logic [31 : 0] data_out[0 : 10000];
    logic [31 : 0] data_out_cnt = 0;
    
    assign m00_axis_tready = 1;
    assign s00_axis_tdata = {data_in[(k*320 + i * 4 + 3)],
                            data_in[(k*320 + i * 4 + 2)],
                            data_in[(k*320 + i * 4 + 1)], 
                            data_in[(k*320 + i * 4)]};
    initial
        $readmemh("/home/george/chann_test.txt", data_in,0,8192);
    int i,k;
    initial begin
        #1000
        @(posedge axis_aclk);  
        axis_aresetn <= 1;
//        s00_axis_tvalid <= 1;
//        @(posedge axis_aclk);  
        for(k = 0; k < 7; k++) begin
            for(i = 64; i < 320; i++) begin
            s00_axis_tvalid <= 1;
            @(posedge axis_aclk);    
            end
            s00_axis_tvalid <= 0;
            repeat(64)@(posedge axis_aclk);
            s00_axis_tvalid <= 1;
        end
        s00_axis_tvalid <= 0;
    end
    
    always@(posedge axis_aclk) begin
        if(m00_axis_tvalid) begin
            data_out[data_out_cnt] <= m00_axis_tdata[0 +: 32];
            data_out[data_out_cnt + 1] <= m00_axis_tdata[32 +: 32];
            data_out[data_out_cnt + 2] <= m00_axis_tdata[64 +: 32];
            data_out[data_out_cnt + 3] <= m00_axis_tdata[96 +: 32];
            data_out_cnt <= data_out_cnt + 4;
            if(data_out_cnt == 7 * 1024)
                $writememh("/home/george/chann_out.txt", data_out, 0, 10000);
        end
    end
    
    ssr_FFT#(
         .FFT_SHIFT(1)
         ) DUT(
        .axis_aclk(axis_aclk),
        .axis_aresetn(axis_aresetn),
        .s00_axis_tready(s00_axis_tready),
        .s00_axis_tdata(s00_axis_tdata),
        .s00_axis_tlast(s00_axis_tlast),
        .s00_axis_tvalid(s00_axis_tvalid),
        .m00_axis_tvalid(m00_axis_tvalid),
        .m00_axis_tdata(m00_axis_tdata),
        .m00_axis_tlast(m00_axis_tlast),
        .m00_axis_tready(m00_axis_tready)
    );
endmodule
