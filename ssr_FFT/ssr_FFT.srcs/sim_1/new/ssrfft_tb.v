`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/12/2022 02:29:41 PM
// Design Name: 
// Module Name: ssrfft_tb
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


module ssrfft_tb(

    );
  wire signed [31 : 0] res;
  reg aclk = 0;
  reg resetn = 0;
  reg signed [15 : 0] high_end = 16'h6488;
  reg signed [15 : 0] low_end = 16'h9B78;
    
  reg [15 : 0] phase = 32'h0032;

  wire signed [ 15 : 0 ]S_AXIS_tdata;
  wire S_AXIS_tready;
  reg S_AXIS_tvalid = 0;

  reg signed [31:0]S_AXIS_CONFIG_tdata = 32'h00000000;
  wire S_AXIS_CONFIG_tready;
  reg S_AXIS_CONFIG_tvalid = 0;
  
  wire [31:0]M_AXIS_tdata;
  wire M_AXIS_tlast;
  wire M_AXIS_tready;
  wire [3:0]M_AXIS_tstrb;
  wire M_AXIS_tvalid;
  
  wire [31:0]M_AXIS_DATA_tdata;
  wire M_AXIS_DATA_tlast;
  wire M_AXIS_DATA_tready;
  wire [3:0]M_AXIS_DATA_tstrb;
  wire M_AXIS_DATA_tvalid;
  reg start = 0;
  
  reg [9 : 0] counter = 0;
    
  assign M_AXIS_tready = 1;
  //assign res = S_AXIS_tdata + phase;
  wire [16 : 0] mag_sq_sample;
  wire signed [15:0] tmp_i; 
  wire signed [15:0] tmp_q;
  wire signed [32:0] tmp_i_sq; 
  wire signed [32:0] tmp_q_sq;
  assign tmp_i_sq = tmp_i * tmp_i;
  assign tmp_q_sq = tmp_q * tmp_q;
  assign mag_sq_sample = (tmp_i_sq >> 15) + (tmp_q_sq >> 15); 
  assign tmp_i = M_AXIS_tdata[15 : 0];
  assign tmp_q = M_AXIS_tdata[32 : 16];
  assign M_AXIS_DATA_tready = 1;
  design_1_wrapper dut
       (
        .S_AXIS_tdata(S_AXIS_tdata),
        .S_AXIS_tvalid(S_AXIS_tvalid),
//        .S_AXIS_CONFIG_tdata(S_AXIS_CONFIG_tdata),
//        .S_AXIS_CONFIG_tvalid(S_AXIS_CONFIG_tvalid),
//        .S_AXIS_CONFIG_tready(S_AXIS_CONFIG_tready),
        .aclk(aclk),
        .M_AXIS_tdata(M_AXIS_tdata),
        .M_AXIS_tready(M_AXIS_tready),
        .M_AXIS_tvalid(M_AXIS_tvalid),
        .M_AXIS_tstrb(M_AXIS_tstrb),
//        .M_AXIS_DATA_tdata(M_AXIS_DATA_tdata),
//        .M_AXIS_DATA_tready(M_AXIS_DATA_tready),
//        .M_AXIS_DATA_tvalid(M_AXIS_DATA_tvalid),
        .aresetn(resetn));

    assign S_AXIS_tdata[15 : 13] = {3 {counter[9]}};
    assign S_AXIS_tdata[12 : 4] = counter[8 : 0];
    assign S_AXIS_tdata[3 : 0] = 4'b0000;
    
    initial begin
        forever #1.25 aclk = ~aclk;
    end 
  
  initial begin
    #100 resetn = 1;
    #87.5 S_AXIS_CONFIG_tvalid <= 1;
    # 20 S_AXIS_CONFIG_tvalid <= 0;
    #700.5
    @(posedge aclk)
    S_AXIS_tvalid <= 1;
    start <= 1;
  end
  
  always @(posedge aclk) begin
    if(!resetn)
        counter <= 10'b0100000000;
    else begin
        if(start) begin
            counter <= counter + 2;
       end 
    end
  end
 
    
//  always @(posedge aclk) begin
//        if(!resetn) begin
//            S_AXIS_tdata <= 16'h00000000;
//        end
//        else begin
//        if(start) begin
//            S_AXIS_tvalid <= 1;
//            if(((res) > high_end)) begin  
//                S_AXIS_tdata <= low_end; //(S_AXIS_DATA_tdata + phase - (high_end + 1)) + low_end;
//            end
//            else 
//                S_AXIS_tdata <= S_AXIS_tdata + phase;
//            end
//        end
//    end
	
endmodule
