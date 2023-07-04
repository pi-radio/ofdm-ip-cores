`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/16/2022 11:28:19 AM
// Design Name: 
// Module Name: ifft_tb
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


module ifft_tb(

    );
    
    logic  s_axis_aclk = 0;
	logic  s_axis_aresetn = 0;
	logic  s00_axis_tready;
	logic [128-1 : 0] s00_axis_tdata;
	logic  s00_axis_tlast;
	logic  s00_axis_tvalid = 0;

	logic  m00_axis_tvalid;
	logic [128 - 1 : 0] m00_axis_tdata;
	logic  m00_axis_tlast;
	logic  m00_axis_tready = 1;
     wire [4-1 : 0] s00_axi_awaddr;
     wire [2 : 0] s00_axi_awprot;
     wire  s00_axi_awvalid;
     wire  s00_axi_awready;
     wire [32-1 : 0] s00_axi_wdata;
     wire [(32/8)-1 : 0] s00_axi_wstrb;
     wire  s00_axi_wvalid;
     wire  s00_axi_wready;
     wire [1 : 0] s00_axi_bresp;
     wire  s00_axi_bvalid;
     wire  s00_axi_bready;
     wire [4-1 : 0] s00_axi_araddr;
     wire [2 : 0] s00_axi_arprot;
     wire  s00_axi_arvalid;
     wire  s00_axi_arready;
     wire [32-1 : 0] s00_axi_rdata;
     wire [1 : 0] s00_axi_rresp;
     wire  s00_axi_rvalid;
     wire  s00_axi_rready;
     logic trigger, trigger2;
    ssr_IFFT #(
        .C_M00_AXIS_TDATA_WIDTH(256),
        .scaled(1),
        .insert_cp(1)
    ) dut
	(
		.*
	);
	
	initial begin
	   forever #5 s_axis_aclk = ~s_axis_aclk;
	end
	
	
	logic [127 : 0] buffer[0 : 1023];
	logic [31 : 0] buffer32[0 : 4191];
	logic [11 : 0] idx = 0;
	logic [20 : 0] idx2 = 0;
	integer l;
	
//	always@(posedge s_axis_aclk) begin
//        if(m00_axis_tvalid)	begin
//            buffer[idx] <= m00_axis_tdata;
//            if(idx >= 1024 && idx < 2048) begin
//                for(l = 0 ; l < 4; l++) begin
//                    buffer32[idx2 + l] <= (buffer[idx2/4] >> l * 32);
//                end
//                idx2 <= idx2 + 4;
//                idx++;
//            end
//            else if(idx < 1024)
//                idx++;
//            else begin
//                //$writememh("/home/george/ifft.txt", buffer32, 0, 4191);
//                $finish;
//            end
                
//        end
//	end
	integer i;
	
	initial begin
	   repeat(100) @(posedge s_axis_aclk);
	   s00_axis_tvalid <= 1;
	   s00_axis_tdata <= 0;
	   s_axis_aresetn <= 1;
	   for(i = 0; i < 2560 ; i++) begin
	       @(posedge s_axis_aclk);
	       if(!s00_axis_tready) begin
	           wait(s00_axis_tready);
	           repeat(1)@(posedge s_axis_aclk);
	       end
           if(i % 256 == 55)
               s00_axis_tdata <= 128'h03fff;
           else
               s00_axis_tdata <= 0;
	   end
	   s00_axis_tvalid <= 0;
	   repeat(100) @(posedge s_axis_aclk);
	   s00_axis_tvalid <= 1;
	   for(i = 0; i < 2560; i++) begin
	       @(posedge s_axis_aclk);
	       if(!s00_axis_tready) begin
	           wait(s00_axis_tready);
	           repeat(1)@(posedge s_axis_aclk);
	       end
           if(i % 256 == 55)
               s00_axis_tdata <= 128'h03fff;
           else
               s00_axis_tdata <= 0;
	   end
	    s00_axis_tvalid <= 0;
	   wait(!m00_axis_tvalid);
	   $finish;
	end
endmodule
