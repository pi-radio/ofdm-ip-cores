`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/09/2022 12:29:50 PM
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
    reg  s_axis_aclk = 0 ;
    reg  s_axis_aresetn;
    wire  s00_axis_tready;
    wire [128-1 : 0] s00_axis_tdata;
    wire [(128/8)-1 : 0] s00_axis_tstrb;
    wire  s00_axis_tlast;
    reg  s00_axis_tvalid = 0;

    wire  m00_axis_tvalid;
    wire [128 - 1 : 0] m00_axis_tdata;
    wire [(128/8)-1 : 0] m00_axis_tstrb;
    wire  m00_axis_tlast;
    reg  m00_axis_tready = 1;
    reg [20 : 0 ]count = 0;
    reg [20 : 0] count_valid = 0;
	reg valid = 0;
	reg [20 : 0] i;
	reg [20 : 0] halted;
	reg [20 : 0] valid_idle = 1000;
    
    //assign s00_axis_tdata = 128'h00003fff00003fff00003fff00003fff;
    assign s00_axis_tdata = 128'h0000c0000000c0000000c0000000c000;
    
    ssr_IFFT_v1_0  #(
    .C_S00_AXIS_TDATA_WIDTH(128),
    .C_M00_AXIS_TDATA_WIDTH(128),
    .insert_cp(0),
    .scaled(1)
    ) dut
	(
		s_axis_aclk,
		s_axis_aresetn,
		s00_axis_tready,
		s00_axis_tdata,
		s00_axis_tlast,
		s00_axis_tvalid,

		m00_axis_tvalid,
		m00_axis_tdata,
		m00_axis_tlast,
		m00_axis_tready
	);
	reg reset;
	initial begin
	   forever #5 s_axis_aclk = ~s_axis_aclk;
	end
	    /* Make sure Valids deassert with reset*/
    assert property (@(posedge s_axis_aclk)
	   !s_axis_aresetn |-> !m00_axis_tvalid);

    assert property (@(posedge s_axis_aclk)
	   !s_axis_aresetn |-> !s00_axis_tvalid);
	   
	/* Make sure data does not change if m_axis_tready deasserts*/
	assert property (@(posedge s_axis_aclk)
	   m00_axis_tvalid && !m00_axis_tready && s_axis_aresetn
	       |=> m00_axis_tvalid && $stable(m00_axis_tdata));
	
	initial begin
	   s_axis_aresetn <= 0;
	   s_axis_aclk <= 0;
	   reset <= 1;
	   count <= 0;
	   #200 
	   @(posedge s_axis_aclk)
	   s_axis_aresetn <= 1;
	   s00_axis_tvalid <= 1; 
	   for(i = 0 ; i< 20000; i++) begin
//	       @(posedge s_axis_aclk)
//	       if(halted + valid_idle < i) begin
//	           if(halted != 0) begin
//                    s00_axis_tvalid <= 1;
//                    halted <= 0;
//                end
//            end
//           if(s00_axis_tvalid && s00_axis_tready) begin
//                count <= count + 1;
//                if((count[9 : 8] == 3) && count[7 : 0] == 8'hff && s00_axis_tready) begin
//                    s00_axis_tvalid <= 0;
//                    halted <= i;
//                end
//           end
	   end

//	   $finish;
	end
	
endmodule
