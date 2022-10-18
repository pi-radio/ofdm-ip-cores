`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/21/2022 04:48:13 PM
// Design Name: 
// Module Name: correlator_tb
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


module correlator_tb
    ();
    
    reg  s_axis_aclk = 0;
	reg  s_axis_aresetn = 0;
    wire  s00_axis_tready;
	wire [128-1 : 0] s00_axis_tdata;
	wire [(128/8)-1 : 0] s00_axis_tstrb;
	wire  s00_axis_tlast;
	wire  s00_axis_tvalid;

	wire  s00_axis_config_tready;
	wire [31 : 0] s00_axis_config_tdata;
	wire [(32/8)-1 : 0] s00_axis_config_tstrb;
	wire  s00_axis_config_tlast;
	wire  s00_axis_config_tvalid;

	wire  m00_axis_tvalid;
	wire [128-1 : 0] m00_axis_tdata;
	wire [(128/8)-1 : 0] m00_axis_tstrb;
	wire  m00_axis_tlast;
	wire  m00_axis_tread;
	reg [31 : 0] rand_val;
	
	reg [12 : 0] swc_counter = 0;
	
    OFDM_correlator corr_inst
	(
		s_axis_aclk,
		s_axis_aresetn,
		s00_axis_tready,
		s00_axis_tdata,
		s00_axis_tstrb,
		s00_axis_tlast,
		s00_axis_tvalid,

		s00_axis_config_tready,
		s00_axis_config_tdata,
		s00_axis_config_tstrb,
		s00_axis_config_tlast,
		s00_axis_config_tvalid,

		m00_axis_tvalid,
		m00_axis_tdata,
		m00_axis_tstrb,
		m00_axis_tlast,
		m00_axis_tready
	); 
	
    assign s00_axis_config_tdata = rand_val;
    assign s00_axis_config_tvalid = (swc_counter < 1024);
    
    assign s00_axis_tvalid = ~s00_axis_config_tready;
    assign s00_axis_tdata = 128'hffff;
                                 
    assign m00_axis_tready = 1;
    
    always@ (posedge s_axis_aclk) rand_val <= $random;
    always@ (posedge s_axis_aclk) begin
        if(!s_axis_aresetn)
            swc_counter <= 0;
        else begin
            if(s00_axis_config_tready)
                swc_counter <= swc_counter + 1;
        end
    end
    
    initial begin
        forever #5 s_axis_aclk = ~s_axis_aclk;
    end
    
    initial begin
        #200
        @(posedge s_axis_aclk)
        s_axis_aresetn <= 1;
    end
    
    
    //Assert that if m_valid asserts, it doesn't deassert again
    assert property (
        @(posedge s_axis_aclk)
	   (m00_axis_tvalid |=> m00_axis_tvalid)
	   );
    
endmodule
