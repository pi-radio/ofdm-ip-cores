`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 09/28/2022 11:11:56 AM
// Design Name: 
// Module Name: pilot_zero_rem_tb
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


module pilot_zero_rem_tb(

    );
    
    reg  axis_aclk = 0;
	reg  axis_aresetn = 0;
	wire  s00_axis_tready;
	wire [127 : 0] s00_axis_tdata;
	wire  s00_axis_tlast;
	reg  s00_axis_tvalid = 0;
	reg  m00_axis_tvalid;
	wire [127 : 0] m00_axis_tdata;
	wire  m00_axis_tlast;
	wire  m00_axis_tready;
	reg  m00_axis_log_tvalid;
	wire [127 : 0] m00_axis_log_tdata;
	wire  m00_axis_log_tlast;
	wire  m00_axis_log_tready;
	
	reg [31 : 0] counter = 0;
	reg [31 : 0] i;
	wire [127 : 0] log;
    
    pilot_zero_remover dut(
    	axis_aclk,
		axis_aresetn,
		s00_axis_tready,
		s00_axis_tdata,
		s00_axis_tlast,
		s00_axis_tvalid,
		m00_axis_tvalid,
		m00_axis_tdata,
		m00_axis_tlast,
		m00_axis_tready,
		m00_axis_log_tvalid,
		m00_axis_log_tdata,
		m00_axis_log_tlast,
		m00_axis_log_tready
    );
    
    initial begin
        forever #5 axis_aclk = ~axis_aclk;
    end
    
    assign s00_axis_tdata = {counter + 3, counter + 2, counter + 1, counter};
    assign m00_axis_tready = 1;
    
    initial begin
    #1000
    @(posedge axis_aclk)
    axis_aresetn <= 1;
    s00_axis_tvalid <= 1;
    for(i = 0; i < 10000; i ++) begin
        @(posedge axis_aclk)
        counter <= counter + 4;
    end
    end
endmodule
