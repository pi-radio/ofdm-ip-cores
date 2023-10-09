
`timescale 1 ns / 1 ps

/*
Author : George Vardakis

This block adds a delay to the input axi stream interface.
The output is zero padded for DELAY number of clock cycles
after reset and if m_axis_ready is asserted.
*/
	module delay #
	(
		// Parameters of Axi Slave Bus Interface S00_AXIS
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,

		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer DELAY	= 0
	)
	(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output wire  s00_axis_tready,
		input wire [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input wire [(C_S00_AXIS_TDATA_WIDTH/8)-1 : 0] s00_axis_tstrb,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid,

		output wire  m00_axis_tvalid,
		output wire [C_M00_AXIS_TDATA_WIDTH-1 : 0] m00_axis_tdata,
		output wire [(C_M00_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		output wire  m00_axis_tlast,
		input wire  m00_axis_tready
	);
    
    reg [13 : 0] count = 0;
    assign s00_axis_tready = (count < DELAY) ? 0 : m00_axis_tready;
    assign m00_axis_tdata = (count < DELAY) ? 32'h00000000 : s00_axis_tdata;
    assign m00_axis_tvalid = s00_axis_tvalid;
    
    always@(posedge axis_aclk) begin
        if(~axis_aresetn)
            count <= 0;
        else begin
            if(s00_axis_tvalid && m00_axis_tready && count < DELAY)
                count <= count + 1;
        end
    end

	endmodule
