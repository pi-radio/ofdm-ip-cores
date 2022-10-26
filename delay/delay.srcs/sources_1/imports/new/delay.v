
`timescale 1 ns / 1 ps

	module delay #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Slave Bus Interface S00_AXIS
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,

		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer DELAY	= 0
	)
	(
		// Users to add ports here

		// User ports ends
		// Do not modify the ports beyond this line


		// Ports of Axi Slave Bus Interface S00_AXIS
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
