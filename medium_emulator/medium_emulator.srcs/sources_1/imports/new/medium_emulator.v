
`timescale 1 ns / 1 ps

	module medium_emulator_v1_0 #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Slave Bus Interface S00_AXIS
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,

		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_START_COUNT	= 32
	)
	(

		input wire  s_axis_aclk,
		input wire  s_axis_aresetn,
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
	reg [31 : 0] reg_out[0 : 3];
    reg [31 : 0] taps = 32'd6571454629;
    wire [C_M00_AXIS_TDATA_WIDTH - 1 : 0] seed;
    assign seed = { 7'h0000,reg_out[3][24 : 16], 7'h0000, reg_out[3][8 : 0],
                     7'h0000,reg_out[2][24 : 16], 7'h0000, reg_out[2][8 : 0],
                     7'h0000,reg_out[1][24 : 16], 7'h0000, reg_out[1][8 : 0],
                      7'h0000,reg_out[0][24 : 16], 7'h0000, reg_out[0][8 : 0]};
    reg go = 0;
    reg [20 : 0] counter = 0;
    localparam init_delay = C_M00_AXIS_START_COUNT;
    wire [3 : 0] lsb;
    assign lsb[0] = reg_out[0][0];
    assign lsb[1] = reg_out[1][0];
    assign lsb[2] = reg_out[2][0];
    assign lsb[3] = reg_out[3][0];
    
    wire [127 : 0] noisy_out;
    genvar i;
    
    //reg [31 : 0] taps = 32'd6571454629;
    
    
    always @(posedge s_axis_aclk) begin
        if(!s_axis_aresetn) begin
            reg_out[0] <= 32'h909cd12b;
            reg_out[1] <= 32'h9aacd542;
            reg_out[2] <= 32'h38c01a4e;
            reg_out[3] <= 32'ha6782f5c;
        end
        else begin
            if(lsb[0])
                reg_out[0] <= {1'b0, reg_out[0][31 : 1]} ^ taps;
            else
                reg_out[0] <= {1'b0, reg_out[0][31 : 1]};
            if(lsb[1])
                reg_out[1] <= {1'b0, reg_out[1][31 : 1]} ^ taps;
            else
                reg_out[1] <= {1'b0, reg_out[1][31 : 1]};
            if(lsb[2])
                reg_out[2] <= {1'b0, reg_out[2][31 : 1]} ^ taps;
            else
                reg_out[2] <= {1'b0, reg_out[2][31 : 1]};
            if(lsb[3])
                reg_out[3] <= {1'b0, reg_out[3][31 : 1]} ^ taps;
            else
                reg_out[3] <= {1'b0, reg_out[3][31 : 1]};
        end
    end
    

    assign s00_axis_tready = m00_axis_tready;
    generate
    for(i = 0; i < 4; i = i + 1) begin
        assign noisy_out[i * 32 +: 16] = s00_axis_tdata[i * 32 +: 16] + reg_out[i][8 : 0];
        assign noisy_out[i * 32 + 16 +: 16] = s00_axis_tdata[i * 32 + 16 +: 16] + reg_out[i][24 : 16];
    end
    endgenerate
    
    
    assign m00_axis_tdata = m00_axis_tready ?( s00_axis_tvalid ? s00_axis_tdata /*(noisy_out)*/ :
                    (32'h00000000/*seed*/)) : 32'h00000000/*seed*/ ;
    assign m00_axis_tvalid = counter >= init_delay;
    
    always@(posedge s_axis_aclk) begin
        if(!s_axis_aresetn)
            counter <= 0;
        else
            if(counter < init_delay)
                counter <= counter + 1;
    end

	endmodule
