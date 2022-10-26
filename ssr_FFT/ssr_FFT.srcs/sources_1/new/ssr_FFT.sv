`timescale 1 ns / 1 ps

	module ssr_FFT #
	(
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer scaled = 1
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

    wire [C_S00_AXIS_TDATA_WIDTH/2 - 1 : 0] in_real;
	wire [C_S00_AXIS_TDATA_WIDTH/2 - 1: 0] in_imag;
	wire [9 : 0] scale_in;
	wire [9 : 0] scale_out;
	wire [25 : 0] o_im_0;
    wire [25 : 0] o_im_1;
    wire [25 : 0] o_re_0;
    wire [25 : 0] o_re_1;
    wire [25 : 0] o_im_2;
    wire [25 : 0] o_im_3;
    wire [25 : 0] o_re_2;
    wire [25 : 0] o_re_3;
    wire signed [15 : 0] o_im_0_shifted;
    wire signed [15 : 0] o_im_1_shifted;
    wire signed [15 : 0] o_re_0_shifted;
    wire signed [15 : 0] o_re_1_shifted;
    wire signed [15 : 0] o_im_2_shifted;
    wire signed [15 : 0] o_im_3_shifted;
    wire signed [15 : 0] o_re_2_shifted;
    wire signed [15 : 0] o_re_3_shifted;
    wire fft_valid_out;
    wire fft_last;
    reg [20 : 0] bit_index = 0;
    
    assign m00_axis_tvalid = fft_valid_out;
    assign m00_axis_tdata = (scaled == 1) ? {o_im_3_shifted, o_re_3_shifted
                            ,o_im_2_shifted, o_re_2_shifted
                            ,o_im_1_shifted, o_re_1_shifted
                            ,o_im_0_shifted, o_re_0_shifted} :
                            {6'h00,o_im_3,6'h00, o_re_3, 
                            6'h00,o_im_2,6'h00, o_re_2, 
                            6'h00,o_im_1,6'h00, o_re_1,
                            6'h00,o_im_0,6'h00, o_re_0};
    
    assign o_im_0_shifted = o_im_0[24 : 9];
    assign o_im_1_shifted = o_im_1[24 : 9];
    assign o_im_2_shifted = o_im_2[24 : 9];
    assign o_im_3_shifted = o_im_3[24 : 9];
    assign o_re_0_shifted = o_re_0[24 : 9];
    assign o_re_1_shifted = o_re_1[24 : 9];
    assign o_re_2_shifted = o_re_2[24 : 9];
    assign o_re_3_shifted = o_re_3[24 : 9];
	
	assign in_real[15 : 0] = s00_axis_tdata[15 : 0];
    assign in_imag[15 : 0] = s00_axis_tdata[31 : 16];
    assign in_real[31 : 16] = s00_axis_tdata[47 : 32];
    assign in_imag[31 : 16] = s00_axis_tdata[63 : 48];
    assign in_real[47 : 32] = s00_axis_tdata[79 : 64];
    assign in_imag[47 : 32] = s00_axis_tdata[95 : 80];
    assign in_real[63 : 48] = s00_axis_tdata[111 : 96];
    assign in_imag[63 : 48] = s00_axis_tdata[127 : 112];
	
	assign scale_in = 10'h000;
	assign s00_axis_tready = m00_axis_tready;

    sysgenssrfft_0 ssrfft_inst (
      .si(scale_in),         
      .vi(s00_axis_tvalid),
      .i_im_0(in_imag[15 : 0]),
      .i_im_1(in_imag[31 : 16]), 
      .i_re_0(in_real[15 : 0]), 
      .i_re_1(in_real[31 : 16]),
      .i_im_2(in_imag[47 : 32]),
      .i_im_3(in_imag[63 : 48]),
      .i_re_2(in_real[47 : 32]),
      .i_re_3(in_real[63 : 48]), 
      .clk(axis_aclk),
      .last(fft_last),
      .so(scale_out),
      .vo(fft_valid_out), 
      .o_im_0(o_im_0), 
      .o_im_1(o_im_1), 
      .o_im_2(o_im_2), 
      .o_im_3(o_im_3),
      .o_re_0(o_re_0),
      .o_re_1(o_re_1),
      .o_re_2(o_re_2), 
      .o_re_3(o_re_3)  
    );
    
    // Make sure s_tvalid is always asserted for at least 256 cycles  
	reg [7 : 0] count_s_valid = 0;
	always @(posedge axis_aclk) begin
        if(s00_axis_tvalid && s00_axis_tready)
            count_s_valid <= count_s_valid + 1;
    end
    assert property (@(posedge axis_aclk)
	   $fell(s00_axis_tvalid) |=> 
	               (count_s_valid == 0)); 
	assert property (@(posedge axis_aclk)
	   $fell(s00_axis_tready) |=> 
	               (count_s_valid == 0)); 

	endmodule
