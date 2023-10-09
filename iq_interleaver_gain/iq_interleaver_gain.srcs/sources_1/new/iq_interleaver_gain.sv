
`timescale 1 ns / 1 ps
/*
Author: George Vardakis

This core interleaves the Real (s00_axis interface) with the Imaginary (s01_axis interface)
at the input. It optionally left-shifts the input data by the value programmed at the MM register.
*/
	module iq_interleaver_gain #
	(
		parameter integer SAMPLES_PER_CYCLE	        = 4,
		parameter integer SAMPLE_SIZE	            = 16,
		parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		parameter integer C_S00_AXI_ADDR_WIDTH	= 4		
	)
	(
		input wire clk,
		input wire aresetn,
		output reg  s00_axis_tready,
		input wire [(SAMPLE_SIZE * SAMPLES_PER_CYCLE)-1 : 0] s00_axis_tdata,
		input wire [((SAMPLE_SIZE * SAMPLES_PER_CYCLE)/8)-1 : 0] s00_axis_tstrb,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid,

		// Ports of Axi Slave Bus Interface S01_AXIS
		output reg  s01_axis_tready,
		input wire [(SAMPLE_SIZE * SAMPLES_PER_CYCLE)-1 : 0] s01_axis_tdata,
		input wire [((SAMPLE_SIZE * SAMPLES_PER_CYCLE)/8)-1 : 0] s01_axis_tstrb,
		input wire  s01_axis_tlast,
		input wire  s01_axis_tvalid,

		// Ports of Axi Master Bus Interface M00_AXIS
		output reg  m00_axis_tvalid,
		output reg [(SAMPLE_SIZE * SAMPLES_PER_CYCLE)*2 - 1 : 0] m00_axis_tdata,
		output wire  m00_axis_tlast,
		input wire  m00_axis_tready,
		
		input logic [C_S00_AXI_ADDR_WIDTH-1 : 0] s_axi_awaddr,
		input logic [2 : 0] s_axi_awprot,
		input logic  s_axi_awvalid,
		output logic  s_axi_awready,
		input logic [C_S00_AXI_DATA_WIDTH-1 : 0] s_axi_wdata,
		input logic [(C_S00_AXI_DATA_WIDTH/8)-1 : 0] s_axi_wstrb,
		input logic  s_axi_wvalid,
		output logic  s_axi_wready,
		output logic [1 : 0] s_axi_bresp,
		output logic  s_axi_bvalid,
		input logic  s_axi_bready,
		input logic [C_S00_AXI_ADDR_WIDTH-1 : 0] s_axi_araddr,
		input logic [2 : 0] s_axi_arprot,
		input logic  s_axi_arvalid,
		output logic  s_axi_arready,
		output logic [C_S00_AXI_DATA_WIDTH-1 : 0] s_axi_rdata,
		output logic [1 : 0] s_axi_rresp,
		output logic  s_axi_rvalid,
		input logic  s_axi_rready
	);
	logic [3 : 0] gain;

	reg [10 : 0] index;
	
	 axil_slave axil_slave_i_inst(
        .clk(clk),
        .aresetn(aresetn),
        .*
    );
    

	always_comb begin
        m00_axis_tvalid <= s00_axis_tvalid && s01_axis_tvalid;
        s00_axis_tready <= m00_axis_tready;
        s01_axis_tready <= m00_axis_tready;
    end
    
    always_comb begin
        for(index=0; index < (SAMPLE_SIZE * SAMPLES_PER_CYCLE); index=index + SAMPLE_SIZE) begin
            m00_axis_tdata[ 2* index +: 2*SAMPLE_SIZE] <= {s01_axis_tdata[index +: SAMPLE_SIZE] << gain,
                                                             s00_axis_tdata[index +: SAMPLE_SIZE] << gain};
        end
    end

	endmodule
