`timescale 1ns / 1ps

import demodulator_package::*;
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/23/2022 02:51:23 PM
// Design Name: 
// Module Name: OFDM_demodulator
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


module OFDM_demodulator
        import demodulator_package::*;
        #(
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128, 
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		// Parameters of Axi Slave Bus Interface S00_AXI
		parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		parameter integer C_S00_AXI_ADDR_WIDTH	= 4,
		parameter integer SOFT_OUTPUT           = 1
	)
	(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output logic  s00_axis_tready,
		input logic [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input logic [(C_S00_AXIS_TDATA_WIDTH/8)-1 : 0] s00_axis_tstrb,
		input logic  s00_axis_tlast,
		input logic  s00_axis_tvalid,

		output logic  m00_axis_tvalid,
		output logic [C_M00_AXIS_TDATA_WIDTH-1 : 0] m00_axis_tdata,
		output logic [(C_M00_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		output logic  m00_axis_tlast,
		input logic  m00_axis_tready,
		
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
	logic [C_S00_AXIS_TDATA_WIDTH-1 : 0] in_tdata;
	logic in_tvalid, in_tready, in_tlast;
	logic enable_hard;
	logic enable_soft;
    logic [C_M00_AXIS_TDATA_WIDTH-1 : 0] demod_soft_outt;
    logic [C_M00_AXIS_TDATA_WIDTH-1 : 0] demod_hard_outt;
    logic demod_soft_tvalid, demod_hard_tvalid;
    logic demod_soft_tready, demod_hard_tready; 
    logic demod_hard_tlast;
    logic comb_in_valid, comb_out_valid, demod_in_tvalid;
    logic [C_S00_AXIS_TDATA_WIDTH - 1 : 0] comb_in_tdata;
    logic [C_M00_AXIS_TDATA_WIDTH - 1 : 0] comb_out_tdata;
    logic [C_M00_AXIS_TDATA_WIDTH - 1 : 0] demod_in_tdata;
    mod_t modulation;
    
    assign m00_axis_tdata = (SOFT_OUTPUT) ? demod_soft_outt : demod_hard_outt;
    assign m00_axis_tvalid = (SOFT_OUTPUT) ? demod_soft_tvalid : demod_hard_tvalid;
    //assign demod_soft_tready = (SOFT_OUTPUT) ? m00_axis_tready : 0;
    assign m00_axis_tlast = (SOFT_OUTPUT) ? 0 : demod_hard_tlast;
    assign s00_axis_tready = (SOFT_OUTPUT) ? demod_soft_tready : demod_hard_tready;
    assign comb_in_valid = (C_S00_AXIS_TDATA_WIDTH != C_M00_AXIS_TDATA_WIDTH) 
                                        ? s00_axis_tvalid : 0;
    assign comb_in_tdata = (C_S00_AXIS_TDATA_WIDTH != C_M00_AXIS_TDATA_WIDTH) 
                                        ? s00_axis_tdata : 32'h0;
    assign demod_in_tvalid = (C_S00_AXIS_TDATA_WIDTH != C_M00_AXIS_TDATA_WIDTH) 
                                        ? comb_out_valid : s00_axis_tvalid;
    assign demod_in_tdata = (C_S00_AXIS_TDATA_WIDTH != C_M00_AXIS_TDATA_WIDTH) 
                                        ? comb_out_tdata : s00_axis_tdata;                         
    
    input_combiner input_combiner_inst(
        .clk(axis_aclk),
        .aresetn(axis_aresetn),
        .s_axis_tdata(comb_in_tdata),
        .s_axis_tvalid(comb_in_valid),
        .m_axis_tdata(comb_out_tdata),
        .m_axis_tvalid(comb_out_valid)
    );
    
    demod_hard_out demod_hard_out_inst(
        .axis_aclk(axis_aclk),
        .axis_aresetn(axis_aresetn),
        .s00_axis_tready(demod_hard_tready),
        .s00_axis_tdata(demod_in_tdata),
        .s00_axis_tvalid(demod_in_tvalid),
        .out_hard_axis_tdata(demod_hard_outt),
        .out_hard_axis_tvalid(demod_hard_tvalid),
        .out_hard_axis_tready(m00_axis_tready),
        .out_hard_axis_tlast(demod_hard_tlast),
        .modulation(modulation)
    );
    
    demod_soft_out demod_soft_out_inst(
        .axis_aclk(axis_aclk),
        .axis_aresetn(axis_aresetn),
        .s00_axis_tready(demod_soft_tready),
        .s00_axis_tdata(demod_in_tdata),
        .s00_axis_tvalid(demod_in_tvalid),
        .out_soft_axis_tdata(demod_soft_outt),
        .out_soft_axis_tvalid(demod_soft_tvalid),
        .out_soft_axis_tready(m00_axis_tready),
        .modulation(modulation)
    );
    
    axil_slave axil_slave_inst(
        .clk(axis_aclk),
        .aresetn(axis_aresetn),
        .*
    );
		
endmodule