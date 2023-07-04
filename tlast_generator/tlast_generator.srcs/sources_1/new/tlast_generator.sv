`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/31/2023 08:31:40 AM
// Design Name: 
// Module Name: tlast_generator
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


module tlast_generator#(
        parameter integer C_S00_AXIS_TDATA_WIDTH	= 128, 
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		parameter integer C_S00_AXI_ADDR_WIDTH	= 4
        )(
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
    logic [31 : 0] frame_len;
    logic [31 : 0] sample_cnt;
    logic reset_len;
    
    assign m00_axis_tvalid = s00_axis_tvalid;
    assign m00_axis_tdata = s00_axis_tdata;
    assign s00_axis_tready = m00_axis_tready;
    assign m00_axis_tlast = (sample_cnt == frame_len - 1);
    
    always@(posedge axis_aclk) begin
        if(!axis_aresetn)
            sample_cnt <= 0;
        else begin
            if(reset_len)  begin
                sample_cnt <= 0;
            end
            else begin
                if(s00_axis_tvalid && m00_axis_tready) begin
                    if(sample_cnt < frame_len - 1)
                        sample_cnt <= sample_cnt + 1;
                    else
                        sample_cnt <= 0;
                end
            end
        end
    end
    
    axil_slave_tlast axil_slave_tlast_inst(
    .clk(axis_aclk),
    .aresetn(axis_aresetn),
    .*
    );
endmodule
