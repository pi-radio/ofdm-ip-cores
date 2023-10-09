`timescale 1ns / 1ps
/*
Author: George Vardakis

This core is responsible for reconfiguring the Xilinx SDFEC core.
As the Xilinx core requires one configuration block per data block
at its input, this core helps to count the data at the input of the 
SDFEC core and program it accordingly when required. It uses a memory
mapped interface in order for the user to program the number of bytes
per block as well as the configuration word for the SDFEC core.
*/


module fec_controller        #(
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 40,
		parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		parameter integer C_S00_AXI_ADDR_WIDTH	= 4,
		parameter integer BITS_PER_SYMBOL       = 1
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
    
    localparam symbols_per_input = C_S00_AXIS_TDATA_WIDTH / BITS_PER_SYMBOL;
    typedef enum {IDLE, ACTIVE_CTRL, ACTIVE_NO_CTRL} state_t;
    logic [39 : 0] ctrl_data;
    logic [31 : 0] block_len;
    logic ctrl_active;
    state_t state;
    logic [31 : 0] symbol_counter;
    
    assign s00_axis_tready = 1;
    assign m00_axis_tdata = ctrl_data;
    assign m00_axis_tvalid = (state == ACTIVE_CTRL);
    
    always@(posedge axis_aclk) begin
        if(!axis_aresetn) begin
            symbol_counter <= 0;
        end
        if(state != IDLE) begin
            if(s00_axis_tvalid && m00_axis_tready) begin
                if(symbol_counter == block_len - symbols_per_input)
                    symbol_counter <= 0;
                else
                    symbol_counter <= symbol_counter + symbols_per_input;
            end
        end
    end
    
    always @(posedge axis_aclk) begin
        if(!axis_aresetn) begin
            state <= IDLE;
        end
        else begin
            case(state) 
                IDLE: begin
                    if(ctrl_active) state <= ACTIVE_CTRL;
                end
                ACTIVE_CTRL : begin
                    if(!ctrl_active) state <= IDLE;
                    else if(m00_axis_tready) state <= ACTIVE_NO_CTRL;
                end
                ACTIVE_NO_CTRL : begin
                    if(!ctrl_active) state <= IDLE;
                    else if((symbol_counter == block_len - symbols_per_input) 
                                && s00_axis_tvalid)
                            state <= ACTIVE_CTRL;
                end
            endcase
        end
    end
    
    
     axi_slave axil_slave_inst(
        .clk(axis_aclk),
        .aresetn(axis_aresetn),
        .*
    );
endmodule
