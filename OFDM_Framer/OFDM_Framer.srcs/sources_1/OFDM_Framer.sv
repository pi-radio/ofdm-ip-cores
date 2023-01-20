import piradio_ofdm::*;

`timescale 1 ns / 1 ps
	module OFDM_Framer #
	(
		parameter integer C_S_AXIS_DATA_TDATA_WIDTH	= 32,
		parameter integer C_M_AXIS_DATA_TDATA_WIDTH	= 128
	)
	(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output wire  s_axis_data_tready,
		input wire [C_S_AXIS_DATA_TDATA_WIDTH-1 : 0] s_axis_data_tdata,
		input wire  s_axis_data_tlast,
		input wire  s_axis_data_tvalid,
		output wire  m_axis_data_tvalid,
		output wire [C_M_AXIS_DATA_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output wire  m_axis_data_tlast,
		input wire  m_axis_data_tready,
		output wire  s_axis_config_tready,
		input wire [C_S_AXIS_DATA_TDATA_WIDTH - 1 : 0] s_axis_config_tdata,
		input wire [(C_S_AXIS_DATA_TDATA_WIDTH/8)-1 : 0] s_axis_config_tstrb,
		input wire  s_axis_config_tlast,
		input wire  s_axis_config_tvalid
	);

    wire [127 : 0] s_axis_fifo_tdata;
    wire s_axis_fifo_tvalid;
    wire s_axis_fifo_tready;
    wire s_axis_fifo_tlast;
    wire fifo_almost_full;
    wire ena, enb;
    wire [0 : 0] wea;
    wire [127 : 0] dina, doutb;
    wire [3 : 0] doutb_map;
    wire [8 : 0] addra, addrb;
    wire structs_ready;
    bram_fifo_in_iface bram_syncw_bus();
    bram_fifo_in_iface#(.WIDTH(132)) bram_temp_bus();
    
    assign wea = 1;
    
	sync_word_module sync_word_mod_inst (
        .s_axis_config_aclk(axis_aclk),
		.s_axis_config_aresetn(axis_aresetn),
		.s_axis_config_tready(s_axis_config_tready),
		.s_axis_config_tdata(s_axis_config_tdata),
		.s_axis_config_tstrb(s_axis_config_tstrb),
		.s_axis_config_tlast(s_axis_config_tlast),
		.s_axis_config_tvalid(s_axis_config_tvalid),
		.structs_ready(structs_ready),
		.bram_syncw_bus(bram_syncw_bus.slave),
		.bram_temp_bus(bram_temp_bus.slave)
       );
            
       data_module #(
        .S_AXIS_TDATA_WIDTH(C_S_AXIS_DATA_TDATA_WIDTH),
        .M_AXIS_TDATA_WIDTH(C_M_AXIS_DATA_TDATA_WIDTH)
       )
       data_module_inst 
       (
            .s_axis_data_aclk(axis_aclk),
            .s_axis_data_aresetn(axis_aresetn),
            .s_axis_data_tready(s_axis_data_tready),
            .s_axis_data_tdata(s_axis_data_tdata),
            .s_axis_data_tstrb(s_axis_data_tstrb),
            .s_axis_data_tlast(s_axis_data_tlast),
            .s_axis_data_tvalid(s_axis_data_tvalid),
            .m_axis_data_tvalid(s_axis_fifo_tvalid),
            .m_axis_data_tdata(s_axis_fifo_tdata),
            .m_axis_data_tlast(s_axis_fifo_tlast),
            .m_axis_data_tready(s_axis_fifo_tready),
            .structs_ready(structs_ready),
            .fifo_almost_full(fifo_almost_full),
            .bram_syncw_bus(bram_syncw_bus.master),
		    .bram_temp_bus(bram_temp_bus.master)
       );
       
     xpm_fifo_axis #(
     .CDC_SYNC_STAGES(2), // DECIMAL
     .CLOCKING_MODE("common_clock"), // String
     .ECC_MODE("no_ecc"), // String
     .FIFO_DEPTH(256), // DECIMAL
     .FIFO_MEMORY_TYPE("auto"), // String
     .PACKET_FIFO("false"), // String
     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
     .RELATED_CLOCKS(0), // DECIMAL
     .SIM_ASSERT_CHK(0), // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
     .TDATA_WIDTH(128), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    xpm_fifo_axis_inst (
     .m_axis_tdata(m_axis_data_tdata),
     .m_axis_tvalid(m_axis_data_tvalid),
     .m_axis_tlast(m_axis_data_tlast),
     .s_axis_tready(s_axis_fifo_tready),
     .m_aclk(axis_aclk),
     .m_axis_tready(m_axis_data_tready),
     .s_aclk(axis_aclk),
     .s_aresetn(axis_aresetn),
     .s_axis_tdata(s_axis_fifo_tdata),
     .s_axis_tvalid(s_axis_fifo_tvalid),
     .s_axis_tlast(s_axis_fifo_tlast),
     .prog_full_axis(fifo_almost_full)
    );

        
	endmodule
