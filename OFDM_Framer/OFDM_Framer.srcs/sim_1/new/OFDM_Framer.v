
`timescale 1 ns / 1 ps

/**
This core wraps layer-2 data into OFDM suitable Frames of 1024 bits/subcarriers (in the BPSK case).
The config AXIS channel is used to provide the synchronization word at the beginning of execution.
Until the sync word has been provided, the slave data channel will not assert tready.
As soon as it is provided, the core can accept layer-2 data. The core will add null subcarriers, as
well as pilots before passing the data to the modulator. The outgoing frame has the following form:

N N N N ... N P D D D D P D D D D ... P D D D D N N P D D D D ... P D D D D N N N ... N
|____ ______| | |_____|                         |_|                         |__________| 
     |      Pilot  |                          2 Null                              |
  111 Null        Data                        Subcarriers                       111 Null   
Subcarriers   |_______________________________|     |_____________________|     Subcarriers
                           |                                    |
                 400 Data/Pilot Subcarriers          400 Data/Pilot Subcarriers
                 
                 
The core will always output the sync word symbol first, and then 9 symbols with the above structure,
before sending again the sync word and repeating the structure.

**/

	module OFDM_Framer #
	(
		parameter integer C_S_AXIS_DATA_TDATA_WIDTH	= 32,
		parameter integer C_M_AXIS_DATA_TDATA_WIDTH	= 1024
	)
	(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output wire  s_axis_data_tready,
		input wire [C_S_AXIS_DATA_TDATA_WIDTH-1 : 0] s_axis_data_tdata,
		input wire [(C_S_AXIS_DATA_TDATA_WIDTH/8)-1 : 0] s_axis_data_tstrb,
		input wire  s_axis_data_tlast,
		input wire  s_axis_data_tvalid,
		output wire  m_axis_data_tvalid,
		output wire [C_M_AXIS_DATA_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output wire [C_M_AXIS_DATA_TDATA_WIDTH-1 : 0] m_axis_data_tstrb,
		output wire  m_axis_data_tlast,
		input wire  m_axis_data_tready,
		output wire  s_axis_config_tready,
		input wire [32-1 : 0] s_axis_config_tdata,
		input wire [(32/8)-1 : 0] s_axis_config_tstrb,
		input wire  s_axis_config_tlast,
		input wire  s_axis_config_tvalid
	);
	
	wire [799 : 0] sync_word;

	sync_word_module #(
       .USED_CARRIERS(800),
       .S_AXIS_TDATA_WIDTH(32)
       ) sync_word_mod_inst (
        .s_axis_config_aclk(axis_aclk),
		.s_axis_config_aresetn(axis_aresetn),
		.s_axis_config_tready(s_axis_config_tready),
		.s_axis_config_tdata(s_axis_config_tdata),
		.s_axis_config_tstrb(s_axis_config_tstrb),
		.s_axis_config_tlast(s_axis_config_tlast),
		.s_axis_config_tvalid(s_axis_config_tvalid),
		.sync_word(sync_word)
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
            .sync_word(sync_word),
            .sync_word_ready(!s_axis_config_tready),
            .m_axis_data_tvalid(m_axis_data_tvalid),
            .m_axis_data_tdata(m_axis_data_tdata),
            .m_axis_data_tstrb(m_axis_data_tstrb),
            .m_axis_data_tlast(m_axis_data_tlast),
            .m_axis_data_tready(m_axis_data_tready)
       );

        
	endmodule
