`timescale 1ns / 1ps

/*
    stream_sync
    
     This module holds FIFO's for all three inputs to the synchronizer.
     Since the two correlation results might appear  at different times
     at the inputs of the core, and since we need the to be synchronized
     as they traverse the inner chains of the synchronizer, this module
     also arbitrates the FIFO's output so that when the first synchronizer
     processes the samples of the first correlation, the second one also
     processes the samples of the second correlation in parallel.
*/
module stream_sync #(
        parameter CORR_DATA_WIDTH = 32,
        parameter DATA_WIDTH = 128
        )(
        input wire clk,
        input wire resetn,
        input logic [CORR_DATA_WIDTH - 1 : 0] s_axis_corr_1_tdata,
        input logic s_axis_corr_1_tvalid,
        output logic s_axis_corr_1_tready,
        input logic s_axis_corr_1_tlast,
        input logic [CORR_DATA_WIDTH  -1 : 0] s_axis_corr_2_tdata,
        input logic s_axis_corr_2_tvalid,
        output logic s_axis_corr_2_tready,
        input logic s_axis_corr_2_tlast,
        input logic [DATA_WIDTH - 1 : 0] s_axis_tdata,
        input logic s_axis_tvalid,
        output logic s_axis_tready,
        input logic s_axis_tlast,
        axis_iface.master m_axis_corr_1,
        axis_iface.master m_axis_corr_2,
        axis_iface.master m_axis_data
        
    );
    
    logic [2 : 0] fifos_out_valid;
    logic streams_fifo_ready;
    
    /* FIFO output becomes ready only when both correlation inputs have valid data available */
    
    always_comb streams_fifo_ready = fifos_out_valid[0] && fifos_out_valid[1];
                    
    always_comb m_axis_corr_1.tvalid <= streams_fifo_ready;
    always_comb m_axis_corr_2.tvalid <= streams_fifo_ready;
    

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
     .TDATA_WIDTH(CORR_DATA_WIDTH), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    xpm_fifo_corr_1_inst (
     .m_axis_tdata(m_axis_corr_1.tdata),
     .m_axis_tvalid(fifos_out_valid[0]),
     .m_axis_tlast(m_axis_corr_1.tlast),
     .s_axis_tready(s_axis_corr_1_tready),
     .m_aclk(clk),
     .m_axis_tready(streams_fifo_ready),
     .s_aclk(clk),
     .s_aresetn(resetn),
     .s_axis_tdata(s_axis_corr_1_tdata),
     .s_axis_tvalid(s_axis_corr_1_tvalid),
     .s_axis_tlast(s_axis_corr_1_tlast)
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
     .TDATA_WIDTH(CORR_DATA_WIDTH), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    xpm_fifo_corr_2_inst (
     .m_axis_tdata(m_axis_corr_2.tdata),
     .m_axis_tvalid(fifos_out_valid[1]),
     .m_axis_tlast(m_axis_corr_2.tlast),
     .s_axis_tready(s_axis_corr_2_tready),
     .m_aclk(clk),
     .m_axis_tready(streams_fifo_ready),
     .s_aclk(clk),
     .s_aresetn(resetn),
     .s_axis_tdata(s_axis_corr_2_tdata),
     .s_axis_tvalid(s_axis_corr_2_tvalid),
     .s_axis_tlast(s_axis_corr_2_tlast)
    );  

     xpm_fifo_axis #(
     .CDC_SYNC_STAGES(2), // DECIMAL
     .CLOCKING_MODE("common_clock"), // String
     .ECC_MODE("no_ecc"), // String
     .FIFO_DEPTH(4096), // DECIMAL
     .FIFO_MEMORY_TYPE("auto"), // String
     .PACKET_FIFO("false"), // String
     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
     .RELATED_CLOCKS(0), // DECIMAL
     .SIM_ASSERT_CHK(0), // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
     .TDATA_WIDTH(DATA_WIDTH), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    xpm_fifo_data_inst (
     .m_axis_tdata(m_axis_data.tdata),
     .m_axis_tvalid(m_axis_data.tvalid),
     .m_axis_tlast(m_axis_data.tlast),
     .s_axis_tready(s_axis_tready),
     .m_aclk(clk),
     .m_axis_tready(m_axis_data.tready),
     .s_aclk(clk),
     .s_aresetn(resetn),
     .s_axis_tdata(s_axis_tdata),
     .s_axis_tvalid(s_axis_tvalid),
     .s_axis_tlast(s_axis_tlast)
    );
    
    //If all of the conditions are 1 then streams_fifo_ready should also be 1
    assert property (@(posedge clk)
	   (!streams_fifo_ready) |-> (!fifos_out_valid[0] || !fifos_out_valid[1]));
	
    
endmodule
