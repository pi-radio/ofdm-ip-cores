`timescale 1ns / 1ps

// Piradio OFDM synchronizer
// 
// The Piradio OFDM synchronizer takes as input the result of two correlations
// One is the output of the correlation of the time domain received samples with
// the known sync word, and the other is the correlation of the time domain samples
// delayed by half a symbol, with the known sync word. This helps to detect symbol
// boundaries when timing is not optimal. The third input to the core is the time
// domain samples themselves. 
//

module synchronizer #
        ( parameter CORR_DATA_WIDTH = 256,
          parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		  parameter integer C_S00_AXI_ADDR_WIDTH	= 4,
          parameter DATA_WIDTH = 128,
          parameter integer cp_rm_enable = 0,
          parameter integer NUM_DATA_SYMBOLS = 9
        )
        (
        input logic clk,
        input logic resetn,
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
        output logic [DATA_WIDTH - 1 : 0] m_axis_tdata,
        output logic m_axis_tvalid,
        input logic m_axis_tready,
        output logic m_axis_tlast,
        
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
    
    /* Interface declarations */
    logic [31 : 0] threshold;
    
    axis_iface #(.DATA_WIDTH(CORR_DATA_WIDTH)) corr_1_iface_out();
    axis_iface #(.DATA_WIDTH(CORR_DATA_WIDTH)) corr_2_iface_out();
    axis_iface #(.DATA_WIDTH(DATA_WIDTH)) data_iface_out();
    
    axil_slave_sync axil_slave_sync_inst(
        .clk(clk),
        .aresetn(resetn),
        .threshold(threshold),
		.s_axi_awaddr(s_axi_awaddr),
		.s_axi_awprot(s_axi_awprot),
		.s_axi_awvalid(s_axi_awvalid),
		.s_axi_awready(s_axi_awready),
		.s_axi_wdata(s_axi_wdata),
		.s_axi_wstrb(s_axi_wstrb),
		.s_axi_wvalid(s_axi_wvalid),
		.s_axi_wready(s_axi_wready),
		.s_axi_bresp(s_axi_bresp),
		.s_axi_bvalid(s_axi_bvalid),
		.s_axi_bready(s_axi_bready),
		.s_axi_araddr(s_axi_araddr),
		.s_axi_arprot(s_axi_arprot),
		.s_axi_arvalid(s_axi_arvalid),
		.s_axi_arready(s_axi_arready),
		.s_axi_rdata(s_axi_rdata),
		.s_axi_rresp(s_axi_rresp),
		.s_axi_rvalid(s_axi_rvalid),
		.s_axi_rready(s_axi_rready)
    );
    

    frame_det2corr_arbiter_iface frame_det2corr_arbiter1();
    frame_det2corr_arbiter_iface frame_det2corr_arbiter2();
    corr_arbiter2sample_buff_iface corr_arbiter2sample_buff();
    sample_buff2cp_rm_iface#(.NUM_DATA_SYMBOLS(NUM_DATA_SYMBOLS)) sample_buff2cp_rm();
    cp_rm2out_iface cp_rm2out();
                                          
//    always_comb corr_1_iface_out.tready <= 1;
//    always_comb corr_2_iface_out.tready <= 1;
    
    always_comb m_axis_tdata <= cp_rm2out.samples_out;
    always_comb m_axis_tvalid <= cp_rm2out.samples_valid;
    always_comb m_axis_tlast <= cp_rm2out.samples_last;
    
    assign log = {{32{1'b0}}, correlator_arbiter_inst.counter};
    
    stream_sync  #(.CORR_DATA_WIDTH(CORR_DATA_WIDTH))
        stream_sync_inst
       (
        .clk(clk),
        .resetn(resetn),
        .s_axis_corr_1_tdata(s_axis_corr_1_tdata),
        .s_axis_corr_1_tvalid(s_axis_corr_1_tvalid),
        .s_axis_corr_1_tready(s_axis_corr_1_tready),
        .s_axis_corr_1_tlast(s_axis_corr_1_tlast),
        .s_axis_corr_2_tdata(s_axis_corr_2_tdata),
        .s_axis_corr_2_tvalid(s_axis_corr_2_tvalid),
        .s_axis_corr_2_tready(s_axis_corr_2_tready),
        .s_axis_corr_2_tlast(s_axis_corr_2_tlast),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .m_axis_corr_1(corr_1_iface_out),
        .m_axis_corr_2(corr_2_iface_out),
        .m_axis_data(data_iface_out)
    );
    
    /* 1st correlator related cores */
    
    peak_detector peak_detector_inst1(
        .clk(clk),
        .resetn(resetn),
        .corr_iface_out(corr_1_iface_out),
        .threshold(threshold),
        .frame_det2corr_arbiter(frame_det2corr_arbiter1)
    ); 

     /* 2nd correlator related cores */
    
    peak_detector peak_detector_inst2(
        .clk(clk),
        .resetn(resetn),
        .corr_iface_out(corr_2_iface_out),
        .threshold(threshold),
        .frame_det2corr_arbiter(frame_det2corr_arbiter2)
    );
    /* --------------------------------------------------- */
    correlator_arbiter correlator_arbiter_inst(
        .clk(clk),
        .resetn(resetn),
        .frame_det2corr_arbiter1(frame_det2corr_arbiter1),
        .frame_det2corr_arbiter2(frame_det2corr_arbiter2),
        .corr_arbiter2sample_buff(corr_arbiter2sample_buff)
    );
    
    bram_ctrl bram_ctrl_inst(
        .clk(clk),
        .resetn(resetn),
        .corr_arbiter2sample_buff(corr_arbiter2sample_buff),
        .input_fifo2buff(data_iface_out),
        .sample_buff2cp_rm(sample_buff2cp_rm)
    );
    
    cp_remover cp_remover_inst(
        .clk(clk),
        .resetn(resetn),
        .enable(cp_rm_enable),
        .sample_buff2cp_rm(sample_buff2cp_rm),
        .cp_rm2out(cp_rm2out)
    );
    
endmodule

module cp_remover(
    input wire clk,
    input wire resetn,
    input logic enable,
    sample_buff2cp_rm_iface.slave sample_buff2cp_rm,
    cp_rm2out_iface.master cp_rm2out
    );
    
    logic [$clog2(sample_buff2cp_rm.TOTAL_SYMBOL_LEN) - 1 : 0] sample_cnt = 0;
    
    always_comb cp_rm2out.samples_out <= sample_buff2cp_rm.samples_out;
    always_comb cp_rm2out.samples_last <= sample_buff2cp_rm.samples_last;
    always_comb cp_rm2out.samples_valid <= (enable) ? ((sample_cnt >= sample_buff2cp_rm.CP_LEN) && sample_buff2cp_rm.samples_valid)
                                               : sample_buff2cp_rm.samples_valid;
    
    always@(posedge clk) begin
        if(!resetn) sample_cnt <= 0;
        else begin
            if(sample_buff2cp_rm.samples_valid) begin
                if(sample_buff2cp_rm.samples_last)
                    sample_cnt <= 0;
                else
                    sample_cnt <= sample_cnt + 1;
            end
        end
    end
    
endmodule

/*
    correlator_arbiter
    
    The correlator arbiter takes the output of the two synchronizers for the two
    correlators and decides which one's computed start of frame will end up to the
    BRAM controller. The arbitration works in a first come-first serve manner. It also
    blocks any more input to the BRAM controller if it's already outputting a frame.
*/
module correlator_arbiter(
    input wire clk,
    input wire resetn,
    frame_det2corr_arbiter_iface.slave frame_det2corr_arbiter1,
    frame_det2corr_arbiter_iface.slave frame_det2corr_arbiter2,
    corr_arbiter2sample_buff_iface.master corr_arbiter2sample_buff
    );
    logic [31 : 0] counter = 0;
    always@(posedge clk)
         corr_arbiter2sample_buff.samples_valid <= frame_det2corr_arbiter1.samples_valid;
    always@(posedge clk) begin
        if(corr_arbiter2sample_buff.src_ready) begin
            if(frame_det2corr_arbiter1.start_idx_valid 
                && frame_det2corr_arbiter1.start_idx < 192
                && frame_det2corr_arbiter1.start_idx > 0) begin
                corr_arbiter2sample_buff.start_idx_valid <= frame_det2corr_arbiter1.start_idx_valid;
                corr_arbiter2sample_buff.start_idx <= frame_det2corr_arbiter1.start_idx;
                corr_arbiter2sample_buff.ssr_idx <= frame_det2corr_arbiter1.ssr_idx;
                corr_arbiter2sample_buff.correlator_idx <= 2'h1;
                counter <= counter + 1;
            end
            else if(frame_det2corr_arbiter2.start_idx_valid 
            && frame_det2corr_arbiter2.start_idx < 192
            && frame_det2corr_arbiter2.start_idx > 0) begin
                corr_arbiter2sample_buff.start_idx_valid <= frame_det2corr_arbiter2.start_idx_valid;
                corr_arbiter2sample_buff.start_idx <= frame_det2corr_arbiter2.start_idx;
                corr_arbiter2sample_buff.ssr_idx <= frame_det2corr_arbiter2.ssr_idx;
                corr_arbiter2sample_buff.correlator_idx <= 2'h2;
                counter <= counter + 1;
            end
        end
        else begin
            corr_arbiter2sample_buff.start_idx_valid <= 0;
        end
    end
    
    
endmodule

