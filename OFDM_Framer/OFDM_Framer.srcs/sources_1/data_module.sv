`timescale 1ns / 1ps


module data_module
        import piradio_ofdm::*;
        #(
        parameter integer M_AXIS_TDATA_WIDTH = 128,
        parameter integer S_AXIS_TDATA_WIDTH = 32,
        parameter integer TOTAL_CARRIERS = 1024,
        parameter integer SAMPS_PER_FRAME = 180,
        parameter integer MAP_WIDTH = 4,
        parameter integer TEMPLATE_WIDTH = 128,
        parameter integer BRAM_ADDR_WIDTH = 9,
        parameter integer BRAM_FIFO_LATENCY = 3
        )
        (
    	input logic  s_axis_data_aclk,
		input logic  s_axis_data_aresetn,
		output logic  s_axis_data_tready,
		input logic [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_data_tdata,
		input logic [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_data_tstrb,
		input logic  s_axis_data_tlast,
		input logic  s_axis_data_tvalid,
		output logic  s_axis_ctrl_tready,
		input logic [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_ctrl_tdata,
		input logic  s_axis_ctrl_tlast,
		input logic  s_axis_ctrl_tvalid,
		output logic  m_axis_data_tvalid,
		output logic [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output logic [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tstrb,
		output logic  m_axis_data_tlast,
		input logic  m_axis_data_tready,
		input logic fifo_almost_full,
		input logic structs_ready,
		bram_fifo_in_iface.master bram_syncw_bus,
		bram_fifo_in_iface.master bram_temp_bus
    );
    logic enable_syncw, enable_temp;
    logic [M_AXIS_TDATA_WIDTH-1:0] fifo_syncw_data;
    logic [M_AXIS_TDATA_WIDTH-1:0] fifo_temp_data;
    logic fifo_syncw_valid,fifo_temp_valid;
    logic fifo_syncw_last, fifo_temp_last;
    logic [9 : 0] symbol_cnt = 0;
    logic samples_out_rdy, samples_out_valid;
    logic [S_AXIS_TDATA_WIDTH - 1 : 0] samples_out[0 : MAP_WIDTH - 1];
    state_t state, last_state;
    localparam sym_per_frame = 10;
    logic [BRAM_FIFO_LATENCY - 1 : 0] fifo_afull_shift_logic = 0;
    
    // Create interfaces
    bram_fifo_out_iface #(.WIDTH(128)) bram_fifo_syncw_out();
    bram_fifo_out_iface #(.WIDTH(132)) bram_fifo_temp_out();
    frame_parser_in_iface#(.SAMPS_PER_FRAME(SAMPS_PER_FRAME)) frame_parser_bus();
    ctrl_in_iface ctrl_in();
    parser_to_mod_iface#(.SAMPS_PER_FRAME(SAMPS_PER_FRAME)) parser_to_mod_bus(s_axis_data_aclk, s_axis_data_aresetn);
    piradio_framer_data_modulator_out_iface#(.SRC_DATA_WIDTH(32)) fdm_bus();
    
    always_comb
        s_axis_data_tready = frame_parser_bus.src_rdy & structs_ready;
    
    piradio_bram_fifo syncw_bram_fifo
    (
        .clk(s_axis_data_aclk),
        .resetn(s_axis_data_aresetn),
        .bram_fifo_in(bram_syncw_bus),
        .bram_fifo_out(bram_fifo_syncw_out),
        .structs_ready(structs_ready)
    );
    
    piradio_bram_fifo temp_bram_fifo
    (
        .clk(s_axis_data_aclk),
        .resetn(s_axis_data_aresetn),
        .bram_fifo_in(bram_temp_bus),
        .bram_fifo_out(bram_fifo_temp_out),
        .structs_ready(structs_ready)
    );
    
    always_comb
        frame_parser_bus.src_valid = s_axis_data_tvalid;
    always_comb 
        frame_parser_bus.src_data = s_axis_data_tdata;
    always_comb
        frame_parser_bus.structs_rdy = structs_ready;
    always_comb 
        samples_out_rdy = m_axis_data_tready && structs_ready && !fifo_afull_shift_logic[0];
    
    always_comb 
        m_axis_data_tdata = {samples_out[3], samples_out[2], samples_out[1], samples_out[0]};
    always_comb 
        m_axis_data_tvalid = samples_out_valid;
    
    always_comb
        ctrl_in.ctrl_data = s_axis_ctrl_tdata;
    always_comb
        ctrl_in.ctrl_valid = s_axis_ctrl_tvalid;
    always_comb
        s_axis_ctrl_tready = ctrl_in.ctrl_ready;
        
    piradio_frame_parser frame_parser(
        .frame_parser_bus(frame_parser_bus),
        .ctrl_in(ctrl_in),
        .parser_to_mod_bus(parser_to_mod_bus.master)
    );
    
    piradio_framer_data_modulator 
        framer_data_modulator(
        .parser_to_mod_bus(parser_to_mod_bus.slave),
        .fdm_bus(fdm_bus.master)
    );
    
    piradio_sample_interleaver frame_interleaver(
        .clk(s_axis_data_aclk),
        .resetn(s_axis_data_aresetn),
        .bram_syncw_out(bram_fifo_syncw_out.slave),
        .bram_temp_out(bram_fifo_temp_out.slave),
        .fdm_out(fdm_bus.slave),
        .samples_out_valid(samples_out_valid),
        .samples_out_rdy(samples_out_rdy),
        .samples_out(samples_out)
    );
    

    `ifdef OLD_CODE

     /* CODE ASSERTIONS */
    
    // There should always be at least as many bits available as we need to output
    // THis practically means that the input to this block must be enough to populate
    // a full Frame

    assume property (@(posedge s_axis_data_aclk)
	   ((state != IDLE) && (state != FIFO_AFULL) && (symbol_cnt < (sym_per_frame - 1))) |->##[1:20](samples_out_valid));
	   
	// Assert ranges
	always@(posedge s_axis_data_aclk) begin
        assert(symbol_cnt <= (sym_per_frame - 1));
        assert((state == IDLE) || (state == SYNC_WORD) || (state == DATA) || (state == FIFO_AFULL));
        assert((parser_to_mod_bus.modulation == BPSK) || (parser_to_mod_bus.modulation == QPSK) 
            || (parser_to_mod_bus.modulation == QAM16) || (parser_to_mod_bus.modulation == QAM64) || (parser_to_mod_bus.modulation == QAM256));
    end
    
    // Do not request next symbol if FIFO doesnt have enough space available
	assert property (@(posedge s_axis_data_aclk)
	   (fifo_afull_shift_logic[0]) |=> (!samples_out_valid));
	 
//	// Only go int FIFO_AFULL state at the end of the symbol 
//	assert property (@(posedge s_axis_data_aclk)
//	   (fifo_afull_shift_logic[0]) |=> (enable_syncw && bram_syncw_bus.bram_addr == 0) || (enable_temp && bram_temp_bus.bram_addr == 0));
    
    // Addresses should increase by 1 or be 0	   
	assert property (@(posedge s_axis_data_aclk)
	   ($past(bram_syncw_bus.bram_addr) == (bram_syncw_bus.bram_addr - 1)) || $stable(bram_syncw_bus.bram_addr) || (bram_syncw_bus.bram_addr == 0));
    // Addresses should increase by 1 or be 0	   
	assert property (@(posedge s_axis_data_aclk)
	   ($past(bram_temp_bus.bram_addr) == (bram_temp_bus.bram_addr - 1)) || $stable(bram_temp_bus.bram_addr) || (bram_temp_bus.bram_addr == 0));
	// If output FIFO is almost full, don't output more than 256 samples before going
	// into FIFO_AFULL state
	assert property (@(posedge s_axis_data_aclk)
	   fifo_almost_full && (state!=IDLE) |-> ##[1:256] (state == FIFO_AFULL));  
	   
	// Assert IDLE state transition
    assert property (@(posedge s_axis_data_aclk)
	   ($past(state) == IDLE) |=> (state == IDLE) || (state == SYNC_WORD));
	 	
	// Assert SYNC_WORD state transition
    assert property (@(posedge s_axis_data_aclk)
	   (state == SYNC_WORD) && (bram_syncw_bus.bram_addr == 255) && (!fifo_almost_full) |=> (state == DATA)); 
	   
    assert property (@(posedge s_axis_data_aclk)
	   (state == SYNC_WORD) && ((bram_syncw_bus.bram_addr == 255)) && (fifo_almost_full) |=> (state == FIFO_AFULL));  
    
    // Assert DATA state transition
    assert property (@(posedge s_axis_data_aclk)
	   (state == DATA) && (bram_temp_bus.bram_addr == 255) && (symbol_cnt == (sym_per_frame - 1)) && (!fifo_almost_full) |=> 
	               ((state == SYNC_WORD)) || (state == IDLE));    
	assert property (@(posedge s_axis_data_aclk)
	   (state == DATA) && (bram_temp_bus.bram_addr == 255) && (symbol_cnt == (sym_per_frame - 1)) && (fifo_almost_full) |=> 
	               (state == FIFO_AFULL)); 
	               
	// Assert FIFO_AFULL state transition
	assert property (@(posedge s_axis_data_aclk)
	   (state == FIFO_AFULL) && (fifo_almost_full) |=> 
	               (state == FIFO_AFULL));
	assert property (@(posQuick Accessedge s_axis_data_aclk)
	   (state == FIFO_AFULL) && (!fifo_almost_full) |=> 
	               (state != FIFO_AFULL)); 
 
	   
	// Make sure m_tvalid is always asserted for at least 256 cycles               
    logic [7 : 0] count_m_valid = 0;
	always @(posedge s_axis_data_aclk) begin
        if(m_axis_data_tvalid && m_axis_data_tready)
            count_m_valid <= count_m_valid + 1;
    end
    assert property (@(posedge s_axis_data_aclk)
	   $fell(m_axis_data_tvalid) |=> 
	               (count_m_valid == 0)); 
	               
	// The address input to the BRAM should not change
	// without the enable signal asserted.
    assert property (@(posedge s_axis_data_aclk)
	   (!bram_syncw_bus.bram_rd_en) |=> $stable(bram_syncw_bus.bram_addr));
	assert property (@(posedge s_axis_data_aclk)
	   (!bram_temp_bus.bram_rd_en) |=> $stable(bram_temp_bus.bram_addr));
	// The data output from the BRAMs should not change
	// if tvalid is not asserted.
	assert property (@(posedge s_axis_data_aclk)
	   (!m_axis_data_tvalid) |->  $stable(samples_out));
	
   // `define	CVG
   `ifdef CVG
    covergroup cg @(posedge s_axis_data_aclk);
        coverpoint state{   bins b1 = (IDLE => SYNC_WORD);
                            bins b2 = (SYNC_WORD => DATA);
                            bins b3 = (DATA => SYNC_WORD);
                            bins b4 = (DATA => IDLE);
                            bins b5 = (DATA => FIFO_AFULL);
                            bins b6 = (SYNC_WORD => FIFO_AFULL);
                            illegal_bins ib1 = (SYNC_WORD => IDLE);
                            bins b7 = default;
                            }
    endgroup
    
    cg cg_inst;
    
    `endif
    
    `endif
endmodule
