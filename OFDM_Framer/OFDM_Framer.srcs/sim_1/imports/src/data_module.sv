`timescale 1ns / 1ps

module data_module #
        (
        parameter integer M_AXIS_TDATA_WIDTH = 128,
        parameter integer S_AXIS_TDATA_WIDTH = 32,
        parameter integer MODULATION = 0
        )
        (
    	input wire  s_axis_data_aclk,
		input wire  s_axis_data_aresetn,
		output wire  s_axis_data_tready,
		input wire [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_data_tdata,
		input wire [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_data_tstrb,
		input wire  s_axis_data_tlast,
		input wire  s_axis_data_tvalid,
        input wire [31 : 0] sync_word [0 : 1023],
        input wire [31 : 0] template [0 : 1023],
        input wire [1023 : 0] map,
        input wire sync_word_ready,
		output reg  m_axis_data_tvalid = 0,
		output reg [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output reg [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tstrb,
		output wire  m_axis_data_tlast,
		input wire  m_axis_data_tready,
		input wire fifo_almost_full,
		output wire bram_en,
		input wire [127 : 0] sync_temp_dout,
		input wire [3 : 0] map_dout,
		output reg [8 : 0] bram_addr
    );
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
    typedef enum {BPSK, QPSK, QAM16, QAM64, QAM256} mod_t;
    typedef enum {IDLE, SYNC_WORD, DATA, FIFO_AFULL} state_t;
    state_t state = IDLE;
    state_t last_state = IDLE;
    mod_t modulation = BPSK;
    reg [127 : 0] shift_reg = 0;
    reg [7 : 0] bits_available = 0;
    wire [7 : 0] bits_consumed;
    reg [4 : 0] bits_per_mod [0 : 4];
    reg [10 : 0] subcarrier_cnt = 0;
    reg [9 : 0] symbol_cnt = 0;
    reg [3 : 0] ones_lut[0 : 15];
    wire [3 : 0] current_map_slice;
    reg [2 : 0] i;
    reg [31 : 0] mods[0 : 4][0 : 15];
    wire [4 : 0] current_bits_per_mod;
    wire [2 : 0] ones_past[0 : 3];
    reg [1 : 0] valid_shift_reg = 0;

    assign bits_consumed = (state == DATA) ? (ones_lut[current_map_slice] * current_bits_per_mod) : 32'h00000000;
    assign bram_en = (s_axis_data_tvalid || (bram_addr != 0 && (bram_addr != 256))) && (state != FIFO_AFULL) && sync_word_ready;
    assign current_map_slice = map_dout;
    assign s_axis_data_tready = (bits_available - bits_consumed < 64) && sync_word_ready
            && (state != FIFO_AFULL);
    assign current_bits_per_mod = bits_per_mod[modulation];
    assign ones_past[0] = 0;
    assign ones_past[1] = ones_lut[current_map_slice[0 : 0]];
    assign ones_past[2] = ones_lut[current_map_slice[1 : 0]];
    assign ones_past[3] = ones_lut[current_map_slice[2 : 0]];
    
    // Keep a shift register of two positions for the bram enabe signal,
    // since there's a 2 cycle latency when requesting data
    always@(posedge s_axis_data_aclk) begin
        valid_shift_reg <= {bram_en, valid_shift_reg[1]};
    end
    
    /* Create arrays with constellation points for each modulation */
    always@(posedge s_axis_data_aclk) begin
        if(~s_axis_data_aresetn) begin
            bits_per_mod = '{1,2,4,6,8};
            mods = '{'{32'h00008000, 32'h00007fff, 32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00
                        ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00},
                        '{32'h80008000, 32'h80007fff,
                         32'h7fff8000, 32'h7fff7fff,32'h00, 32'h00,32'h00, 32'h00
                         ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00},
                         '{32'h7fff8000, 32'h7fffc000, 32'h7fff7fff, 32'h7fff3fff,
                            32'h3fff8000, 32'h3fffc000, 32'h3fff7fff, 32'h3fff3fff,
                            32'h80008000, 32'h8000c000, 32'h80007fff, 32'h80003fff,
                            32'hc0008000, 32'hc000c000, 32'hc0007fff, 32'hc0003fff},
                         '{32'h00,32'h00,32'h00008000, 32'h00007fff,32'h00, 32'h00,32'h00, 32'h00
                         ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00},
                         '{32'h00,32'h00,32'h00008000, 32'h00007fff,32'h00, 32'h00,32'h00, 32'h00
                         ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00}};
            ones_lut = '{0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4};
        end
    end
    
    always@(posedge s_axis_data_aclk) begin
        if(~s_axis_data_aresetn) begin
            state <= IDLE;
            subcarrier_cnt <= 0;
            bram_addr <= 0;
            symbol_cnt <= 0;
            `ifdef	CVG
            cg_inst = new();
            `endif
        end
        else begin
            case(state)
                IDLE: begin
                `ifdef	CVG
                    $display("Coverage = %0.2f %%", cg_inst.get_inst_coverage());
                 `endif
                    if(s_axis_data_tvalid && sync_word_ready) begin
                        state <= SYNC_WORD;
                        bram_addr <= bram_addr + 1;
                    end
                end
                SYNC_WORD: begin
                        bram_addr <= bram_addr + 1;
                        if(bram_addr == 255) begin
                            state <= DATA;
                            symbol_cnt <= symbol_cnt + 1;
                            if(fifo_almost_full) begin
                                state <= FIFO_AFULL;
                                last_state <= DATA;
                             end
                        end
                end
                DATA: begin
                        if(bram_addr == 511) begin
                            if(fifo_almost_full) begin
                                state <= FIFO_AFULL;
                                if(symbol_cnt == 9 && s_axis_data_tvalid) begin
                                    last_state <= SYNC_WORD;
                                    symbol_cnt <= 0;
                                    bram_addr <= 0;
                                end
                                else if((symbol_cnt == 9) && (!s_axis_data_tvalid)) begin
                                    last_state <= IDLE;
                                    symbol_cnt <= 0;
                                    bram_addr <= 0;
                                end
                                else begin
                                    last_state <= DATA;
                                    symbol_cnt <= symbol_cnt + 1;
                                    bram_addr <= 256;
                                end
                            end
                            else begin
                                if(symbol_cnt == 9) begin
                                    if(s_axis_data_tvalid)begin
                                        symbol_cnt <= 0;
                                        state <= SYNC_WORD;
                                        bram_addr <= 0;
                                    end
                                    else begin
                                        symbol_cnt <= 0;
                                        state <= IDLE;
                                        bram_addr <= 0;
                                    end
                                end
                                else begin
                                    symbol_cnt <= symbol_cnt + 1;
                                    bram_addr <= 256;
                                end
                            end
                        end
                        else
                            bram_addr <= bram_addr + 1;
                    end
                FIFO_AFULL: begin
                    if(~fifo_almost_full) begin
                        state <= last_state;
                        if(s_axis_data_tvalid) begin
                        end
                    end
                end
            endcase
        end
    end
    
    always @(posedge s_axis_data_aclk) begin
        if(sync_word_ready && m_axis_data_tready && ~(state == FIFO_AFULL)) begin
            if(((bits_available - bits_consumed) < 64) && s_axis_data_tvalid) begin
                bits_available <= bits_available - bits_consumed + 32 ; 
                shift_reg <= (shift_reg >> bits_consumed) | s_axis_data_tdata << (bits_available - bits_consumed);
            end
            else begin
                bits_available <= bits_available - bits_consumed;
                shift_reg <= shift_reg >> bits_consumed;
            end
        end
    end
    
    always @(posedge s_axis_data_aclk) begin 
        if(m_axis_data_tready && (state == SYNC_WORD) && valid_shift_reg[0]) begin
            m_axis_data_tdata <= sync_temp_dout;
            m_axis_data_tvalid <= 1;
        end
        else begin
            if(m_axis_data_tready && valid_shift_reg[0]) begin
                m_axis_data_tvalid <= 1;
                for(i = 0; i < 4 ; i = i + 1) begin
                    if(current_map_slice[i]) begin
                        case(modulation)
                                BPSK: m_axis_data_tdata[i*32 +: 32] <= mods[BPSK][shift_reg[ones_past[i]]];
                                QPSK: m_axis_data_tdata[i*32 +: 32] <= mods[QPSK][shift_reg[ones_past[i] * 2 +: 2]];
                                QAM16: m_axis_data_tdata[i*32 +: 32] <= mods[QAM16][shift_reg[ones_past[i] * 4 +: 4]];
                                QAM64: m_axis_data_tdata[i*32 +: 32] <= mods[QAM64][shift_reg[ones_past[i] * 6 +: 6]];
                                QAM256: m_axis_data_tdata[i*32 +: 32] <= mods[QAM256][shift_reg[ones_past[i] * 8 +: 8]];
                         endcase
                    end
                    else begin
                        m_axis_data_tdata[i*32 +: 32] <= sync_temp_dout[i*32 +: 32];
                    end 
                end
            end
            else
                m_axis_data_tvalid <= 0;
        end
    end
    
    /* CODE ASSERTIONS */
    
    // There should always be at least as many bits available as we need to output
    // THis practically means that the input to this block must be enough to populate
    // a full Frame
    always@(posedge s_axis_data_aclk) begin
        assume(bits_available >= bits_consumed);
    end
    
    assume property (@(posedge s_axis_data_aclk)
	   ((state != IDLE) && (state != FIFO_AFULL) && (symbol_cnt < 9)) |=> (bits_available > 0));
	   
	// Assert ranges
	always@(posedge s_axis_data_aclk) begin
        assert(symbol_cnt <= 9);
        assert(subcarrier_cnt <= 1020);
        assert((state == IDLE) || (state == SYNC_WORD) || (state == DATA) || (state == FIFO_AFULL));
        assert(bits_available <= 128);
        assert((modulation == BPSK) || (modulation == QPSK) 
            || (modulation == QAM16) || (modulation == QAM64) || (modulation == QAM256));
    end
    
    // Do not request next symbol if FIFO doesnt have enough space available
    assert property (@(posedge s_axis_data_aclk)
	   (state == FIFO_AFULL) |-> !s_axis_data_tready);
	assert property (@(posedge s_axis_data_aclk)
	   (state == FIFO_AFULL) |-> (bits_consumed == 0));
	 
	// Only go int FIFO_AFULL state at the end of the symbol 
	assert property (@(posedge s_axis_data_aclk)
	   (state == FIFO_AFULL) |-> (subcarrier_cnt == 0));
    
    // Subcariier count should increase by 4 or be 0	   
	assert property (@(posedge s_axis_data_aclk)
	   ($past(subcarrier_cnt) == (subcarrier_cnt - 4)) || (subcarrier_cnt == 0));

	// If output FIFO is almost full, don't output more than 256 samples before going
	// into FIFO_AFULL state
	assert property (@(posedge s_axis_data_aclk)
	   fifo_almost_full && (state!=IDLE) |-> ##[1:256] (state == FIFO_AFULL));  
	   
	// Assert IDLE state transition
    assert property (@(posedge s_axis_data_aclk)
	   ($past(state) == IDLE) |=> (state == IDLE) || (state == SYNC_WORD));
	 	
	// Assert SYNC_WORD state transition
    assert property (@(posedge s_axis_data_aclk)
	   (state == SYNC_WORD) && (subcarrier_cnt == 1020) && (!fifo_almost_full)|=> (state == DATA)); 
	   
    assert property (@(posedge s_axis_data_aclk)
	   (state == SYNC_WORD) && (subcarrier_cnt == 1020) && (fifo_almost_full)|=> (state == FIFO_AFULL));  
    
    // Assert DATA state transition
    assert property (@(posedge s_axis_data_aclk)
	   (state == DATA) && (subcarrier_cnt == 1020) && (symbol_cnt == 9) && (!fifo_almost_full) |=> 
	               ((state == SYNC_WORD) && (bits_available > 0)) ||
	                  (state == IDLE) && (bits_available == 0));    
	assert property (@(posedge s_axis_data_aclk)
	   (state == DATA) && (subcarrier_cnt == 1020) && (symbol_cnt == 9) && (fifo_almost_full) |=> 
	               (state == FIFO_AFULL)); 
	               
	// Assert FIFO_AFULL state transition
	assert property (@(posedge s_axis_data_aclk)
	   (state == FIFO_AFULL) && (fifo_almost_full) |=> 
	               (state == FIFO_AFULL));
	assert property (@(posedge s_axis_data_aclk)
	   (state == FIFO_AFULL) && (!fifo_almost_full) |=> 
	               (state != FIFO_AFULL)); 
	// s_tready is asserted only when the available bits in the shift register are below a threshold 
	assert property (@(posedge s_axis_data_aclk)
	   ((bits_available - bits_consumed) < 64) && sync_word_ready && (state != FIFO_AFULL) |-> s_axis_data_tready); 
	   
	// Make sure m_tvalid is always asserted for at least 256 cycles               
    reg [7 : 0] count_m_valid = 0;
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
	   (!bram_en) |=> $stable(bram_addr));
	
	// The data output from the BRAMs should not change
	// if tvalid is not asserted.
	assert property (@(posedge s_axis_data_aclk)
	   (!m_axis_data_tvalid) |=>  $stable(sync_temp_dout) && $stable(map_dout));
	
endmodule
