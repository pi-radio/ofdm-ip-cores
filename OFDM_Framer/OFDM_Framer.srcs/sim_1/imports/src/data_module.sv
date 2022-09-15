`timescale 1ns / 1ps

module data_module #
        (
        parameter integer M_AXIS_TDATA_WIDTH = 128,
        parameter integer S_AXIS_TDATA_WIDTH = 32,
        parameter integer MODULATION = 0,
        parameter integer SAMPS_PER_FRAME = 180,
        parameter integer MAP_WIDTH = 4,
        parameter integer TEMPLATE_WIDTH = 128,
        parameter integer BRAM_ADDR_WIDTH = 9
        )
        (
    	input wire  s_axis_data_aclk,
		input wire  s_axis_data_aresetn,
		output wire  s_axis_data_tready,
		input wire [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_data_tdata,
		input wire [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_data_tstrb,
		input wire  s_axis_data_tlast,
		input wire  s_axis_data_tvalid,
        input wire sync_word_ready,
		output reg  m_axis_data_tvalid = 0,
		output reg [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output reg [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tstrb,
		output wire  m_axis_data_tlast,
		input wire  m_axis_data_tready,
		input wire fifo_almost_full,
		output wire bram_en,
		input wire [TEMPLATE_WIDTH - 1 : 0] sync_temp_dout,
		input wire [MAP_WIDTH - 1 : 0] map_dout,
		output reg [BRAM_ADDR_WIDTH - 1 : 0] bram_addr
    );
    typedef enum {BPSK, QPSK, QAM16, QAM64, QAM256} mod_t;
    typedef enum {IDLE, SYNC_WORD,MOD_SAMPLE_ON, DATA, FIFO_AFULL} state_t;
    state_t state = IDLE;
    state_t last_state = IDLE;
    mod_t modulation = BPSK;
    localparam sym_per_frame = 10;
    localparam bram_size = 512;
    localparam shift_reg_width = 128;
    
    reg [shift_reg_width - 1 : 0] shift_reg = 0;
    reg [7 : 0] bits_available = 0;
    wire [7 : 0] bits_consumed;
    reg [4 : 0] bits_per_mod [0 : 4];
    reg [9 : 0] symbol_cnt = 0;
    reg [3 : 0] ones_lut[0 : 15];
    wire [3 : 0] current_map_slice;
    reg [2 : 0] i;
    reg [31 : 0] mods[0 : 4][0 : 15];
    wire [4 : 0] current_bits_per_mod;
    wire [2 : 0] ones_past[0 : 3];
    reg [1 : 0] valid_shift_reg = 0;
    reg [20 : 0] input_counter;
    wire [20 : 0] input_samps_per_frame;

    assign input_samps_per_frame = SAMPS_PER_FRAME * current_bits_per_mod;
    assign bits_consumed = (state == DATA) ? (ones_lut[current_map_slice] * current_bits_per_mod) : 32'h00000000;
    assign bram_en = (s_axis_data_tvalid || (bram_addr != 0 && (bram_addr != bram_size/2))) && (state != FIFO_AFULL) && sync_word_ready;
    assign current_map_slice = map_dout;
    assign s_axis_data_tready = (bits_available - bits_consumed < (shift_reg_width/2) ) && sync_word_ready
            && (state != FIFO_AFULL);
    assign current_bits_per_mod = bits_per_mod[modulation];
    
    // The ones_past bus contains information about how many 1's exist in current_map_slice[0 : N - 1]
    // for the index N of current_map_slice. For example, if the current_map_slice is 0101, the ones_past
    // of the LSB is 0 as no other bits are in lower position than it. ones_past for bit index 1 is 1,
    // as the LSB (index 0) is 1, ones_past[2] is also 1 (bit 0 is 1 and bit 1 is 0, so 1 ace), and 
    // ones_past[3] is 2 as there are 2 1's in the bits that precede it. We need this bus to calculate
    // the correct position to put the modulated sample on the output bus in the for loop below.
    
    assign ones_past[0] = 0;
    assign ones_past[1] = ones_lut[current_map_slice[0 : 0]];
    assign ones_past[2] = ones_lut[current_map_slice[1 : 0]];
    assign ones_past[3] = ones_lut[current_map_slice[2 : 0]];
    
    //Count the input samples so that we know when the modulation
    //sample is present in the stream
    always@(posedge s_axis_data_aclk) begin
        if(~s_axis_data_aresetn) 
            input_counter <= 0;
        else begin
            if(s_axis_data_tvalid && s_axis_data_tready && sync_word_ready) begin
                if(input_counter == 0)
                    modulation <= mod_t'(s_axis_data_tdata);
                input_counter <= input_counter + 1;
                if(input_counter == input_samps_per_frame)
                    input_counter <= 0;
            end
        end
    end
    
    // Keep a shift register of two positions for the bram enabe signal,
    // since there's a 2 cycle latency when requesting data
    always@(posedge s_axis_data_aclk) begin
        valid_shift_reg <= {bram_en, valid_shift_reg[1]};
    end
    
    // Create arrays with constellation points for each modulation */
    // The system generated FFT cores require the 2 MSBs of the real and
    // imaginary parts of the input to be indentical in order to avoid internal
    // overflows 
    always@(posedge s_axis_data_aclk) begin
        if(~s_axis_data_aresetn) begin
            bits_per_mod = '{1,2,4,6,8};
            mods = '{'{32'h0000c000, 32'h00003fff, 32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00
                        ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00},
                        '{32'hc000c000, 32'hc0003fff,
                         32'h3fffc000, 32'h3fff3fff,32'h00, 32'h00,32'h00, 32'h00
                         ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00},
                         '{32'h3fffc000, 32'h3fffeaaa, 32'h3fff3fff, 32'h3fff1555,
                            32'h1555c000, 32'h1555eaaa, 32'h15553fff, 32'h15551555,
                            32'hc000c000, 32'hc000eaaa, 32'hc0003fff, 32'hc0001555,
                            32'heaaac000, 32'heaaaeaaa, 32'heaaa3fff, 32'heaaa1555},
                         '{32'h00,32'h00,32'h00008000, 32'h00003fff,32'h00, 32'h00,32'h00, 32'h00
                         ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00},
                         '{32'h00,32'h00,32'h00008000, 32'h00007fff,32'h00, 32'h00,32'h00, 32'h00
                         ,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00,32'h00, 32'h00}};
            ones_lut = '{0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4};
        end
    end
    
    always@(posedge s_axis_data_aclk) begin
        if(~s_axis_data_aresetn) begin
            state <= IDLE;
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
                        if(bram_addr == (bram_size/2 - 1)) begin
                            state <= DATA;
                            symbol_cnt <= symbol_cnt + 1;
                            if(fifo_almost_full) begin
                                state <= FIFO_AFULL;
                                last_state <= DATA;
                             end
                        end
                end
                DATA: begin
                        if(bram_addr == (bram_size - 1)) begin
                            if(fifo_almost_full) begin
                                state <= FIFO_AFULL;
                                if(symbol_cnt == (sym_per_frame - 1) && s_axis_data_tvalid) begin
                                    last_state <= SYNC_WORD;
                                    symbol_cnt <= 0;
                                    bram_addr <= 0;
                                end
                                else if((symbol_cnt == (sym_per_frame - 1)) && (!s_axis_data_tvalid)) begin
                                    last_state <= IDLE;
                                    symbol_cnt <= 0;
                                    bram_addr <= 0;
                                end
                                else begin
                                    last_state <= DATA;
                                    symbol_cnt <= symbol_cnt + 1;
                                    bram_addr <= bram_size/2;
                                end
                            end
                            else begin
                                if(symbol_cnt == (sym_per_frame - 1)) begin
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
                                    bram_addr <= bram_size/2;
                                end
                            end
                        end
                        else
                            bram_addr <= bram_addr + 1;
                    end
                FIFO_AFULL: begin
                    if(~fifo_almost_full) begin
                        state <= last_state;
                    end
                end
            endcase
        end
    end
    
    // Calculate how many bits we have available in the shift register and fill it in
    always @(posedge s_axis_data_aclk) begin
        if(sync_word_ready && m_axis_data_tready && ~(state == FIFO_AFULL)) begin
            if(((bits_available - bits_consumed) < shift_reg_width/2 ) && s_axis_data_tvalid && (input_counter != 0)) begin
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
	   ((state != IDLE) && (state != FIFO_AFULL) && (symbol_cnt < (sym_per_frame - 1))) |=> (bits_available > 0));
	   
	// Assert ranges
	always@(posedge s_axis_data_aclk) begin
        assert(symbol_cnt <= (sym_per_frame - 1));
        assert(bram_addr < bram_size);
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
	   (state == FIFO_AFULL) |-> (bram_addr == 0) || (bram_addr == 256));
    
    // Subcariier count should increase by 4 or be 0	   
	assert property (@(posedge s_axis_data_aclk)
	   ($past(bram_addr) == (bram_addr - 1)) || ($past(bram_addr) == 511) || $stable(bram_addr));

	// If output FIFO is almost full, don't output more than 256 samples before going
	// into FIFO_AFULL state
	assert property (@(posedge s_axis_data_aclk)
	   fifo_almost_full && (state!=IDLE) |-> ##[1:256] (state == FIFO_AFULL));  
	   
	// Assert IDLE state transition
    assert property (@(posedge s_axis_data_aclk)
	   ($past(state) == IDLE) |=> (state == IDLE) || (state == SYNC_WORD));
	 	
	// Assert SYNC_WORD state transition
    assert property (@(posedge s_axis_data_aclk)
	   (state == SYNC_WORD) && (bram_addr == 255) && (!fifo_almost_full) |=> (state == DATA)); 
	   
    assert property (@(posedge s_axis_data_aclk)
	   (state == SYNC_WORD) && ((bram_addr == 255) || (bram_addr == 511)) && (fifo_almost_full) |=> (state == FIFO_AFULL));  
    
    // Assert DATA state transition
    assert property (@(posedge s_axis_data_aclk)
	   (state == DATA) && (bram_addr == 511) && (symbol_cnt == (sym_per_frame - 1)) && (!fifo_almost_full) |=> 
	               ((state == SYNC_WORD) && (bits_available > 0)) ||
	                  (state == IDLE) && (bits_available == 0));    
	assert property (@(posedge s_axis_data_aclk)
	   (state == DATA) && (bram_addr == 511) && (symbol_cnt == (sym_per_frame - 1)) && (fifo_almost_full) |=> 
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
	   ((bits_available - bits_consumed) < shift_reg_width/2 ) && sync_word_ready && (state != FIFO_AFULL) |-> s_axis_data_tready); 
	   
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
endmodule
