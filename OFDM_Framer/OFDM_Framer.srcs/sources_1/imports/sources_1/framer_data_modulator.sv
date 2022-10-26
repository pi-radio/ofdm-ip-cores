`timescale 1ns / 1ps


/* Here I'm breaking out the shift register for clarity */
module piradio_data_shift_reg
    import piradio_ofdm::*;
    #(
        DATA_WIDTH = 32,
        COUNT_WDITH = 7,
        SYMBOL_WIDTH = 4
    )
    (
        input logic clk,
        input logic aresetn,
        
        input mod_t modulation_in,
        input logic [DATA_WIDTH-1:0] data_words,
        output logic data_words_ready,
        input logic data_words_valid,
        input logic data_words_last,

        output mod_t modulation_sr2e,
        output logic [DATA_WIDTH-1:0] data_bits,
        output logic data_bits_valid,
        input logic data_bits_rdy,
        output logic data_bits_last
    );
    
    localparam SHIFT_REG_WIDTH = 2 * DATA_WIDTH;
    logic [SHIFT_REG_WIDTH - 1:0] shift_reg;
    mod_t shift_reg_mod;
    modulation_t cur_mod;
    integer bits_available, ba2;
    integer last_count;
    integer modulation_bits;
    
    logic do_shift_in;
    logic do_shift_out;
    integer available_space;
    
    always_comb cur_mod = modulations[shift_reg_mod];    
    always_comb modulation_bits = SYMBOL_WIDTH * cur_mod.bits_per_symbol;   
   
    always_comb do_shift_out = aresetn && (shift_reg_mod != MOD_NONE) && (bits_available >= modulation_bits) && (~data_bits_valid | (data_bits_valid & data_bits_rdy));

    always_comb ba2 = bits_available - (do_shift_out ? modulation_bits : 0);

    always_comb available_space = SHIFT_REG_WIDTH - ba2;

    always_comb data_words_ready = aresetn && (available_space >= DATA_WIDTH) && (modulation_in == shift_reg_mod || bits_available == 0);

    always_comb do_shift_in = data_words_ready & data_words_valid;

    always @(posedge clk)
    begin
        if (~aresetn) begin
            data_bits <= 1'b0;
            data_bits_valid <= 1'b0;
            data_bits_last <= 1'b0;
        end else if (do_shift_out) begin
            data_bits <= shift_reg[DATA_WIDTH-1:0];
            data_bits_valid <= 1'b1;
            data_bits_last <= (last_count == modulation_bits);
            modulation_sr2e <= shift_reg_mod;
        end else if (data_bits_rdy) begin
            data_bits_valid <= 1'b0;
        end 
    end
    
    always @(posedge clk)
    begin
        if (~aresetn) begin
            shift_reg <= 0;
        end else begin
            shift_reg <= ((do_shift_out ? (shift_reg >> modulation_bits) : shift_reg) |
                          (do_shift_in ? (data_words << ba2) : 0));
        end
    end
    
    always @(posedge clk)
    begin
        if (~aresetn) begin
            last_count <= 0;
        end else if (last_count) begin
            last_count = do_shift_out ? last_count - modulation_bits : last_count;
        end else if (do_shift_in && data_words_last) begin
            last_count = ba2 + DATA_WIDTH;
        end           
    end

    always @(posedge clk) shift_reg_mod <= ~aresetn ? MOD_NONE : do_shift_in ? modulation_in : shift_reg_mod;

    always @(posedge clk) bits_available <= ~aresetn ? 0 : bits_available + (do_shift_in ? DATA_WIDTH : 0) - (do_shift_out ? modulation_bits : 0);
            
endmodule

/* BIG WARNING HERE -- this module assumes that the total number of symbols is divisible by 4 */
/* Like, turn me into an assert or something */
module piradio_symbol_extractor
    import piradio_ofdm::*;
    #(
        parameter integer DATA_WIDTH = 32,
        parameter integer COUNT_WIDTH = 7,
        parameter integer SYMBOL_WIDTH = 4
    )
    (
        input logic clk,
        input logic aresetn,
        
        input mod_t modulation_sr2e,
        input logic [DATA_WIDTH-1:0] data_bits,
        input logic data_bits_valid,
        output logic data_bits_rdy,
        input logic data_bits_last,        
        
        output mod_t modulation_se2gb,
        input logic mod_symbols_rdy,
        output ofdm_symbol_t mod_symbols[0:3],
        output logic mod_symbols_valid,
        output logic mod_symbols_last
    );
    genvar i;
    logic advance;
    
    modulation_t cur_mod;
    assign cur_mod = modulations[modulation_sr2e]; 
    
    always_comb
    begin
        if (~aresetn || modulation_sr2e == MOD_NONE) begin
            data_bits_rdy <= 0;
        end else if (mod_symbols_rdy) begin
            data_bits_rdy <= 1;
        end else begin
            data_bits_rdy <= 0;
        end
    end
    
    always_comb advance = data_bits_rdy & data_bits_valid;
    
    always @(posedge clk)
    begin
        if (~aresetn) begin
            modulation_se2gb <= MOD_NONE;
            mod_symbols_valid <= 0;
            mod_symbols_last <= 0;
        end else if (advance) begin
            mod_symbols_valid <= 1'b1;
            modulation_se2gb <= modulation_sr2e;
            mod_symbols_last <= data_bits_last;
        end else if (mod_symbols_rdy) begin
            mod_symbols_valid <= 1'b0;
        end else begin
            mod_symbols_valid <= mod_symbols_valid;
        end
    end

    for (i = 0; i < SYMBOL_WIDTH; i++) begin
        always @(posedge clk)
        begin
            if (~aresetn) begin
                mod_symbols[i] <= 0;
            end else if (advance) begin 
                mod_symbols[i] <= (modulation_sr2e == BPSK) ? data_bits[i] :
                              (modulation_sr2e == QPSK) ? data_bits[i * 2 +: 2] :
                              (modulation_sr2e == QAM16) ? data_bits[i * 4 +: 4] :
                              (modulation_sr2e == QAM64) ? data_bits[i * 6 +: 6] :
                              (modulation_sr2e == QAM256) ? data_bits[i * 8 +: 8] :
                              8'b0;
            end 
        end
    end    
endmodule

module piradio_symbol_gearbox
    import piradio_ofdm::*;
    #(
        parameter integer DATA_WIDTH = 32,
        parameter integer COUNT_WIDTH = 7,
        parameter integer SYMBOL_WIDTH = 4
    )
    (
        input logic clk,
        input logic aresetn,
        
        input mod_t modulation_se2gb,
        output logic mod_symbols_rdy,
        input ofdm_symbol_t mod_symbols[0:3],
        input logic mod_symbols_valid,
        input logic mod_symbols_last,        
        
        output mod_t modulation_gb2m,
        input logic mod_gb_symbols_rdy,
        output ofdm_symbol_t mod_gb_symbols[0:3],
        output logic mod_gb_symbols_valid,
        output logic mod_gb_symbols_last
    );

    integer i;    
    ofdm_symbol_t symbol_p[0:3];
    ofdm_symbol_t symbol_e[0:3];
    logic symbol_p_valid, symbol_e_valid;
    logic symbol_p_last, symbol_e_last;
    mod_t mod_p, mod_e;
    
    
    always @(posedge clk)
    begin
        if (~aresetn) begin
            for (i = 0; i < SYMBOL_WIDTH; i++) begin
                symbol_p[i] = 0;
                symbol_e[i] = 0;
            end
            symbol_p_valid <= 1'b0;
            symbol_e_valid <= 1'b0;
            symbol_p_last <= 1'b0;
            symbol_e_last <= 1'b0;
            mod_p <= MOD_NONE;
            mod_e <= MOD_NONE;
        end else begin
            if (mod_symbols_rdy) begin
                symbol_p <= mod_symbols;
                symbol_p_valid <= mod_symbols_valid;
                symbol_p_last <= mod_symbols_last;
                mod_p <= modulation_se2gb;
                if (mod_gb_symbols_rdy == 0) begin
                    symbol_e <= symbol_p;
                    symbol_e_valid <= symbol_p_valid;
                    symbol_e_last <= symbol_p_last;
                    mod_e <= mod_p;
                end
            end

            if (mod_gb_symbols_rdy == 1) begin
                symbol_e_valid <= 0;
            end        
        end
    end
    
    always_comb
    begin
        mod_symbols_rdy = ~symbol_e_valid;
        
        mod_gb_symbols_valid = symbol_p_valid | symbol_e_valid;
        mod_gb_symbols = symbol_e_valid ? symbol_e : symbol_p;
        mod_gb_symbols_last = symbol_e_valid ? symbol_e_last : symbol_p_last;
        modulation_gb2m = symbol_e_valid ? mod_e : mod_p;
    end
endmodule


module piradio_modulator
    import piradio_ofdm::*;
    #(
        parameter integer DATA_WIDTH = 32,
        parameter integer COUNT_WIDTH = 7,
        parameter integer SYMBOL_WIDTH = 4
    )
    (
        input logic clk,
        input logic aresetn,
        
        input mod_t modulation_gb2m,
        output logic mod_gb_symbols_rdy,
        input ofdm_symbol_t mod_gb_symbols[0:3],
        input logic mod_gb_symbols_valid,
        input logic mod_gb_symbols_last,        
        
        output ofdm_sample_t mod_samples[0:3],
        input logic mod_samples_rdy,
        output logic mod_samples_valid,
        output logic mod_samples_last   
    );
   
    genvar i;
    logic advance;
    
    modulation_t cur_mod;
    
    assign cur_mod = modulations[modulation_gb2m]; 

    always_comb advance = mod_gb_symbols_rdy & mod_gb_symbols_valid;

    always_comb mod_gb_symbols_rdy = ((mod_samples_rdy & mod_samples_valid) | ~mod_samples_valid);
   
    always @(posedge clk)
    begin
        if (~aresetn) begin
            mod_samples_valid <= 0;
            mod_samples_last <= 0;
        end else begin
            if (mod_gb_symbols_rdy & mod_gb_symbols_valid) begin
                mod_samples_valid <= 1'b1;
                mod_samples_last <= mod_gb_symbols_last;
            end else if (mod_samples_rdy) begin
                mod_samples_valid <= 1'b0;
            end else begin
                mod_samples_valid <= mod_samples_valid;
            end
        end
    end
    

    for (i = 0; i < SYMBOL_WIDTH; i++) begin
        always @(posedge clk)
        begin
            if (~aresetn) begin
                mod_samples[i] <= 0;            
            end else if (advance) begin
                mod_samples[i] <= cur_mod.constellation[mod_gb_symbols[i]];
            end
        end
    end    
endmodule

module piradio_sample_fifo
    import piradio_ofdm::*;
    #(
        NSAMPLES = 4
    )
    (
        input logic clk,
        input logic aresetn,

        input ofdm_sample_t mod_samples[0:3],
        output logic mod_samples_rdy,
        input logic mod_samples_valid,
        input logic mod_samples_last,  

        output ofdm_sample_t samples_out[0:NSAMPLES-1],
        input logic [2:0] samples_out_desired,
        output logic [2:0] samples_out_valid,
        output logic samples_out_last 
    );
    
    localparam QUEUE_DEPTH = NSAMPLES * 4;
    localparam PTR_WIDTH = $clog2(QUEUE_DEPTH);
    
    genvar i;

    ofdm_sample_t sample_q[0:QUEUE_DEPTH-1];
    
    logic [PTR_WIDTH-1:0] head, tail;
    
    logic output_advance;
    
    integer samples_avail, free_space;    
    
    integer last_count, next_last_count;
    
    always_comb samples_avail = (head <= tail) ? (tail - head) : (QUEUE_DEPTH - head + tail);
    
    always_comb free_space = QUEUE_DEPTH - samples_avail;
    
    always_comb samples_out_valid = (samples_avail >= NSAMPLES) ? NSAMPLES : samples_avail;
    
    always_comb output_advance = (samples_out_valid >= samples_out_desired);
    
    always_comb
    begin
        if (~aresetn) begin
            mod_samples_rdy <= 1'b0;
        end else if (free_space > NSAMPLES) begin
            mod_samples_rdy <= 1'b1;
        end else begin
            mod_samples_rdy <= 1'b0;
        end
    end
    
    always_comb samples_out_last = (last_count & output_advance) ? (last_count == samples_out_desired) : 1'b0;
    
    always @(posedge clk)
    begin
        if (~aresetn) begin
            last_count <= 0;
        end else if (last_count) begin
            last_count <= last_count - samples_out_desired;    
        end else if (mod_samples_last) begin
            last_count <= samples_avail - (output_advance ? samples_out_desired : 0) + NSAMPLES;
        end
    end
    
    for (i = 0; i < NSAMPLES; i++) begin
        integer sample_out_ptr;
        
        // Allow for non-power of 2 queue depth
        always_comb 
        begin
            sample_out_ptr = ((head+i) >= QUEUE_DEPTH) ? (head + i - QUEUE_DEPTH) : (head + i);
            samples_out[i] = sample_q[sample_out_ptr];
            $display("Updating output: %d head: %d tail: %d ptr: %d data: %0x", i, head, tail, sample_out_ptr, sample_q[sample_out_ptr]); 
        end
    end

    for (i = 0; i < QUEUE_DEPTH; i++) begin
        integer slot_offset;
        
        always @(posedge clk)
        begin
            // Allow for non-power of 2 queue depth
            slot_offset = (i >= tail) ? (i - tail) : (i + QUEUE_DEPTH - tail);
            
            if (~aresetn) begin
                sample_q[i] <= 0;
            end else if (mod_samples_rdy && mod_samples_valid) begin
                if (slot_offset < NSAMPLES) begin
                    $display("sample_q[%d] <= %d %0x head: %d tail: %d", 
                             i, slot_offset, mod_samples[slot_offset], head, tail);
                    sample_q[i] <= mod_samples[slot_offset];
                end
            end
        end
    end

    
    always @(posedge clk)
    begin
        if (~aresetn) begin
            head <= 0;
            tail <= 0;
        end else begin
            if (output_advance) begin
                head <= (head + samples_out_desired) % QUEUE_DEPTH; 
            end 
            
            if (mod_samples_rdy && mod_samples_valid) begin
                tail <= tail + NSAMPLES;
            end
        end
    end
endmodule


module piradio_framer_data_modulator 
    import piradio_ofdm::*;
    (
        parser_to_mod_iface.slave parser_to_mod_bus,
        piradio_framer_data_modulator_out_iface.master fdm_bus
    );
    
    genvar i;
    
    logic clk, aresetn;

    localparam DATA_WIDTH = $bits(parser_to_mod_bus.dst_data);
    localparam COUNT_WIDTH = 7;
    localparam SYMBOL_WIDTH = 4;

    logic data_words_ready;
    logic data_words_valid;
    logic [DATA_WIDTH-1:0] data_words;
    logic data_words_last;
    
    logic mod_symbols_rdy;
    ofdm_symbol_t mod_symbols[0:3];
    logic mod_symbols_valid, mod_symbols_last;
    mod_t modulation_in, modulation_sr2e, modulation_se2gb;

    logic mod_gb_symbols_rdy;
    ofdm_symbol_t mod_gb_symbols[0:3];
    logic mod_gb_symbols_valid, mod_gb_symbols_last;
    mod_t modulation_gb2m;

    ofdm_sample_t mod_samples[0:3];
    logic mod_samples_rdy;
    logic mod_samples_valid;
    logic mod_samples_last;


    logic [DATA_WIDTH-1:0] data_bits;
    logic data_bits_valid;
    logic data_bits_rdy;
    logic data_bits_last;
        
         
    always_comb clk = parser_to_mod_bus.clk;
    always_comb aresetn = parser_to_mod_bus.rstn;
    always_comb data_words = parser_to_mod_bus.dst_data;
    always_comb parser_to_mod_bus.dst_rdy = data_words_ready;
    always_comb data_words_valid = parser_to_mod_bus.dst_valid;
    always_comb data_words_last = parser_to_mod_bus.dst_last;
    always_comb modulation_in = parser_to_mod_bus.modulation;
    
    ofdm_sample_t out_samples[0:3];
 
    
    piradio_data_shift_reg #(.DATA_WIDTH(DATA_WIDTH)) 
        input_shift_reg(.*);
    
    piradio_symbol_extractor #(.DATA_WIDTH(DATA_WIDTH))
        symbol_extractor(.*);
    
    piradio_symbol_gearbox gearbox(.*);
    
    piradio_modulator #() modulator(.*);
    
    piradio_sample_fifo #() sample_fifo(
        .samples_out(out_samples),
        .samples_out_desired (fdm_bus.samples_rdy),
        .samples_out_valid(fdm_bus.samples_valid),
        .samples_out_last(fdm_bus.samples_last),
        .*);
        
     for (i = 0; i < SYMBOL_WIDTH; i++) begin
        always_comb fdm_bus.samples[i] = out_samples[i];
     end
    
endmodule
