`timescale 1ns / 1ps

module piradio_framer_data_modulator 
    import piradio_ofdm::*;
    (
        parser_to_mod_iface.slave parser_to_mod_bus,
        piradio_framer_data_modulator_out_iface.master fdm_bus
    );
    
    integer bits_available, bits_consumed, space_avail;
    
    localparam SHIFT_REG_WIDTH = $bits(fdm_bus.samples) * 2;
    
    (* mark_debug = "true" *) logic [SHIFT_REG_WIDTH - 1:0] 	  shift_reg;
    
    assign space_avail = SHIFT_REG_WIDTH - bits_available;
   
    mod_t modulation;
    
    /* So, here, we can probably leave off the dst_rdy, as we'll queue the
    data into the shift register anyway */
    assign parser_to_mod_bus.dst_rdy = (space_avail >= fdm_bus.SRC_DATA_WIDTH);
    
    genvar i;
    
    
    
    ofdm_symbol_t symbols[0:3];
    
    
    for (i = 0; i < fdm_bus.MAX_SYMBOLS; i++) begin
        assign symbols[i] = (modulation == BPSK) ? shift_reg[i] :
                            (modulation == QPSK) ? shift_reg[i * 2 +: 2] :
                            (modulation == QAM16) ? shift_reg[i * 4 +: 4] :
                            (modulation == QAM64) ? shift_reg[i * 6 +: 6] :
                            (modulation == QAM256) ? shift_reg[i * 8 +: 8] :
                            8'b0;
                            
        assign fdm_bus.samples[i] = cur_mod.constellation[symbols[i]];
    end

    integer total_samples_valid;
   
   
    modulation_t cur_mod;
    
    always_comb cur_mod = modulations[modulation];
        
    always_comb
        total_samples_valid = (modulation != MOD_NONE) ? bits_available / cur_mod.bits_per_symbol : 0;

    always_comb fdm_bus.samples_valid = (total_samples_valid > fdm_bus.MAX_SYMBOLS) ? fdm_bus.MAX_SYMBOLS : total_samples_valid;
    
    always_comb bits_consumed = fdm_bus.samples_rdy * cur_mod.bits_per_symbol;
   
    // Using a temporary here to make the code easier to read
    // but still use a non-blocking assignment at the end so synthesis
    // doesn't cock it up.
    integer new_bits_available;
    logic [SHIFT_REG_WIDTH - 1:0] new_shift_reg;
    
    
    logic [7:0] samples_last_cnt, new_samples_last_cnt;

    always_comb fdm_bus.samples_last = ((samples_last_cnt > 0) && (fdm_bus.samples_rdy == samples_last_cnt));

    always @(posedge parser_to_mod_bus.clk) begin
        if (~parser_to_mod_bus.rstn) begin
            new_bits_available = 0;
            new_shift_reg = 0;
            new_samples_last_cnt = 0;
        end else begin
            new_bits_available = bits_available;
            new_shift_reg = shift_reg;
            new_samples_last_cnt = samples_last_cnt;
            
            if(fdm_bus.samples_rdy && fdm_bus.samples_rdy <= fdm_bus.samples_valid) begin
                new_bits_available = new_bits_available - bits_consumed;
                new_shift_reg = new_shift_reg >> bits_consumed;
                new_samples_last_cnt = (new_samples_last_cnt > fdm_bus.samples_rdy) ? new_samples_last_cnt - fdm_bus.samples_rdy : 0;
            end
    
            if(parser_to_mod_bus.dst_rdy && parser_to_mod_bus.dst_valid) begin
                if (new_bits_available) begin
                    // Be sure to drain symbols if modulation is changing
                    if (parser_to_mod_bus.modulation == modulation) begin
                        new_shift_reg |= parser_to_mod_bus.dst_data << new_bits_available;
                        new_bits_available += fdm_bus.SRC_DATA_WIDTH;
                        new_samples_last_cnt += parser_to_mod_bus.dst_last ? new_bits_available / cur_mod.bits_per_symbol : 0;
                    end
                end else begin
                    modulation <= parser_to_mod_bus.modulation;
                    new_shift_reg = parser_to_mod_bus.dst_data;
                    new_bits_available = fdm_bus.SRC_DATA_WIDTH;        
                    new_samples_last_cnt += parser_to_mod_bus.dst_last ? new_bits_available / cur_mod.bits_per_symbol : 0;
                end 
            end
        end
        bits_available <= new_bits_available;
        shift_reg <= new_shift_reg;
        samples_last_cnt <= new_samples_last_cnt;
    end
    
	// s_tready is asserted only when the available bits in the shift register are below a threshold 
	assert property (@(posedge parser_to_mod_bus.clk)
	   ((bits_available) < SHIFT_REG_WIDTH/2 ) &&
	            (fdm_bus.samples_rdy && fdm_bus.samples_rdy <= fdm_bus.samples_valid) |-> parser_to_mod_bus.dst_rdy);
	
	always@(posedge parser_to_mod_bus.clk) begin
        assert(bits_available >= bits_consumed) else begin
            $display("Bits available (%d) < Bits consumed (%d)", bits_available, bits_consumed);
            $stop;
        end
    end
endmodule
