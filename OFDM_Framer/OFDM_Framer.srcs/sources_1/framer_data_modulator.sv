`timescale 1ns / 1ps
import piradio_ofdm::*;

const logic [31 : 0] bpsk_mods[0 : 15] = { 32'h0000c000, 32'h00003fff, 32'h00, 32'h00,
					   32'h00, 32'h00, 32'h00, 32'h00, 
					   32'h00, 32'h00, 32'h00, 32'h00, 
					   32'h00, 32'h00, 32'h00, 32'h00};
module piradio_framer_data_modulator 
    (
        parser_to_mod_iface.slave parser_to_mod_bus,
        piradio_framer_data_modulator_out_iface.master fdm_bus,
        output wire [31 : 0] test
    );
    
    integer 				  bits_available, bits_consumed, space_avail;
    localparam MAX_SYMBOLS = 4;
    
    localparam SHIFT_REG_WIDTH = fdm_bus.SRC_DATA_WIDTH * 2;
    
    logic [SHIFT_REG_WIDTH - 1:0] 	  shift_reg;
    
    assign space_avail = SHIFT_REG_WIDTH - bits_available;
   
    mod_t modulation;
    
    /* So, here, we can probably leave off the dst_rdy, as we'll queue the
    data into the shift register anyway */
    assign parser_to_mod_bus.dst_rdy = (space_avail >= fdm_bus.SRC_DATA_WIDTH);
    
    genvar i;
    
    ofdm_symbol_t symbols[0:3];
    
    
    for (i = 0; i < MAX_SYMBOLS; i++) begin
        assign symbols[i] = (modulation == BPSK) ? shift_reg[i] :
                            (modulation == QPSK) ? shift_reg[i * 2 +: 2] :
                            (modulation == QAM16) ? shift_reg[i * 4 +: 4] :
                            (modulation == QAM64) ? shift_reg[i * 6 +: 6] :
                            (modulation == QAM256) ? shift_reg[i * 8 +: 8] :
                            8'b0;
                            
        assign fdm_bus.samples[i] = bpsk_mods[symbols[i]];
    end

    integer total_samples_valid;
    
    always_comb
        total_samples_valid = bits_available / 1;//modulations[parser_to_mod_bus.modulation].bits_per_symbol;
        
    

    assign fdm_bus.samples_valid = (total_samples_valid > MAX_SYMBOLS) ? MAX_SYMBOLS : total_samples_valid;
    
    assign bits_consumed = fdm_bus.samples_rdy * 1;//modulations[parser_to_mod_bus.modulation].bits_per_symbol;
   
    // Using a temporary here to make the code easier to read
    // but still use a non-blocking assignment at the end so synthesis
    // doesn't cock it up.
    integer new_bits_available;
    logic [SHIFT_REG_WIDTH - 1:0] new_shift_reg;
   
//    assign test[0] = symbols[0];
//    assign test[1] = symbols[1];
//    assign test[2] = symbols[2];
//    assign test[3] = symbols[3];
//        assign test[31 : 4] = bpsk_mods[symbols[0]];

    always @(posedge parser_to_mod_bus.clk) begin
        if (~parser_to_mod_bus.rstn) begin
            bits_available = 0;
        end else begin
            new_bits_available = bits_available;
            new_shift_reg = shift_reg;
            
            if(fdm_bus.samples_rdy && fdm_bus.samples_rdy <= fdm_bus.samples_valid) begin
                new_bits_available = new_bits_available - bits_consumed;
                new_shift_reg = new_shift_reg >> bits_consumed;
            end
    
            if(parser_to_mod_bus.dst_rdy && parser_to_mod_bus.dst_valid) begin
                if (new_bits_available) begin
                    // Be sure to drain symbols if modulation is changing
                    if (parser_to_mod_bus.modulation == modulation) begin
                        new_shift_reg |= parser_to_mod_bus.dst_data << new_bits_available;
                        new_bits_available += fdm_bus.SRC_DATA_WIDTH;
                    end
                end else begin
                    modulation <= parser_to_mod_bus.modulation;
                    new_shift_reg = parser_to_mod_bus.dst_data;
                    new_bits_available = fdm_bus.SRC_DATA_WIDTH;        
                end 
            end
            bits_available <= new_bits_available;
            shift_reg <= new_shift_reg;
        end
    end
    
	// s_tready is asserted only when the available bits in the shift register are below a threshold 
	assert property (@(posedge parser_to_mod_bus.clk)
	   ((bits_available) < SHIFT_REG_WIDTH/2 ) &&
	            (fdm_bus.samples_rdy && fdm_bus.samples_rdy <= fdm_bus.samples_valid) |-> parser_to_mod_bus.dst_rdy);
	
	always@(posedge parser_to_mod_bus.clk) begin
        assume(bits_available >= bits_consumed);
    end
endmodule
