import piradio_ofdm::*;

module piradio_frame_parser 
    (
    frame_parser_in_iface.master frame_parser_bus,
    parser_to_mod_iface.master parser_to_mod_bus
    );
    integer  word_count;
    integer  words_per_frame;
    localparam MAX_MOD_INDEX = 5;
    
    assign words_per_frame = frame_parser_bus.SAMPS_PER_FRAME * modulations[parser_to_mod_bus.modulation].bits_per_symbol;
    
    assign parser_to_mod_bus.dst_valid = (word_count == 0) ? 0 : frame_parser_bus.src_valid;
    assign parser_to_mod_bus.dst_last = word_count == words_per_frame;
    assign parser_to_mod_bus.dst_data = frame_parser_bus.src_data;
    assign frame_parser_bus.src_rdy = parser_to_mod_bus.dst_rdy; 
    
    always @(posedge parser_to_mod_bus.clk)
    begin
        if (~parser_to_mod_bus.rstn) begin
            word_count <= 0;
            parser_to_mod_bus.modulation <= BPSK;
        end else if (frame_parser_bus.src_valid && frame_parser_bus.src_rdy) begin
            if (word_count == 0) begin
                parser_to_mod_bus.modulation <= (frame_parser_bus.src_data <= MAX_MOD_INDEX) ? mod_t'(frame_parser_bus.src_data)
                                        : BPSK;
            end
            
            word_count <= (word_count == words_per_frame) ? 0 : word_count + 1;
        end	else begin
            parser_to_mod_bus.modulation <= parser_to_mod_bus.modulation;
        end
    end // always @ (posedge clk)
    
endmodule