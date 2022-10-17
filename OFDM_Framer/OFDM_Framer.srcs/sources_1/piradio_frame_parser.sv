
module piradio_frame_parser 
    import piradio_ofdm::*;
    (
    frame_parser_in_iface.master frame_parser_bus,
    parser_to_mod_iface.master parser_to_mod_bus
    );
    integer  word_count;
    integer  words_per_frame;
    localparam MAX_MOD_INDEX = 5;
    
    typedef enum {
        HEADER,
        DATA
    } state_t;
    
    assign words_per_frame = frame_parser_bus.SAMPS_PER_FRAME * modulations[parser_to_mod_bus.modulation].bits_per_symbol;
    
    assign parser_to_mod_bus.dst_valid = (state == HEADER) ? 0 : frame_parser_bus.src_valid;
    assign parser_to_mod_bus.dst_last = (word_count == words_per_frame - 1);
    assign parser_to_mod_bus.dst_data = frame_parser_bus.src_data;
    assign frame_parser_bus.src_rdy = parser_to_mod_bus.dst_rdy; 
    
    state_t state;
    
    always @(posedge parser_to_mod_bus.clk)
    begin
        if (~parser_to_mod_bus.rstn) begin
            word_count <= 0;
            parser_to_mod_bus.modulation <= BPSK;
            state <= HEADER;
        end else if (frame_parser_bus.src_valid && frame_parser_bus.src_rdy) begin
            if (state == HEADER) begin
                parser_to_mod_bus.modulation <= (frame_parser_bus.src_data <= MAX_MOD_INDEX) ? mod_t'(frame_parser_bus.src_data)
                                        : BPSK;
                word_count <= 0;
                state <= DATA;            
            end else begin
                if (word_count == words_per_frame - 1) begin
                    state <= HEADER;
                    word_count = 0;
                end else begin
                    word_count = word_count + 1;
                end
            end
        end	else begin
            parser_to_mod_bus.modulation <= parser_to_mod_bus.modulation;
        end
    end // always @ (posedge clk)
    
endmodule