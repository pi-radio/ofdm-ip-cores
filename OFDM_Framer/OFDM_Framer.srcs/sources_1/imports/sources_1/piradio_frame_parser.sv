module piradio_frame_parser 
    import piradio_ofdm::*;
    (
    frame_parser_in_iface.master frame_parser_bus,
    ctrl_in_iface.slave ctrl_in,
    parser_to_mod_iface.master parser_to_mod_bus
    );
    integer  word_count;
    integer  words_per_frame;
    localparam MAX_MOD_INDEX = 5;
    logic [ctrl_in.WIDTH - 1 : 0] ctrl_fifo_data;
    logic ctrl_fifo_valid;
    logic ctrl_fifo_ready;
    
    typedef enum {
        HEADER,
        DATA
    } state_t;
    state_t state;
    assign words_per_frame = frame_parser_bus.SAMPS_PER_FRAME * modulations[parser_to_mod_bus.modulation].bits_per_symbol;
    
    assign parser_to_mod_bus.dst_valid = ((state == HEADER) || !frame_parser_bus.structs_rdy) ? 0 : frame_parser_bus.src_valid;
    assign parser_to_mod_bus.dst_last = (word_count == words_per_frame - 1);
    assign parser_to_mod_bus.dst_data = frame_parser_bus.src_data;
    assign frame_parser_bus.src_rdy = parser_to_mod_bus.dst_rdy && (state != HEADER); 
    
    
    
    always @(posedge parser_to_mod_bus.clk)
    begin
        if (~parser_to_mod_bus.rstn) begin
            word_count <= 0;
            parser_to_mod_bus.modulation <= MOD_NONE;
            state <= HEADER;
        end else if (frame_parser_bus.src_valid && frame_parser_bus.src_rdy && frame_parser_bus.structs_rdy) begin
            ctrl_fifo_ready <= 0;
            if (state == DATA) begin
                if (word_count == words_per_frame - 1) begin
                    state <= HEADER;
                    word_count = 0;
                end else begin
                    word_count = word_count + 1;
                end
            end
        end else if(ctrl_fifo_valid && (state == HEADER) && frame_parser_bus.structs_rdy) begin
            parser_to_mod_bus.modulation <= (ctrl_fifo_data <= MAX_MOD_INDEX) ? mod_t'(ctrl_fifo_data)
                                        : MOD_NONE;
            ctrl_fifo_ready <= 1;
            word_count <= 0;
            state <= DATA; 
        end	else begin
            ctrl_fifo_ready <= 0;
            parser_to_mod_bus.modulation <= parser_to_mod_bus.modulation;
        end
    end // always @ (posedge clk)
    
    
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
     .TDATA_WIDTH(ctrl_in.WIDTH), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    xpm_fifo_axis_inst (
     .m_axis_tdata(ctrl_fifo_data),
     .m_axis_tvalid(ctrl_fifo_valid),
     .s_axis_tready(ctrl_in.ctrl_ready),
     .m_aclk(parser_to_mod_bus.clk),
     .m_axis_tready(ctrl_fifo_ready),
     .s_aclk(parser_to_mod_bus.clk),
     .s_aresetn(parser_to_mod_bus.rstn),
     .s_axis_tdata(ctrl_in.ctrl_data),
     .s_axis_tvalid(ctrl_in.ctrl_valid)
    );
    
endmodule