module sync_word_module#
        ( 
        parameter integer TOTAL_CARRIERS = 1024,
        parameter integer S_AXIS_TDATA_WIDTH = 128,
        parameter integer OUT_WIDTH = 128
        )
        (
    	input wire  s_axis_config_aclk,
		input wire  s_axis_config_aresetn,
		output wire  s_axis_config_tready,
		input wire [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_config_tdata,
		input wire [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_config_tstrb,
		input wire  s_axis_config_tlast,
		input wire  s_axis_config_tvalid,
		input wire [8 : 0] bram_addr,
		output wire [OUT_WIDTH - 1 : 0] sync_temp_dout,
		output wire [3 : 0] map_dout,
		input wire bram_en,
		output reg structs_ready
    );
    localparam map_byte_width = 4;
    reg sync_temp_en = 0;
    wire map_en;
    typedef enum {IDLE, SYNC_WORD, TEMPLATE, MAP, FIN} config_state_t;
    config_state_t state = IDLE;
    reg [10 : 0] word_count = 0;
    reg [OUT_WIDTH - 1 : 0] map_shift_reg;
    reg [7 : 0] bits_available = 0;
    reg [OUT_WIDTH - 1 : 0] sync_temp_reg = 0;
    
    assign s_axis_config_tready = (state == MAP) ? (((bits_available - 4 == 0) || (bits_available == 0)) && s_axis_config_tvalid) :
                                     (!(state == FIN) && s_axis_config_aresetn);
    //assign sync_temp_en = (s_axis_config_tvalid && s_axis_config_tready) && ((state != MAP));
    assign map_en = (bits_available > 0) && (state == MAP);
    
    always @(posedge s_axis_config_aclk) begin
        if ( s_axis_config_aresetn == 1'b0 ) begin
            word_count <= 0;
            structs_ready <= 0;
        end
        else begin
            if(sync_temp_en) sync_temp_en <= 0;
            case(state)
                IDLE: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        state <= SYNC_WORD;
                        word_count <= word_count + 1;
                        sync_temp_reg <= {s_axis_config_tdata, sync_temp_reg[127 : 32]};
                    end
                end
                SYNC_WORD: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        word_count <= word_count + 1;
                        sync_temp_reg <= {s_axis_config_tdata, sync_temp_reg[127 : 32]};
                        if((word_count + 1) % 4 == 0) sync_temp_en <= 1;
                        if(s_axis_config_tlast) state <= TEMPLATE;
                    end
                end
                TEMPLATE: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        if((word_count + 1) % 4 == 0) sync_temp_en <= 1;
                        sync_temp_reg <= {s_axis_config_tdata, sync_temp_reg[127 : 32]};
                        if(s_axis_config_tlast) begin
                            state <= MAP;
                            word_count <= 0;
                        end
                        else begin
                            word_count <= word_count + 1;
                        end
                    end
                end
                MAP: begin
                    if(bits_available - 4 > 0 && bits_available != 0) begin
                        word_count <= word_count + 1;
                        bits_available <= bits_available - 4;
                        map_shift_reg <= {4'h0, map_shift_reg[127 : 4]};
                    end
                    else if(bits_available == 0) begin
                        map_shift_reg <= s_axis_config_tdata;
                        bits_available <= S_AXIS_TDATA_WIDTH;
                    end
                    else begin
                        if(s_axis_config_tvalid) begin
                            map_shift_reg <= s_axis_config_tdata;
                            bits_available <= S_AXIS_TDATA_WIDTH;
                            word_count <= word_count + 1;
                        end
                        else begin
                            bits_available <= bits_available - 4;
                            state <= FIN;
                            structs_ready <= 1;
                            word_count <= 0;
                        end
                    end
                end
            endcase
        end
    end
    
xpm_memory_sdpram #(
   .ADDR_WIDTH_A(9),               // DECIMAL
   .ADDR_WIDTH_B(9),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(OUT_WIDTH),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(65536),             // DECIMAL
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(OUT_WIDTH),         // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(OUT_WIDTH),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
sync_temp_ram_inst (                                
   .doutb(sync_temp_dout),
   .addra((word_count - 4) / 4),
   .addrb(bram_addr),
   .clka(s_axis_config_aclk),
   .clkb(s_axis_config_aclk),
   .dina(sync_temp_reg),
   .ena(sync_temp_en),
   .enb(bram_en),
   .regceb(1),                        
   .wea(1)
);

xpm_memory_sdpram #(
   .ADDR_WIDTH_A(8),               // DECIMAL
   .ADDR_WIDTH_B(8),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(map_byte_width),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(1024),             // DECIMAL
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(map_byte_width),         // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(map_byte_width),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
map_ram_inst (                                
   .doutb(map_dout),
   .addra(word_count),
   .addrb(bram_addr[7 : 0]),
   .clka(s_axis_config_aclk),
   .clkb(s_axis_config_aclk),
   .dina(map_shift_reg[3 : 0]),
   .ena(map_en),
   .enb(bram_en),
   .regceb(1),                        
   .wea(1)
);
    
endmodule
