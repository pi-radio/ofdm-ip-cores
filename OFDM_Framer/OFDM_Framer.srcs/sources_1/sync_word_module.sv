
module sync_word_module#
        ( 
        parameter integer TOTAL_CARRIERS = 1024,
        parameter integer S_AXIS_TDATA_WIDTH = 32,
        parameter integer OUT_WIDTH = 128,
        parameter integer MAP_WIDTH = 4
        )
        (
    	input wire  s_axis_config_aclk,
		input wire  s_axis_config_aresetn,
		output wire  s_axis_config_tready,
		input wire [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_config_tdata,
		input wire [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_config_tstrb,
		input wire  s_axis_config_tlast,
		input wire  s_axis_config_tvalid,
		output reg structs_ready,
		bram_fifo_in_iface.slave bram_syncw_bus,
		bram_fifo_in_iface.slave bram_temp_bus
		);
		
    localparam samps_per_cycle = 4;
    typedef enum {IDLE, SYNC_WORD, TEMPLATE, MAP, FIN} config_state_t;
    config_state_t state = IDLE;
    reg syncw_in_en = 0;
    reg temp_in_en = 0;
    reg [10 : 0] word_count = 0;
    reg [MAP_WIDTH - 1 : 0] map_shift_reg;
    reg [OUT_WIDTH - 1 : 0] sync_word_reg = 0;
    reg [OUT_WIDTH - 1 : 0] temp_map_reg = 0;
   
    
    assign s_axis_config_tready = (!(state == FIN) && s_axis_config_aresetn);
    
    always @(posedge s_axis_config_aclk) begin
        if ( s_axis_config_aresetn == 1'b0 ) begin
            word_count <= 0;
            structs_ready <= 0;
            bram_syncw_bus.fifo_restart <= 0;
            bram_temp_bus.fifo_restart <= 0;
        end else begin
            if(syncw_in_en) syncw_in_en <= 0;
            if(temp_in_en) temp_in_en <= 0;
            case(state)
                IDLE: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        state <= SYNC_WORD;
                        word_count <= word_count + 1;
                        sync_word_reg <= {s_axis_config_tdata, sync_word_reg[S_AXIS_TDATA_WIDTH +: (OUT_WIDTH - S_AXIS_TDATA_WIDTH)]};
                        bram_syncw_bus.fifo_restart <= 0;
                        bram_temp_bus.fifo_restart <= 0; 
                    end
                end
                SYNC_WORD: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        word_count <= word_count + 1;
                        sync_word_reg <= {s_axis_config_tdata, sync_word_reg[S_AXIS_TDATA_WIDTH +: (OUT_WIDTH - S_AXIS_TDATA_WIDTH)]};
                        if((word_count + 1) % 4 == 0) syncw_in_en <= 1;
                        if(s_axis_config_tlast) state <= TEMPLATE;
                        bram_syncw_bus.fifo_restart <= 0;
                        bram_temp_bus.fifo_restart <= 0; 
                    end
                end
                TEMPLATE: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        temp_map_reg <= {s_axis_config_tdata, temp_map_reg[S_AXIS_TDATA_WIDTH +: (OUT_WIDTH - S_AXIS_TDATA_WIDTH)]};
                        state <= MAP;
                        bram_syncw_bus.fifo_restart <= 0;
                        bram_temp_bus.fifo_restart <= 0; 
                    end
                end
                MAP: begin
                    if(s_axis_config_tvalid && s_axis_config_tready) begin
                        if((word_count + 1) % 4 == 0) temp_in_en <= 1;
                        map_shift_reg <= {s_axis_config_tdata > 0 ? 1 : 0,
                            map_shift_reg[MAP_WIDTH - 1 : 1]};
                        if(s_axis_config_tlast) begin
                            state <= FIN;
                            bram_syncw_bus.fifo_restart <= 1;
                            bram_temp_bus.fifo_restart <= 1;                            
                            word_count <= 0;
                            structs_ready <= 1;
                        end
                        else begin
                            state <= TEMPLATE;
                            word_count <= word_count + 1;
                        end
                    end
                end
                FIN: begin
                    bram_syncw_bus.fifo_restart <= 0;
                    bram_temp_bus.fifo_restart <= 0; 
                end
            endcase
        end
    end
    
xpm_memory_sdpram #(
   .ADDR_WIDTH_A($clog2(TOTAL_CARRIERS / 4)),               // DECIMAL
   .ADDR_WIDTH_B($clog2(TOTAL_CARRIERS / 4)),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(OUT_WIDTH),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(OUT_WIDTH * (TOTAL_CARRIERS / samps_per_cycle)),             // DECIMAL
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(OUT_WIDTH),  // DECIMAL
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
sync_word_ram_inst (                                
   .doutb(bram_syncw_bus.bram_data),
   .addra((word_count - 4) / 4),
   .addrb(bram_syncw_bus.bram_addr),
   .clka(s_axis_config_aclk),
   .clkb(s_axis_config_aclk),
   .dina(sync_word_reg),
   .ena(syncw_in_en),
   .enb(bram_syncw_bus.bram_rd_en),
   .regceb(1),                        
   .wea(1)
);

xpm_memory_sdpram #(
   .ADDR_WIDTH_A($clog2(TOTAL_CARRIERS / 4)),               // DECIMAL
   .ADDR_WIDTH_B($clog2(TOTAL_CARRIERS / 4)),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A((OUT_WIDTH + MAP_WIDTH)),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(((OUT_WIDTH + MAP_WIDTH) * (TOTAL_CARRIERS / samps_per_cycle))),             // DECIMAL
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(OUT_WIDTH + MAP_WIDTH),         // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(OUT_WIDTH + MAP_WIDTH),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
temp_map_ram_inst (                                
   .doutb(bram_temp_bus.bram_data),
   .addra((word_count - 4) / 4),
   .addrb(bram_temp_bus.bram_addr),
   .clka(s_axis_config_aclk),
   .clkb(s_axis_config_aclk),
   .dina({map_shift_reg, temp_map_reg}),
   .ena(temp_in_en),
   .enb(bram_temp_bus.bram_rd_en),
   .regceb(1),                        
   .wea(1)
);
    
endmodule
