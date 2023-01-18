`timescale 1ns / 1ps

/*
    bram_ctrl
    
    This module holds a BRAM of size equal to two symbols (2 * FFT_SIZE). This BRAM
    is continuously been written to as a ring buffer. When a peak is detected, this
    module takes in the index of the detected peak and calculates where the start
    of the symbol in the ring buffer is according to that index.

*/
module bram_ctrl(
        input wire clk,
        input wire resetn,
        corr_arbiter2sample_buff_iface.slave corr_arbiter2sample_buff,
        axis_iface.slave input_fifo2buff,
        sample_buff2cp_rm_iface.master sample_buff2cp_rm
    );
    typedef enum {IDLE, TXING} buffer_state_t;
    buffer_state_t buffer_state;
    logic samples_ready;
    logic [$clog2(sample_buff2cp_rm.BUFFER_LEN) - 1 : 0] addr_a;
    logic [$clog2(sample_buff2cp_rm.BUFFER_LEN) - 1 : 0] addr_b;
    logic peak_at_0_ssr_idx;
    logic last_sample;
    logic en_b;
    logic out_tlast;
    logic [$clog2(sample_buff2cp_rm.SAMPLE_WIDTH * 
            sample_buff2cp_rm.TOTAL_SYMBOL_LEN * sample_buff2cp_rm.NUM_DATA_SYMBOLS) - 1 : 0] frame_samples_count; 
    logic [sample_buff2cp_rm.BRAM_LATENCY - 1 : 0] bram_out_valid = 0;
    logic [sample_buff2cp_rm.BRAM_LATENCY - 1 : 0] bram_out_last = 0;
    
    always@(posedge clk) bram_out_valid <= {en_b, bram_out_valid[sample_buff2cp_rm.BRAM_LATENCY - 1  : 1]};
    always@(posedge clk) bram_out_last <= {out_tlast, bram_out_last[sample_buff2cp_rm.BRAM_LATENCY - 1  : 1]};
    
    always_comb last_sample <= frame_samples_count == sample_buff2cp_rm.TOTAL_SYMBOL_LEN * sample_buff2cp_rm.NUM_DATA_SYMBOLS - 1;
    always_comb peak_at_0_ssr_idx <= corr_arbiter2sample_buff.ssr_idx != 0;
    always_comb samples_ready <= corr_arbiter2sample_buff.samples_valid;
    always_comb input_fifo2buff.tready <= samples_ready;
    always_comb sample_buff2cp_rm.samples_valid <= bram_out_valid[0];
    always_comb sample_buff2cp_rm.samples_last <= bram_out_last[0];
    always_comb corr_arbiter2sample_buff.src_ready <= (buffer_state == IDLE);
    
    
    always@(posedge clk) begin
        if(!resetn) begin
            addr_b <= 0;
            en_b <= 0;
            frame_samples_count <= 0;
            out_tlast <= 0;
        end
        else begin
            if(corr_arbiter2sample_buff.start_idx_valid && buffer_state != TXING) begin
                addr_b <= (corr_arbiter2sample_buff.correlator_idx == 2'h1) ? 
                                addr_a - corr_arbiter2sample_buff.start_idx + 1 - peak_at_0_ssr_idx :
                                addr_a - (corr_arbiter2sample_buff.start_idx + 128) + 1 - peak_at_0_ssr_idx;
                en_b <= 1;
            end
            if(buffer_state == TXING) begin
                if(frame_samples_count % (sample_buff2cp_rm.TOTAL_SYMBOL_LEN) == (sample_buff2cp_rm.TOTAL_SYMBOL_LEN - 2))
                    out_tlast <= 1;
                else
                    out_tlast <= 0;
                if(last_sample) begin
                    en_b <= 0;
                    frame_samples_count <= 0;
                end
                else begin
                    addr_b <= addr_b + 1;
                    frame_samples_count <= frame_samples_count + 1;
                end
            end
        end
    end
    
    always@(posedge clk) begin
        if(!resetn) begin
            buffer_state <= IDLE;
        end
        else begin
            if(corr_arbiter2sample_buff.start_idx_valid) begin
                case (buffer_state)
                    IDLE: buffer_state <= TXING;
                    TXING : buffer_state <= TXING;
                    default: buffer_state <= IDLE;
                endcase
            end
            if(buffer_state == TXING && last_sample)
                buffer_state <= IDLE;
        end
    end
    
    always@ (posedge clk) begin
        if(!resetn) begin
            addr_a <= 0;
            
        end
        else begin
            if(samples_ready) begin
                addr_a <= addr_a + 1;
            end
        end
    end
    
    
    
xpm_memory_sdpram #(
   .ADDR_WIDTH_A($clog2(sample_buff2cp_rm.BUFFER_LEN)),               // DECIMAL
   .ADDR_WIDTH_B($clog2(sample_buff2cp_rm.BUFFER_LEN)),               // DECIMAL
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(sample_buff2cp_rm.SAMPLE_WIDTH),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(sample_buff2cp_rm.SAMPLE_WIDTH * sample_buff2cp_rm.BUFFER_LEN),             // DECIMAL
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(sample_buff2cp_rm.SAMPLE_WIDTH),  // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(sample_buff2cp_rm.SAMPLE_WIDTH),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
buffer_ram_inst (                                
   .doutb(sample_buff2cp_rm.samples_out),
   .addra(addr_a),
   .addrb(addr_b),
   .clka(clk),
   .clkb(clk),
   .dina(input_fifo2buff.tdata),
   .ena(samples_ready),
   .enb(en_b),
   .regceb(1),                        
   .wea(1)
);

/* Assert memory address ranges */
assert property (@(posedge clk)
	   (addr_b >= 0 && addr_b < 512));
assert property (@(posedge clk)
	   (addr_a >= 0 && addr_a < 512));
	   
	   
endmodule


