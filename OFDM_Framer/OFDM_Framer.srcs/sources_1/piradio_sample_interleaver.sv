`timescale 1ns / 1ps

module piradio_sample_interleaver
    import piradio_ofdm::*;
    (
    input logic clk,
    input logic resetn,
    bram_fifo_out_iface.slave bram_syncw_out,
    bram_fifo_out_iface.slave bram_temp_out,
    piradio_framer_data_modulator_out_iface.slave fdm_out,
    output logic samples_out_valid,
    input logic samples_out_rdy,
    output logic [fdm_out.DST_DATA_WIDTH/fdm_out.MAX_SYMBOLS - 1 : 0] samples_out[0 : fdm_out.MAX_SYMBOLS - 1]
    );
    
    logic [fdm_out.MAX_SYMBOLS - 1 : 0] current_map;
    //logic samples_in_rdy;       // The amount of samples we need at each cycle
    genvar i;
    logic [2 : 0] count_ones[fdm_out.MAX_SYMBOLS - 1 : 0];
    
    assign count_ones[0] = 0;
    assign count_ones[1] = ones_lut[current_map[0]];
    assign count_ones[2] = ones_lut[current_map[1 : 0]];
    assign count_ones[3] = ones_lut[current_map[2 : 0]];
    

    assign sync_word_active = bram_syncw_out.fifo_valid;
    assign template_active = bram_temp_out.fifo_valid;
                                                                                        
    assign test = fdm_out.samples_rdy;
    
    
    typedef enum {
        IDLE,
        SYNC_WORD,
        DATA,
        TRAILER        
    } state_t;
    
    state_t state;
    
    always_comb 
        bram_syncw_out.fifo_rdy = (state == SYNC_WORD) ? samples_out_rdy : 1'b0;
        
        
    always_comb 
        current_map = (state == DATA | state == TRAILER) ? bram_temp_out.fifo_data[bram_temp_out.WIDTH - 1 : bram_temp_out.WIDTH - fdm_out.MAX_SYMBOLS]
                                            : {fdm_out.MAX_SYMBOLS{1'b0}};

    always_comb
        bram_syncw_out.fifo_restart = 0;
    
    always_comb
        bram_temp_out.fifo_restart = 0;
        
    
    
    always @(posedge clk)
    begin
        if (~resetn) begin
            state <= IDLE;
        end else begin
            case (state)
                IDLE: begin
                    if (fdm_out.samples_valid > 0) begin
                        // Now we start the sync word
                        state <= SYNC_WORD; 
                    end else begin
                        state <= IDLE;
                    end
                end
                
                SYNC_WORD: begin
                    if (bram_syncw_out.fifo_last) begin
                        state <= DATA;
                    end else begin
                        state <= SYNC_WORD;
                    end
                end
                
                DATA: begin
                    if (fdm_out.samples_last) begin
                        state <= TRAILER;
                    end else begin
                        state <= DATA;
                    end
                end
                    
                TRAILER: begin
                    if (bram_temp_out.fifo_last) begin
                        if (fdm_out.samples_valid > 0) begin
                            state <= SYNC_WORD;
                        end else begin
                            state <= IDLE;
                        end
                    end else begin
                        state <= TRAILER;
                    end
                end
               
            endcase
        end
    end

    always_comb bram_syncw_out.fifo_rdy = (state == SYNC_WORD) ? samples_out_rdy : 0;
    always_comb bram_temp_out.fifo_rdy = (state == DATA || state == TRAILER) ? samples_out_rdy : 0;

    for (i = 0; i < fdm_out.MAX_SYMBOLS; i++) begin
        always_comb begin
            if (~resetn) begin
                samples_out[i] <= 32'hBCBCBCBC;
            end else if (state == IDLE) begin
                samples_out[i] <= 32'hADADADAD;
            end else if (state == SYNC_WORD) begin
                samples_out[i] = bram_syncw_out.fifo_data[i * 32 +: 32];
            end else if (state == DATA) begin
                samples_out[i] = current_map[i] ? fdm_out.samples[count_ones[i]] : bram_temp_out.fifo_data[i * 32 +: 32];
            end else if (state == TRAILER) begin
                samples_out[i] = bram_temp_out.fifo_data[i * 32 +: 32];
            end
        end
    end
    
    integer j;
    
    always @(posedge clk)
    begin
        if (state == DATA) begin
            $display("Time: %0t: State: %d map: %0x samples: %0x", 
                     $time(), state, current_map, fdm_out.samples);
            $display("    count_ones: %d %d %d %d syncw: %0x template: %0x", 
                     count_ones[0], count_ones[1], count_ones[2], count_ones[3], 
                     bram_syncw_out.fifo_data, bram_temp_out.fifo_data);
        end
    end
    
    always_comb begin
        if (state == DATA) begin
            fdm_out.samples_rdy = (samples_out_rdy) ? ones_lut[current_map] : 0;
        end else begin
            fdm_out.samples_rdy = 0;
        end 
    end    
    
    always_comb begin
        if (~resetn) begin
            samples_out_valid <= 0;
        end else if (state == IDLE) begin
            samples_out_valid <= 0;            
        end else if (state == SYNC_WORD) begin
            samples_out_valid <= bram_syncw_out.fifo_valid;
        end else if (state == DATA) begin
            samples_out_valid <= bram_temp_out.fifo_valid;
        end else if (state == TRAILER) begin
            samples_out_valid <= bram_temp_out.fifo_valid;
        end
    end

    
    
endmodule
