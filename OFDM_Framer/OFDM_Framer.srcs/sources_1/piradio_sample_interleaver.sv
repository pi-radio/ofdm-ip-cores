`timescale 1ns / 1ps
import piradio_ofdm::*;

module piradio_sample_interleaver(
    input wire clk,
    input wire resetn,
    bram_fifo_out_iface.slave bram_syncw_out,
    bram_fifo_out_iface.slave bram_temp_out,
    piradio_framer_data_modulator_out_iface.slave fdm_out,
    output logic samples_out_valid,
    input logic samples_out_rdy,
    output reg [fdm_out.DST_DATA_WIDTH/fdm_out.MAX_SYMBOLS - 1 : 0] samples_out[0 : fdm_out.MAX_SYMBOLS - 1]
    );
    
    logic sync_word_active;
    logic template_active;
    logic [fdm_out.MAX_SYMBOLS - 1 : 0] current_map;
    //logic samples_in_rdy;       // The amount of samples we need at each cycle
    genvar i;
    logic [2 : 0] count_ones[fdm_out.MAX_SYMBOLS - 1 : 0];
    
    assign count_ones[0] = 0;
    assign count_ones[1] = ones_lut[current_map[0]];
    assign count_ones[2] = ones_lut[current_map[1 : 0]];
    assign count_ones[3] = ones_lut[current_map[2 : 0]];
    assign fdm_out.samples_rdy = (samples_out_rdy) ? (template_active ? ones_lut[current_map] : 0) : 0;
    assign bram_syncw_out.fifo_rdy = samples_out_rdy;
    assign bram_temp_out.fifo_rdy = samples_out_rdy;
    assign sync_word_active = bram_syncw_out.fifo_valid;
    assign template_active = bram_temp_out.fifo_valid;
    assign current_map = (template_active) ? bram_temp_out.fifo_data[bram_temp_out.WIDTH - 1 : bram_temp_out.WIDTH - fdm_out.MAX_SYMBOLS]
                                            : {fdm_out.MAX_SYMBOLS{1'b0}};
    assign test = fdm_out.samples_rdy;
    for( i = 0; i < fdm_out.MAX_SYMBOLS; i++) begin
        always@(posedge clk) begin
            if(!resetn) 
                samples_out_valid <= 0;
            if(samples_out_rdy) begin
                if (template_active & fdm_out.samples_valid >= fdm_out.samples_rdy)  begin
                    samples_out_valid <= 1;
                    samples_out[i] <= (current_map[i]) ? fdm_out.samples[count_ones[i]] : 
                                                        bram_temp_out.fifo_data[i * 32 +: 32];
                end
                else if(sync_word_active) begin
                    samples_out[i] <= bram_syncw_out.fifo_data[i * 32 +: 32];
                    samples_out_valid <= 1;
                end
                else
                    samples_out_valid <= 0;
            end
            else
                samples_out_valid <= 0;
        end
    end
    
endmodule
