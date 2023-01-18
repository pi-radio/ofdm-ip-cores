`timescale 1ns / 1ps


module symbol_start_detect(
        input wire clk,
        input wire resetn,
        max_cmpt2peak_det_iface.slave max_cmpt2peak_det
    );
    peak_det2sym_start_iface peak_det2sym_start();
    peak_detect peak_detect_inst(
        .*,
        .max_cmpt2peak_det(max_cmpt2peak_det),
        .peak_det2sym_start(peak_det2sym_start)
    );
    
    
endmodule

module peak_detect(
    input wire clk,
    input wire resetn,
    max_cmpt2peak_det_iface.slave max_cmpt2peak_det,
    peak_det2sym_start_iface.master peak_det2sym_start
    );
    
    logic [max_cmpt2peak_det.SAMPLE_WIDTH - 1 : 0] symbol_max_mag;
    logic [$clog2(max_cmpt2peak_det.SSR) - 1 : 0] symbol_max_idx;
    logic [10 : 0] sample_cntr;
    
    always @(posedge clk) peak_det2sym_start.samples_valid <= max_cmpt2peak_det.max_valid;
    
    always @(posedge clk) begin
        if(!resetn) begin
            sample_cntr <= 0;
            symbol_max_mag <= 0;
            symbol_max_idx <= 0;
        end
        else begin
            if(max_cmpt2peak_det.max_valid) begin
                if(max_cmpt2peak_det.max_last) begin
                    peak_det2sym_start.symbol_last <= 1;
                    if(max_cmpt2peak_det.max_mag > symbol_max_mag) begin
                        peak_det2sym_start.max_idx <= sample_cntr;
                        peak_det2sym_start.ssr_idx <= max_cmpt2peak_det.max_idx;
                        peak_det2sym_start.idx_valid <= 1;
                    end
                    else if(symbol_max_mag > 0) peak_det2sym_start.idx_valid <= 1;
                    else peak_det2sym_start.idx_valid <= 0;
                        
                    symbol_max_mag <= 0;
                    symbol_max_idx <= 0;
                    sample_cntr <= 0;
                end
                else begin
                   if(max_cmpt2peak_det.max_valid) begin
                        peak_det2sym_start.symbol_last <= 0;
                        if(max_cmpt2peak_det.max_mag > symbol_max_mag) begin
                            symbol_max_mag <= max_cmpt2peak_det.max_mag;
                            symbol_max_idx <= max_cmpt2peak_det.max_idx;
                            peak_det2sym_start.max_idx <= sample_cntr;
                            peak_det2sym_start.ssr_idx <= max_cmpt2peak_det.max_idx;
                        end
                    end
                    sample_cntr <= sample_cntr + 1;
                    peak_det2sym_start.idx_valid <= 0;
                end
            end
        end 
    end
endmodule

module symbol_start_det(
    input wire clk,
    input wire resetn,
    peak_det2sym_start_iface.slave peak_det2sym_start,
    sym_start2sample_buff_iface.master sym_start2sample_buff 
    );
    
    typedef enum {IDLE, FIRST_SEARCH, SECOND_SEARCH} state_peak_det_t;
    state_peak_det_t state_peak_det;
    logic [10 : 0] max_idx;
    logic [1 : 0] peak_ssr_idx;
    
    logic peak_detected;
    logic correct_peak;
    
    always_comb peak_detected <= peak_det2sym_start.symbol_last && peak_det2sym_start.idx_valid;
    always_comb correct_peak <= peak_det2sym_start.max_idx == max_idx && 
                                                peak_det2sym_start.ssr_id == peak_ssr_idx;
    
    always@(posedge clk) sym_start2sample_buff.start_idx_valid <= 
                        (peak_detected && correct_peak && state_peak_det == SECOND_SEARCH);
    
    always@(posedge clk) begin
        if(!resetn) begin
           max_idx <= 0;
           peak_ssr_idx <= 0;
           state_peak_det <= IDLE;
        end
        else begin
            if(peak_det2sym_start.samples_valid) begin
                case (state_peak_det)
                    IDLE: state_peak_det <= FIRST_SEARCH;
                    FIRST_SEARCH: begin
                        if(peak_detected) begin
                            max_idx <= peak_det2sym_start.max_idx;
                            peak_ssr_idx <= peak_det2sym_start.ssr_idx;
                            state_peak_det <= SECOND_SEARCH;
                        end
                    end
                    SECOND_SEARCH: begin
                        state_peak_det <= FIRST_SEARCH;
                        if(peak_detected && correct_peak) begin
                            sym_start2sample_buff.start_idx <= max_idx;
                            sym_start2sample_buff.ssr_idx <= peak_ssr_idx;
                        end
                    end
                endcase
            end
        end
    end
    
endmodule