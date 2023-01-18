`timescale 1ns / 1ps


module peak_detector(
        input wire clk,
        input wire resetn,
        axis_iface.slave corr_iface_out,
        frame_det2corr_arbiter_iface.master frame_det2corr_arbiter
    );
    peak_det2frame_det_iface peak_det2frame_det();
    mag_sq2max_cmpt_iface mag_sq2max_cmpt();           
    max_cmpt2peak_det_iface max_cmpt2peak_det();
    
    mag_squared mag_squared_inst1(
        .*,
        .corr_output(corr_iface_out),
        .mag_sq2max_cmpt(mag_sq2max_cmpt)
    );
    
    max_compute max_compute_inst(
        .*,
        .mag_sq2max_cmpt(mag_sq2max_cmpt),
        .max_cmpt2peak_det(max_cmpt2peak_det)
    );
    
    peak_detect peak_detect_inst(
        .*,
        .max_cmpt2peak_det(max_cmpt2peak_det),
        .peak_det2frame_det(peak_det2frame_det)
    );
    
    frame_detect frame_detect_inst(
        .*,
        .peak_det2frame_det(peak_det2frame_det),
        .frame_det2corr_arbiter(frame_det2corr_arbiter)
    );
    
endmodule

/*
    mag_squared
    
    This module compute the magnitude squared of the input samples.
*/
module mag_squared (
    input wire clk,
    input wire resetn,
    axis_iface.slave corr_output,
    mag_sq2max_cmpt_iface.master mag_sq2max_cmpt
);
        logic signed [mag_sq2max_cmpt.CORR_SAMPLE_WIDTH * 2 - 1 : 0] tmp_i_sq; 
        logic signed [mag_sq2max_cmpt.CORR_SAMPLE_WIDTH * 2 - 1 : 0] tmp_q_sq;
        logic signed [mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1 : 0] tmp_i[0 : 3]; 
        logic signed [mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1 : 0] tmp_q[0 : 3];
        genvar l,i;
        
        // Calculates the magnitude squared of the input sample
        function[mag_sq2max_cmpt.CORR_SAMPLE_WIDTH : 0] mag_squared;
           input signed [mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1 : 0] i;
           input signed [mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1 : 0] q;
           begin
               tmp_i_sq = i * i;
               tmp_q_sq = q * q;
               mag_squared = (tmp_i_sq >> (mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1)) + 
                               (tmp_q_sq >> (mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1));
           end
        endfunction 
        
        generate
        for(l = 0 ; l < mag_sq2max_cmpt.SSR ; l = l + 1) begin
           assign tmp_i[l] = corr_output.tdata[(mag_sq2max_cmpt.CORR_COMPLEX_SIZE * l) + mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1 : mag_sq2max_cmpt.CORR_COMPLEX_SIZE * l];
           assign tmp_q[l] = corr_output.tdata[((mag_sq2max_cmpt.CORR_COMPLEX_SIZE * l) + (mag_sq2max_cmpt.CORR_COMPLEX_SIZE / 2)) + mag_sq2max_cmpt.CORR_SAMPLE_WIDTH - 1 :
                                                                            (mag_sq2max_cmpt.CORR_COMPLEX_SIZE * l) + (mag_sq2max_cmpt.CORR_COMPLEX_SIZE / 2)];
        end                                                                     
        endgenerate
        
        for (i = 0; i < mag_sq2max_cmpt.SSR; i++) begin
            always @(posedge clk) begin
                mag_sq2max_cmpt.mag_sq[i] <= mag_squared(tmp_i[i], tmp_q[i]);
            end
        end
        
        always@(posedge clk) mag_sq2max_cmpt.mag_sq_valid <= corr_output.tvalid;
        always@(posedge clk) mag_sq2max_cmpt.mag_sq_last <= corr_output.tlast;
    
endmodule

/*
    max_compute
    
    This module takes as input the magnitude squared of the samples in a SSR sample,
    and finds the maximum magnitude among those SSR complex samples as well as its 
    index in the SSR sample. In the case of piradio SSR = 4 samples per cycle.
*/
module max_compute(
    input wire clk,
    input wire resetn,
    mag_sq2max_cmpt_iface.slave mag_sq2max_cmpt,
    max_cmpt2peak_det_iface.master max_cmpt2peak_det
);
    logic [max_cmpt2peak_det.SAMPLE_WIDTH - 1 : 0] max_tmp[0 : 1];
    logic [$clog2(max_cmpt2peak_det.SSR) - 1 : 0] max_idx_tmp[0 : 1];
    
    /* In order to find the maximum out of the SSR complexes, compare them first
    in pairs, and then compare the two maximum of the pairs */
    genvar k;
	generate
	   for(k = 0; k < 4; k = k + 2) begin
	       comparator c(mag_sq2max_cmpt.mag_sq[k], mag_sq2max_cmpt.mag_sq[k + 1], k, k + 1, 
	           max_tmp[k/2], max_idx_tmp[k/2]);
	   end
	endgenerate
	
	always@(posedge clk) begin
	   if(resetn) begin
           if(max_tmp[0] > max_tmp[1]) begin
               max_cmpt2peak_det.max_mag <= max_tmp[0];
               max_cmpt2peak_det.max_idx <= max_idx_tmp[0];
           end
           else begin
               max_cmpt2peak_det.max_mag <= max_tmp[1];
               max_cmpt2peak_det.max_idx <= max_idx_tmp[1];
           end
	   end
	end
	
	always@(posedge clk) begin
	       max_cmpt2peak_det.max_valid <= mag_sq2max_cmpt.mag_sq_valid;
	       max_cmpt2peak_det.max_last <= mag_sq2max_cmpt.mag_sq_last;
    end
endmodule

module comparator(
    input logic [26:0] a,
    input logic [26:0] b,
    input logic [1 : 0] a_idx,
    input logic [1 : 0] b_idx,
    output logic [26:0] max,
    output logic [1 : 0] max_idx
    );
    
    always@* begin
        if(a > b) begin
            max <= a;
            max_idx <= a_idx;
        end
        else begin
            max <= b;
            max_idx <= b_idx; 
        end
    end
endmodule

/*
    peak_detect

    This module tries to detect a peak inside the space of FFT_SIZE samples that would indicate
    that perhaps a sync word will be detected. If a peak is detected (a maximum value other than 0)
    then when TLAST is asserted in the input stream the computed index of the max value is passed on
    to the next module.
*/

module peak_detect(
    input wire clk,
    input wire resetn,
    max_cmpt2peak_det_iface.slave max_cmpt2peak_det,
    peak_det2frame_det_iface.master peak_det2frame_det
    );
    
    logic [max_cmpt2peak_det.SAMPLE_WIDTH - 1 : 0] symbol_max_mag;
    logic [$clog2(max_cmpt2peak_det.SSR) - 1 : 0] symbol_max_idx;
    logic [10 : 0] sample_cntr;
    
    always @(posedge clk) peak_det2frame_det.samples_valid <= max_cmpt2peak_det.max_valid;
    
    always @(posedge clk) begin
        if(!resetn) begin
            sample_cntr <= 0;
            symbol_max_mag <= 0;
            symbol_max_idx <= 0;
        end
        else begin
            if(max_cmpt2peak_det.max_valid) begin
                if(max_cmpt2peak_det.max_last) begin
                    peak_det2frame_det.symbol_last <= 1;
                    if(max_cmpt2peak_det.max_mag > symbol_max_mag) begin
                        peak_det2frame_det.max_idx <= sample_cntr;
                        peak_det2frame_det.ssr_idx <= max_cmpt2peak_det.max_idx;
                        peak_det2frame_det.idx_valid <= 1;
                    end
                    else if(symbol_max_mag > 0) peak_det2frame_det.idx_valid <= 1;
                    else peak_det2frame_det.idx_valid <= 0;
                        
                    symbol_max_mag <= 0;
                    symbol_max_idx <= 0;
                    sample_cntr <= 0;
                end
                else begin
                   if(max_cmpt2peak_det.max_valid) begin
                        peak_det2frame_det.symbol_last <= 0;
                        if(max_cmpt2peak_det.max_mag > symbol_max_mag) begin
                            symbol_max_mag <= max_cmpt2peak_det.max_mag;
                            symbol_max_idx <= max_cmpt2peak_det.max_idx;
                            peak_det2frame_det.max_idx <= sample_cntr;
                            peak_det2frame_det.ssr_idx <= max_cmpt2peak_det.max_idx;
                        end
                    end
                    sample_cntr <= sample_cntr + 1;
                    peak_det2frame_det.idx_valid <= 0;
                end
            end
        end 
    end
endmodule

/*
    frame_detect
    
    This module takes as input the detected peaks' indexes and decides whether
    there is a sync word present or not. A sync word is present if a peak appears
    at the same index of two consecutive correlator output symbols of size FFT_SIZE.
    For that reason there are two states apart from the IDLE state: The FIRST_SEARCH 
    state searches for the first peak while the SECOND_SEARCH looks for the second.
*/

module frame_detect(
    input wire clk,
    input wire resetn,
    peak_det2frame_det_iface.slave peak_det2frame_det,
    frame_det2corr_arbiter_iface.master frame_det2corr_arbiter
    );
    
    typedef enum {IDLE, FIRST_SEARCH, SECOND_SEARCH} state_peak_det_t;
    state_peak_det_t state_peak_det;
    logic [10 : 0] max_idx;
    logic [1 : 0] peak_ssr_idx;
    
    logic peak_detected;
    logic correct_peak;
    
    always_comb peak_detected <= peak_det2frame_det.symbol_last && peak_det2frame_det.idx_valid;
    always_comb correct_peak <= peak_det2frame_det.max_idx == max_idx && 
                                                peak_det2frame_det.ssr_idx == peak_ssr_idx;
    
    always@(posedge clk) frame_det2corr_arbiter.start_idx_valid <= 
                        (peak_detected && correct_peak && state_peak_det == SECOND_SEARCH);
    always @(posedge clk) frame_det2corr_arbiter.samples_valid <= peak_det2frame_det.samples_valid;
    
    always@(posedge clk) begin
        if(!resetn) begin
           max_idx <= 0;
           peak_ssr_idx <= 0;
           state_peak_det <= IDLE;
        end
        else begin
            if(peak_det2frame_det.samples_valid) begin
                case (state_peak_det)
                    IDLE: state_peak_det <= FIRST_SEARCH;
                    FIRST_SEARCH: begin
                        if(peak_detected) begin
                            max_idx <= peak_det2frame_det.max_idx;
                            peak_ssr_idx <= peak_det2frame_det.ssr_idx;
                            state_peak_det <= SECOND_SEARCH;
                        end
                    end
                    SECOND_SEARCH: begin
                        if(peak_det2frame_det.symbol_last) begin
                            state_peak_det <= FIRST_SEARCH;
                            if(peak_detected && correct_peak) begin
                                frame_det2corr_arbiter.start_idx <= max_idx;
                                frame_det2corr_arbiter.ssr_idx <= peak_ssr_idx;
                                max_idx <= 0;
                                peak_ssr_idx <= 0;
                            end
                        end
                    end
                endcase
            end
        end
    end
    
endmodule