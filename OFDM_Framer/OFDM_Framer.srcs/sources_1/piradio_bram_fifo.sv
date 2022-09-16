import piradio_ofdm::*;

module piradio_bram_fifo(
        input wire clk,
        input wire resetn,
        input wire enable,
        bram_fifo_in_iface.master bram_fifo_in,
        bram_fifo_out_iface.master bram_fifo_out
    );
    
    localparam CACHE_DEPTH = 4;
    
    logic [CACHE_DEPTH* bram_fifo_out.WIDTH-1:0] cache_shift_reg;
    logic [CACHE_DEPTH-1:0] cache_last;
    
    logic [$clog2(CACHE_DEPTH):0] cache_valid_cnt;
    logic [bram_fifo_in.BRAM_LATENCY-1:0] inflight_cnt;
    
    
    logic [bram_fifo_in.BRAM_LATENCY-1:0] bram_valid;
    logic [bram_fifo_in.BRAM_LATENCY-1:0] bram_last;
    
    assign bram_fifo_out.fifo_data = cache_shift_reg[bram_fifo_out.WIDTH-1:0];
    assign bram_fifo_out.fifo_last = cache_last[0];
    
    always @(posedge clk)
    begin
        if (~resetn) begin
            bram_valid <= {bram_fifo_in.BRAM_LATENCY{1'b0}};
            bram_last <= {bram_fifo_in.BRAM_LATENCY{1'b0}};
        end else begin
            bram_valid <= { bram_fifo_in.bram_rd_en, bram_valid[bram_fifo_in.BRAM_LATENCY-1:1] };
            bram_last <= { bram_fifo_in.bram_addr == {bram_fifo_in.BRAM_ADDR_WIDTH{1'b1}} - bram_fifo_in.N_BEFORE_LAST,
                                 bram_last[bram_fifo_in.BRAM_LATENCY-1:1] };
        end
    end
    
    assign bram_fifo_in.bram_rd_en = ((cache_valid_cnt + inflight_cnt) < CACHE_DEPTH) && bram_fifo_out.fifo_rdy && enable;

    always @(posedge clk)
    begin
        if (~resetn) begin
            bram_fifo_in.bram_addr <= 0;
        end else if (bram_fifo_in.bram_rd_en) begin
            bram_fifo_in.bram_addr <= bram_fifo_in.bram_addr + 1;
        end
    end

    assign bram_fifo_out.fifo_valid = cache_valid_cnt > 0; 
    
    logic [$clog2(CACHE_DEPTH):0] next_cache_valid_cnt;
    logic [bram_fifo_in.BRAM_LATENCY-1:0] next_inflight_cnt;
    logic [CACHE_DEPTH* bram_fifo_in.WIDTH-1:0] next_cache_shift_reg;
    logic [CACHE_DEPTH-1:0] next_cache_last;
    
    always @(posedge clk)
    begin
        if (~resetn) begin
            inflight_cnt <= 0;            
            cache_valid_cnt <= 0;
            cache_shift_reg <= 0;
            cache_last <= 0;
        end else begin
            next_cache_valid_cnt = cache_valid_cnt;
            next_inflight_cnt = inflight_cnt;
            next_cache_shift_reg = cache_shift_reg;
            next_cache_last = cache_last;
            
            if (bram_fifo_in.bram_rd_en) begin
                next_inflight_cnt += 1;            
            end
        
            if (bram_fifo_out.fifo_valid & bram_fifo_out.fifo_rdy) begin
                next_cache_valid_cnt -= 1;
                next_cache_shift_reg = next_cache_shift_reg >> bram_fifo_out.WIDTH;
                next_cache_last = next_cache_last >> 1;
            end
            
            if (bram_valid[0]) begin
                next_inflight_cnt = next_inflight_cnt - 1;
                next_cache_shift_reg[next_cache_valid_cnt* bram_fifo_out.WIDTH +: bram_fifo_out.WIDTH] = bram_fifo_in.bram_data;
                next_cache_last[next_cache_valid_cnt] = bram_last[0];
                next_cache_valid_cnt += 1;
            end
            
            cache_valid_cnt <= next_cache_valid_cnt;
            inflight_cnt <= next_inflight_cnt;
            cache_shift_reg <= next_cache_shift_reg;
            cache_last <= next_cache_last;
        end
    end
endmodule