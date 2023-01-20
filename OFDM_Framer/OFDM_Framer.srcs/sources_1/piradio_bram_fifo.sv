module piradio_bram_fifo
    import piradio_ofdm::*;
    (
        input wire clk,
        input wire resetn,
        bram_fifo_in_iface.master bram_fifo_in,
        bram_fifo_out_iface.master bram_fifo_out,
        input logic structs_ready
    );
    genvar i;
    
    localparam QUEUE_DEPTH = 4;
    
    logic [bram_fifo_out.WIDTH-1:0] cache_queue[0:QUEUE_DEPTH-1];
    logic cache_last[0:QUEUE_DEPTH-1];
    logic [bram_fifo_in.BRAM_LATENCY-1:0] bram_valid;
    logic [bram_fifo_in.BRAM_LATENCY-1:0] bram_last;
    
    logic do_reset;
    logic do_read;
    logic do_write;
    logic do_advance;
    
    integer cnt;
    integer valid_cnt;
    integer read_ptr, next_read_ptr;
    integer write_ptr, next_write_ptr;

    always_comb bram_fifo_in.bram_rd_en = structs_ready;//resetn;

    /* Reset logic */
    always_comb do_reset = ~resetn || bram_fifo_in.fifo_restart || bram_fifo_out.fifo_restart;
    
    /* Count logic */    
    always @(posedge clk) cnt <= do_reset ? 0 : cnt + (do_read ? -1 : 0) + (do_advance ? 1 : 0);;
    always @(posedge clk) valid_cnt <= do_reset ? 0 : valid_cnt + (do_read ? -1 : 0) + (do_write ? 1 : 0);;

    /* Read logic */        
    always_comb do_read = (valid_cnt > 0) && (~bram_fifo_out.fifo_valid | (bram_fifo_out.fifo_valid & bram_fifo_out.fifo_rdy));
    
    always @(posedge clk) write_ptr <= next_write_ptr;

    always_comb
    begin
        if (do_reset) begin
            next_read_ptr = 0;
        end else if (do_read) begin
            next_read_ptr = (read_ptr + 1) % QUEUE_DEPTH;
        end else begin
            next_read_ptr = read_ptr;
        end
    end
    
    always @(posedge clk) read_ptr <= next_read_ptr;
    
    always @(posedge clk)
    begin
        if (do_reset) begin
            bram_fifo_out.fifo_valid <= 1'b0;
            bram_fifo_out.fifo_data <= 0;
            bram_fifo_out.fifo_last <= 1'b0;
        end else if (do_read) begin
            bram_fifo_out.fifo_valid <= 1'b1;
            bram_fifo_out.fifo_data <= cache_queue[read_ptr];
            bram_fifo_out.fifo_last <= cache_last[read_ptr];
        end else if (bram_fifo_out.fifo_rdy) begin
            bram_fifo_out.fifo_valid <= 1'b0;
        end
    end

    /* Write logic */
    always_comb next_write_ptr = do_reset ? 0 : do_write ? ((write_ptr + 1) % QUEUE_DEPTH) : write_ptr;
    
    always @(posedge clk) write_ptr <= next_write_ptr;
    
    always_comb do_write = bram_valid[0];
    
    for (i = 0; i < QUEUE_DEPTH; i++)
    begin
        always @(posedge clk)
        begin
            if (do_reset) begin
                cache_queue[i] <= 1'b0;
                cache_last[i] <= 1'b0;
            end else if (do_write && write_ptr == i) begin
                cache_queue[i] <= bram_fifo_in.bram_data;
                cache_last[i] <= bram_last[0];
            end
        end
    end
    
    /* Address logic */
    always_comb do_advance = ((cnt < QUEUE_DEPTH) || do_read) && structs_ready;
    
    always @(posedge clk) bram_valid <= do_reset ? 0 : { do_advance, bram_valid[bram_fifo_in.BRAM_LATENCY-1:1] };
    always @(posedge clk) bram_last <= do_reset ? 0 : { bram_fifo_in.bram_addr == {bram_fifo_in.BRAM_ADDR_WIDTH{1'b1}}, bram_last[bram_fifo_in.BRAM_LATENCY-1:1] };
    
    always @(posedge clk)
    begin
        if (do_reset) begin
            bram_fifo_in.bram_addr <= 0;    
        end else if (do_advance) begin
            bram_fifo_in.bram_addr <= bram_fifo_in.bram_addr + 1;
        end
    end   
endmodule