`timescale 1ns / 1ps
import piradio_ofdm::*;

module bram_fifo_tb(

    );
    localparam BRAM_ADDR_WIDTH = 8;
    localparam S_AXIS_TDATA_WIDTH = 32;
    localparam TOTAL_CARRIERS = 1024;
    localparam OUT_WIDTH = 128;
    localparam MAP_WIDTH = 4;
    logic clk = 0;
    logic rstn = 0;
    logic enable;
    logic restart;
    logic [BRAM_ADDR_WIDTH-1:0] bram_addr;
    logic [OUT_WIDTH-1:0] bram_data;
    logic bram_rd_en;
    
    logic [OUT_WIDTH-1:0] fifo_data;
    logic fifo_valid;
    logic fifo_last;
    logic fifo_rdy;
    logic  s_axis_config_aclk;
	logic  s_axis_config_aresetn;
	logic  s_axis_config_tready;
	logic [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_config_tdata;
	logic [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_config_tstrb;
	logic  s_axis_config_tlast;
	logic  s_axis_config_tvalid;
	logic [$clog2(TOTAL_CARRIERS / 4) - 1 : 0] bram_syncw_addr;
	logic [$clog2(TOTAL_CARRIERS / 4) - 1 : 0] bram_temp_addr;
	logic [OUT_WIDTH - 1 : 0] syncw_dout;
	logic [(OUT_WIDTH + MAP_WIDTH) - 1 : 0] temp_dout;
	logic syncw_out_en;
	logic temp_out_en;
	logic structs_ready;
	logic [31 : 0] template [0 : 1023];
	logic [31 : 0] map[0 : 31];
	logic [20 : 0] sw_counter = 0;
    state_tb_t state = TB_IDLE;
    logic ready = 1;
    logic enable = 0;
    initial begin
        forever #5 clk = ~clk;
    end

    localparam INPUT_SAMPLES = 2048;
    logic [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
    assign template = input_samples[1024 : 2047];
    initial begin
        $readmemh("../../../../../OFDM_Framer.srcs/sim_1/new/output.txt", input_samples, 0, INPUT_SAMPLES - 1);
    end 
    initial begin
        $readmemh("../../../../../OFDM_Framer.srcs/sim_1/new/map.txt", map, 0, 31);
    end
    
    assign s_axis_config_tvalid = ((state == TB_SYNC_WORD)) || (state == TB_TEMPLATE) || (state == TB_MAP);
    assign s_axis_config_tdata = (state == TB_SYNC_WORD) ? input_samples[sw_counter] :
                                  (state == TB_TEMPLATE) ? template[sw_counter]:
                                  (state == TB_MAP) ? ((map[sw_counter / 32] & (1 << sw_counter % 32))
                                                 ? {31'h0000000, 1'b1} : 32'h00000000) : 32'h00000000 ;
    always@ (posedge clk) begin
      if(s_axis_config_tready && rstn) begin
        if(s_axis_config_tlast) s_axis_config_tlast <= 0;
        case(state) 
            TB_IDLE: begin
                state <= TB_SYNC_WORD;
            end
            TB_SYNC_WORD: begin
                if(sw_counter <= 1023) begin
                    if(sw_counter == 1023) begin
                        state <= TB_TEMPLATE;
                        sw_counter <= 0;
                    end
                    else if(sw_counter == 1022) begin
                        s_axis_config_tlast <= 1;
                        sw_counter <= sw_counter + 1;
                    end
                    else
                        sw_counter <= sw_counter + 1;
                end 
            end
            TB_TEMPLATE: begin
                state <= TB_MAP;
                if(sw_counter == TOTAL_CARRIERS - 1) s_axis_config_tlast <= 1;
            end
            TB_MAP: begin
                if(sw_counter < TOTAL_CARRIERS - 1) begin
                    sw_counter <= sw_counter + 1;
                    state <= TB_TEMPLATE;
                end
                else begin
                    state <= TB_FIN;
                    sw_counter <= 0;
                end
            end
        endcase
      end
    end
    
	sync_word_module sync_word_mod_inst (
        .s_axis_config_aclk(clk),
		.s_axis_config_aresetn(rstn),
		.s_axis_config_tready(s_axis_config_tready),
		.s_axis_config_tdata(s_axis_config_tdata),
		.s_axis_config_tstrb(s_axis_config_tstrb),
		.s_axis_config_tlast(s_axis_config_tlast),
		.s_axis_config_tvalid(s_axis_config_tvalid),
		.bram_syncw_addr(bram_addr),
		.bram_temp_addr(bram_temp_addr),
		.syncw_dout(bram_data),
		.temp_dout(temp_dout),
		.syncw_out_en(bram_rd_en),
		.temp_out_en(temp_out_en),
		.structs_ready(structs_ready)
       );
        
    piradio_bram_fifo #(
        .WIDTH(128),
        .BRAM_DEPTH(256)
    )dut
    (
        .clk(clk),
        .rstn(rstn),
        .enable(enable),
        .restart(0),
        .bram_addr(bram_addr),
        .bram_data(bram_data),
        .bram_rd_en(bram_rd_en),
        
        .fifo_data(fifo_data),
        .fifo_valid(fifo_valid),
        .fifo_last(fifo_last),
        .fifo_rdy(structs_ready && ready)
    );
    
    always@(posedge clk)
        if(fifo_last) enable <= 0;
    
    initial begin
        enable <= 0;
        #1000
        @(posedge clk)
        rstn <= 1;
        #61000
        @(posedge clk)
        enable <= 1;
        
    end
endmodule
