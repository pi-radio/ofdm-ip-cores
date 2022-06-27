`timescale 1ns / 1ps

module data_module #
        (
        parameter integer SYMBOLS_PER_FRAME = 10,
        parameter integer USED_CARRIERS = 800,
        parameter integer PILOT_DENSITY = 5,
        parameter integer M_AXIS_TDATA_WIDTH = 1024,
        parameter integer S_AXIS_TDATA_WIDTH = 32
        )
        (
    	input wire  s_axis_data_aclk,
		input wire  s_axis_data_aresetn,
		output wire  s_axis_data_tready,
		input wire [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_data_tdata,
		input wire [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_data_tstrb,
		input wire  s_axis_data_tlast,
		input wire  s_axis_data_tvalid,
        input wire [799 : 0] sync_word,
        input wire sync_word_ready,
		output wire  m_axis_data_tvalid,
		output wire [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output reg [M_AXIS_TDATA_WIDTH-1 : 0] m_axis_data_tstrb,
		output wire  m_axis_data_tlast,
		input wire  m_axis_data_tready
    );
    reg [9 : 0] symbol_cnt = 0;
    reg[7 : 0] bit_index;
    reg[9 : 0] plt_index;
    wire state_sync_word;
    reg [USED_CARRIERS - 1 : 0] current_symbol;
    reg [1023 : 0] sync_word_symbol;
    reg [9 : 0] index = 0;
    reg data_valid = 0;
    localparam step = (S_AXIS_TDATA_WIDTH/ 8) * 10;
    
    assign m_axis_data_tdata = (state_sync_word) ? sync_word_symbol
                                                 :  ((data_valid) ? {111'h0000000, current_symbol[USED_CARRIERS-1 : 400],
                                                    2'b00, current_symbol[399 : 0], 111'h0000000} : m_axis_data_tdata);
    assign s_axis_data_tready = (m_axis_data_tready && sync_word_ready);
    assign m_axis_data_tvalid = (state_sync_word && s_axis_data_tvalid && sync_word_ready) || data_valid;
    assign state_sync_word = (symbol_cnt == 0);
    
    always@(*) begin
        if(~s_axis_data_aresetn) begin
            sync_word_symbol <= 1024'h0000;
        end
        else begin
            if(sync_word_ready) begin
                sync_word_symbol[510 : 111] <= sync_word[399 : 0];
                sync_word_symbol[912 : 513] <= sync_word[799 : 400];
            end     
        end
    end
    
    always@(posedge s_axis_data_aclk) begin
        if(~s_axis_data_aresetn) begin
            current_symbol <= 800'h0000;
            index <= 0;
            for(plt_index=0; plt_index < USED_CARRIERS ; plt_index=plt_index + PILOT_DENSITY) begin
                if(plt_index % (2 * PILOT_DENSITY) == 0)
                    current_symbol[plt_index] <= 1;
                else if(plt_index % (2 * PILOT_DENSITY) == PILOT_DENSITY)
                    current_symbol[plt_index] <= 0;
            end  
        end
        else begin
            if(s_axis_data_tready && s_axis_data_tvalid) begin
                if(data_valid)
                    data_valid <= 0;
                if(index < USED_CARRIERS - step)
                    index <= index + step;
                else begin
                    index <= 0;
                    data_valid <= 1;
                end
                for(bit_index=0; bit_index < step; bit_index=bit_index +  PILOT_DENSITY) begin
                    current_symbol[index + bit_index + 1 +: 4] <= s_axis_data_tdata[bit_index - bit_index/PILOT_DENSITY +: 4];
                end
            end
            else if(!s_axis_data_tvalid && m_axis_data_tready)
                if(index == USED_CARRIERS - step)
                    index <= 0;
                if(data_valid)
                    data_valid <= 0;
        end
    end
    
    always@(posedge s_axis_data_aclk) begin
        if(!s_axis_data_aresetn)
            symbol_cnt <= 0;
        else begin
            if(m_axis_data_tvalid)
                if(symbol_cnt < SYMBOLS_PER_FRAME - 1)
                    symbol_cnt <= symbol_cnt + 1;
                else
                    symbol_cnt <= 0;
        end
    end
     
endmodule
