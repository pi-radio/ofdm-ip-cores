`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/18/2022 03:23:52 PM
// Design Name: 
// Module Name: pilot_zero_remover
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module pilot_zero_remover(
    	input wire  axis_aclk,
		input wire  axis_aresetn,
		output wire  s00_axis_tready,
		input wire [127 : 0] s00_axis_tdata,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid,

		output reg  m00_axis_tvalid,
		output wire [127 : 0] m00_axis_tdata,
		output wire  m00_axis_tlast,
		input wire  m00_axis_tready,
	    
	    output reg  m00_axis_log_tvalid,
		output wire [127 : 0] m00_axis_log_tdata,
		output wire  m00_axis_log_tlast,
		input wire  m00_axis_log_tready
    );
    const logic [2 : 0] ones_lut [0 : 15] = '{0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4};
    
    function [0 : 0] is_valid;
        input [9 : 0] index;
        begin
            is_valid = (index > 110 && index < 913 && index != 511 && index != 512) &&
                (((index < 511) && ((index - 1) % 5 != 0)) || ((index > 512) && ((index - 3) % 5 != 0)));
        end
    
    endfunction
    
    reg [127 : 0] out_fifo[0 : 1];
    reg out_index = 0;
    reg [9 : 0] counter = 0;
    wire [3 : 0] in_valid;
    wire [3 : 0] count_valids[0 : 3];
    reg [2 : 0] samples_consumed = 0;
    reg [2 : 0] new_samples_consumed = 0;
    reg [3 : 0] in_here;
    genvar i;
    
    assign in_valid[0] = is_valid(counter);
    assign in_valid[1] = is_valid(counter + 1);
    assign in_valid[2] = is_valid(counter + 2);
    assign in_valid[3] = is_valid(counter + 3);
    
    assign count_valids[0] = 0;
    assign count_valids[1] = ones_lut[in_valid[0]];
    assign count_valids[2] = ones_lut[in_valid[1 : 0]];
    assign count_valids[3] = ones_lut[in_valid[2 : 0]];
    
    assign m00_axis_log_tdata[3 : 0] = in_valid;
    assign m00_axis_log_tdata[13 : 4] = counter;
    assign m00_axis_log_tdata[14] = out_index;
    assign m00_axis_log_tdata[17 : 15] = samples_consumed;
    assign m00_axis_log_tdata[21 : 18] = in_here;
    
    always @(posedge axis_aclk) begin
        if(!axis_aresetn)
            counter <= 0;
        else begin
            if(s00_axis_tready && s00_axis_tvalid)
                counter <= counter + 4;
        end
    end
    
    reg[127 : 0] interm_buff [0 : 1];
    reg [2 : 0] interm_consumed = 0;
    reg new_out_index;
    reg new_valid;
    reg [3 : 0] in_here_temp = 0;
    reg [3 : 0] store_ic [0 : 3];
    reg [3 : 0] ic [0 : 3] = {0, 0, 0, 0};
        always@(posedge axis_aclk) begin
            if(!axis_aresetn) begin
                m00_axis_tvalid <= 0;
                out_fifo[0] <= 0;
                out_fifo[1] <= 0;
            end
            else begin
            if(s00_axis_tready && s00_axis_tvalid) begin
                in_here_temp = in_here;
                interm_consumed = samples_consumed;
                store_ic = ic;
                new_out_index = out_index;
                new_valid = m00_axis_tvalid;
                interm_buff[0] = out_fifo[0];
                interm_buff[1] = out_fifo[1];
                if(in_valid[0]) begin
                    in_here_temp[0] = 1;
                    interm_buff[new_out_index] = {s00_axis_tdata[ 0 +: 32], interm_buff[new_out_index][32 +: 96]};
                    interm_consumed = interm_consumed + 1;
                    store_ic[0] = interm_consumed;
                    if((interm_consumed / 4) != (samples_consumed / 4) && (new_out_index == out_index)) begin
                        new_out_index = !new_out_index;
                    end
                end
                else
                    in_here_temp[0] = 0;
                if(in_valid[1]) begin
                    in_here_temp[1] = 1;
                    interm_buff[new_out_index] = {s00_axis_tdata[32 +: 32], interm_buff[new_out_index][32 +: 96]};
                    interm_consumed = interm_consumed + 1;
                    store_ic[1] = interm_consumed;
                    if(((interm_consumed / 4) != (samples_consumed / 4)) && (new_out_index == out_index)) begin
                        new_out_index = !new_out_index;
                    end
                end
                else
                    in_here_temp[1] = 0;
                if(in_valid[2]) begin
                    in_here_temp[2] = 1;
                    interm_buff[new_out_index]  = {s00_axis_tdata[ 64 +: 32], interm_buff[new_out_index][32 +: 96]};
                    interm_consumed = interm_consumed + 1;
                    store_ic[2] = interm_consumed;
                    if((interm_consumed / 4) != (samples_consumed / 4)&& (new_out_index == out_index)) begin
                        new_out_index = !new_out_index;
                    end
                end
                else
                    in_here_temp[2] = 0;
                if(in_valid[3]) begin
                    in_here_temp[3] = 1;
                    interm_buff[new_out_index] = {s00_axis_tdata[96 +: 32], interm_buff[new_out_index][32 +: 96]};
                    interm_consumed = interm_consumed + 1;
                    store_ic[3] = interm_consumed;
                    if((interm_consumed / 4) != (samples_consumed / 4) && (new_out_index == out_index)) begin
                        new_out_index = !new_out_index;
                    end
                end
                else
                    in_here_temp[3] = 0;
                if(new_out_index != out_index) begin
                    new_valid = 1;
                end
                else begin
                    new_valid = 0;
                end
                samples_consumed <= interm_consumed;
                out_index <= new_out_index;
                out_fifo[0] <= interm_buff[0];
                out_fifo[1] <= interm_buff[1];
                m00_axis_tvalid <= new_valid;
                in_here <= in_here_temp;
                ic <= store_ic;
             end
             end
        end
    
    assign m00_axis_log_tdata[25 : 22] = ic[0];
    assign m00_axis_log_tdata[29 : 26] = ic[1];
    assign m00_axis_log_tdata[33 : 30] = ic[2];
    assign m00_axis_log_tdata[37 : 34] = ic[3];
    assign s00_axis_tready = m00_axis_tready;
    assign m00_axis_tdata = out_fifo[!out_index];
    
endmodule
