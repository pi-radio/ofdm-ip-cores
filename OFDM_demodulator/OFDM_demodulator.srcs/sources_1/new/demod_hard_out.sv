`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/02/2023 11:40:40 AM
// Design Name: 
// Module Name: demod_hard_out
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


module demod_hard_out
        import demodulator_package::*;
        #(
        parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 32)
		(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output logic  s00_axis_tready,
		input logic [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input logic  s00_axis_tlast,
		input logic  s00_axis_tvalid,

		output logic  out_hard_axis_tvalid,
		output logic [C_M00_AXIS_TDATA_WIDTH-1 : 0] out_hard_axis_tdata,
		output logic  out_hard_axis_tlast,
		input logic  out_hard_axis_tready,
		mod_t modulation
    );
	reg [4 : 0] bits_per_mod [0 : 4];
	reg signed [15 : 0] mods[0 : 4][0 : 31];
	reg [4 : 0] step_counter = 0;
	reg [10 : 0] valid_counter = 0;
	reg [3 : 0] i;
	reg [9 : 0] j;
	wire signed [15 : 0] real_input [0 : 3];
	wire signed [15 : 0] imag_input [0 : 3];
	reg [C_M00_AXIS_TDATA_WIDTH - 1 : 0] out_regs[0 : 1];
	reg current_out_idx = 0;
	genvar k, l;
	genvar ii;
	
	assign s00_axis_tready = out_hard_axis_tready;
	assign out_hard_axis_tdata = out_regs[!current_out_idx];

	generate 
	   for(ii = 0; ii < 4; ii = ii + 1) begin
	       assign real_input[ii] = s00_axis_tdata[ii * 32 +: 16];
	       assign imag_input[ii] = s00_axis_tdata[((ii + 1) * 32) - 16 +: 16];
	   end
	endgenerate
	
	always@(posedge axis_aclk) begin
	   if(~axis_aresetn) begin
	       step_counter <= 0;
	       out_hard_axis_tvalid <= 0;
	       valid_counter <= 0;
	       out_hard_axis_tlast <= 0;
	   end
	   else begin
	       if(s00_axis_tvalid) begin
	           case(modulation)
	               BPSK: begin
	                   step_counter <= step_counter + 4;
	                   if(step_counter == 28) begin
	                       valid_counter <= valid_counter + 1;
	                       out_hard_axis_tvalid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           out_hard_axis_tlast <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QPSK: begin
	                   step_counter <= step_counter + 8;
	                   if(step_counter == 24) begin
	                       valid_counter <= valid_counter + 1;
	                       out_hard_axis_tvalid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 359) begin
	                           out_hard_axis_tlast <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QAM16: begin
	                   step_counter <= step_counter + 16;
	                   if(step_counter == 16) begin
	                       valid_counter <= valid_counter + 1;
	                       out_hard_axis_tvalid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           out_hard_axis_tlast <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QAM64: begin
	                   step_counter <= step_counter + 24;
	                   if(step_counter + 24 > 32) begin
	                       valid_counter <= valid_counter + 1;
	                       out_hard_axis_tvalid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           out_hard_axis_tlast <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QAM256: begin
	                   step_counter <= step_counter + 32;
	                   valid_counter <= valid_counter + 1;
                       out_hard_axis_tvalid <= 1;
                       current_out_idx <= ~current_out_idx;
                       if(valid_counter == 179) begin
                           out_hard_axis_tlast <= 1;
                           valid_counter <= 0;
                       end
	               end
	           endcase
	       end
           if(out_hard_axis_tvalid && !(modulation == QAM256)) begin
               out_hard_axis_tvalid <= 0;
               if(out_hard_axis_tlast)
                   out_hard_axis_tlast <= 0;
           end
	   end
	end
	
	always@(posedge axis_aclk) begin
	   if(s00_axis_tvalid) begin
           for(i = 0; i < 4; i = i + 1) begin
               case(modulation) 
                   BPSK: begin
                       out_regs[current_out_idx][step_counter + i] <= (real_input[i] >= 0) ? 1 : 0;
                   end
                   QPSK: begin
                       out_regs[current_out_idx][step_counter + (2 * i) +: 2] <= (real_input[i] > 0) ? 
                                                   ((imag_input[i] > 0) ? 2'b11 : 2'b01) :
                                                   ((imag_input[i] > 0) ? 2'b10 : 2'b00);
                   end
               endcase
           end
	   end
	end    
endmodule
