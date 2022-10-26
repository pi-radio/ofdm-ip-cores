`timescale 1ns / 1ps

import demodulator_package::*;
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/04/2022 05:33:24 PM
// Design Name: 
// Module Name: demodulator
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


module demodulator #(
        parameter integer C_M00_AXIS_TDATA_WIDTH = 32,
        parameter integer C_S00_AXIS_TDATA_WIDTH = 128
    )(
        input logic clk,
        input logic aresetn,
        input logic m_ready,
        output logic m_valid,
        output logic [C_M00_AXIS_TDATA_WIDTH - 1 : 0] m_data,
        output logic m_last,
        input logic s_valid,
        output logic s_ready,
        input logic [C_S00_AXIS_TDATA_WIDTH - 1 : 0] s_data,
        mod_t modulation
    );

	reg [4 : 0] bits_per_mod [0 : 4];
	reg signed [15 : 0] mods[0 : 4][0 : 31];
	reg [4 : 0] step_counter = 0;
	reg [7 : 0] valid_counter = 0;
	reg [3 : 0] i;
	reg [9 : 0] j;
	wire signed [15 : 0] real_input [0 : 3];
	wire signed [15 : 0] imag_input [0 : 3];
	reg [C_M00_AXIS_TDATA_WIDTH - 1 : 0] out_regs[0 : 1];
	reg current_out_idx = 0;
	wire [33 : 0] distances_qam16[0 : 15][0 : 3];
	wire [3 : 0] min_index_qam16_l1[0 : 3][0 : 3];
	wire [3 : 0] min_index_qam16_l2[0 : 3];
	wire [33 : 0] min_value_qam16_l1[0 : 3][0 : 3];
	wire [33 : 0] min_value_qam16_l2[0 : 3];
	genvar k, l;
	genvar ii;
	
	assign s_ready = m_ready;
	assign m_data = out_regs[!current_out_idx];

	generate 
	   for(ii = 0; ii < 4; ii = ii + 1) begin
	       assign real_input[ii] = s_data[ii * 32 +: 16];
	       assign imag_input[ii] = s_data[((ii + 1) * 32) - 16 +: 16];
	   end
	endgenerate
	
	/* Create arrays with constellation points for each modulation */
    always@(posedge clk) begin
        if(~aresetn) begin
            bits_per_mod = '{1,2,4,6,8};
            mods = '{'{16'h0000,16'hc000, 16'h0000,16'h3fff, 16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00
                        ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00, 16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00
                        ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00},
                        '{16'hc000,16'hc000, 16'hc000,16'h3fff,
                         16'h3fff, 16'hc000, 16'h3fff, 16'h3fff,16'h00, 16'h00
                        ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00, 16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00
                        ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00},
                         '{16'h3fff, 16'hc000, 16'h3fff, 16'heaaa, 16'h3fff, 16'h3fff, 16'h3fff, 16'h1555,
                            16'h1555, 16'hc000, 16'h1555, 16'heaaa, 16'h1555, 16'h3fff, 16'h1555, 16'h1555,
                            16'hc000, 16'hc000, 16'hc000, 16'heaaa, 16'hc000, 16'h3fff, 16'hc000, 16'h1555,
                            16'heaaa, 16'hc000, 16'heaaa, 16'heaaa, 16'heaaa, 16'h3fff, 16'heaaa, 16'h1555},
                         '{16'h00,16'h00,16'h0000c000, 16'h00003fff,16'h00, 16'h00,16'h00, 16'h00
                         ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,
                         16'h00,16'h00,16'h0000c000, 16'h00003fff,16'h00, 16'h00,16'h00, 16'h00
                         ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00},
                         '{16'h00,16'h00,16'h0000c000, 16'h00003fff,16'h00, 16'h00,16'h00, 16'h00
                         ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,
                         16'h00,16'h00,16'h0000c000, 16'h00003fff,16'h00, 16'h00,16'h00, 16'h00
                         ,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00,16'h00, 16'h00}};
        end
    end
	
	always@(posedge clk) begin
	   if(~aresetn) begin
	       step_counter <= 0;
	       m_valid <= 0;
	       valid_counter <= 0;
	       m_last <= 0;
	   end
	   else begin
	       if(s_valid && m_ready) begin
	           case(modulation)
	               BPSK: begin
	                   step_counter <= step_counter + 4;
	                   if(step_counter == 28) begin
	                       valid_counter <= valid_counter + 1;
	                       m_valid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           m_last <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QPSK: begin
	                   step_counter <= step_counter + 8;
	                   if(step_counter == 24) begin
	                       valid_counter <= valid_counter + 1;
	                       m_valid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           m_last <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QAM16: begin
	                   step_counter <= step_counter + 16;
	                   if(step_counter == 16) begin
	                       valid_counter <= valid_counter + 1;
	                       m_valid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           m_last <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QAM64: begin
	                   step_counter <= step_counter + 24;
	                   if(step_counter + 24 > 32) begin
	                       valid_counter <= valid_counter + 1;
	                       m_valid <= 1;
	                       current_out_idx <= ~current_out_idx;
	                       if(valid_counter == 179) begin
	                           m_last <= 1;
	                           valid_counter <= 0;
	                       end
	                   end
	               end
	               QAM256: begin
	                   step_counter <= step_counter + 32;
	                   valid_counter <= valid_counter + 1;
                       m_valid <= 1;
                       current_out_idx <= ~current_out_idx;
                       if(valid_counter == 179) begin
                           m_last <= 1;
                           valid_counter <= 0;
                       end
	               end
	           endcase
	       end
           if(m_valid && m_ready && !(modulation == QAM256)) begin
               m_valid <= 0;
               if(m_last)
                   m_last <= 0;
           end
	   end
	end

	generate
	   for(l = 0; l < 4 ; l = l + 1) begin
	       for(k = 0; k < 32; k = k + 2) begin
	           assign distances_qam16[k/2][l] = (real_input[l] - mods[modulation][k + 1]) * (real_input[l] - mods[modulation][k + 1]) +
	                               (imag_input[l] - mods[modulation][k]) * (imag_input[l] - mods[modulation][k]);
	       end
	   end
	endgenerate
	
	generate
	   for(l = 0; l < 4 ; l = l + 1) begin
	       for( k = 0; k < 16; k = k + 4) begin
	           compare4 cmp4(distances_qam16[k][l],
	                          distances_qam16[k + 1][l],
	                          distances_qam16[k + 2][l],
	                          distances_qam16[k + 3][l],
	                          k, k +1, k + 2, k + 3,
	                          min_index_qam16_l1[k/4][l],
	                          min_value_qam16_l1[k/4][l]);
	       end
	   end
	endgenerate
	
	generate
	   for(l = 0; l < 4 ; l = l + 1) begin
	       compare4 cmp4_qam16(min_value_qam16_l1[0][l],
	                          min_value_qam16_l1[1][l],
	                          min_value_qam16_l1[2][l],
	                          min_value_qam16_l1[3][l],
	                          min_index_qam16_l1[0][l],
	                          min_index_qam16_l1[1][l],
	                          min_index_qam16_l1[2][l],
	                          min_index_qam16_l1[3][l],
	                          min_index_qam16_l2[l],
	                          min_value_qam16_l2[l]);
	   end
	endgenerate
	
	always@(posedge clk) begin
	   if(s_valid && s_ready) begin
           for(i = 0; i < 4; i = i + 1) begin
               case(modulation) 
                   BPSK: begin
                       out_regs[current_out_idx][step_counter + i] <= (real_input[i] > 0) ? 1 : 0;
                   end
                   QPSK: begin
                       out_regs[current_out_idx][step_counter + (2 * i) +: 2] <= (real_input[i] > 0) ? 
                                                   ((imag_input[i] > 0) ? 2'b11 : 2'b01) :
                                                   ((imag_input[i] > 0) ? 2'b10 : 2'b00);
                   end
                   QAM16: begin
                        for(j = 0; j < 16; j = j + 1) begin
                            if((imag_input[i] == mods[2][j * 2]) && (real_input[i] == mods[2][j * 2 + 1])) begin
                                out_regs[current_out_idx][step_counter + (4 * i) +: 4] <= j;
                            end
                        end
                   end
               endcase
           end
	   end
	end
endmodule
