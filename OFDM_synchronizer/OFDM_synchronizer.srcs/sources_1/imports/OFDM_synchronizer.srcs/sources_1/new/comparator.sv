`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/14/2022 02:38:00 PM
// Design Name: 
// Module Name: comparator
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


module comparator(
    input wire [26:0] a,
    input wire [26:0] b,
    input wire [1 : 0] a_idx,
    input wire [1 : 0] b_idx,
    output reg [26:0] max,
    output reg [1 : 0] max_idx
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
