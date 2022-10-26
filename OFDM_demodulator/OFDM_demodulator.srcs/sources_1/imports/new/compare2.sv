`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/17/2022 10:04:51 AM
// Design Name: 
// Module Name: compare2
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


module compare2(
    input wire [26:0] a,
    input wire [26:0] b,
    input wire [26:0] a_idx,
    input wire [26:0] b_idx,
    output reg [26:0] min_index
    );
    
    always@* begin
        if(a < b)
            min_index = a_idx;
        else
           min_index = b_idx;
    end
endmodule
