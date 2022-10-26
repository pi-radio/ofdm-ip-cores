`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/22/2022 01:48:07 PM
// Design Name: 
// Module Name: synchronizer_tb
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


module synchronizer_tb(

    );
    
    wire [128 : 0] test_wire;
    wire [32 : 0] div [0 : 3];
    genvar i;
    assign test_wire = 128'hfffffffff;
    
    generate
    for(i = 0; i < 4 ; i = i + 1) begin
        assign div[i] = test_wire[i * 32 +: 32];
    end
    endgenerate
endmodule
