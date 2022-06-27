`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/13/2022 06:01:47 PM
// Design Name: 
// Module Name: simple_test
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
    input wire [10 : 0] a,
    input wire [10 : 0] b,
    output reg [10 : 0] max
);
    always@* begin
        if(a > b)
            max = a;
        else
            max = b;
    end
endmodule

module simple_test(

    );
    
    reg [10 : 0] counter = 0;
    reg clk = 0;
    reg valid = 0;
    wire [10 : 0] max[ 0 : 1];
    
    always @(posedge clk) begin
        if(valid)
            counter <= counter + 1;
    end
                
    initial begin
        forever #5 clk = ~clk;
    end
    
    initial begin
        #100 
        @(posedge clk);
        valid = 1;
    end
    
endmodule
