`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/26/2022 01:40:11 PM
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


module simple_test2(

    );
    
    reg [10 : 0] counter = 0;
    reg clk = 0;
    reg valid = 0, ready = 0;
    
   always@(posedge clk) begin
        if(valid && ready)
            counter <= counter + 1;
    end
    
    initial begin
       forever #5 clk = ~clk;
    end
    
    initial begin
        #100
        @(posedge clk);
        valid = 1;
        #100
        @(posedge clk);
        ready = 1;
    end
    

            
endmodule
