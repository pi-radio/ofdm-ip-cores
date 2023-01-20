`timescale 1ns / 1ps

module compare4(
    input wire [33:0] a,
    input wire [33:0] b,
    input wire [33:0] c,
    input wire [33:0] d,    
    input wire [3:0] a_idx,
    input wire [3:0] b_idx,
    input wire [3:0] c_idx,
    input wire [3:0] d_idx,
    output reg [3:0] min_index,
    output reg [33:0] min_value
    );
    
    always@* begin
        if((a <= b) && (a <= c) && (a <= d)) begin
            min_index <= a_idx;
            min_value <= a;
        end
        else if((b <= a) && (b <= c) && (b <= d)) begin
            min_index <= b_idx;
            min_value <= b;
        end
        else if((c <= a) && (c <= b) && (c <= d)) begin
            min_index <= c_idx;
            min_value <= c;
        end
        else begin
            min_index <= d_idx;
            min_value <= d;
        end
    end
endmodule