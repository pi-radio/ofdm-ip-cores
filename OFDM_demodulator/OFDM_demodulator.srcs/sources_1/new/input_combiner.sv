`timescale 1ns / 1ps

module input_combiner #(
    parameter integer IN_DATA_WIDTH  = 96,
    parameter integer OUT_DATA_WIDTH = 128,
    parameter integer COMPLEX_SIZE = 32,
    parameter integer IN_SSR = 3,
    parameter integer OUT_SSR = 4
    )(
    input wire clk,
    input wire aresetn,
    input logic [IN_DATA_WIDTH - 1 : 0] s_axis_tdata,
    input logic s_axis_tvalid,
    output logic m_axis_tvalid,
    output logic [OUT_DATA_WIDTH - 1 : 0] m_axis_tdata
    );
    
    logic [IN_DATA_WIDTH * 2 - 1 : 0] input_sr;
    logic [10 : 0] available_out;
    
    assign m_axis_tvalid = available_out >= OUT_SSR;
    assign m_axis_tdata = input_sr[0 +: OUT_SSR * COMPLEX_SIZE];
    
    always@(posedge clk) begin
        if(~aresetn) begin
            input_sr <= {IN_DATA_WIDTH * 2{1'b0}};
            available_out <= 0;
        end
        else begin
            if(s_axis_tvalid) begin
                if(available_out == IN_SSR * 2) begin
                    input_sr <= {s_axis_tdata, input_sr[OUT_SSR * COMPLEX_SIZE +: 2 * COMPLEX_SIZE]};
                    available_out <= 2*IN_SSR - 1;
                end
                else if(available_out == 2*IN_SSR - 1) begin
                    input_sr <= {s_axis_tdata, input_sr[OUT_SSR * COMPLEX_SIZE +: COMPLEX_SIZE]};
                    available_out <= 10'd4;
                end
                else if(available_out ==10'd4) begin
                    input_sr <= s_axis_tdata;
                    available_out <= IN_SSR;
                end
                else if(available_out == IN_SSR) begin
                    input_sr <= {s_axis_tdata, input_sr[0 +: IN_SSR * COMPLEX_SIZE]};
                    available_out <= 2*IN_SSR;
                end
                else if(available_out == 0) begin
                    input_sr <= s_axis_tdata;
                    available_out <= IN_SSR;
                end               
            end
            else if(available_out >= OUT_SSR) begin
                available_out <= 0;
            end
        end
    end
    
endmodule
