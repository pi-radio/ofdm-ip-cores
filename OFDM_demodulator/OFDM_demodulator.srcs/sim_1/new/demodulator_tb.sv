`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08/17/2022 01:48:04 PM
// Design Name: 
// Module Name: demodulator_tb
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

`define QAM16

module demodulator_tb #(
        parameter integer BPSK_INPUT_SAMPLES = 115200,
        parameter integer QPSK_INPUT_SAMPLES = 115200,
        parameter integer QAM16_INPUT_SAMPLES = 115200,
        parameter integer INPUT_SAMPLES = BPSK_INPUT_SAMPLES,
    
        parameter integer BPSK_OUTPUT_SAMPLES = 3600,
        parameter integer QPSK_OUTPUT_SAMPLES = 7200,
        parameter integer QAM16_OUTPUT_SAMPLES = 14400,
        parameter integer OUTPUT_SAMPLES = QAM16_OUTPUT_SAMPLES
    )
    ();
    
    reg  axis_aclk = 0;
    reg  axis_aresetn = 0;
    wire  s00_axis_tready;
    wire [127 : 0] s00_axis_tdata;
    wire  s00_axis_tlast;
    reg  s00_axis_tvalid = 0;
    reg [31 : 0] input_counter =0;
    reg [31 : 0] output_counter = 0;
    reg  m00_axis_tvalid;
    wire [127 : 0] m00_axis_tdata;
    reg  m00_axis_tlast;
    reg  m00_axis_tready = 0;
    reg [127 : 0] input_samples[0 : INPUT_SAMPLES - 1];
    reg [31 : 0] output_samples[0 : OUTPUT_SAMPLES - 1];
    wire [31 : 0] exp_output;
    reg [31 : 0] rand_val;
    localparam string path =  "../../../../OFDM_demodulator.srcs/sim_1/new/";
    localparam string input_filename = { path, "mod_input.txt" }; 
    logic [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
    
    
    
    initial
        $readmemh(input_filename, input_samples, 0, 159);
        
    initial begin
        forever #5 axis_aclk = ~axis_aclk;
    end
    
    assign s00_axis_tdata = input_samples[input_counter];
//    assign s00_axis_tdata = {32'h3fffc000, 32'h3fff3fff, 32'hc000c000, 32'hc0003fff};
                                        
    
    always@(posedge axis_aclk) begin
        rand_val = $random;
    end
    
   // assign exp_output = output_samples[output_counter];
    
    OFDM_demodulator
    dut (
        .axis_aclk(axis_aclk),
		.axis_aresetn(axis_aresetn),
		.s00_axis_tready(s00_axis_tready),
		.s00_axis_tdata(s00_axis_tdata),
		.s00_axis_tlast(s00_axis_tlast),
		.s00_axis_tvalid(s00_axis_tvalid),
		.m00_axis_tvalid(m00_axis_tvalid),
		.m00_axis_tdata(m00_axis_tdata),
		.m00_axis_tlast(m00_axis_tlast),
		.m00_axis_tready(m00_axis_tready)
    );
    
    always@(posedge axis_aclk) begin
        if(m00_axis_tvalid && m00_axis_tready)
            if(exp_output != m00_axis_tdata)
                $display("Data Missmatch at count 0x%0h", output_counter);
    end
    
    module linear_scale (
  input wire clk,
  input wire signed [15:0] x,
  input wire signed [15:0] min_val,
  input wire signed [15:0] max_val,
  input wire signed [15:0] new_min_val,
  input wire signed [15:0] new_max_val,
  output reg signed [15:0] scaled_x
);
  parameter WIDTH = 15; // Number of fractional bits
  
  // Calculate the scaling factor
  reg signed [31:0] factor;
  always @* begin
    factor = ((new_max_val - new_min_val) << WIDTH) / (max_val - min_val);
  end
  
  // Scale the input value
  always @* begin
    scaled_x = (((x - min_val) * factor) >> WIDTH) + new_min_val;
  end
  
endmodule
    reg signed scaled_x;
    linear_scale linear_scale_inst(
        .clk(axis_aclk),
        .x(16'h001f),
        .min_val(16'hc000),
        .max_val(16'h3fff),
        .new_min_val(16'hfff1),
        .new_max_val(16'h000f),
        .scaled_x(scaled_x)
    );
//    always@(posedge axis_aclk) begin
//        if(axis_aresetn) begin
//            if(rand_val[8 : 0] == 1 && input_counter <= 30000)
//                m00_axis_tready <= ~m00_axis_tready;
//        end
//    end
    
    reg [20 : 0] ii;
    reg [20 : 0] init_cnt = 0;
    reg [20 : 0] halted = 0;
    reg [20 : 0] valid_idle_duration = 1000;
    initial begin
        input_counter <=  0;
        output_counter <= 0;
        #100 
        @(posedge axis_aclk);
        axis_aresetn <= 1;

        //s_axis_config_tdata <= output_samples[sw_counter];
        @(posedge axis_aclk);
        s00_axis_tvalid <= 1;
        @(posedge axis_aclk);
        m00_axis_tready <= 1;
        
        for(ii = 0 ; ii< 100000; ii++) begin
            @(posedge axis_aclk)
            input_counter <= input_counter + 1;
                
            if(input_counter == 160) 
                    $finish;
            if(s00_axis_tready && s00_axis_tvalid) begin
                if(input_counter == 20000) begin
                    s00_axis_tvalid <= 0;
                    halted <= ii;
                end
                else if(input_counter == (60000)) begin
                    s00_axis_tvalid <= 0;
                    halted <= ii;
                end
                else
                    input_counter <= input_counter + 1;
            end
            if(m00_axis_tready && m00_axis_tvalid) begin
                    output_counter <= output_counter + 1;
            end
        end
    end
    
        /* Make sure Valids deassert with reset*/
    assert property (@(posedge axis_aclk)
	   !axis_aresetn |-> !m00_axis_tvalid);

    assert property (@(posedge axis_aclk)
	   !axis_aresetn |-> !s00_axis_tvalid);
	   
	/* Make sure data does not change if m_axis_tready deasserts*/
	assert property (@(posedge axis_aclk)
	   m00_axis_tvalid && !m00_axis_tready && axis_aresetn
	       |=> m00_axis_tvalid && $stable(m00_axis_tdata));
	       
endmodule

