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
    reg [31 : 0] input_counter = 0;
    reg [31 : 0] output_counter = 0;
    reg  m00_axis_tvalid;
    wire [31 : 0] m00_axis_tdata;
    reg  m00_axis_tlast;
    reg  m00_axis_tready = 0;
    reg [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
    reg [31 : 0] output_samples[0 : OUTPUT_SAMPLES - 1];
    wire [31 : 0] exp_output;
    reg [31 : 0] rand_val;
    
    `ifdef BPSK
        initial begin
            $readmemh("../../../../OFDM_demodulator.srcs/sim_1/new/input_data_o.txt", input_samples, 0, INPUT_SAMPLES - 1);
        end
        
        initial begin
            $readmemh("../../../../OFDM_demodulator.srcs/sim_1/new/output.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QPSK
        initial begin
            $readmemh("../../../../OFDM_demodulator.srcs/sim_1/new/input_data_qpsk_o.txt", input_samples, 0,INPUT_SAMPLES  - 1);
        end

        initial begin
            $readmemh("../../../../OFDM_demodulator.srcs/sim_1/new/output_qpsk.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QAM16
        initial begin
            $readmemh("../../../../OFDM_demodulator.srcs/sim_1/new/input_data_qam16_o.txt", input_samples, 0, INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh("../../../../OFDM_demodulator.srcs/sim_1/new/output_qam16.txt", output_samples, 0, OUTPUT_SAMPLES  - 1);
        end
    `endif
    
    initial begin
        forever #5 axis_aclk = ~axis_aclk;
    end
    
    assign s00_axis_tdata = {input_samples[input_counter + 3], input_samples[input_counter + 2],
                                input_samples[input_counter + 1], input_samples[input_counter]};
    
    always@(posedge axis_aclk)
        rand_val = $random;
    
    assign exp_output = output_samples[output_counter];
    
    OFDM_demodulator dut(
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
    
    always@(posedge axis_aclk) begin
        if(axis_aresetn) begin
            if(rand_val[8 : 0] == 1 && input_counter <= 30000)
                m00_axis_tready <= ~m00_axis_tready;
        end
    end
    
    reg [20 : 0] ii;
    reg [20 : 0] init_cnt = 0;
    reg [20 : 0] halted = 0;
    reg [20 : 0] valid_idle_duration = 1000;
    initial begin
        input_counter <= 0;
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
            if(halted + valid_idle_duration < ii) begin
                if(halted != 0) begin
                    s00_axis_tvalid <= 1;
                    halted <= 0;
                    input_counter <= input_counter + 4;
                end
            end
                
            if(output_counter == OUTPUT_SAMPLES) 
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
                    input_counter <= input_counter + 4;
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
