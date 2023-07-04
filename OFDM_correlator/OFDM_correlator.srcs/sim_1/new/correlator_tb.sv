`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 01/25/2023 02:00:18 PM
// Design Name: 
// Module Name: correlator_tb
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


module correlator_tb(
        
    );
    
     logic  clk = 0;
     logic  resetn = 0;
     logic  s00_axis_tready;
     logic [128-1 : 0] s00_axis_tdata;
     logic [(128/8)-1 : 0] s00_axis_tstrb;
     logic  s00_axis_tlast;
     logic  s00_axis_tvalid;

     logic  s00_axis_config_tready;
     logic [32-1 : 0] s00_axis_config_tdata;
     logic [(32/8)-1 : 0] s00_axis_config_tstrb;
     logic  s00_axis_config_tlast;
     logic  s00_axis_config_tvalid;

     logic  m00_axis_tvalid;
     logic [128-1 : 0] m00_axis_tdata;
     logic [(128/8)-1 : 0] m00_axis_tstrb;
     logic  m00_axis_tlast;
     logic  m00_axis_tready;
    
    OFDM_correlator OFDM_correlator_inst
	(
		.*
	);
	
	
	
	localparam string path =  "../../../../../OFDM_correlator.srcs/sources_1/new/";
	localparam string input_filename = { path, "sync_temp.txt" }; 
	logic [31 : 0] sync_word [0 : 1023];
	logic [127 : 0] rand_int;
	integer j;
	
	logic [31 : 0] input_samples[0 : 1024 - 1];
	assign sync_word = input_samples[0 : 1023];
	
	initial 
	   $readmemh(input_filename, input_samples, 0, 1024 - 1);
	
	initial begin
        forever #5 clk = ~clk;
    end
	
	always@(posedge clk)
        rand_int = {$random,$random,$random,$random};
	
	initial
    begin
        repeat (100)  @(posedge clk);
        resetn <= 1;
        wait(resetn);
        
        wait(s00_axis_config_tready);
        for (j = 0; j < 1024; j++) begin
            @(posedge clk);
            s00_axis_config_tdata <= sync_word[j];
            s00_axis_config_tvalid <= 1;
            s00_axis_config_tlast <= (j == 1023);
        end
        wait(s00_axis_tready);
        repeat (100)  @(posedge clk);
        for (j = 0; j < 10240; j++) begin
            @(posedge clk);
            s00_axis_tdata <= rand_int;
            s00_axis_tvalid <= 1;
        end
    end
endmodule
