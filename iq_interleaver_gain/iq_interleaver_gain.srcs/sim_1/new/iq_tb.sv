`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/15/2023 10:52:06 AM
// Design Name: 
// Module Name: iq_tb
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


module iq_tb(

    );
    
logic clk = 0;
logic aresetn = 0;
logic  s00_axis_tready;
logic [63 : 0] s00_axis_tdata;
logic [15 : 0] s00_axis_tstrb;
logic  s00_axis_tlast;
logic  s00_axis_tvalid;

// Ports of Axi Slave Bus Interface S01_AXIS
logic  s01_axis_tready;
logic [63 : 0] s01_axis_tdata;
logic[15 : 0] s01_axis_tstrb;
logic s01_axis_tlast;
logic s01_axis_tvalid;

// Ports of Axi Master Bus Interface M00_AXIS
logic  m00_axis_tvalid;
logic [127 - 1 : 0] m00_axis_tdata;
logic  m00_axis_tlast;
logic  m00_axis_tready;

logic [4-1 : 0] s_axi_awaddr;
logic [2 : 0] s_axi_awprot;
logic  s_axi_awvalid;
logic  s_axi_awready;
logic [4-1 : 0] s_axi_wdata;
logic [(4/8)-1 : 0] s_axi_wstrb;
logic  s_axi_wvalid;
logic  s_axi_wready;
logic [1 : 0] s_axi_bresp;
logic  s_axi_bvalid;
logic  s_axi_bready;
logic [4-1 : 0] s_axi_araddr;
logic [2 : 0] s_axi_arprot;
logic  s_axi_arvalid;
logic  s_axi_arready;
logic [4-1 : 0] s_axi_rdata;
logic [1 : 0] s_axi_rresp;
logic  s_axi_rvalid;
logic  s_axi_rready;

iq_interleaver_gain iq_interleaver_gain_inst (
    .*
);

initial begin
    forever #5 clk = ~clk;
end

integer i;
initial begin
    wait(200)@(posedge clk);
    aresetn = 0;
    s00_axis_tvalid = 1;
    s01_axis_tvalid = 1;
    @(posedge clk);
    for(i = 0; i < 1000 ; i++) begin
        s00_axis_tdata <= {$random, $random, $random, $random};
        s01_axis_tdata <= {$random, $random, $random, $random};
        @(posedge clk);
    end
end
endmodule
