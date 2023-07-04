`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02/15/2023 10:46:14 AM
// Design Name: 
// Module Name: signal_detect_tb
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


module signal_detect_tb(

    );
    
     logic  clk = 0;
     logic  aresetn = 0;
     logic [4-1 : 0] s_axi_awaddr;
     logic [2 : 0] s_axi_awprot;
     logic  s_axi_awvalid;
     logic  s_axi_awready;
     logic [32-1 : 0] s_axi_wdata;
     logic [(32/8)-1 : 0] s_axi_wstrb;
     logic  s_axi_wvalid;
     logic  s_axi_wready;
     logic [1 : 0] s_axi_bresp;
     logic  s_axi_bvalid;
     logic  s_axi_bready;
     logic [4-1 : 0] s_axi_araddr;
     logic [2 : 0] s_axi_arprot;
     logic  s_axi_arvalid;
     logic  s_axi_arready;
     logic [32-1 : 0] s_axi_rdata;
     logic [1 : 0] s_axi_rresp;
     logic  s_axi_rvalid;
     logic  s_axi_rready;
     logic [128 - 1 : 0] s_axis_data = 0;
     logic s_axis_tvalid = 0;
     logic s_axis_tready;
     
     logic [127 : 0] no_signal;
     logic [127 : 0] signal;
     logic [31 : 0] rand_val;
     int i;
     initial begin
        forever #5 clk = ~clk;
     end
     
     always@(posedge clk) begin
        signal <= {$random, $random, $random, $random};
        rand_val <= $random;
        no_signal <= {27'h0, rand_val[5 : 0], 27'h0, rand_val[11 : 6],
                    27'h0, rand_val[17 : 12],27'h0, rand_val[23 : 18]};
     end
     
     signal_detect signal_detect_inst
     (
        .*
     );
        
     
     initial begin
        repeat (100) @(posedge clk);
        aresetn <= 1;
        s_axis_tvalid <= 1;
        @(posedge clk)
        for (i = 0; i < 4000; i++) begin
            @(posedge clk);
            s_axis_data <= no_signal;
        end
            
        for (i = 0; i < 4000; i++) begin
            @(posedge clk);
            s_axis_data <= signal;
        end
        
        for (i = 0; i < 4000; i++) begin
            @(posedge clk);
            s_axis_data <= no_signal;
        end    
        $finish;
     end
endmodule
