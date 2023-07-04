module signal_detect
    #(
        parameter integer C_S_AXI_DATA_WIDTH	= 32,
        parameter integer C_S_AXIS_DATA_WIDTH	= 128,
        parameter integer C_S_AXI_ADDR_WIDTH	= 4,
        parameter integer INTEGRATION_LENGTH    = 1024,
        parameter integer SSR                   = 4,
        parameter integer SAMPLE_WIDTH	        = 32,
        parameter integer INTEGRATION_TIME      = 512
    )
    (
    	input logic  clk,
		input logic  aresetn,
		input logic [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_awaddr,
		input logic [2 : 0] s_axi_awprot,
		input logic  s_axi_awvalid,
		output logic  s_axi_awready,
		input logic [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_wdata,
		input logic [(C_S_AXI_DATA_WIDTH/8)-1 : 0] s_axi_wstrb,
		input logic  s_axi_wvalid,
		output logic  s_axi_wready,
		output logic [1 : 0] s_axi_bresp,
		output logic  s_axi_bvalid,
		input logic  s_axi_bready,
		input logic [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_araddr,
		input logic [2 : 0] s_axi_arprot,
		input logic  s_axi_arvalid,
		output logic  s_axi_arready,
		output logic [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_rdata,
		output logic [1 : 0] s_axi_rresp,
		output logic  s_axi_rvalid,
		input logic  s_axi_rready,
		
		input logic [C_S_AXIS_DATA_WIDTH - 1 : 0] s_axis_data,
		input logic s_axis_tvalid,
		output logic s_axis_tready
    );
    logic [SAMPLE_WIDTH / 2 - 1 : 0] energy;
    logic [SAMPLE_WIDTH / 2 - 1 + $clog2(INTEGRATION_TIME) : 0] estimate;
    logic [SAMPLE_WIDTH / 2 - 1 : 0] subtracted;
    logic [SAMPLE_WIDTH / 2 - 1 : 0] m_axis_fifo_data;
    logic m_axis_fifo_tvalid;
    logic prog_full;
    logic energy_valid;
    logic estimate_valid;
    
    assign s_axis_tready = 1;
    assign subtracted = (prog_full) ? m_axis_fifo_data : {(SAMPLE_WIDTH / 2 - 1){1'b0}};
    energy_calc energy_calc_inst
       (
       .*
       );
    
    always@(posedge clk) begin
        if(~aresetn)
            estimate <= 0;
        else begin
            if(energy_valid) begin
                estimate_valid <= 1;
                estimate <= estimate + energy - subtracted;
            end
        end
    end
    
    xpm_fifo_axis #(
     .CDC_SYNC_STAGES(2), // DECIMAL
     .CLOCKING_MODE("common_clock"), // String
     .ECC_MODE("no_ecc"), // String
     .FIFO_DEPTH(2048), // DECIMAL
     .FIFO_MEMORY_TYPE("auto"), // String
     .PACKET_FIFO("false"), // String
     .PROG_EMPTY_THRESH(10), // DECIMAL
     .PROG_FULL_THRESH(INTEGRATION_TIME), // DECIMAL
     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
     .RELATED_CLOCKS(0), // DECIMAL
     .SIM_ASSERT_CHK(0), // DECIMAL
     .TDATA_WIDTH(SAMPLE_WIDTH/2), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .USE_ADV_FEATURES("1002"), // String
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    integration_fifo_inst (
     .m_axis_tdata(m_axis_fifo_data),
     .m_axis_tvalid(m_fifo_valid),
     .m_axis_tlast(m_axis_data_tlast),
     .s_axis_tready(s_fifo_ready),
     .m_aclk(axis_aclk),
     .m_axis_tready(prog_full),
     .s_aclk(clk),
     .s_aresetn(aresetn),
     .s_axis_tdata(energy),
     .s_axis_tvalid(energy_valid),
     .prog_full_axis(prog_full)
    );
    
    axi_slave axi_slave_inst
    (
    .*,
    .energy_est(estimate)
    );
    
endmodule

module energy_calc #(
    parameter integer SAMPLE_WIDTH	= 32,
    parameter integer SSR           = 4
    )
    (
        input wire clk,
        input logic [SAMPLE_WIDTH * SSR - 1 : 0] s_axis_data,
		input logic s_axis_tvalid,
		output logic [SAMPLE_WIDTH / 2 - 1 : 0] energy,
		output logic energy_valid
    );
    logic signed [SAMPLE_WIDTH - 1 : 0] tmp_i_sq; 
    logic signed [SAMPLE_WIDTH - 1 : 0] tmp_q_sq;
    function[SAMPLE_WIDTH/2 : 0] mag_squared;
       input signed [SAMPLE_WIDTH/2 - 1 : 0] i;
       input signed [SAMPLE_WIDTH/2 - 1 : 0] q;
       begin
           tmp_i_sq = i * i;
           tmp_q_sq = q * q;
           mag_squared = (tmp_i_sq >> (SAMPLE_WIDTH/2 - 1)) + 
                           (tmp_q_sq >> (SAMPLE_WIDTH/2 - 1));
       end
    endfunction 
        
    logic signed [SAMPLE_WIDTH / 2 : 0] sample_i [0 : SSR - 1];
    logic signed [SAMPLE_WIDTH / 2 : 0] sample_q [0 : SSR - 1];
    logic [SAMPLE_WIDTH/2 - 1 + SSR : 0] energy_estimate;
    
    genvar i,k;
    
    generate
        for(i = 0 ; i < SSR; i++) begin
            assign sample_i[i] = s_axis_data[i * SAMPLE_WIDTH +: SAMPLE_WIDTH/2];
            assign sample_q[i] = s_axis_data[i * SAMPLE_WIDTH + SAMPLE_WIDTH/2 +: SAMPLE_WIDTH/2];
        end
    endgenerate
    
    assign energy_estimate = mag_squared(sample_i[0], sample_q[0]) +
                            mag_squared(sample_i[1], sample_q[1]) +
                            mag_squared(sample_i[2], sample_q[2]) +
                            mag_squared(sample_i[3], sample_q[3]); 
                            
    always_comb 
        energy <= energy_estimate >> $clog2(SSR);
    
    always@(posedge clk)
        energy_valid <= s_axis_tvalid;
    
endmodule