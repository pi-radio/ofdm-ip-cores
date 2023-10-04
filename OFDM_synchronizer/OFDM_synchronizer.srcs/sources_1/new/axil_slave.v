module axil_slave_sync
    #(
        parameter integer C_S_AXI_DATA_WIDTH	= 32,
        parameter integer C_S_AXI_ADDR_WIDTH	= 4
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
		output logic [31 : 0] threshold
    );
    localparam ADDRLSB = $clog2(C_S_AXI_DATA_WIDTH) - 3;
    
    logic [C_S_AXI_ADDR_WIDTH - 1 : 0] write_addr;
    logic [C_S_AXI_ADDR_WIDTH - 1 : 0] read_addr;
    logic [31 : 0] frame_len_reg;
    logic write_rdy;
    logic read_rdy;
    logic aread_rdy;
    
    assign s_axi_bresp = 2'b00;
    assign s_axi_rresp = 2'b00;
    assign s_axi_awready = write_rdy;
    assign s_axi_wready = write_rdy;
    assign write_addr = s_axi_awaddr[C_S_AXI_ADDR_WIDTH - 1 : ADDRLSB];
    assign read_addr = s_axi_araddr[C_S_AXI_ADDR_WIDTH - 1 : ADDRLSB];
    assign s_axi_arready = aread_rdy;
    assign read_rdy = s_axi_arvalid && s_axi_arready;
    
    assign frame_len = frame_len_reg;
    assign reset_len = write_rdy;
        
    always @(posedge clk) begin
        if(!aresetn)
            s_axi_bvalid <= 0;
        else begin
            if(write_rdy)
                s_axi_bvalid <= 1;
            else if(s_axi_bready)
                s_axi_bvalid <= 0;
        end
    end
    
    always_comb
        aread_rdy <= !s_axi_rvalid;
    
    always @(posedge clk) begin
        if(!aresetn)
            s_axi_rvalid <= 0;
        else begin
            if(read_rdy)
                s_axi_rvalid <= 1;
            else if(s_axi_rready)
                s_axi_rvalid <= 0;
        end
    end
    
    always @(posedge clk) begin
        if(!aresetn)
            write_rdy <= 0;
        else
            write_rdy <= !write_rdy &&
                (s_axi_awvalid && s_axi_wvalid) &&
                (!s_axi_bvalid || s_axi_bready);
    end
    
    always @(posedge clk) begin
        if(!aresetn) begin
            threshold <= 32'h00000050;
        end
        else begin
            if(write_rdy) begin
                case(write_addr)
                    1'b0 : threshold <= s_axi_wdata[31 : 0];
                endcase
            end
        end
    end
    
   always @(posedge clk) begin
        if(read_rdy) begin
            case(read_addr)
                1'b0 : s_axi_rdata <= threshold;
            endcase
        end
    end
    
endmodule

