interface axi_iface
    #(parameter integer C_S_AXI_DATA_WIDTH	= 32,
     parameter integer C_S_AXI_ADDR_WIDTH	= 4);
    	wire  clk;
		wire  aresetn;
        logic [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_awaddr;
        logic [2 : 0] s_axi_awprot;
        logic  s_axi_awvalid;
        logic  s_axi_awready;
        logic [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_wdata;
        logic [(C_S_AXI_DATA_WIDTH/8)-1 : 0] s_axi_wstrb;
        logic  s_axi_wvalid;
        logic  s_axi_wready;
        logic [1 : 0] s_axi_bresp;
        logic  s_axi_bvalid;
        logic  s_axi_bready;
        logic [C_S_AXI_ADDR_WIDTH-1 : 0] s_axi_araddr;
        logic [2 : 0] s_axi_arprot;
        logic  s_axi_arvalid;
        logic  s_axi_arready;
        logic [C_S_AXI_DATA_WIDTH-1 : 0] s_axi_rdata;
        logic [1 : 0] s_axi_rresp;
        logic  s_axi_rvalid;
        logic  s_axi_rready;
        
        modport master(output tdata, output tvalid,
                output tlast, input tready);
        modport slave(input tdata, input tvalid,
                input tlast, output tready); 
endinterface