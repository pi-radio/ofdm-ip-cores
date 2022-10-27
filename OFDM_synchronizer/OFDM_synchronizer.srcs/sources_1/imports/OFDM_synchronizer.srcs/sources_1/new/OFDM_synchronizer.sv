
`timescale 1 ns / 1 ps

	module OFDM_synchronizer #
	(
		// Parameters of Axi Master Bus Interface M_AXIS_DATA
		parameter integer C_M_AXIS_DATA_TDATA_WIDTH	= 128,

		// Parameters of Axi Slave Bus Interface S00_AXI
		parameter integer C_S00_AXI_DATA_WIDTH	= 32,
		parameter integer C_S00_AXI_ADDR_WIDTH	= 4,

		// Parameters of Axi Slave Bus Interface S_AXIS_CORR1
		parameter integer C_S_AXIS_CORR1_TDATA_WIDTH	= 256,

		// Parameters of Axi Slave Bus Interface S_AXIS_CORR2
		parameter integer C_S_AXIS_CORR2_TDATA_WIDTH	= 256,

		// Parameters of Axi Slave Bus Interface S_AXIS_DATA_IN
		parameter integer C_S_AXIS_DATA_IN_TDATA_WIDTH	= 128
	)
	(

		input wire  axis_data_aclk,
		input wire  axis_data_aresetn,
		output wire  m_axis_data_tvalid,
		output wire [C_M_AXIS_DATA_TDATA_WIDTH-1 : 0] m_axis_data_tdata,
		output wire [(C_M_AXIS_DATA_TDATA_WIDTH/8)-1 : 0] m_axis_data_tstrb,
		output reg  m_axis_data_tlast,
		input wire  m_axis_data_tready,
		
		output wire  m_axis_log_tvalid,
		output wire [127 : 0] m_axis_log_tdata,
		output wire [(128/8)-1 : 0] m_axis_log_tstrb,
		output reg  m_axis_log_tlast,
		input wire  m_axis_log_tready,

		input wire [C_S00_AXI_ADDR_WIDTH-1 : 0] s00_axi_awaddr,
		input wire [2 : 0] s00_axi_awprot,
		input wire  s00_axi_awvalid,
		output wire  s00_axi_awready,
		input wire [C_S00_AXI_DATA_WIDTH-1 : 0] s00_axi_wdata,
		input wire [(C_S00_AXI_DATA_WIDTH/8)-1 : 0] s00_axi_wstrb,
		input wire  s00_axi_wvalid,
		output wire  s00_axi_wready,
		output wire [1 : 0] s00_axi_bresp,
		output wire  s00_axi_bvalid,
		input wire  s00_axi_bready,
		input wire [C_S00_AXI_ADDR_WIDTH-1 : 0] s00_axi_araddr,
		input wire [2 : 0] s00_axi_arprot,
		input wire  s00_axi_arvalid,
		output wire  s00_axi_arready,
		output wire [C_S00_AXI_DATA_WIDTH-1 : 0] s00_axi_rdata,
		output wire [1 : 0] s00_axi_rresp,
		output wire  s00_axi_rvalid,
		input wire  s00_axi_rready,

		output wire  s_axis_corr1_tready,
		input wire [C_S_AXIS_CORR1_TDATA_WIDTH-1 : 0] s_axis_corr1_tdata,
		input wire [(C_S_AXIS_CORR1_TDATA_WIDTH/8)-1 : 0] s_axis_corr1_tstrb,
		input wire  s_axis_corr1_tlast,
		input wire  s_axis_corr1_tvalid,
		
		output wire  s_axis_corr2_tready,
		input wire [C_S_AXIS_CORR2_TDATA_WIDTH-1 : 0] s_axis_corr2_tdata,
		input wire [(C_S_AXIS_CORR2_TDATA_WIDTH/8)-1 : 0] s_axis_corr2_tstrb,
		input wire  s_axis_corr2_tlast,
		input wire  s_axis_corr2_tvalid,

		output wire  s_axis_data_in_tready,
		input wire [C_S_AXIS_DATA_IN_TDATA_WIDTH-1 : 0] s_axis_data_in_tdata,
		input wire [(C_S_AXIS_DATA_IN_TDATA_WIDTH/8)-1 : 0] s_axis_data_in_tstrb,
		input wire  s_axis_data_in_tlast,
		input wire  s_axis_data_in_tvalid
	);

    localparam corr_sample_size = 64;
    localparam corr_real_imag_size = 26;
    reg signed [51 : 0] tmp_i_sq; 
    reg signed [51 : 0] tmp_q_sq;
	wire [31 : 0] threshold;
	wire signed [corr_real_imag_size - 1 : 0] tmp1_i[0 : 3]; 
    wire signed [corr_real_imag_size - 1 : 0] tmp1_q[0 : 3];
	wire signed [corr_real_imag_size - 1 : 0] tmp2_i[0 : 3]; 
    wire signed [corr_real_imag_size - 1 : 0] tmp2_q[0 : 3];
    reg [corr_real_imag_size : 0] mag_sq_corr1_tmp[0 : 3];
    reg [corr_real_imag_size : 0] mag_sq_corr2_tmp[0 : 3];   
    reg [corr_real_imag_size : 0] mag_sq_corr1; //wire
    reg [corr_real_imag_size : 0] mag_sq_corr2; //wire
    wire [corr_real_imag_size : 0] max_four_corr1[0 : 1];
	wire [corr_real_imag_size : 0] max_four_corr2[0 : 1];
    reg [27 : 0] max_mag1_c1 = 0;
    reg [27 : 0] max_mag1_c2 = 0;
    reg [27 : 0] max_mag2_c1 = 0;
    reg [27 : 0] max_mag2_c2 = 0;
        
    reg state_tx_c1 = 0;
    reg state_tx_c2 = 0;
	localparam IDLE = 0,
	           TXING = 1;

    reg [2 : 0] NOISE_EST = 2'b00,
                FIRST_SEARCH = 2'b01,
                SECOND_SEARCH = 2'b10,
                PEAK_DROP = 2'b11,
                PEAK_DET = 3'b100;
    reg [2 : 0] state_peak_det_c1 = 3'h7;
	reg [2 : 0] state_peak_det_c2 = 3'h0;
    localparam noise_samples = 256;
    localparam symbol_size = 256;
    localparam cp_len = 64;
    localparam total_samples_per_symb = 9 * 320;
    reg [8 : 0] sample_cntr = 0;
    reg [8 : 0] sample_cntr = 0;
    
    wire [8 : 0] start_idx;
    reg [8 : 0] start_idx_c1 = 0;
    reg [8 : 0] start_idx_c2 = 0;
    
    wire state_tx;
    reg [31 : 0] accum = 0;
    reg [31 : 0] total = 0;
    
    reg [127 : 0] buffer [0 : 2*symbol_size];
    reg [8 : 0] buffer_idx = 0;
    reg signed [8 : 0] max_idx1_c1 = -1;
    reg signed [8 : 0] max_idx2_c1 = -1;
    reg signed [8 : 0] max_idx1_c2 = -1;
    reg signed [8 : 0] max_idx2_c2 = -1;
    
    wire [8 : 0] buffer_read_idx;
    reg [15 : 0] samples_sent = 0;
    reg [8 : 0] cp_rm_count = 0;
    
    reg [53 : 0] noise_accum = 0;
    reg [26 : 0] noise_floor = 0;
    wire [31 : 0] test_wire;
    
    reg active_correlator1 = 0;
    reg active_correlator2 = 0;
    
    reg [8 : 0] symbol_counter = 0;
    
    reg [1 : 0] prev_state_c1 = 0;
    reg [1 : 0] prev_state_c2 = 0;
    reg swap_max_master = 0;
    reg swap_c2_idx = 0;
    
    reg dbg_max_det = 0;
    reg dbg_alert = 0;
    reg [2: 0] dbg_cntr = 0;
    reg [5 : 0] i;
    reg [7 : 0] count_mtvalid = 0;
    wire test4;
    assign test4 = mag_sq_corr1 > (noise_floor + threshold);
    assign test_wire = (noise_floor + threshold);

    assign m_axis_log_tvalid = 1;
    
	OFDM_synchronizer_S00_AXI # ( 
		.C_S_AXI_DATA_WIDTH(C_S00_AXI_DATA_WIDTH),
		.C_S_AXI_ADDR_WIDTH(C_S00_AXI_ADDR_WIDTH)
	) synchronizer_v2_0_S00_AXI_inst (
		.S_AXI_ACLK(s00_axi_aclk),
		.S_AXI_ARESETN(s00_axi_aresetn),
		.S_AXI_AWADDR(s00_axi_awaddr),
		.S_AXI_AWPROT(s00_axi_awprot),
		.S_AXI_AWVALID(s00_axi_awvalid),
		.S_AXI_AWREADY(s00_axi_awready),
		.S_AXI_WDATA(s00_axi_wdata),
		.S_AXI_WSTRB(s00_axi_wstrb),
		.S_AXI_WVALID(s00_axi_wvalid),
		.S_AXI_WREADY(s00_axi_wready),
		.S_AXI_BRESP(s00_axi_bresp),
		.S_AXI_BVALID(s00_axi_bvalid),
		.S_AXI_BREADY(s00_axi_bready),
		.S_AXI_ARADDR(s00_axi_araddr),
		.S_AXI_ARPROT(s00_axi_arprot),
		.S_AXI_ARVALID(s00_axi_arvalid),
		.S_AXI_ARREADY(s00_axi_arready),
		.S_AXI_RDATA(s00_axi_rdata),
		.S_AXI_RRESP(s00_axi_rresp),
		.S_AXI_RVALID(s00_axi_rvalid),
		.S_AXI_RREADY(s00_axi_rready),
		.thresh(threshold)
	);
	// Calculates the magnitude squared of the input sample
	function[26 : 0] mag_squared;
	   input signed [25 : 0] i;
	   input signed [25 : 0] q;
	   begin
	       tmp_i_sq = i * i;
	       tmp_q_sq = q * q;
	       mag_squared = (tmp_i_sq >> 25) + (tmp_q_sq >> 25);
	   end
	endfunction 
	
	genvar k, l;
	generate
	   for(k = 0; k < 4; k = k + 2) begin
	       comparator c(mag_sq_corr1_tmp[k], mag_sq_corr1_tmp[k + 1], max_four_corr1[k/2]);
	   end
	endgenerate
	
	generate
	   for(k = 0; k < 4; k = k + 2) begin
	       comparator c(mag_sq_corr2_tmp[k], mag_sq_corr2_tmp[k + 1], max_four_corr2[k/2]);
	   end
	endgenerate
	
	always@(*) begin
	   mag_sq_corr1 <= (max_four_corr1[0] > max_four_corr1[1]) ? max_four_corr1[0] : max_four_corr1[1];
	   mag_sq_corr2 <= (max_four_corr2[0] > max_four_corr2[1]) ? max_four_corr2[0] : max_four_corr2[1];
	end
	
//	assign mag_sq_corr1 = (max_four_corr1[0] > max_four_corr1[1]) ? max_four_corr1[0] : max_four_corr1[1];
//	assign mag_sq_corr2 = (max_four_corr2[0] > max_four_corr2[1]) ? max_four_corr2[0] : max_four_corr2[1];
	assign s_axis_corr1_tready = s_axis_corr2_tvalid;
    assign s_axis_corr2_tready = s_axis_corr1_tvalid;
    assign s_axis_data_in_tready =  s_axis_corr1_tvalid && s_axis_corr2_tvalid;
    
    assign buffer_read_idx = start_idx + samples_sent;
    
    assign m_axis_data_tdata =  (state_tx) ? buffer[buffer_read_idx] : 32'h00000000;
    assign m_axis_data_tvalid = (state_tx && /*(cp_rm_count >= cp_len) &&*/ samples_sent < total_samples_per_symb );
    
    assign start_idx = active_correlator1 ? start_idx_c1 :
                        (active_correlator2 ? start_idx_c2 : 32'h00000000);
    assign state_tx = state_tx_c1 || state_tx_c2;
	
	 generate
	   for(l = 0 ; l < 4 ; l = l + 1) begin
	       assign tmp1_i[l] = s_axis_corr1_tdata[(corr_sample_size * l) + corr_real_imag_size - 1 : corr_sample_size * l];
	       assign tmp1_q[l] = s_axis_corr1_tdata[((corr_sample_size * l) + (corr_sample_size / 2)) + corr_real_imag_size - 1 :
	                                                                        (corr_sample_size * l) + (corr_sample_size / 2)];
	       assign tmp2_i[l] = s_axis_corr2_tdata[(corr_sample_size * l) + corr_real_imag_size - 1 : corr_sample_size * l];
	       assign tmp2_q[l] = s_axis_corr2_tdata[((corr_sample_size * l) + (corr_sample_size / 2)) + corr_real_imag_size - 1 :
	                                                                        (corr_sample_size * l) + (corr_sample_size / 2)];
	   end
	 endgenerate

    always@(posedge axis_data_aclk) begin
        for(i = 0; i < 4; i = i + 1) begin
            mag_sq_corr1_tmp[i] <= mag_squared(tmp1_i[i], tmp1_q[i]); 
            mag_sq_corr2_tmp[i] <= mag_squared(tmp2_i[i], tmp2_q[i]);
        end
    end
    
    always @(posedge axis_data_aclk) begin
        if(~axis_data_aresetn) begin
            state_peak_det_c1 <= 0;
            state_tx_c1 = IDLE;
            noise_floor <= 0;
            start_idx_c1 <= 0;
            active_correlator1 <= 0;
            swap_max_master <= 0;
            
        end
        if(state_tx_c1 == TXING && samples_sent == total_samples_per_symb -1) begin
            state_tx_c1 = IDLE;
            active_correlator1 <= 0;
        end
        if(swap_max_master == 1)
            swap_max_master <= 0;
        if(s_axis_corr1_tlast) begin
            case(state_peak_det_c1) 
                 NOISE_EST: begin
                        noise_floor <= (noise_accum) >> 10;
                        state_peak_det_c1 <= FIRST_SEARCH;
                 end
                 FIRST_SEARCH: begin
                    if(max_idx1_c1 >= 0)
                        state_peak_det_c1 <= SECOND_SEARCH;
                 end
                 SECOND_SEARCH: begin
                    if(max_idx2_c1 > 0 && max_idx2_c1 < 192 
                            && max_idx1_c1 == max_idx2_c1) begin  // Should it also be state_tx != TXING?
                            state_tx_c1 <= TXING;
                            active_correlator1 <= 1;
                            start_idx_c1 <= (sample_cntr[8]) ? 512 - max_idx2_c1 : 256 - max_idx2_c1;
                            state_peak_det_c1 <= FIRST_SEARCH;
                     end
//                     else if(max_idx2_c1 >= 0 && max_idx2_c1 < 192 
//                            && max_idx1_c1 != max_idx2_c1) begin
//                            /*
//                            * In this case, a false positive first peak was detected, and a second peak comes 
//                            * right after. In order not to reset the detection process we notify the appropriate 
//                            * circuit to retain the second max index value and keep searching for the real second one
//                            */
//                        swap_max_master <= 1;            
//                     end
                     else
                        state_peak_det_c1 <= FIRST_SEARCH;
                 end
             endcase 
         end
    end
    
    always @(posedge axis_data_aclk) begin
        if(~axis_data_aresetn) begin
            state_peak_det_c2 <= NOISE_EST;
            start_idx_c2 <= 0;
            active_correlator2 <= 0;
            state_tx_c2 = IDLE;
            swap_c2_idx <= 0;
        end
        if(state_tx_c2 == TXING && samples_sent == total_samples_per_symb -1) begin
            state_tx_c2 = IDLE;
            active_correlator2 <= 0;    
        end
        if(swap_c2_idx)
            swap_c2_idx <= 0;
        if(s_axis_corr2_tlast) begin
            case(state_peak_det_c2) 
                 NOISE_EST: begin
                        state_peak_det_c2 <= FIRST_SEARCH;
                 end
                 FIRST_SEARCH: begin
                    if(max_idx1_c2 >= 0)
                        state_peak_det_c2 <= SECOND_SEARCH;
                 end
                 SECOND_SEARCH: begin
                    if((max_idx2_c2 > 0) && (max_idx2_c2 < 192) 
                            && (max_idx1_c2 == max_idx2_c2) && (state_tx_c1 != TXING)) begin  // Should it also be state_tx != TXING?
                            state_tx_c2 <= TXING;
                            active_correlator2 <= 1;
                            start_idx_c2 <= (sample_cntr[8]) ? 512 - (max_idx2_c2 + 128) : 256 - (max_idx2_c2 + 128);
                        state_peak_det_c2 <= FIRST_SEARCH;
                        end
                        else if((max_idx2_c2 >= 0) && (max_idx2_c2 < 192) 
                            && (max_idx1_c2 != max_idx2_c2) && (state_tx_c1 != TXING)) begin 
                            swap_c2_idx <= 1;        
                        end
                        else 
                            state_peak_det_c2 <= FIRST_SEARCH;
                 end
             endcase 
         end
    end
    

    
    always @(posedge axis_data_aclk) begin
        if(~axis_data_aresetn) begin
            samples_sent <= 0;
            cp_rm_count <= 0;
            symbol_counter <= 0;
        end
        else begin
        if(state_tx) begin
            if(samples_sent < total_samples_per_symb - 1) begin
                samples_sent <= samples_sent + 1;
                if(symbol_counter == 318) m_axis_data_tlast <= 1;
                else m_axis_data_tlast <= 0;
                if(symbol_counter == 319) begin // Reset cp counter for every symbol
                    cp_rm_count <= 0;
                    symbol_counter <= 0;
                end
                else 
                    symbol_counter <= symbol_counter + 1;
                if(cp_rm_count < cp_len)
                    cp_rm_count <= cp_rm_count + 1;
            end
            else begin
                cp_rm_count <= 0;
                symbol_counter <= 0;
                m_axis_data_tlast <= 0;
            end    
        end
        else begin
            samples_sent <= 0;
            cp_rm_count <= 0;
            symbol_counter <= 0;
        end
        end
    end
    
    always @(posedge axis_data_aclk) begin
        if(~axis_data_aresetn) begin
            prev_state_c1 <= 0;
            prev_state_c2 <= 0;
            sample_cntr <= 0;
            buffer_idx <= 0;
            max_idx1_c1 <= -1;
            max_idx2_c1 <= -1;
            max_mag1_c1 <= 0;
            max_mag2_c1 <= 0;
            max_idx1_c2 <= -1;
            max_idx2_c2 <= -1;
            max_mag1_c2 <= 0;
            max_mag2_c2 <= 0;
        end
        else begin
        if(s_axis_corr1_tvalid && s_axis_corr2_tvalid && s_axis_data_in_tvalid) begin
            accum <= accum + mag_sq_corr2;
            total <= total + 1;
            if (state_peak_det_c1 == NOISE_EST) 
                noise_accum <= noise_accum + mag_sq_corr1;
            if(swap_max_master)
                max_idx1_c1 <= max_idx2_c1;
            if(swap_c2_idx)
                max_idx1_c2 <= max_idx2_c2;
            prev_state_c1 <= state_peak_det_c1;
            prev_state_c2 <= state_peak_det_c2;
            sample_cntr <= sample_cntr + 1;
            buffer_idx <= buffer_idx + 1;
            buffer[buffer_idx] <= s_axis_data_in_tdata;
            if(mag_sq_corr1 > (noise_floor + threshold)) begin
                if(state_peak_det_c1 == FIRST_SEARCH && mag_sq_corr1 > max_mag1_c1) begin 
                    max_idx1_c1 <=  (buffer_idx[7:0] > 0) ? buffer_idx[7:0] - 1 : 255;
                    max_mag1_c1 <= mag_sq_corr1;
                end
                else if(state_peak_det_c1 == SECOND_SEARCH && mag_sq_corr1 > max_mag2_c1) begin
                    max_idx2_c1 <=  (buffer_idx[7:0] > 0) ? buffer_idx[7:0] - 1 : 255;
                    max_mag2_c1 <= mag_sq_corr1;
                end
            end
            if(mag_sq_corr2 > (noise_floor + threshold)) begin
                if(state_peak_det_c2 == FIRST_SEARCH && mag_sq_corr2 > max_mag1_c2) begin
                    max_idx1_c2 <=  (buffer_idx[7:0] > 0) ? buffer_idx[7:0] - 1 : 255;
                    max_mag1_c2 <= mag_sq_corr2;          
                end
                else if(state_peak_det_c2 == SECOND_SEARCH && mag_sq_corr2 > max_mag2_c2) begin
                    max_idx2_c2 <= (buffer_idx[7:0] > 0) ? buffer_idx[7:0] - 1 : 255;
                    max_mag2_c2 <= mag_sq_corr2;   
                end
             end
             if(prev_state_c1 == SECOND_SEARCH && state_peak_det_c1 != SECOND_SEARCH) begin
            // if(state_tx == TXING && samples_sent == 0) begin
                    max_idx1_c1 <= -1;
                    max_idx2_c1 <= -1;
                    max_mag1_c1 <= 0;
                    max_mag2_c1 <= 0;
             end   
            if(prev_state_c2 == SECOND_SEARCH && state_peak_det_c2 != SECOND_SEARCH) begin
            // if(state_tx == TXING && samples_sent == 0) begin
                    max_idx1_c2 <= -1;
                    max_idx2_c2 <= -1;
                    max_mag1_c2 <= 0;
                    max_mag2_c2 <= 0;
             end   
        end
        end
    end
    
    // The three slave axi stream interfaces must be active at the same time
    assert property (
        @(posedge axis_data_aclk)
	   ((s_axis_corr1_tvalid && s_axis_corr1_tready) || (s_axis_corr2_tvalid && s_axis_corr2_tready)
	           || (s_axis_data_in_tvalid && s_axis_data_in_tready) |-> (s_axis_corr1_tvalid && s_axis_corr1_tready) 
	           && (s_axis_corr2_tvalid && s_axis_corr2_tready)
	           && (s_axis_data_in_tvalid && s_axis_data_in_tready))
	   );
	// TLASTs of the correlators outputs should be asserted together
	assert property (
        @(posedge axis_data_aclk)
	   ((s_axis_corr1_tlast || s_axis_corr2_tlast)  |-> (s_axis_corr1_tlast && s_axis_corr2_tlast))
	);
	
	always @(posedge axis_data_aclk)
	   if(m_axis_data_tready && m_axis_data_tvalid)
	       count_mtvalid <= count_mtvalid + 1;
	
	// Make sure we output precisely 256 samples each time
	assert property (
        @(posedge axis_data_aclk)
	   (!(m_axis_data_tready && m_axis_data_tvalid)  |-> (count_mtvalid == 0))
	);
	
//	// Make sure either none or one of the two correlators is active at any point
//	assert property (
//        @(posedge axis_data_aclk)
//	   ((!active_correlator1 && !active_correlator2) || (active_correlator1 ^ active_correlator2))
//	);
	
	//Make sure start_idx doesn't change while state_tx is asserted
    assert property (
        @(posedge axis_data_aclk)
	   (state_tx |=> (($stable(start_idx) && state_tx) || !state_tx))
	);
	

	endmodule
