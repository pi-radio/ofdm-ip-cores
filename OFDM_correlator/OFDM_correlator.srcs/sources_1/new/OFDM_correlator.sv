
`timescale 1 ns / 1 ps

	module OFDM_correlator #
	(
	    parameter integer C_S00_AXIS_CONFIG_TDATA_WIDTH	= 32,
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128
	)
	(
		input wire  s_axis_aclk,
		input wire  s_axis_aresetn,
		output wire  s00_axis_tready,
		input wire [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input wire [(C_S00_AXIS_TDATA_WIDTH/8)-1 : 0] s00_axis_tstrb,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid,

		output wire  s00_axis_config_tready,
		input wire [C_S00_AXIS_CONFIG_TDATA_WIDTH-1 : 0] s00_axis_config_tdata,
		input wire [(C_S00_AXIS_CONFIG_TDATA_WIDTH/8)-1 : 0] s00_axis_config_tstrb,
		input wire  s00_axis_config_tlast,
		input wire  s00_axis_config_tvalid,

		output reg  m00_axis_tvalid,
		output reg [C_M00_AXIS_TDATA_WIDTH-1 : 0] m00_axis_tdata,
		output wire [(C_M00_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		output wire  m00_axis_tlast,
		input wire  m00_axis_tready
	);
	wire s_cmpy_a_ready[0 : 3];
	wire s_cmpy_b_ready[0 : 3];
	wire m_cmpy_valid[0 : 3];
	wire s_cmpy_a_valid, s_cmpy_b_valid;
	wire [127 : 0] sync_word_in;
	wire [127 : 0] sync_word_out;
    reg [9 : 0] sync_word_in_addr = 0;
    reg [7 : 0] sync_word_out_addr = 0;
    reg sync_word_in_en = 0;
    wire sync_word_out_en;
    reg [9 : 0] sync_word_count = 0;
    reg config_ready = 1;
    wire s_cmpy_a_all_ready;
    wire s_cmpy_b_all_ready;
    wire m_cmpy_all_valid;
    wire signed [31 : 0] tmp[0 : 3]; 
    wire signed [31 : 0] input_conj[0 : 3];
    wire [72 : 0] m_cmpy_data[0 : 3];
    reg [1 : 0] shift_reg;
    reg [255 : 0] input_shift_reg;
    reg [4 : 0] l;
    genvar i;
    wire signed [15 : 0] sync_word_re_signed[0 : 3];
    localparam fft_size = 1024;
    localparam samples_per_cycle = 4;
    reg [C_M00_AXIS_TDATA_WIDTH - 1 : 0] config_samples = 0;
    
    xpm_memory_sdpram #(
       .ADDR_WIDTH_A(8),               // DECIMAL
       .ADDR_WIDTH_B(8),               // DECIMAL
       .AUTO_SLEEP_TIME(0),            // DECIMAL
       .BYTE_WRITE_WIDTH_A(128),        // DECIMAL
       .CASCADE_HEIGHT(0),             // DECIMAL
       .CLOCKING_MODE("common_clock"), // String
       .ECC_MODE("no_ecc"),            // String
       .MEMORY_INIT_FILE("none"),      // String
       .MEMORY_INIT_PARAM("0"),        // String
       .MEMORY_OPTIMIZATION("true"),   // String
       .MEMORY_PRIMITIVE("auto"),      // String
       .MEMORY_SIZE(32768),             // DECIMAL
       .MESSAGE_CONTROL(0),            // DECIMAL
       .READ_DATA_WIDTH_B(128),         // DECIMAL
       .READ_LATENCY_B(2),             // DECIMAL
       .READ_RESET_VALUE_B("0"),       // String
       .RST_MODE_A("SYNC"),            // String
       .RST_MODE_B("SYNC"),            // String
       .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
       .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
       .USE_MEM_INIT(1),               // DECIMAL
       .USE_MEM_INIT_MMI(0),           // DECIMAL
       .WAKEUP_TIME("disable_sleep"),  // String
       .WRITE_DATA_WIDTH_A(128),        // DECIMAL
       .WRITE_MODE_B("no_change"),     // String
       .WRITE_PROTECT(1)               // DECIMAL
    )
    sync_word_ram_inst (                                
       .doutb(sync_word_out),
       .addra((sync_word_in_addr / 4) - 1),
       .addrb(sync_word_out_addr),
       .clka(s_axis_aclk),
       .clkb(s_axis_aclk),
       .dina(config_samples),
       .ena(sync_word_in_en),
       .enb(sync_word_out_en),
       .regceb(1),                        
       .wea(1)
    );
    
    corr_cmpy_0 cmpy_0_inst (
        .aclk(s_axis_aclk),                              // input wire aclk
        .aresetn(s_axis_aresetn),
        .s_axis_a_tvalid(s_cmpy_a_valid),        // input wire s_axis_a_tvalid
        .s_axis_a_tready(s_cmpy_a_ready[0]),        // output wire s_axis_a_tready
        .s_axis_a_tdata(input_conj[0]),          // input wire [31 : 0] s_axis_a_tdata
        .s_axis_b_tvalid(s_cmpy_b_valid),        // input wire s_axis_b_tvalid
        .s_axis_b_tready(s_cmpy_b_ready[0]),        // output wire s_axis_b_tready
        .s_axis_b_tdata(sync_word_out[31 : 0]),          // input wire [31 : 0] s_axis_b_tdata
        .m_axis_dout_tvalid(m_cmpy_valid[0]),  // output wire m_axis_dout_tvalid
        .m_axis_dout_tready(m00_axis_tready),  // input wire m_axis_dout_tready
        .m_axis_dout_tdata(m_cmpy_data[0])    // output wire [31 : 0] m_axis_dout_tdata
    );
    corr_cmpy_0 cmpy_1_inst (
        .aclk(s_axis_aclk),                              // input wire aclk
        .aresetn(s_axis_aresetn),
        .s_axis_a_tvalid(s_cmpy_a_valid),        // input wire s_axis_a_tvalid
        .s_axis_a_tready(s_cmpy_a_ready[1]),        // output wire s_axis_a_tready
        .s_axis_a_tdata(input_conj[1]),          // input wire [31 : 0] s_axis_a_tdata
        .s_axis_b_tvalid(s_cmpy_b_valid),        // input wire s_axis_b_tvalid
        .s_axis_b_tready(s_cmpy_b_ready[1]),        // output wire s_axis_b_tready
        .s_axis_b_tdata(sync_word_out[63 : 32]),          // input wire [31 : 0] s_axis_b_tdata
        .m_axis_dout_tvalid(m_cmpy_valid[1]),  // output wire m_axis_dout_tvalid
        .m_axis_dout_tready(m00_axis_tready),  // input wire m_axis_dout_tready
        .m_axis_dout_tdata(m_cmpy_data[1])    // output wire [31 : 0] m_axis_dout_tdata
    );
    corr_cmpy_0 cmpy_2_inst (
        .aclk(s_axis_aclk),                              // input wire aclk
        .aresetn(s_axis_aresetn),
        .s_axis_a_tvalid(s_cmpy_a_valid),        // input wire s_axis_a_tvalid
        .s_axis_a_tready(s_cmpy_a_ready[2]),        // output wire s_axis_a_tready
        .s_axis_a_tdata(input_conj[2]),          // input wire [31 : 0] s_axis_a_tdata
        .s_axis_b_tvalid(s_cmpy_b_valid),        // input wire s_axis_b_tvalid
        .s_axis_b_tready(s_cmpy_b_ready[2]),        // output wire s_axis_b_tready
        .s_axis_b_tdata(sync_word_out[95 : 64]),          // input wire [31 : 0] s_axis_b_tdata
        .m_axis_dout_tvalid(m_cmpy_valid[2]),  // output wire m_axis_dout_tvalid
        .m_axis_dout_tready(m00_axis_tready),  // input wire m_axis_dout_tready
        .m_axis_dout_tdata(m_cmpy_data[2])    // output wire [31 : 0] m_axis_dout_tdata
    );
    corr_cmpy_0 cmpy_3_inst (
        .aclk(s_axis_aclk),                              // input wire aclk
        .aresetn(s_axis_aresetn),
        .s_axis_a_tvalid(s_cmpy_a_valid),        // input wire s_axis_a_tvalid
        .s_axis_a_tready(s_cmpy_a_ready[3]),        // output wire s_axis_a_tready
        .s_axis_a_tdata(input_conj[3]),          // input wire [31 : 0] s_axis_a_tdata
        .s_axis_b_tvalid(s_cmpy_b_valid),        // input wire s_axis_b_tvalid
        .s_axis_b_tready(s_cmpy_b_ready[3]),        // output wire s_axis_b_tready
        .s_axis_b_tdata(sync_word_out[127 : 96]),          // input wire [31 : 0] s_axis_b_tdata
        .m_axis_dout_tvalid(m_cmpy_valid[3]),  // output wire m_axis_dout_tvalid
        .m_axis_dout_tready(m00_axis_tready),  // input wire m_axis_dout_tready
        .m_axis_dout_tdata(m_cmpy_data[3])    // output wire [31 : 0] m_axis_dout_tdata
    );
    
    generate
        for(i = 0; i < 4; i = i + 1) begin
            assign sync_word_re_signed[i] = sync_word_out[i * 32 +: 16];
        end
    endgenerate

    
    assign s_cmpy_a_all_ready = s_cmpy_a_ready[0] && s_cmpy_a_ready[1] && 
                                s_cmpy_a_ready[2] && s_cmpy_a_ready[3];
    assign s_cmpy_b_all_ready = s_cmpy_b_ready[0] && s_cmpy_b_ready[1] && 
                                s_cmpy_b_ready[2] && s_cmpy_b_ready[3];
    assign m_cmpy_all_valid = m_cmpy_valid[0] && m_cmpy_valid[1] && 
                                m_cmpy_valid[2] && m_cmpy_valid[3];
                                
    assign tmp[0] = input_shift_reg[31 : 16] * (-1);
    assign input_conj[0][31 : 16] = tmp[0][15 : 0];
    assign input_conj[0][15 : 0] = input_shift_reg[15 : 0];
    
    assign tmp[1] = input_shift_reg[63 : 48] * (-1);
    assign input_conj[1][31 : 16] = tmp[1][15 : 0];
    assign input_conj[1][15 : 0] = input_shift_reg[47 : 32];
    
    assign tmp[2] = input_shift_reg[95 : 80] * (-1);
    assign input_conj[2][31 : 16] = tmp[2][15 : 0];
    assign input_conj[2][15 : 0] = input_shift_reg[79 : 64];
    
    assign tmp[3] = input_shift_reg[127 : 112] * (-1);
    assign input_conj[3][31 : 16] = tmp[3][15 : 0];
    assign input_conj[3][15 : 0] = input_shift_reg[111 : 96];

    assign s00_axis_config_tready = config_ready;
    //assign sync_word_in_en = config_ready && s00_axis_config_tvalid;
    assign s00_axis_tready = !s00_axis_config_tready; //!s00_axis_config_tready && s_cmpy_a_all_ready;
    
//    assign m00_axis_tdata[15 : 0] = (m_cmpy_data[0][32 : 0] >> 15);
//    assign m00_axis_tdata[31 : 16] = (m_cmpy_data[0][72 : 40] >> 15);
//    assign m00_axis_tdata[47 : 32] = (m_cmpy_data[1][32 : 0] >> 15);
//    assign m00_axis_tdata[63 : 48] = (m_cmpy_data[1][72 : 40] >> 15);
//    assign m00_axis_tdata[79 : 64] = (m_cmpy_data[2][32 : 0] >> 15);
//    assign m00_axis_tdata[95 : 80] = (m_cmpy_data[2][72 : 40] >> 15);
//    assign m00_axis_tdata[111 : 96] = (m_cmpy_data[3][32 : 0] >> 15);
//    assign m00_axis_tdata[127 : 112] = (m_cmpy_data[3][72 : 40] >> 15);
    
    assign s_cmpy_b_valid = shift_reg[0] && s_axis_aresetn;//!s00_axis_config_tready;// && S_AXIS_TVALID && s_axis_a_tready && s_axis_b_tready && M_AXIS_TREADY;
    assign s_cmpy_a_valid = shift_reg[0] && s_axis_aresetn;
    assign sync_word_out_en = s00_axis_tvalid && !s00_axis_config_tready;

    always @(posedge s_axis_aclk) begin
        shift_reg <= {sync_word_out_en, shift_reg[1]};
    end
    
    always @(posedge s_axis_aclk) begin
        input_shift_reg <= {s00_axis_tdata, input_shift_reg[255 : 128]};
    end
    
    always @(posedge s_axis_aclk) begin
        if(!s_axis_aresetn) begin
            sync_word_in_addr <= 0;
            config_ready <= 1;
        end
        else begin
            if(sync_word_in_addr >= (fft_size - 1)) begin
                config_ready <= 0;
            end
            if(sync_word_in_en) sync_word_in_en <= 0;
            if(config_ready && s00_axis_config_tvalid) begin
                config_samples <= {s00_axis_config_tdata, config_samples[C_S00_AXIS_CONFIG_TDATA_WIDTH +:
                                                         (C_M00_AXIS_TDATA_WIDTH-C_S00_AXIS_CONFIG_TDATA_WIDTH)]};
                if(sync_word_in_addr < fft_size) begin
                    sync_word_in_addr <= sync_word_in_addr + 1;
                    if(sync_word_in_addr % samples_per_cycle == (samples_per_cycle - 1)) begin
                        sync_word_in_en <= 1;
                    end
                end
            end
        end
    end
    
    
    always @(posedge s_axis_aclk) begin
        if(!s_axis_aresetn) begin
            sync_word_out_addr <= 0;
        end
        else begin
            if(sync_word_out_en /* && s_cmpy_b_all_ready*/) begin//S_AXIS_TREADY && S_AXIS_TVALID && s_axis_a_tready && s_axis_b_tready && M_AXIS_TREADY) begin
                sync_word_out_addr <= sync_word_out_addr + 1;
            end
        end
    end
    
    always @(posedge s_axis_aclk) begin
        if(s_cmpy_a_valid) begin
            m00_axis_tvalid <= 1;
            for(l = 0; l < 4; l = l + 1) begin
                if(sync_word_re_signed[l] > 0) begin
                    m00_axis_tdata[l * 32 +: 16] <= input_conj[l][15 : 0];
                    m00_axis_tdata[l * 32 + 16 +: 16] <= input_conj[l][31 : 16];
                end
                else if(sync_word_re_signed[l] < 0) begin
                    m00_axis_tdata[l * 32 +: 16] <= (~input_conj[l][15 : 0]) + 1;
                    m00_axis_tdata[l * 32 + 16 +: 16] <= (~input_conj[l][31 : 16]) + 1;
                end
                else if(sync_word_re_signed[l] == 0) begin
                    m00_axis_tdata[l * 32 +: 32] <= 32'h00000000;
                end
            end
        end
        else
            m00_axis_tvalid <= 0;
    end
    // The multiplications should start two cycles after assertion of data_tvalid
    // because of the latency of the BRAM holding the sync word
    assert property (
        @(posedge s_axis_aclk)
	   ($rose(s00_axis_tvalid) |=> ##2 (s_cmpy_a_valid == 1))
	   );
	   
	// Assert that the input data to the complex multipliers are stable if
	// any of the controll signals are deasserted
    assert property (
        @(posedge s_axis_aclk)
	   (!(s_cmpy_a_valid && s_cmpy_a_all_ready 
	   && s_cmpy_b_valid && s_cmpy_b_all_ready) && s_axis_aresetn) |=> 
	   ($stable(sync_word_out) && $stable(input_conj[0]) && $stable(input_conj[1]) && 
	               $stable(input_conj[2]) && $stable(input_conj[3]))
	   );
	   
endmodule
