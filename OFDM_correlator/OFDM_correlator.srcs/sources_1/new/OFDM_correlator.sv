`timescale 1 ns / 1 ps

	module OFDM_correlator #
	(
	    parameter integer C_CONFIG_TDATA_WIDTH	= 32,
		parameter integer C_TDATA_WIDTH	= 128,
		parameter integer SSR = 4
	)
	(
		input wire  clk,
		input wire  resetn,
		output logic  s00_axis_tready,
		input logic [C_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input logic [(C_TDATA_WIDTH/8)-1 : 0] s00_axis_tstrb,
		input logic  s00_axis_tlast,
		input logic  s00_axis_tvalid,

		output logic  s00_axis_config_tready,
		input logic [C_CONFIG_TDATA_WIDTH-1 : 0] s00_axis_config_tdata,
		input logic [(C_CONFIG_TDATA_WIDTH/8)-1 : 0] s00_axis_config_tstrb,
		input logic  s00_axis_config_tlast,
		input logic  s00_axis_config_tvalid,

		output logic  m00_axis_tvalid,
		output logic [C_TDATA_WIDTH-1 : 0] m00_axis_tdata,
		output logic [(C_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		output logic  m00_axis_tlast,
		input logic  m00_axis_tready
	);
	localparam complex_width = C_TDATA_WIDTH / SSR;

	bram2corr_iface bram2corr();
	datain2corr_iface datain2corr();

	bram_sync_word bram_sync_word_inst(
	   .*,
	   .bram2corr(bram2corr)
	);
	data_in data_in_inst(
	   .*,
	   .datain2corr(datain2corr)
	);

    always_comb s00_axis_tready = bram2corr.config_done;
    always @(posedge clk) m00_axis_tvalid <= bram2corr.bram_valid;

    reg [4 : 0] l;
    genvar i, k;
    logic signed [15 : 0] sync_word_re_signed[0 : 3];

    generate
        for(i = 0; i < SSR; i = i + 1) begin
            assign sync_word_re_signed[i] = bram2corr.tdata[i * complex_width +: complex_width/2];
        end
    endgenerate

    assign bram2corr.bram_en = datain2corr.out_valid && s00_axis_tready;//!s00_axis_config_tready;
    assign datain2corr.out_ready = bram2corr.bram_valid;

    always @(posedge clk) begin
        if(bram2corr.bram_valid) begin
            for(l = 0; l < 4; l = l + 1) begin
                if(sync_word_re_signed[l] > 0) begin
                    m00_axis_tdata[l * 32 +: 16] <= datain2corr.conj_real[l];
                    m00_axis_tdata[l * 32 + 16 +: 16] <= datain2corr.conj_imag[l];
                end
                else if(sync_word_re_signed[l] < 0) begin
                    m00_axis_tdata[l * 32 +: 16] <= (~datain2corr.conj_real[l]) + 1;
                    m00_axis_tdata[l * 32 + 16 +: 16] <= (~datain2corr.conj_imag[l]) + 1;
                end
                else if(sync_word_re_signed[l] == 0) begin
                    m00_axis_tdata[l * 32 +: 32] <= 32'h00000000;
                end
            end
        end
    end

endmodule

module bram_sync_word #(
        parameter CONFIG_TDATA_WIDTH = 32,
        parameter TDATA_WIDTH = 128,
        parameter SSR = 4
    )
    (
        input wire clk,
        input wire resetn,
        input logic [CONFIG_TDATA_WIDTH-1 : 0] s00_axis_config_tdata,
		input logic  s00_axis_config_tlast,
		input logic  s00_axis_config_tvalid,
		output logic s00_axis_config_tready,
		bram2corr_iface.master bram2corr
    );
    localparam fft_size_words = bram2corr.FFT_SIZE/SSR;

    logic [$clog2(fft_size_words) : 0] config_word_count = 0;
    logic [$clog2(SSR) - 1 : 0] bram_in_enable_reg;
    logic bram_in_enable;
    logic [TDATA_WIDTH - 1 : 0] data_shift_reg = 0;
    logic [bram2corr.BRAM_LATENCY - 1 : 0] bram_out_valid_reg;
    logic [$clog2(fft_size_words) - 1 : 0] bram_out_addr;

    assign s00_axis_config_tready = (resetn && !bram2corr.config_done);

    always@(posedge clk) bram_in_enable <= (bram_in_enable_reg == (SSR - 1)) && !bram2corr.config_done;
    always@(posedge clk) begin
        if(!resetn)
            config_word_count <= 0;
        else
            config_word_count <= (bram_in_enable) ?
                    config_word_count + 1 : config_word_count;
    end

    always@(posedge clk) bram_out_valid_reg <= {bram2corr.bram_en, bram_out_valid_reg[bram2corr.BRAM_LATENCY - 1 : 1]};
    assign bram2corr.bram_valid = bram_out_valid_reg[0];
    always_comb bram2corr.config_done <= (config_word_count >= fft_size_words);

    always@(posedge clk) begin
        if(!resetn)
            bram_out_addr <= 0;
        else
            if(bram2corr.bram_en)
                bram_out_addr <= bram_out_addr + 1;
    end

    always@(posedge clk) begin
        if(!resetn) begin
            data_shift_reg <= 0;
            bram_in_enable_reg <= 0;
        end
        else begin
            if(s00_axis_config_tvalid) begin
                data_shift_reg <= {s00_axis_config_tdata, data_shift_reg[CONFIG_TDATA_WIDTH +: TDATA_WIDTH - CONFIG_TDATA_WIDTH]};
                bram_in_enable_reg <= bram_in_enable_reg + 1;
            end
        end
    end

     xpm_memory_sdpram #(
       .ADDR_WIDTH_A(8),               // DECIMAL
       .ADDR_WIDTH_B(8),               // DECIMAL
       .AUTO_SLEEP_TIME(0),            // DECIMAL
       .BYTE_WRITE_WIDTH_A(TDATA_WIDTH),        // DECIMAL
       .CASCADE_HEIGHT(0),             // DECIMAL
       .CLOCKING_MODE("common_clock"), // String
       .ECC_MODE("no_ecc"),            // String
       .MEMORY_INIT_FILE("none"),      // String
       .MEMORY_INIT_PARAM("0"),        // String
       .MEMORY_OPTIMIZATION("true"),   // String
       .MEMORY_PRIMITIVE("auto"),      // String
       .MEMORY_SIZE((bram2corr.FFT_SIZE/SSR) * TDATA_WIDTH),
       .MESSAGE_CONTROL(0),            // DECIMAL
       .READ_DATA_WIDTH_B(TDATA_WIDTH),         // DECIMAL
       .READ_LATENCY_B(2),             // DECIMAL
       .READ_RESET_VALUE_B("0"),       // String
       .RST_MODE_A("SYNC"),            // String
       .RST_MODE_B("SYNC"),            // String
       .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
       .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
       .USE_MEM_INIT(1),               // DECIMAL
       .USE_MEM_INIT_MMI(0),           // DECIMAL
       .WAKEUP_TIME("disable_sleep"),  // String
       .WRITE_DATA_WIDTH_A(TDATA_WIDTH),        // DECIMAL
       .WRITE_MODE_B("no_change"),     // String
       .WRITE_PROTECT(1)               // DECIMAL
    )
    sync_word_ram_inst (
       .doutb(bram2corr.tdata),
       .addra(config_word_count),
       .addrb(bram_out_addr),
       .clka(clk),
       .clkb(clk),
       .dina(data_shift_reg),
       .ena(bram_in_enable),
       .enb(bram2corr.bram_en),
       .regceb(1),
       .wea(1)
    );
endmodule

module data_in #(
        parameter C_TDATA_WIDTH = 128,
        parameter SSR = 4,
        parameter COMPLEX_WIDTH = 32
        )
        (
    	input wire  clk,
		input wire  resetn,
		input logic [C_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input logic  s00_axis_tlast,
		input logic  s00_axis_tvalid,
		datain2corr_iface.master datain2corr
    );
    genvar k;
    logic [C_TDATA_WIDTH - 1 : 0] fifo_out;
    logic fifo_in_rdy;

    generate
        for(k = 0; k < SSR; k = k + 1) begin
            assign datain2corr.conj_real[k] =  fifo_out[k * COMPLEX_WIDTH +: COMPLEX_WIDTH/2];
            assign datain2corr.conj_imag[k] =  fifo_out[k * COMPLEX_WIDTH + COMPLEX_WIDTH/2 +: COMPLEX_WIDTH/2] * (-1);
        end
    endgenerate

    xpm_fifo_axis #(
     .CDC_SYNC_STAGES(2), // DECIMAL
     .CLOCKING_MODE("common_clock"), // String
     .ECC_MODE("no_ecc"), // String
     .FIFO_DEPTH(16), // DECIMAL
     .FIFO_MEMORY_TYPE("auto"), // String
     .PACKET_FIFO("false"), // String
     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
     .RELATED_CLOCKS(0), // DECIMAL
     .SIM_ASSERT_CHK(0), // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
     .TDATA_WIDTH(C_TDATA_WIDTH), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    xpm_fifo_corr_2_inst (
     .m_axis_tdata(fifo_out),
     .m_axis_tvalid(datain2corr.out_valid),
     .s_axis_tready(fifo_in_rdy),
     .m_aclk(clk),
     .m_axis_tready(datain2corr.out_ready),
     .s_aclk(clk),
     .s_aresetn(resetn),
     .s_axis_tdata(s00_axis_tdata),
     .s_axis_tvalid(s00_axis_tvalid),
     .s_axis_tlast(s00_axis_tlast)
    );

endmodule
