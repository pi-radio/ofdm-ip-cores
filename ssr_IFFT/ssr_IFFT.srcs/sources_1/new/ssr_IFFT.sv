
`timescale 1 ns / 1 ps

	module ssr_IFFT_v1_0 #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Slave Bus Interface S00_AXIS
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,

		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 256,
		parameter integer insert_cp = 0,
		parameter integer scaled = 0
	)
	(
		input wire  s_axis_aclk,
		input wire  s_axis_aresetn,
		output wire  s00_axis_tready,
		input wire [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid,

		output wire  m00_axis_tvalid,
		output wire [C_M00_AXIS_TDATA_WIDTH - 1 : 0] m00_axis_tdata,
		output wire  m00_axis_tlast,
		input wire  m00_axis_tready
	);
    
    typedef enum {IDLE, OUT_CP, OUT_DATA} out_state_t;
    out_state_t state = IDLE;
	wire [C_S00_AXIS_TDATA_WIDTH/2 - 1 : 0] in_real;
	wire [C_S00_AXIS_TDATA_WIDTH/2 - 1: 0] in_imag;
    wire [9 : 0] scale_in;
    wire [(C_M00_AXIS_TDATA_WIDTH / 4) - 1 : 0] m_axis_out_tdata_tmp[0 : 3];
    wire [9 : 0] out_scale;
    wire signed [15 : 0] samp0_real;
    wire signed [15 : 0] samp0_imag;
    wire signed [15 : 0] samp1_real;
    wire signed [15 : 0] samp1_imag;
    wire signed [15 : 0] samp2_real;
    wire signed [15 : 0] samp2_imag;
    wire signed [15 : 0] samp3_real;
    wire signed [15 : 0] samp3_imag;
    reg [8 : 0] read_index = 192;
    reg [8 : 0] write_index = 0;
    wire sysgen_fft_in_valid;
    reg [10 : 0]tlast_counter = 0;
    wire [127 : 0] interm_buff_input;
    wire [127 : 0] interm_buff_output;
    wire en_interm_buff_in;
    wire en_interm_buff_out;
    reg [1 : 0] shift_reg = 0; 
    reg [1 : 0] avail = 0;
    wire s_fifo_valid;
    wire s_fifo_ready;
    wire [127 : 0] s_fifo_data;
    wire fft_valid;
    wire [127 : 0] m_fifo_data;
    wire m_fifo_valid;
    reg [20 : 0] count_input = 0;
    reg [20 : 0] count_test_cp = 0;
    wire [25 : 0] o_im_0;
    wire [25 : 0] o_im_1;
    wire [25 : 0] o_re_0;
    wire [25 : 0] o_re_1;
    wire [25 : 0] o_im_2;
    wire [25 : 0] o_im_3;
    wire [25 : 0] o_re_2;
    wire [25 : 0] o_re_3;
    
    xpm_memory_sdpram #(
       .ADDR_WIDTH_A(9),               // DECIMAL
       .ADDR_WIDTH_B(9),               // DECIMAL
       .AUTO_SLEEP_TIME(0),            // DECIMAL
       .BYTE_WRITE_WIDTH_A(128),        // DECIMAL
       .CASCADE_HEIGHT(0),             // DECIMAL
       .CLOCKING_MODE("common_clock"), // String
       .ECC_MODE("no_ecc"),            // String
       .MEMORY_INIT_FILE("none"),      // String
       .MEMORY_INIT_PARAM("0"),        // String
       .MEMORY_OPTIMIZATION("true"),   // String
       .MEMORY_PRIMITIVE("auto"),      // String
       .MEMORY_SIZE(65536),             // DECIMAL
       .MESSAGE_CONTROL(0),            // DECIMAL
       .READ_DATA_WIDTH_B(128),         // DECIMAL
       .READ_LATENCY_B(2),             // DECIMAL
       .READ_RESET_VALUE_B("0"),       // String
       .RST_MODE_A("SYNC"),            // String
       .RST_MODE_B("SYNC"),            // String
       .SIM_ASSERT_CHK(1),             // DECIMAL
       .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
       .USE_MEM_INIT(1),               // DECIMAL
       .USE_MEM_INIT_MMI(0),           // DECIMAL
       .WAKEUP_TIME("disable_sleep"),  // String
       .WRITE_DATA_WIDTH_A(128),        // DECIMAL
       .WRITE_MODE_B("no_change"),     // String
       .WRITE_PROTECT(1)               // DECIMAL
    )
    interm_buffer_inst (                                
       .doutb(interm_buff_output),
       .addra(write_index),
       .addrb(read_index),
       .clka(s_axis_aclk),
       .clkb(s_axis_aclk),
       .dina(m_fifo_data),
       .ena(m_fifo_valid),
       .enb(en_interm_buff_out),
       .regceb(1),                        
       .wea(1)
    );
    
    xpm_fifo_axis #(
     .CDC_SYNC_STAGES(2), // DECIMAL
     .CLOCKING_MODE("common_clock"), // String
     .ECC_MODE("no_ecc"), // String
     .FIFO_DEPTH(2048), // DECIMAL
     .FIFO_MEMORY_TYPE("auto"), // String
     .PACKET_FIFO("false"), // String
     .PROG_EMPTY_THRESH(10), // DECIMAL
     .PROG_FULL_THRESH(257), // DECIMAL
     .RD_DATA_COUNT_WIDTH(1), // DECIMAL
     .RELATED_CLOCKS(0), // DECIMAL
     .SIM_ASSERT_CHK(0), // DECIMAL
     .TDATA_WIDTH(128), // DECIMAL
     .TDEST_WIDTH(1), // DECIMAL
     .TID_WIDTH(1), // DECIMAL
     .TUSER_WIDTH(1), // DECIMAL
     .USE_ADV_FEATURES("1000"), // String
     .WR_DATA_COUNT_WIDTH(1) // DECIMAL
    )
    output_fifo_inst (
     .m_axis_tdata(m_fifo_data),
     .m_axis_tvalid(m_fifo_valid),
     .m_axis_tlast(m_axis_data_tlast),
     .s_axis_tready(s_fifo_ready),
     .m_aclk(axis_aclk),
     .m_axis_tready(en_interm_buff_in),
     .s_aclk(s_axis_aclk),
     .s_aresetn(s_axis_aresetn),
     .s_axis_tdata(s_fifo_data),
     .s_axis_tvalid(fft_valid),
     .s_axis_tlast(s_axis_fifo_tlast)
    );
    
    sysgenssrifft_0 ssr_ifft_inst (
        .si(scale_in), 
        .vi(sysgen_fft_in_valid), 
        .i_im_0(in_imag[15 : 0]), 
        .i_im_1(in_imag[31 : 16]),
        .i_re_0(in_real[15 : 0]),
        .i_re_1(in_real[31 : 16]),
        .i_im_2(in_imag[47 : 32]), 
        .i_im_3(in_imag[63 : 48]),
        .i_re_2(in_real[47 : 32]), 
        .i_re_3(in_real[63 : 48]), 
        .clk(s_axis_aclk),    
        .last(last), 
        .so(out_scale),
        .vo(fft_valid), 
        .o_im_0(o_im_0), 
        .o_im_1(o_im_1), 
        .o_re_0(o_re_0),
        .o_re_1(o_re_1), 
        .o_im_2(o_im_2),
        .o_im_3(o_im_3),  
        .o_re_2(o_re_2),  
        .o_re_3(o_re_3)  
    );
    
    assign en_interm_buff_in = m_fifo_valid && insert_cp;
    assign s_fifo_data = {m_axis_out_tdata_tmp[3],m_axis_out_tdata_tmp[2],
                                                m_axis_out_tdata_tmp[1],m_axis_out_tdata_tmp[0]};
    assign en_interm_buff_out = (state == OUT_CP || state == OUT_DATA);
    assign m00_axis_tdata = (insert_cp) ? interm_buff_output : {m_axis_out_tdata_tmp[3],m_axis_out_tdata_tmp[2],
                                                        m_axis_out_tdata_tmp[1],m_axis_out_tdata_tmp[0]};
    assign m00_axis_tvalid = (insert_cp) ? shift_reg[0] : fft_valid;
    assign scale_in = 10'h000;
    assign samp0_real = o_re_0[25 : 10];;//o_re_0>>>10;// o_re_0[23 : 8];
    assign samp0_imag = o_im_0[25 : 10];//o_im_0>>>10;//o_im_0[23 : 8];
    assign samp1_real = o_re_1[25 : 10];//o_re_1>>>10;//
    assign samp1_imag = o_im_1[25 : 10];//o_im_1>>>10;//
    assign samp2_real = o_re_2[25 : 10]; //o_re_2>>>10;//
    assign samp2_imag = o_im_2[25 : 10];//o_im_2>>>10;//
    assign samp3_real = o_re_3[25 : 10];//o_re_3>>>10;// 
    assign samp3_imag = o_im_3[25 : 10];//o_im_3>>>10;//
    
    assign m00_axis_tlast = (insert_cp) ? tlast_counter == 319 : tlast_counter == 255;
    assign s00_axis_tready = (insert_cp) ? (count_input <= 255) : 1;
	assign sysgen_fft_in_valid = (insert_cp) ? s00_axis_tready && s00_axis_tvalid : s00_axis_tvalid;

	/* Adjust input to be in the form the sysgen core needs it, ie. all real parts and all imaginary bit_index
	together */
	
	assign in_real[15 : 0] = s00_axis_tdata[15 : 0];
    assign in_imag[15 : 0] = s00_axis_tdata[31 : 16];
    assign in_real[31 : 16] = s00_axis_tdata[47 : 32];
    assign in_imag[31 : 16] = s00_axis_tdata[63 : 48];
    assign in_real[47 : 32] = s00_axis_tdata[79 : 64];
    assign in_imag[47 : 32] = s00_axis_tdata[95 : 80];
    assign in_real[63 : 48] = s00_axis_tdata[111 : 96];
    assign in_imag[63 : 48] = s00_axis_tdata[127 : 112];
    
    assign m_axis_out_tdata_tmp[0][(C_M00_AXIS_TDATA_WIDTH / 4) - 1  : 0] = scaled ? {samp0_imag, samp0_real} :
                                                                        {6'h00, o_im_0, 6'h00, o_re_0};
    assign m_axis_out_tdata_tmp[1][(C_M00_AXIS_TDATA_WIDTH / 4) - 1  : 0] = scaled ? {samp1_imag, samp1_real} :
                                                                        {6'h00, o_im_1, 6'h00, o_re_1};
    assign m_axis_out_tdata_tmp[2][(C_M00_AXIS_TDATA_WIDTH / 4) - 1  : 0] = scaled ? {samp2_imag, samp2_real} :
                                                                        {6'h00, o_im_2, 6'h00, o_re_2};
    assign m_axis_out_tdata_tmp[3][(C_M00_AXIS_TDATA_WIDTH / 4) - 1  : 0] = scaled ? {samp3_imag, samp3_real} :
                                                                        {6'h00, o_im_3, 6'h00, o_re_3};
    
    always@(posedge s_axis_aclk) begin
        shift_reg <= {en_interm_buff_out, shift_reg[1]};
    end
    
    always@(posedge s_axis_aclk) begin
        if(!s_axis_aresetn) begin
            write_index <= 0;
            read_index <= 192;
            state <= IDLE;
        end
        else begin
            if(en_interm_buff_in) begin
                write_index <= write_index + 1;
                if(write_index[7 : 0] == 0)
                    avail[write_index[8]] <= 1;
            end
            if(write_index[7 : 0] == 8'hff && (state == IDLE || state == OUT_DATA)) begin
                state <= OUT_CP;
                avail[read_index[8]] <= 0;
            end
            if(state == OUT_CP)
                if(read_index[7 : 0] < 8'hff)
                    read_index <= read_index + 1;
                else begin
                    state <= OUT_DATA;
                    read_index <= {read_index[8], 8'h00};
                end
            if(state == OUT_DATA) begin
                if(read_index[7 : 0] < 8'hff)
                    read_index <= read_index + 1;
                else begin
                    if(avail[~read_index[8]]) begin
                        state <= OUT_CP;
                        read_index <= {~read_index[8], 8'hC0}; 
                    end
                    else begin
                        state <= IDLE;
                        read_index <= {~read_index[8], 8'hC0}; 
                    end
                end
            end
        end
    end 
    
    always@(posedge s_axis_aclk) begin
        if(!s_axis_aresetn)
            tlast_counter <= 0;
         else begin
            if(m00_axis_tready && m00_axis_tvalid) begin
                if(insert_cp) begin
                    if(tlast_counter < 319)
                        tlast_counter <= tlast_counter + 1;
                    else
                        tlast_counter <= 0;
                end
                else begin
                     if(tlast_counter < 255)
                        tlast_counter <= tlast_counter + 1;
                    else
                        tlast_counter <= 0;               
                end
            end
         end
    end
    
    /* Input condition refers to the first symbol which is to be output.
    *  For that first symbol only we do not deassert s_axis_tready. We start
    *  deasserting it only from the second symbol on for latency reasons.
    * 
    */
    always @(posedge s_axis_aclk) begin
        if(!s_axis_aresetn)
            count_input <= 0;
        else begin
            if(s00_axis_tvalid || (!s00_axis_tvalid && count_input != 0)) begin
                if(count_input < 319)
                    count_input <= count_input + 1;
                else
                    count_input <= 0;
            end
        end
    end

    // Make sure the CP is added properly by checking if the
    // last 64 samples transmitted for every frame are the same
    // as the first 64. We also keep a counter register for help
    always@(posedge s_axis_aclk) begin
        if(!s_axis_aresetn)
            count_test_cp <= 0;
        else begin
            if(m00_axis_tready && m00_axis_tvalid) begin
                if(count_test_cp < 319)
                    count_test_cp <= count_test_cp + 1;
                else
                    count_test_cp <= 0;
            end
        end
    end

    always@(posedge s_axis_aclk) begin
        if(insert_cp && count_test_cp > 255)
            assert(m00_axis_tdata == $past(m00_axis_tdata, 256));
    end
    
    /*Make sure we never fill-up the FIFO */
    assert property (@(posedge s_axis_aclk)
	   (!(!s_fifo_ready && fft_valid && insert_cp)));
    
    /* Make sure data does not change if FIFO saxis_tready or tvalid deasserts*/
	assert property (@(posedge s_axis_aclk)
	   (s_fifo_valid && !s_fifo_ready && s_axis_aresetn && insert_cp)
	       |=> s_fifo_valid && $stable(s_fifo_data));
	
	assert property (@(posedge s_axis_aclk)
	   (!s_fifo_valid && s_fifo_ready && s_axis_aresetn && insert_cp)
	       |-> $stable(s_fifo_data)); 
	       
	// Make sure s_tvalid is always asserted for at least 256 cycles  
	reg [7 : 0] count_s_valid = 0;
	always @(posedge s_axis_aclk) begin
        if(s00_axis_tvalid && s00_axis_tready)
            count_s_valid <= count_s_valid + 1;
    end
    assert property (@(posedge s_axis_aclk)
	   $fell(s00_axis_tvalid) |=> 
	               (count_s_valid == 0)); 
	assert property (@(posedge s_axis_aclk)
	   $fell(s00_axis_tready) |=> 
	               (count_s_valid == 0)); 
	// Make sure we output multiples of 256 / 320 samples depending if we also add the CP          
	reg [8 : 0] count_m_valid = 0;
	always @(posedge s_axis_aclk) begin
        if(m00_axis_tvalid && m00_axis_tready)
            if(!insert_cp)
                count_m_valid <= count_m_valid + 1;
            else begin
                if(count_m_valid < 319)
                    count_m_valid <= count_m_valid + 1;
                else
                    count_m_valid <= 0;
            end
    end
    assert property (@(posedge s_axis_aclk)
	   ($fell(m00_axis_tvalid)) |=> 
	               (count_m_valid == 0));                
	
	endmodule
