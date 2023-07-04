`timescale 1 ns / 1 ps

	module ssr_FFT #
	(
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer scaled = 1,
		parameter integer SSR = 4,
		parameter integer FFT_SHIFT = 0
	)
	(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output wire  s00_axis_tready,
		input wire [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input wire [(C_S00_AXIS_TDATA_WIDTH/8)-1 : 0] s00_axis_tstrb,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid,

		output wire  m00_axis_tvalid,
		output wire [C_M00_AXIS_TDATA_WIDTH-1 : 0] m00_axis_tdata,
		output wire [(C_M00_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		output wire  m00_axis_tlast,
		input wire  m00_axis_tready
	);
    localparam complex_size = 32;
    logic [(complex_size / 2) - 1 : 0] in_real[0 : SSR - 1];
	logic [(complex_size / 2) - 1 : 0] in_imag[0 : SSR - 1];
	logic [(C_M00_AXIS_TDATA_WIDTH / 4) - 1 : 0] m_axis_tdata_tmp[0 : 3];
	logic signed [(complex_size / 2) - 1 : 0] samps_out_real[0 : SSR - 1];
    logic signed [(complex_size / 2) - 1 : 0] samps_out_imag[0 : SSR - 1];
    logic [25 : 0] fft_out[0 : 7];
    logic [C_S00_AXIS_TDATA_WIDTH - 1 : 0] fft_shifted;
    logic fft_shifted_valid;
    logic [C_S00_AXIS_TDATA_WIDTH - 1 : 0] fft_not_shifted;
    logic fft_not_shifted_valid;
    logic [C_S00_AXIS_TDATA_WIDTH - 1 : 0] fft_shifted_in_data;
    logic fft_shifted_in_valid;
    
    assign fft_shifted_in_data = (FFT_SHIFT) ? fft_not_shifted : {C_S00_AXIS_TDATA_WIDTH{1'b0}};
    assign fft_shifted_in_valid = (FFT_SHIFT) ? fft_not_shifted_valid : 1'b0;
    assign m00_axis_tdata = (FFT_SHIFT) ? fft_shifted : fft_not_shifted;
    assign m00_axis_tvalid = (FFT_SHIFT) ? fft_shifted_valid : fft_not_shifted_valid;
    

	wire [9 : 0] scale_in;
	wire [9 : 0] scale_out;
    wire fft_valid_out;
    wire fft_last;
    reg [20 : 0] bit_index = 0;
    localparam shift_bits = 9;
    
    assign fft_not_shifted_valid = fft_valid_out;
    genvar k;
    generate
	   for(k = 0; k < SSR ; k++) begin
	       assign samps_out_real[k] = fft_out[k * 2][shift_bits +: (complex_size / 2)];
	       assign samps_out_imag[k] = fft_out[k * 2 + 1][shift_bits +: (complex_size / 2)];
	   end
	endgenerate
	
	genvar i;
	
	generate
	   for(i = 0; i < SSR ; i++) begin
	       assign in_real[i] = s00_axis_tdata[i * complex_size +: (complex_size / 2)];
	       assign in_imag[i] = s00_axis_tdata[i * complex_size + (complex_size / 2) +: (complex_size / 2)];
	   end
	endgenerate
	
    genvar l;
    
	generate
	   for(l = 0; l < SSR ; l++) begin
	       assign m_axis_tdata_tmp[l] = scaled ?
	                               {samps_out_imag[l], samps_out_real[l]} :  
	                               {6'h00, fft_out[l * 2 + 1], 6'h00, fft_out[l * 2]};
	   end
	endgenerate   
	
    assign fft_not_shifted = {m_axis_tdata_tmp[3],m_axis_tdata_tmp[2],
                                    m_axis_tdata_tmp[1],m_axis_tdata_tmp[0]};

	assign scale_in = 10'h000;
	assign s00_axis_tready = m00_axis_tready;

    sysgenssrfft_0 ssrfft_inst (
        .si(scale_in),         
        .vi(s00_axis_tvalid && m00_axis_tready),
        .i_im_0(in_imag[0]),
        .i_im_1(in_imag[1]),
        .i_re_0(in_real[0]),
        .i_re_1(in_real[1]),
        .i_im_2(in_imag[2]),
        .i_im_3(in_imag[3]),
        .i_re_2(in_real[2]),
        .i_re_3(in_real[3]),
        .clk(axis_aclk),
        .last(fft_last),
        .so(scale_out),
        .vo(fft_valid_out), 
        .o_im_0(fft_out[1]),
        .o_im_1(fft_out[3]),
        .o_re_0(fft_out[0]),
        .o_re_1(fft_out[2]),
        .o_im_2(fft_out[5]),
        .o_im_3(fft_out[7]),
        .o_re_2(fft_out[4]),
        .o_re_3(fft_out[6])
    );
    
    fftshift fftshift_inst(
        .clk(axis_aclk),
        .aresetn(axis_aresetn),
        .fft_in_tdata(fft_shifted_in_data),
        .fft_in_tvalid(fft_shifted_in_valid),
        .fft_out_tdata(fft_shifted),
        .fft_out_tvalid(fft_shifted_valid)
        );
    
    // Make sure s_tvalid is always asserted for at least 256 cycles  
	reg [7 : 0] count_s_valid = 0;
	always @(posedge axis_aclk) begin
        if(s00_axis_tvalid && s00_axis_tready)
            count_s_valid <= count_s_valid + 1;
    end
    assert property (@(posedge axis_aclk)
	   $fell(s00_axis_tvalid) |=> 
	               (count_s_valid == 0)); 
	assert property (@(posedge axis_aclk)
	   $fell(s00_axis_tready) |=> 
	               (count_s_valid == 0)); 

	endmodule

module fftshift #(
    parameter integer DATA_WIDTH = 128,
    parameter integer FFT_LENGTH = 256,
    parameter integer FIFO_SIZE = 2 * FFT_LENGTH
    )(
    input wire clk,
    input wire aresetn,
    input logic [DATA_WIDTH - 1 : 0] fft_in_tdata,
    input logic fft_in_tvalid,
    output logic [DATA_WIDTH - 1 : 0] fft_out_tdata,
    output logic fft_out_tvalid
    );
    
    localparam low = 112 / 4 - 1;
    localparam middle = 512 / 4 - 1;
    localparam high = 912 / 4 - 1;
    logic [255 : 0] samples_data_reg;
    logic [10 : 0] avail;
    logic test_valid;
    


    logic [$clog2(FIFO_SIZE) - 1 : 0] read_addr;
    logic [$clog2(FIFO_SIZE) - 1 : 0] write_addr;
    logic [$clog2(FIFO_SIZE) - 2 : 0] half_fft;
    logic read_enable, write_enable;
    logic [1 : 0] valid_shift_reg;
    logic [7 : 0] cnt = 0;
    
    always@(posedge clk)
        if(fft_out_tvalid) cnt <= cnt + 1;
    
    assign half_fft = FFT_LENGTH / 2;
    assign write_enable = fft_in_tvalid;
    assign fft_out_tvalid = valid_shift_reg[1];
    
    always@(posedge clk) begin
        if(fft_out_tvalid) begin
            if(cnt < low) begin
                test_valid <= 1;
                avail <= 0;
            end
            else if(cnt >= low && cnt < middle) begin
                avail <= 4;
                samples_data_reg <= {{128{1'b0}}, fft_out_tdata};
            end
            else if(cnt == middle) begin
                avail <= 3;
                samples_data_reg <= {{160{1'b0}}, fft_out_tdata[95 : 0]};
            end
            else if(cnt == middle + 1 && cnt < high) begin
                avail <= 4;
                samples_data_reg <= {{64{1'b0}},fft_out_tdata[127 : 32], samples_data_reg[95 : 0]};
            end
            else if(cnt > (middle + 1) && cnt < high) begin
                avail <= 4;
                samples_data_reg <= {{64{1'b0}},fft_out_tdata[127 : 0], samples_data_reg[128 +: 64]};
            end
            else if(cnt == high) begin
                avail <= 4;
                samples_data_reg <= {{96{1'b0}},fft_out_tdata[32 : 0], samples_data_reg[128 +: 64]};
            end
            else begin
                avail <= 0;
                test_valid <= 0;
            end
        end
    end
    
    always@(posedge clk) begin
        if(!aresetn) begin
            write_addr <= FFT_LENGTH / 2;
        end
        else begin
            if(fft_in_tvalid) begin
                if(write_addr[$clog2(FIFO_SIZE) - 2 : 0] == FFT_LENGTH - 1) begin
                    write_addr <= write_addr - FFT_LENGTH + 1;
                end 
                else if(write_addr[$clog2(FIFO_SIZE) - 2 : 0] == FFT_LENGTH / 2 - 1) begin
                    write_addr <= {~write_addr[$clog2(FIFO_SIZE) - 1], half_fft};
                end
                else
                    write_addr <= write_addr + 1;
            end
        end
    end
    
    always@(posedge clk) begin
        if(!aresetn) begin
            read_addr <= 0;
            read_enable <= 0;
        end
        else begin
            if(write_addr[$clog2(FIFO_SIZE) - 2 : 0] == 0 || read_enable) begin
                if(read_enable) read_addr <= read_addr  + 1;
                if(read_addr[$clog2(FIFO_SIZE) - 2 : 0] == FFT_LENGTH - 1) begin
                    if(read_addr == FIFO_SIZE - 1)
                        read_addr <= 0;
                    else
                        read_addr <= FFT_LENGTH;
                    read_enable <= 0;
                end
                else begin
                    read_enable <= 1;
                end
            end
        end
    end
    
    always@(posedge clk) begin
        if(!aresetn)
            valid_shift_reg <= 2'b0;
        else begin
            valid_shift_reg <= {valid_shift_reg[0], read_enable};
        end
    end

 xpm_memory_sdpram #(
   .ADDR_WIDTH_A($clog2(FIFO_SIZE)),  
   .ADDR_WIDTH_B($clog2(FIFO_SIZE)),    
   .AUTO_SLEEP_TIME(0),            // DECIMAL
   .BYTE_WRITE_WIDTH_A(DATA_WIDTH),        // DECIMAL
   .CASCADE_HEIGHT(0),             // DECIMAL
   .CLOCKING_MODE("common_clock"), // String
   .ECC_MODE("no_ecc"),            // String
   .MEMORY_INIT_FILE("none"),      // String
   .MEMORY_INIT_PARAM("0"),        // String
   .MEMORY_OPTIMIZATION("true"),   // String
   .MEMORY_PRIMITIVE("auto"),      // String
   .MEMORY_SIZE(FIFO_SIZE * DATA_WIDTH), // 2 time domain OFDM symbols
   .MESSAGE_CONTROL(0),            // DECIMAL
   .READ_DATA_WIDTH_B(DATA_WIDTH),  // DECIMAL
   .READ_LATENCY_B(2),             // DECIMAL
   .READ_RESET_VALUE_B("0"),       // String
   .RST_MODE_A("SYNC"),            // String
   .RST_MODE_B("SYNC"),            // String
   .SIM_ASSERT_CHK(1),             // DECIMAL; 0=disable simulation messages, 1=enable simulation messages
   .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
   .USE_MEM_INIT(1),               // DECIMAL
   .USE_MEM_INIT_MMI(0),           // DECIMAL
   .WAKEUP_TIME("disable_sleep"),  // String
   .WRITE_DATA_WIDTH_A(DATA_WIDTH),        // DECIMAL
   .WRITE_MODE_B("no_change"),     // String
   .WRITE_PROTECT(1)               // DECIMAL
)
symbol_ram_inst (                                
   .doutb(fft_out_tdata),
   .addra(write_addr),
   .addrb(read_addr),
   .clka(clk),
   .clkb(clk),
   .dina(fft_in_tdata),
   .ena(write_enable),
   .enb(read_enable),
   .regceb(1),                        
   .wea(1)
);       
endmodule