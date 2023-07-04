
`timescale 1 ns / 1 ps

	module ssr_IFFT #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line

		// Parameters of Axi Slave Bus Interface S00_AXIS
		
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,

		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer FFT_SIZE                  = 1024,
		parameter integer CP_DURATION               = 256,
		parameter integer SSR                       = 4,
		parameter integer insert_cp                 = 0,
		parameter integer scaled                    = 0,
		parameter integer fft_shift                 = 0
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
		input wire  m00_axis_tready,
		
		output wire trigger,
		output wire trigger2
	);
	localparam tdata_out_width = (scaled) ? 128 : 256;
	localparam symbol_duration = (insert_cp) ? (FFT_SIZE + CP_DURATION)/4 : (FFT_SIZE)/4;
	
	module_iface #(.TDATA_WIDTH(tdata_out_width))ishift2ifft();
	module_iface #(.TDATA_WIDTH(tdata_out_width))ih2ifftshift();
	module_iface #(.TDATA_WIDTH(tdata_out_width))ifft2switch();
	module_iface #(.TDATA_WIDTH(tdata_out_width))cpadder2switch();
	module_iface #(.TDATA_WIDTH(tdata_out_width))switch2tlast();
	tlast2out_iface #(.TDATA_WIDTH(tdata_out_width)) tlast2out();
	input_handler #(.CP_INSERT(insert_cp))
	   input_handler_inst(
        .clk(s_axis_aclk),
        .aresetn(s_axis_aresetn),
        .ih2ifftshift(ih2ifftshift),
        .s00_axis_tready(s00_axis_tready),
        .s00_axis_tdata(s00_axis_tdata),
        .s00_axis_tlast(s00_axis_tlast),
        .s00_axis_tvalid(s00_axis_tvalid)
	);
	ifftshift #(.ENABLE(fft_shift))
	  ifftshift_inst(
        .clk(s_axis_aclk),
        .aresetn(s_axis_aresetn),
        .ih2ifftshift(ih2ifftshift),
        .ishift2ifft(ishift2ifft)
    );
    
	ifft #(.SCALED(scaled))ifft_inst(
	    .clk(s_axis_aclk),
        .aresetn(s_axis_aresetn),
	   .ishift2ifft(ishift2ifft),
	   .ifft2switch(ifft2switch)
	);
	cp_adder cp_adder_inst(
	   .clk(s_axis_aclk),
        .aresetn(s_axis_aresetn),
        .ifft2cpadder(ifft2switch),
	   .*
	);
	
	switch #(.CP_INSERT(insert_cp))
	   switch_inst(
	   .clk(s_axis_aclk),
       .aresetn(s_axis_aresetn),
	   .*	
	);
	
	tlast_insert#(.DURATION(symbol_duration)) tlast_insert_inst(
	   .clk(s_axis_aclk),
       .aresetn(s_axis_aresetn),
	   .*
	);
	
	assign m00_axis_tdata = tlast2out.tdata;
	assign m00_axis_tvalid = tlast2out.tvalid;
	assign m00_axis_tlast = tlast2out.tlast;


    // Make sure the CP is added properly by checking if the
    // last 64 samples transmitted for every frame are the same
    // as the first 64. We also keep a counter register for help
    
    logic [10 : 0] count_test_cp ;
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

//    /*Make sure we never fill-up the FIFO */
//    assert property (@(posedge s_axis_aclk)
//	   (!(!s_fifo_ready && fft_valid && insert_cp)));

//    /* Make sure data does not change if FIFO saxis_tready or tvalid deasserts*/
//	assert property (@(posedge s_axis_aclk)
//	   (s_fifo_valid && !s_fifo_ready && s_axis_aresetn && insert_cp)
//	       |=> s_fifo_valid && $stable(s_fifo_data));

//	assert property (@(posedge s_axis_aclk)
//	   (!s_fifo_valid && s_fifo_ready && s_axis_aresetn && insert_cp)
//	       |-> $stable(s_fifo_data));

//	// Make sure s_tvalid is always asserted for at least 256 cycles
	
//	always @(posedge s_axis_aclk) begin
//        if(s00_axis_tvalid && s00_axis_tready)
//            count_s_valid <= count_s_valid + 1;
//    end
//    assert property (@(posedge s_axis_aclk)
//	   $fell(s00_axis_tvalid) |=>
//	               (count_s_valid == 0));
//	assert property (@(posedge s_axis_aclk)
//	   $fell(s00_axis_tready) |=>
//	               (count_s_valid == 0));
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

    module input_handler #(
        parameter integer S_AXIS_TDATA_WIDTH = 128,
        parameter integer IFFT_SIZE          = 1024,
        parameter integer SSR                = 4,
        parameter integer CP_LEN             = 256,
        parameter integer CP_INSERT          = 0
    )
    (
        input wire  clk,
		input wire  aresetn,
		output logic  s00_axis_tready,
		input logic [S_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input logic  s00_axis_tlast,
		input logic  s00_axis_tvalid,
		module_iface.master ih2ifftshift
    );
    localparam symbol_duration = (CP_INSERT) ? (IFFT_SIZE + CP_LEN) / SSR : IFFT_SIZE / SSR;
    logic [$clog2((IFFT_SIZE/SSR) + (CP_LEN / SSR)) - 1 : 0] input_count;
    logic inv_input;
    
    assign s00_axis_tready = (input_count < (IFFT_SIZE / SSR) && !inv_input);
    assign ih2ifftshift.tdata = (inv_input) ? 2 : s00_axis_tdata;
    assign ih2ifftshift.tvalid = (input_count < (IFFT_SIZE / SSR)) && (input_count != 0 || s00_axis_tvalid);
    
    // This logic block handles cases where the input is not asserted for
    // the required period, so in order not to mess up the IFFT afterwards
    // we use the inv_input register to fill the remaining input to the 
    // subsequent IFFT with zeros and maintain the FFT SIZE window.
    
    always@(posedge clk) begin
        if(!aresetn) inv_input <= 0;
        else begin
            if((input_count != 0 && input_count < (IFFT_SIZE / SSR)) 
                    && !s00_axis_tvalid) begin
                inv_input <= 1;
            end
            else if(input_count == (symbol_duration - 1)) begin
                inv_input <= 0;
            end
        end
    end
    
    // The input_count register starts counting as soon as valid input is present
    // And stops only after the FFT_LENGTH + CP_LENTH period has passed
    
    always@(posedge clk) begin
        if(!aresetn) input_count <= 0;
        else begin
            if(s00_axis_tvalid && input_count == 0) begin
                input_count <= input_count + 1;
            end
            else if(input_count != 0) begin
                if(input_count < (symbol_duration - 1))
                    input_count <= input_count + 1;
                else
                    input_count <= 0;
            end
        end
    end
    
    endmodule
    
    module ifftshift #(
    parameter integer DATA_WIDTH = 128,
    parameter integer FFT_LENGTH = 256,
    parameter integer FIFO_SIZE = 2 * FFT_LENGTH,
    parameter integer ENABLE = 0
    )(
    input wire clk,
    input wire aresetn,
    module_iface.slave ih2ifftshift,
    module_iface.master ishift2ifft
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
    logic [DATA_WIDTH - 1 : 0] data_out;
    
    always@(posedge clk)
        if(ishift2ifft.tvalid) cnt <= cnt + 1;
    
    assign half_fft = FFT_LENGTH / 2;
    
    assign write_enable = (ENABLE) ? ih2ifftshift.tvalid : 0;
    assign ishift2ifft.tvalid = (ENABLE) ? valid_shift_reg[1] : ih2ifftshift.tvalid;
    assign ishift2ifft.tdata = (ENABLE) ? data_out : ih2ifftshift.tdata;
    
    always@(posedge clk) begin
        if(ishift2ifft.tvalid && ENABLE) begin
            if(cnt < low) begin
                test_valid <= 1;
                avail <= 0;
            end
            else if(cnt >= low && cnt < middle) begin
                avail <= 4;
                samples_data_reg <= {{128{1'b0}}, ishift2ifft.tdata};
            end
            else if(cnt == middle) begin
                avail <= 3;
                samples_data_reg <= {{160{1'b0}}, ishift2ifft.tdata[95 : 0]};
            end
            else if(cnt == middle + 1 && cnt < high) begin
                avail <= 4;
                samples_data_reg <= {{64{1'b0}},ishift2ifft.tdata[127 : 32], samples_data_reg[95 : 0]};
            end
            else if(cnt > (middle + 1) && cnt < high) begin
                avail <= 4;
                samples_data_reg <= {{64{1'b0}},ishift2ifft.tdata[127 : 0], samples_data_reg[128 +: 64]};
            end
            else if(cnt == high) begin
                avail <= 4;
                samples_data_reg <= {{96{1'b0}},ishift2ifft.tdata[32 : 0], samples_data_reg[128 +: 64]};
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
            if(ih2ifftshift.tvalid && ENABLE) begin
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
            if(ENABLE) begin
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
   .doutb(data_out),
   .addra(write_addr),
   .addrb(read_addr),
   .clka(clk),
   .clkb(clk),
   .dina(ih2ifftshift.tdata),
   .ena(write_enable),
   .enb(read_enable),
   .regceb(1),                        
   .wea(1)
);       
endmodule
    
    
    module ifft #(
        parameter integer SCALED             = 1,
        parameter integer SSR                = 4
    )
    (
        input wire  clk,
		input wire  aresetn,
		module_iface.slave ishift2ifft,
		module_iface.master ifft2switch
    );
    localparam complex_size = 32;
    localparam shift_bits = 8;
    logic [9 : 0] scale_in;
    logic [9 : 0] scale_out;
    logic [(complex_size / 2) - 1 : 0] in_real[0 : SSR - 1];
	logic [(complex_size / 2) - 1 : 0] in_imag[0 : SSR - 1];
	logic signed [(complex_size / 2) - 1 : 0] samps_out_real[0 : SSR - 1];
    logic signed [(complex_size / 2) - 1 : 0] samps_out_imag[0 : SSR - 1];
    logic [25 : 0] ifft_out[0 : 2 * SSR - 1];
    logic [(ifft2switch.TDATA_WIDTH / 4) - 1 : 0] data_out[0 : 3];
    logic fft_valid;
    logic [ifft2switch.TDATA_WIDTH - 1 : 0] data_fifo_in;
    logic fifo_ready;
	
	assign scale_in = 10'h000;
    
    genvar i,k;
	
	generate
	   for(i = 0; i < SSR ; i++) begin
	       assign in_real[i] = ishift2ifft.tdata[i * complex_size +: (complex_size / 2)];
	       assign in_imag[i] = ishift2ifft.tdata[i * complex_size + (complex_size / 2) +: (complex_size / 2)];
	   end
	endgenerate
	
	generate
	   for(k = 0; k < SSR ; k++) begin
	       assign samps_out_real[k] = ifft_out[k * 2][shift_bits +: (complex_size / 2)];
	       assign samps_out_imag[k] = ifft_out[k * 2 + 1][shift_bits +: (complex_size / 2)];
	   end
	endgenerate

    genvar l;
    
	generate
	   for(l = 0; l < SSR ; l++) begin
	       assign ifft2switch.tdata[(l + 1) * ifft2switch.TDATA_WIDTH/SSR - 1 : l * ifft2switch.TDATA_WIDTH/SSR] = SCALED ?
	                               {samps_out_imag[l], samps_out_real[l]} :  
	                               {6'h00, ifft_out[l * 2 + 1], 6'h00, ifft_out[l * 2]};
	   end
	endgenerate 
	
	assign ifft2switch.tvalid = fft_valid;
    
     sysgenssrifft_0 ssr_ifft_inst (
        .si(scale_in),
        .vi(ishift2ifft.tvalid),
        .i_im_0(in_imag[0]),
        .i_im_1(in_imag[1]),
        .i_re_0(in_real[0]),
        .i_re_1(in_real[1]),
        .i_im_2(in_imag[2]),
        .i_im_3(in_imag[3]),
        .i_re_2(in_real[2]),
        .i_re_3(in_real[3]),
        .clk(clk),
        .so(scale_out),
        .vo(fft_valid),
        .o_im_0(ifft_out[1]),
        .o_im_1(ifft_out[3]),
        .o_re_0(ifft_out[0]),
        .o_re_1(ifft_out[2]),
        .o_im_2(ifft_out[5]),
        .o_im_3(ifft_out[7]),
        .o_re_2(ifft_out[4]),
        .o_re_3(ifft_out[6])
    );
    
    
      
    endmodule
    
    module cp_adder #(
        parameter integer CP_LEN             = 256,
        parameter integer FFT_SIZE           = 1024,
        parameter integer SSR                = 4
    )
    (
        input wire  clk,
		input wire  aresetn,
		module_iface.slave ifft2cpadder,
		module_iface.master cpadder2switch
    );
    localparam bram_read_latency = 2;
    localparam symbol_size = (FFT_SIZE + CP_LEN) / SSR;
    logic [$clog2(FFT_SIZE/SSR) : 0] write_addr;
    logic [$clog2(FFT_SIZE/SSR) : 0] read_addr;
    logic [127 : 0] out;
    logic read_enable;
    logic copy_cp;
    logic [$clog2(FFT_SIZE/SSR) - 1 : 0] write_in_buffer_addr;
    logic write_buffer_idx;
    logic [$clog2(FFT_SIZE/SSR) - 1 : 0] read_in_buffer_addr;
    logic read_buffer_idx;
    logic [bram_read_latency - 1 : 0] tvalid_shift_reg;
    
    logic test; 
    logic [7 : 0] tt;
    
    assign read_in_buffer_addr  = read_addr[$clog2(FFT_SIZE/SSR) - 1 : 0];
    assign read_buffer_idx      = read_addr[$clog2(FFT_SIZE/SSR)];
    assign write_buffer_idx     = write_addr[$clog2(FFT_SIZE/SSR)];
    assign write_in_buffer_addr = write_addr[$clog2(FFT_SIZE/SSR) - 1: 0];
    
    assign cpadder2switch.tvalid = tvalid_shift_reg[bram_read_latency  - 1];
    
    always@(posedge clk) begin
        if(!aresetn) tvalid_shift_reg <= 0;
        else begin
            tvalid_shift_reg <= {tvalid_shift_reg[bram_read_latency - 2 : 0], read_enable};
        end
    end
    
    always@ (posedge clk) begin
        if(!aresetn) write_addr <= 0;
        else begin
            if(ifft2cpadder.tvalid)
                if(write_addr < symbol_size * 2 - 1)
                    write_addr <= write_addr + 1;
                else
                      write_addr <= 0; 
        end
    end
    
    always@ (posedge clk) begin
        if(!aresetn) begin
            read_addr <= 0;
            read_enable <= 0;
            copy_cp <= 1;
        end
        else begin
            if( write_in_buffer_addr == (FFT_SIZE - CP_LEN)/SSR) begin
                read_enable <= 1;
                read_addr <= {write_buffer_idx, write_in_buffer_addr};
                copy_cp <= 1;
            end
            else if((read_in_buffer_addr == FFT_SIZE/SSR - 1) && copy_cp) begin
                read_addr <= {read_buffer_idx, {$clog2(FFT_SIZE/SSR){1'b0}}};
                copy_cp <= 0;
            end
            else if ((read_in_buffer_addr == FFT_SIZE/SSR - 1) && !copy_cp) begin
                read_enable <= 0;
                copy_cp <= 1;
            end
            else if(read_enable)
                read_addr <= read_addr + 1;
        end
    end
    
    
    xpm_memory_sdpram #(
       .ADDR_WIDTH_A(9),               // DECIMAL
       .ADDR_WIDTH_B(9),               // DECIMAL
       .AUTO_SLEEP_TIME(0),            // DECIMAL
       .BYTE_WRITE_WIDTH_A(ifft2cpadder.TDATA_WIDTH),        // DECIMAL
       .CASCADE_HEIGHT(0),             // DECIMAL
       .CLOCKING_MODE("common_clock"), // String
       .ECC_MODE("no_ecc"),            // String
       .MEMORY_INIT_FILE("none"),      // String
       .MEMORY_INIT_PARAM("0"),        // String
       .MEMORY_OPTIMIZATION("true"),   // String
       .MEMORY_PRIMITIVE("auto"),      // String
       .MEMORY_SIZE(65536),             // DECIMAL
       .MESSAGE_CONTROL(0),            // DECIMAL
       .READ_DATA_WIDTH_B(ifft2cpadder.TDATA_WIDTH),         // DECIMAL
       .READ_LATENCY_B(bram_read_latency),             // DECIMAL
       .READ_RESET_VALUE_B("0"),       // String
       .RST_MODE_A("SYNC"),            // String
       .RST_MODE_B("SYNC"),            // String
       .SIM_ASSERT_CHK(1),             // DECIMAL
       .USE_EMBEDDED_CONSTRAINT(0),    // DECIMAL
       .USE_MEM_INIT(1),               // DECIMAL
       .USE_MEM_INIT_MMI(0),           // DECIMAL
       .WAKEUP_TIME("disable_sleep"),  // String
       .WRITE_DATA_WIDTH_A(ifft2cpadder.TDATA_WIDTH),        // DECIMAL
       .WRITE_MODE_B("no_change"),     // String
       .WRITE_PROTECT(1)               // DECIMAL
    )
    cp_bram_inst (
       .doutb(cpadder2switch.tdata),
       .addra(write_addr),
       .addrb(read_addr),
       .clka(clk),
       .clkb(clk),
       .dina(ifft2cpadder.tdata),
       .ena(ifft2cpadder.tvalid),
       .enb(read_enable),
       .regceb(1),
       .wea(1)
    );
    endmodule
    
    module switch #(
        parameter integer CP_INSERT = 0
        )(
        input wire  clk,
		input wire  aresetn,
		module_iface.slave ifft2switch,
		module_iface.slave cpadder2switch,
		module_iface.slave switch2tlast
    );
    
    assign switch2tlast.tdata = (CP_INSERT) ? cpadder2switch.tdata : ifft2switch.tdata;
    assign switch2tlast.tvalid = (CP_INSERT) ? cpadder2switch.tvalid : ifft2switch.tvalid;
        
    endmodule
    
    module tlast_insert #(
        parameter integer DURATION = 256
        )(
        input wire  clk,
		input wire  aresetn,
		module_iface.slave switch2tlast,
		tlast2out_iface.master tlast2out
    );
    
    logic [$clog2(DURATION) : 0] counter;
    
    assign tlast2out.tdata = switch2tlast.tdata;
    assign tlast2out.tvalid = switch2tlast.tvalid;
    assign tlast2out.tlast = (counter == DURATION - 1);
    
    always@(posedge clk) begin
        if(!aresetn)
            counter <= 0;
        else begin
            if(switch2tlast.tvalid) begin
                if(counter < DURATION - 1) counter <= counter + 1;
                else counter <= 0;
             end
        end
            
    end
        
    endmodule