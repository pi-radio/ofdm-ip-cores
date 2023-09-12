module demod_soft_out
        import demodulator_package::*;
        #(
        parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 128,
		parameter integer SSR                       = 4,
		parameter integer ESTIMATION_WIDTH          = 8
		)
		(
		input wire  axis_aclk,
		input wire  axis_aresetn,
		output logic  s00_axis_tready,
		input logic [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input logic  s00_axis_tlast,
		input logic  s00_axis_tvalid,

		output logic  out_soft_axis_tvalid,
		output logic [C_M00_AXIS_TDATA_WIDTH-1 : 0] out_soft_axis_tdata,
		input logic  out_soft_axis_tready,
		mod_t modulation
    );
    logic [ESTIMATION_WIDTH - 1 : 0] demod_out_tdata[SSR * 2];
    logic demod_out_tvalid;
    logic demod_out_tready;
    logic [10 : 0] bits_available;
    
//    assign s00_axis_tready = out_soft_axis_tready;
//    assign out_soft_axis_tdata = 128'hdedede;
//    assign out_soft_axis_tvalid = s00_axis_tvalid;
    
    mod2soft mod2soft_inst(
        .clk(axis_aclk),
        .aresetn(axis_aresetn),
        .in_tdata(s00_axis_tdata),
        .in_tready(s00_axis_tready),
        .in_tvalid(s00_axis_tvalid),
        .in_tlast(s00_axis_tlast),
        .out_tdata(demod_out_tdata),
        .out_tvalid(demod_out_tvalid),
        .out_tready(demod_out_tready),
        .modulation(modulation),
        .bits_available(bits_available)
    );
      
    packager packager_inst(
        .clk(axis_aclk),
        .aresetn(axis_aresetn),
        .in_tdata(demod_out_tdata),
        .in_tvalid(demod_out_tvalid),
        .in_tready(demod_out_tready),
        .out_tdata(out_soft_axis_tdata),
        .out_tvalid(out_soft_axis_tvalid),
        .out_tready(out_soft_axis_tready),
        .bits_available(bits_available),
        .modulation(modulation)
    );
//    packager packager_inst(
//        .clk(axis_aclk),
//        .aresetn(axis_aresetn),
//        .in_tdata(demod_out_tdata),
//        .in_tvalid(demod_out_tvalid),
//        .in_tready(demod_out_tready),
//        .out_tdata(demod_out_tdata),
//        .out_tvalid(out_soft_axis_tvalid),
//        .out_tready(demod_out_tready),
//        .bits_available(bits_available),
//        .modulation(modulation)
//    );
    
endmodule

module mod2soft
        import demodulator_package::*;
        #(
        parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 64,
		parameter integer ESTIMATION_WIDTH          = 8,
		parameter integer SAMPLE_WIDTH              = 32,
		parameter integer SSR                       = 4
        )
        (
        input wire  clk,
		input wire  aresetn,
		output logic in_tready,
		input logic [C_S00_AXIS_TDATA_WIDTH-1 : 0] in_tdata,
		input logic  in_tlast,
		input logic  in_tvalid,
		output logic [ESTIMATION_WIDTH - 1 : 0] out_tdata[SSR*2],
		output logic out_tvalid,
		input logic out_tready,
		output logic [10 : 0] bits_available,
		mod_t modulation
    );
    localparam max_in_bits = 9;
    logic signed [max_in_bits - 1 : 0] mm = (1 << (max_in_bits - 1 )) + 1;
    logic signed [max_in_bits - 1 : 0] mmc = (1 << (max_in_bits - 1 )) - 1;
//    logic signed [16 - 1 : 0] r_min = {7'hff, mm};
//    logic signed [16 - 1 : 0] r_max = {7'h00, mmc};
    logic signed [5 : 0] t_min = (1 << 5) + 1;
    logic signed [5 : 0] t_max = {22'b0, 6'd31};
    logic signed [16 - 1 : 0] in_real[SSR];
    logic signed [16 - 1 : 0] in_imag[SSR];
    logic [1 : 0] valid_shift_reg;
    
//        localparam max_in_bits = 9;
    logic signed [15 : 0] r_min = (1 << 15) + 1;
    logic signed [15 : 0] r_max = ~(1 << 15);
//    logic signed [5 : 0] t_min = (1 << 5) + 1;
//    logic signed [5 : 0] t_max = {22'b0, 6'd31};
//    logic signed [15 : 0] in_real[SSR];
//    logic signed [15 : 0] in_imag[SSR];
//    logic [1 : 0] valid_shift_reg;
    
    assign out_tvalid = valid_shift_reg[0];
    assign in_tready = out_tready;
    
    assign bits_available = (modulation == BPSK) ? 4 : 8;
    
    always@(posedge clk) begin
        if(!aresetn)
            valid_shift_reg <= 0;
        else begin
            valid_shift_reg <= {valid_shift_reg[0], in_tvalid};
        end
    end
    
    logic signed [16 - 1 : 0] interm[8];
        
    genvar i,j;
    
    for(j = 0; j < SSR; j++) begin
        assign in_real[j] = in_tdata[j * SAMPLE_WIDTH +: SAMPLE_WIDTH / 2] ;
        assign in_imag[j] = in_tdata[j * SAMPLE_WIDTH + SAMPLE_WIDTH / 2 +: SAMPLE_WIDTH / 2];
    end
    
    for(i = 0; i < SSR; i++) begin
        always@(posedge clk) begin
            if(in_tvalid) begin
                if(modulation == BPSK) begin
                    interm[i * 2] <= (((in_real[i]- r_min)/(r_max-r_min)) * (t_max - t_min) + t_min); //(in_real[i] > 0) ? {2'b00, t_max,8'h00} : {2'b11,t_min,8'h00};
                end
                else if (modulation == QPSK) begin
                    interm[2 * i] <= (((in_real[i] - r_min)/(r_max-r_min)) * (t_max - t_min) + t_min);
                    interm[2 * i + 1] <= (((in_imag[i] - r_min)/(r_max-r_min)) * (t_max - t_min) + t_min);
                end
            end
        end   
    end
    
    for(i = 0; i < SSR; i++) begin
        always@(posedge clk) begin
            if(in_tvalid && out_tready) begin
                if(modulation == BPSK) begin
                    out_tdata[2 * i] <= in_real[i][11 : 4];//(interm[i * 2]) >> 8;
                end
                else if (modulation == QPSK) begin
                    out_tdata[2 * i] <= in_real[i][11 : 4]; ;//(interm[2 * i] >> 8);
                    out_tdata[2 * i + 1] <= in_imag[i][11 : 4]; ;//(interm[2 * i + 1] >> 8);
                end
            end
        end   
    end    
    
endmodule

//module demod
//        import demodulator_package::*;
//        #(
//        parameter integer C_S00_AXIS_TDATA_WIDTH	= 128,
//		parameter integer C_M00_AXIS_TDATA_WIDTH	= 64,
//		parameter integer ESTIMATION_WIDTH          = 8,
//		parameter integer SAMPLE_WIDTH              = 32,
//		parameter integer SSR                       = 4
//        )
//        (
//        input wire  clk,
//		input wire  aresetn,
//		output logic  s00_axis_tready,
//		input logic [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
//		input logic  s00_axis_tlast,
//		input logic  s00_axis_tvalid,
//		output logic [C_M00_AXIS_TDATA_WIDTH - 1 : 0] out_tdata,
//		output logic out_tvalid,
//		input logic out_tready,
//		output logic [10 : 0] bits_available,
//		mod_t modulation
//    );
//    logic signed [15 : 0] r_min = (1 << 15) + 1;
//    logic signed [15 : 0] r_max = ~(1 << 15);
//    logic signed [5 : 0] t_min = (1 << 5) + 1;
//    logic signed [5 : 0] t_max = {22'b0, 6'd31};
//    logic signed [15 : 0] ti;
//    logic signed [15 : 0] t1,t2;

    
    	
//	function signed [5 : 0] scale;
//	   input signed [15 : 0] val;
//	   begin
//	       t1 = (((val - r_min)/(r_max-r_min)) * (t_max - t_min) + t_min);
//	       scale <=  t1[15 : 10];
//	   end
//	endfunction 
//		function signed [5 : 0] scale1;
//	   input signed [15 : 0] val;
//	   begin
//	       t1 <= (((val - r_min)/(r_max-r_min)) * (t_max - t_min) + t_min);
//	       scale1 <=  t1[15 : 10];
//	   end
//	endfunction 
    
//   assign s00_axis_tready = out_tready;
     
//    genvar i;
    
//    for(i = 0; i < SSR; i++) begin
//        always@(posedge clk) begin
//            if(s00_axis_tvalid) begin
//                if(modulation == BPSK) begin
//                    out_tdata[i * ESTIMATION_WIDTH +: ESTIMATION_WIDTH] <= 
//                            scale(s00_axis_tdata[i * SAMPLE_WIDTH +: SAMPLE_WIDTH / 2]);
//                    out_tvalid <= 1;
//                end
//                else if(modulation == QPSK) begin
//                    out_tdata[i * ESTIMATION_WIDTH * 2 +: ESTIMATION_WIDTH ] <= 
//                            scale(s00_axis_tdata[i * SAMPLE_WIDTH +: SAMPLE_WIDTH / 2]);
//                    out_tdata[i * ESTIMATION_WIDTH * 2 + ESTIMATION_WIDTH +: ESTIMATION_WIDTH] <= 
//                            scale(s00_axis_tdata[31  : 16]);
//                            //scale(s00_axis_tdata[i * SAMPLE_WIDTH + SAMPLE_WIDTH / 2 +: SAMPLE_WIDTH / 2]);
//                    out_tvalid <= 1;
//                end
//            end
//            else
//                out_tvalid <= 0;
//        end
//    end
    
//endmodule

module packager
        import demodulator_package::*;
        #(
        parameter integer IN_TDATA_WIDTH            = 64,
        parameter integer OUT_TDATA_WIDTH	        = 128,
        parameter integer NUM_LANES                 = 1,
		parameter integer ESTIMATION_WIDTH          = 8,
		parameter integer SSR                       = 4
        )
        (
        input wire  clk,
		input wire  aresetn,
		input logic [ESTIMATION_WIDTH - 1 : 0] in_tdata[SSR * 2],
		input logic in_tvalid,
		output logic in_tready,
		output logic [OUT_TDATA_WIDTH - 1 : 0] out_tdata,
		output logic out_tvalid,
		input logic out_tready,
		input logic [10 : 0] bits_available,
		mod_t modulation
    );
    logic [10 : 0] cnt;
    assign in_tready = out_tready;
    
    always@(posedge clk) begin
        if(!aresetn)
            out_tvalid <= 0;
        else begin
            if(in_tvalid) begin
                out_tvalid <= (cnt == (OUT_TDATA_WIDTH * NUM_LANES)/ (ESTIMATION_WIDTH * bits_available) - 1) ?
                                1 : 0;
            end
            else
                out_tvalid <= 0;
        end
   end
        
    
    always@(posedge clk) begin
        if(!aresetn)
            cnt <= 0;
        else begin
            if(in_tvalid) begin
                if(cnt < (OUT_TDATA_WIDTH * NUM_LANES)/ (ESTIMATION_WIDTH * bits_available) - 1)
                    cnt <= cnt + 1;
                else
                    cnt <= 0;
            end
//            else if(in_tready && !in_tvalid && cnt != 0)
//                cnt <= 0;
        end
    end
    
    always@(posedge clk) begin
        if(in_tvalid) begin
            if(modulation == BPSK) begin
                out_tdata[cnt * ESTIMATION_WIDTH * SSR +: ESTIMATION_WIDTH * SSR] 
                                            <= {in_tdata[6], in_tdata[4], in_tdata[2] ,in_tdata[0] };
            end
            else if(modulation == QPSK) begin
                out_tdata[cnt * ESTIMATION_WIDTH * SSR * 2 +: ESTIMATION_WIDTH * SSR * 2] 
                                            <= {in_tdata[7], in_tdata[6], in_tdata[5] ,in_tdata[4],
                                                in_tdata[3], in_tdata[2], in_tdata[1] ,in_tdata[0] };
            end
        end
    end
    
    
endmodule