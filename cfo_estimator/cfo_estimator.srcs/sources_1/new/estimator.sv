module estimator#(
    parameter integer S_AXIS_TDATA_WIDTH = 128)
    (
    input wire clk,
    input wire aresetn,
    input logic [S_AXIS_TDATA_WIDTH - 1 : 0] s_axis_tdata,
    input logic s_axis_tvalid,
    output logic [S_AXIS_TDATA_WIDTH - 1 : 0] m_axis_tdata,
    output logic m_axis_tvalid,
    bram_ctrl_iface.master bram_ctrl,
    bram_ctrl_iface.master bram_cp_ctrl,
    adder2correction_iface.master adder2correction,
    bram_ctrl2mult_iface.master bram_ctrl2mult
    );
    bram_ctrl2corr_iface bram_ctrl2corr();
    corr2adder_iface corr2adder();
    
    bram_controller #(.BRAM_SIZE_SSR(640))
      bram_controller_inst(
      .clk(clk),
      .aresetn(aresetn),
      .s_tdata(s_axis_tdata),
      .s_tvalid(s_axis_tvalid),
      .bram_ctrl(bram_ctrl),
      .bram_cp_ctrl(bram_cp_ctrl),
      .bram_ctrl2corr(bram_ctrl2corr),
      .bram_ctrl2mult(bram_ctrl2mult)
    );
    
    correlator correlator_inst(
      .clk(clk),
      .aresetn(aresetn),
      .bram_ctrl2corr(bram_ctrl2corr),
      .corr2adder(corr2adder)
    );
    
    adder adder_inst(
      .clk(clk),
      .aresetn(aresetn),
      .corr2adder(corr2adder),
      .adder2correction(adder2correction)
    );
endmodule

module bram_controller #(
    parameter integer DATA_WIDTH = 128,
    parameter integer BRAM_SIZE_SSR = 640,
    parameter integer BRAM_CP_SIZE = 128,
    parameter integer FFT_SIZE = 256,
    parameter integer CP_SIZE = 64)(
    input wire clk,
    input wire aresetn,
    input logic [DATA_WIDTH - 1 : 0] s_tdata,
    input logic s_tvalid,
    bram_ctrl_iface.master bram_ctrl,
    bram_ctrl_iface.master bram_cp_ctrl,
    bram_ctrl2corr_iface.master bram_ctrl2corr,
    bram_ctrl2mult_iface.master bram_ctrl2mult
    );
    
    logic                         cyclic_suffix,cyclic_prefix;
    logic [2* DATA_WIDTH - 1 : 0] bram_data_in_sr, bram_cp_in_sr;
    logic [1 : 0]                 bram_valid_sr,bram_cp_sr;
    logic                         current_frame = 0;
    logic                         bram_cp_valid;
    logic                         tlast;
    logic [2 : 0]                 tlast_sr;
    
    
    
    assign cyclic_prefix = ((bram_ctrl.write_addr >= 0) && (bram_ctrl.write_addr < CP_SIZE)) ||
                            ((bram_ctrl.write_addr >= (FFT_SIZE + CP_SIZE))
                                     && (bram_ctrl.write_addr < (FFT_SIZE + 2 * CP_SIZE)));
    assign cyclic_suffix = ((bram_ctrl.write_addr >= FFT_SIZE) && (bram_ctrl.write_addr < FFT_SIZE + CP_SIZE)) ||
                            ((bram_ctrl.write_addr >= FFT_SIZE + (FFT_SIZE + CP_SIZE))
                                     && (bram_ctrl.write_addr < FFT_SIZE + CP_SIZE) + (FFT_SIZE + CP_SIZE));
    assign bram_ctrl.write_enable = s_tvalid;
    assign bram_ctrl.write_data = s_tdata;
    assign bram_cp_ctrl.read_enable = cyclic_suffix;
    assign bram_cp_ctrl.write_data = s_tdata;
    assign bram_cp_ctrl.write_enable = cyclic_prefix && s_tvalid;
    assign bram_cp_valid = bram_cp_sr[1];
    assign bram_ctrl2corr.symbol_last = tlast_sr[2];
    assign bram_ctrl2mult.symbol_tvalid = bram_valid_sr[1];
    assign bram_ctrl2mult.symbol_data = bram_ctrl.read_data;
    
    always@(posedge clk) begin
        if(~aresetn) begin
            bram_data_in_sr <= {2* DATA_WIDTH{1'b0}};
            bram_cp_sr <= 2'b0;
            bram_valid_sr <= 2'b0;
            tlast_sr <= 2'b0;
        end 
        begin
            bram_cp_sr <= {bram_cp_sr[0], bram_cp_ctrl.read_enable};
            bram_valid_sr <= {bram_valid_sr[0], bram_ctrl.read_enable};
            bram_data_in_sr <= {bram_data_in_sr[DATA_WIDTH - 1 : 0], s_tdata};
            tlast_sr <= {tlast_sr[1 : 0], tlast};
        end 
    end
    
    /* Write into BRAM for symbol */
    always@(posedge clk) begin
        if(~aresetn)
            bram_ctrl.write_addr <= 0;
        else begin
            if(s_tvalid) begin
                if(bram_ctrl.write_addr < BRAM_SIZE_SSR - 1)
                    bram_ctrl.write_addr <= bram_ctrl.write_addr + 1;
                else
                    bram_ctrl.write_addr <= 0;
            end
        end
    end
    
    /* Write into BRAM for cyclic prefix */
    always@(posedge clk) begin
        if(~aresetn)
            bram_cp_ctrl.write_addr <= 0;
        else begin
            if(s_tvalid && cyclic_prefix) begin
                if(bram_cp_ctrl.write_addr < BRAM_CP_SIZE - 1)
                    bram_cp_ctrl.write_addr <= bram_cp_ctrl.write_addr + 1;
                else
                    bram_cp_ctrl.write_addr <= 0;
            end
        end
    end
    
    always@(posedge clk) begin
        if(~aresetn)
            bram_cp_ctrl.read_addr <= 0;
         else begin
            if(tlast) tlast <= 0;
            if(cyclic_suffix) begin
                if(bram_cp_ctrl.read_addr < BRAM_CP_SIZE - 1) begin
                    bram_cp_ctrl.read_addr <= bram_cp_ctrl.read_addr + 1;
                    if((bram_cp_ctrl.read_addr == BRAM_CP_SIZE / 2 - 2) ||
                             (bram_cp_ctrl.read_addr == BRAM_CP_SIZE - 2)) begin
                        tlast <= 1;         
                    end
                end
                else
                    bram_cp_ctrl.read_addr <= 0;
            end
         end
    end
    
    always@(posedge clk) begin
        if(bram_cp_valid) begin
            bram_ctrl2corr.suffix_data <= bram_data_in_sr[DATA_WIDTH +: DATA_WIDTH]; // Take the second item in the shift reg
            bram_ctrl2corr.prefix_data <= bram_cp_ctrl.read_data;
            bram_ctrl2corr.tvalid <= 1;
        end
        else
            bram_ctrl2corr.tvalid <= 0;
    end
    
    always@(posedge clk) begin
        if(~aresetn) begin
            bram_ctrl.read_addr <= CP_SIZE;
        end
        else begin
            if(bram_ctrl2mult.mult_ready) bram_ctrl.read_enable <= 1;
            if(bram_ctrl.read_enable && (bram_ctrl.read_addr < BRAM_SIZE_SSR /2 ||
                                        ((bram_ctrl.read_addr > BRAM_SIZE_SSR /2) 
                                     && (bram_ctrl.read_addr < BRAM_SIZE_SSR)))) begin
                if(bram_ctrl.read_addr == (BRAM_SIZE_SSR /2 - 1) || (bram_ctrl.read_addr == BRAM_SIZE_SSR - 1)) begin
                    bram_ctrl.read_addr <= (bram_ctrl.read_addr == (BRAM_SIZE_SSR /2 - 1)) ? 
                                            BRAM_SIZE_SSR /2 + CP_SIZE :
                                            CP_SIZE;
                    bram_ctrl.read_enable <= 0;
                end
                else begin
                    bram_ctrl.read_addr <= bram_ctrl.read_addr + 1;
                end
            end
        end
    end
    
    
    assert property (@(posedge clk)
	   cyclic_suffix |-> ((bram_ctrl.write_addr >= 256 && bram_ctrl.write_addr < 320 )
	            || (bram_ctrl.write_addr >= 576 && bram_ctrl.write_addr < 640 ))); 
    assert property (@(posedge clk)
	   cyclic_prefix |-> ((bram_ctrl.write_addr >= 0 && bram_ctrl.write_addr < 64 )
	            || (bram_ctrl.write_addr >= 320 && bram_ctrl.write_addr < 384 ))); 
    assert property (@(posedge clk) // Do not write and read concurrently at the same position
	   (bram_ctrl.write_enable && bram_ctrl.read_enable) |-> (bram_ctrl.write_addr != bram_ctrl.read_addr));
    
    assert property (@(posedge clk) // Make sure the output data is correct.
	   (bram_ctrl2corr.tvalid == 1) |-> bram_ctrl2corr.prefix_data == $past(s_tdata,259));
	assert property (@(posedge clk) // 
	   (bram_ctrl2corr.tvalid == 1) |-> bram_ctrl2corr.suffix_data == $past(s_tdata,3));
	assert property (@(posedge clk) // Cyclic prefix valid should stay on for 64 cycles
	   $rose(bram_ctrl2corr.tvalid) |-> ##[0:63] bram_ctrl2corr.tvalid ##1 $fell(bram_ctrl2corr.tvalid));	 
	assert property (@(posedge clk) // Symbol read should stay on for FFT length cycles
	   $rose(bram_ctrl.read_enable) |-> ##[0:255] bram_ctrl.read_enable ##1 $fell(bram_ctrl.read_enable));
	 
endmodule

module correlator (
    input wire clk,
    input wire aresetn,
    bram_ctrl2corr_iface.slave bram_ctrl2corr,
    corr2adder_iface.master corr2adder
    );
    logic signed [bram_ctrl2corr.COMPLEX_SIZE/2 - 1 : 0] suffix_reals[0 : 3];
    logic signed [bram_ctrl2corr.COMPLEX_SIZE/2 - 1 : 0] suffix_imags[0 : 3];
    logic signed [bram_ctrl2corr.COMPLEX_SIZE/2 - 1 : 0] prefix_reals[0 : 3];
    logic signed [bram_ctrl2corr.COMPLEX_SIZE/2 - 1 : 0] prefix_imags[0 : 3];
    
    genvar i;
    logic [3 : 0] k;
    generate
        for(i = 0; i < corr2adder.SSR ; i = i + 1) begin
            assign suffix_reals[i] = bram_ctrl2corr.suffix_data[i * bram_ctrl2corr.COMPLEX_SIZE +: bram_ctrl2corr.COMPLEX_SIZE/2];
            assign prefix_reals[i] = bram_ctrl2corr.prefix_data[i * bram_ctrl2corr.COMPLEX_SIZE +: bram_ctrl2corr.COMPLEX_SIZE/2];
            assign suffix_imags[i] = bram_ctrl2corr.suffix_data[i * bram_ctrl2corr.COMPLEX_SIZE + bram_ctrl2corr.COMPLEX_SIZE/2 
                                                                                +: bram_ctrl2corr.COMPLEX_SIZE/2];
            assign prefix_imags[i] = bram_ctrl2corr.prefix_data[i * bram_ctrl2corr.COMPLEX_SIZE + bram_ctrl2corr.COMPLEX_SIZE/2 
                                                                                +: bram_ctrl2corr.COMPLEX_SIZE/2];
        end
    endgenerate
    
    always@(posedge clk) begin
        if(~aresetn) begin
            for(k = 0; k < corr2adder.SSR; k = k + 1) begin
                corr2adder.corr_data_real[k] <= 0;
                corr2adder.corr_data_imag[k] <= 0;
            end
        end 
        else begin
            if(corr2adder.symbol_last) corr2adder.symbol_last <= 0;
            if(bram_ctrl2corr.tvalid) begin
                if(bram_ctrl2corr.symbol_last) corr2adder.symbol_last <= 1;
                corr2adder.tvalid <= 1;
                for(k = 0; k < corr2adder.SSR; k = k + 1) begin
                    corr2adder.corr_data_real[k] <= ((suffix_reals[k] * prefix_reals[k]) + (suffix_imags[k] * prefix_imags[k]));
                    corr2adder.corr_data_imag[k] <= ((suffix_reals[k] * prefix_imags[k] * (-1)) + (suffix_imags[k] * prefix_reals[k]));
                end
            end
            else
                corr2adder.tvalid <= 0;
        end
    end
endmodule

module adder (
    input wire clk,
    input wire aresetn,
    corr2adder_iface.slave corr2adder,
    adder2correction_iface.master adder2correction
    );
    logic signed [31 : 0] sum_real;
    logic signed [31 : 0] sum_imag;
        
    //assign adder2correction.angle = {sum_imag, sum_real};
    assign adder2correction.angle[31 : 0] = (sum_real[31 : 30] == 2'b10 || sum_real[31 : 29] == 2'b01) ?
                                                    sum_real >> 2 : sum_real;
    assign adder2correction.angle[63 : 32] = (sum_imag[31 : 30] == 2'b10 || sum_imag[31 : 29] == 2'b01) ?
                                                    sum_imag >> 2 : sum_imag;                                                
    always@(posedge clk) begin
        if(~aresetn) begin
            sum_real <= 0;
            sum_imag <= 0;
        end
        else begin
            if(adder2correction.tvalid)
                adder2correction.tvalid <= 0;
            if(corr2adder.tvalid) begin
                if(corr2adder.symbol_last) adder2correction.tvalid <= 1;
                sum_real <= sum_real +
                             corr2adder.corr_data_real[3] +
                             corr2adder.corr_data_real[2] +
                             corr2adder.corr_data_real[1] +
                             corr2adder.corr_data_real[0];
                sum_imag <= sum_imag +
                             corr2adder.corr_data_imag[3] +
                             corr2adder.corr_data_imag[2] +
                             corr2adder.corr_data_imag[1] +
                             corr2adder.corr_data_imag[0];
            end
            else begin
                sum_real <= 0;
                sum_imag <= 0;
            end
        end
    end
endmodule


