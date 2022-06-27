`timescale 1ns / 1ps

module framer_tb(

    );
    
    reg  axis_aclk = 0;
    reg  axis_aresetn = 0;
    wire  s_axis_data_tready;
    wire [31 : 0] s_axis_data_tdata;
    wire [3 : 0] s_axis_data_tstrb;
    wire  s_axis_data_tlast;
    reg  s_axis_data_tvalid = 0;
    wire  m_axis_data_tvalid;
    wire [1023 : 0] m_axis_data_tdata;
    wire [3 : 0] m_axis_data_tstrb;
    wire  m_axis_data_tlast;
    reg  m_axis_data_tready;
    wire  s_axis_config_tready;
    wire [31 : 0] s_axis_config_tdata;
    wire [(32/8)-1 : 0] s_axis_config_tstrb;
    wire s_axis_config_tlast;
    wire  s_axis_config_tvalid;
    reg [31 : 0] sync_word [0 : 24];
    reg [20 : 0] count = 0; 
    reg signed [9 : 0] sw_counter = 0;
    reg [31 : 0] input_samples[0 : 3599];
    reg [31 : 0] output_samples[0 : 6399];
    reg [20 : 0] input_counter, output_counter;
    logic [1023 : 0] exp_output;
    reg [31 : 0] rand_int;
    reg i;
    
    initial begin
        $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/sync_word.txt", sync_word, 0, 24);
    end
    
    initial begin
        $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/input.txt", input_samples, 0, 3599);
    end
    
    initial begin
        $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/output.txt", output_samples, 0, 6399);
    end
    
    assign exp_output[0 * 32 +: 32] = output_samples[output_counter * 32 + 0];
    assign exp_output[1 * 32 +: 32] = output_samples[output_counter * 32 + 1];
    assign exp_output[2 * 32 +: 32] = output_samples[output_counter * 32 + 2];
    assign exp_output[3 * 32 +: 32] = output_samples[output_counter * 32 + 3];
    assign exp_output[4 * 32 +: 32] = output_samples[output_counter * 32 + 4];
    assign exp_output[5 * 32 +: 32] = output_samples[output_counter * 32 + 5];
    assign exp_output[6 * 32 +: 32] = output_samples[output_counter * 32 + 6];
    assign exp_output[7 * 32 +: 32] = output_samples[output_counter * 32 + 7];
    assign exp_output[8 * 32 +: 32] = output_samples[output_counter * 32 + 8];
    assign exp_output[9 * 32 +: 32] = output_samples[output_counter * 32 + 9];
    assign exp_output[10 * 32 +: 32] = output_samples[output_counter * 32 + 10];
    assign exp_output[11 * 32 +: 32] = output_samples[output_counter * 32 + 11];
    assign exp_output[12 * 32 +: 32] = output_samples[output_counter * 32 + 12];
    assign exp_output[13 * 32 +: 32] = output_samples[output_counter * 32 + 13];
    assign exp_output[14 * 32 +: 32] = output_samples[output_counter * 32 + 14];
    assign exp_output[15 * 32 +: 32] = output_samples[output_counter * 32 + 15];
    assign exp_output[16 * 32 +: 32] = output_samples[output_counter * 32 + 16];
    assign exp_output[17 * 32 +: 32] = output_samples[output_counter * 32 + 17];
    assign exp_output[18 * 32 +: 32] = output_samples[output_counter * 32 + 18];
    assign exp_output[19 * 32 +: 32] = output_samples[output_counter * 32 + 19];
    assign exp_output[20 * 32 +: 32] = output_samples[output_counter * 32 + 20];
    assign exp_output[21 * 32 +: 32] = output_samples[output_counter * 32 + 21];
    assign exp_output[22 * 32 +: 32] = output_samples[output_counter * 32 + 22];
    assign exp_output[23 * 32 +: 32] = output_samples[output_counter * 32 + 23];
    assign exp_output[24 * 32 +: 32] = output_samples[output_counter * 32 + 24];
    assign exp_output[25 * 32 +: 32] = output_samples[output_counter * 32 + 25];
    assign exp_output[26 * 32 +: 32] = output_samples[output_counter * 32 + 26];
    assign exp_output[27 * 32 +: 32] = output_samples[output_counter * 32 + 27];
    assign exp_output[28 * 32 +: 32] = output_samples[output_counter * 32 + 28];
    assign exp_output[29 * 32 +: 32] = output_samples[output_counter * 32 + 29];
    assign exp_output[30 * 32 +: 32] = output_samples[output_counter * 32 + 30];
    assign exp_output[31 * 32 +: 32] = output_samples[output_counter * 32 + 31];
    
    assign s_axis_config_tvalid = sw_counter < 25 && axis_aresetn;
    assign s_axis_config_tdata = sync_word[sw_counter];
    
    assign s_axis_data_tdata = input_samples[input_counter];
    
    always@(posedge axis_aclk)
        rand_int = $random;
    
    always@ (posedge axis_aclk) begin
      if(s_axis_config_tready && axis_aresetn) begin
        if(sw_counter < 25) begin
            sw_counter <= sw_counter + 1;
        end
      end
    end
    
    always@(posedge axis_aclk)begin
        if(!axis_aresetn) begin
            input_counter <= 0;
            output_counter <= 0;
        end
        else begin
            if(s_axis_data_tready && s_axis_data_tvalid) begin
                if(input_counter == 3599)
                    input_counter <= 0;
                else
                    input_counter <= input_counter + 1;
            end
            if(m_axis_data_tready && m_axis_data_tvalid) begin
                if(output_counter == 199) 
                    $finish;
                else
                    output_counter <= output_counter + 1;
            end
        end
    end
    
    always@(posedge axis_aclk) begin
        if(m_axis_data_tvalid && m_axis_data_tready)
            if(exp_output != m_axis_data_tdata)
                $display("Data Missmatch at count 0x%0h", output_counter);
    end
    
    OFDM_Framer dut(
        axis_aclk,
		axis_aresetn,
		s_axis_data_tready,
		s_axis_data_tdata,
		s_axis_data_tstrb,
		s_axis_data_tlast,
		s_axis_data_tvalid,
		m_axis_data_tvalid,
		m_axis_data_tdata,
		m_axis_data_tstrb,
		m_axis_data_tlast,
		m_axis_data_tready,
		s_axis_config_tready,
		s_axis_config_tdata,
		s_axis_config_tstrb,
		s_axis_config_tlast,
		s_axis_config_tvalid
    );
    
    always@(posedge axis_aclk) begin
        if(axis_aresetn) begin
            if(rand_int[4 : 0] == 0)
                s_axis_data_tvalid <= ~s_axis_data_tvalid;
            if(rand_int[4 : 0] == 2)
                m_axis_data_tready <= ~m_axis_data_tready;
        end
    end
    
    initial begin
        forever #5 axis_aclk = ~axis_aclk;
    end
    
    /* Make sure Valids deassert with reset*/
    assert property (@(posedge axis_aclk)
	   !axis_aresetn |-> !m_axis_data_tvalid);

    assert property (@(posedge axis_aclk)
	   !axis_aresetn |-> !s_axis_data_tvalid);
	   
	/* Make sure data does not change if m_axis_tready deasserts*/
	assert property (@(posedge axis_aclk)
	   m_axis_data_tvalid && !m_axis_data_tready && axis_aresetn
	       |=> m_axis_data_tvalid && $stable(m_axis_data_tdata));
    
    initial begin
        #100 
        @(posedge axis_aclk);
        axis_aresetn <= 1;
        s_axis_data_tvalid <= 1;
        m_axis_data_tready <= 1;
    end
    
endmodule
