`timescale 1ns / 1ps
import piradio_ofdm::*;

 // To run the simulation and change the modulated output of the
 // Framer, change the define to either BPSK, QPSK or QAM16.
 
`define QPSK

module framer_tb
    ();

    localparam OUTPUT_SAMPLES = 51200;
    localparam S_AXIS_DATA_WIDTH = 32;
    localparam fft_size = 1024;
    state_tb_t state = TB_IDLE;
    wire [2 : 0] mod_index;
    reg  axis_aclk = 0;
    reg  axis_aresetn = 0;
    wire  s_axis_data_tready;
    wire [31 : 0] s_axis_data_tdata;
    wire [3 : 0] s_axis_data_tstrb;
    wire  s_axis_data_tlast;
    reg  s_axis_data_tvalid = 0;
    wire  m_axis_data_tvalid;
    wire [127 : 0] m_axis_data_tdata;
    wire [3 : 0] m_axis_data_tstrb;
    wire  m_axis_data_tlast;
    reg  m_axis_data_tready;
    wire  s_axis_config_tready;
    reg [S_AXIS_DATA_WIDTH - 1 : 0] s_axis_config_tdata;
    wire [(S_AXIS_DATA_WIDTH/8)-1 : 0] s_axis_config_tstrb;
    reg s_axis_config_tlast = 0;
    wire  s_axis_config_tvalid;
    wire [31 : 0] sync_word [0 : 1023];
    wire [31 : 0] template [0 : 1023];
    reg [20 : 0] count = 0; 
    reg [20 : 0] sw_counter = 0;
    
    reg [31 : 0] output_samples[0 : OUTPUT_SAMPLES - 1];
    reg [31 : 0] map[0 : 31];
    reg [20 : 0] input_counter, output_counter;
    logic [127 : 0] exp_output;
    reg [31 : 0] rand_int;
    reg i;
    reg modulation_samp_insert = 1;
    reg [4 : 0] bits_per_mod [0 : 4];
    reg [20 : 0] count_m_valid = 0;
    reg [20 : 0] count_delay = 0;
    
    assign sync_word = output_samples[0 : 1023];
    assign template = output_samples[1024 : 2047];
    `ifdef BPSK
        assign mod_index = 0;
        localparam INPUT_SAMPLES = 9000;
        reg [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/input.txt", input_samples, 0, INPUT_SAMPLES - 1);
        end     
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/output.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QPSK
        assign mod_index = 1;
        localparam INPUT_SAMPLES = 18000;
        reg [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
        initial begin
            $readmemh("../../../../../OFDM_Framer.srcs/sim_1/new/input_qpsk.txt", input_samples, 0, INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh("../../../../../OFDM_Framer.srcs/sim_1/new/output_qpsk.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QAM16
        assign mod_index = 2;
        localparam INPUT_SAMPLES = 36000;
        reg [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/input_qam16.txt", input_samples, 0, INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/output_qam16.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `endif
    
    initial begin
        $readmemh("../../../../../OFDM_Framer.srcs/sim_1/new/map.txt", map, 0, 31);
    end
    
    assign exp_output[0 * 32 +: 32] = output_samples[output_counter];
    assign exp_output[1 * 32 +: 32] = output_samples[output_counter + 1];
    assign exp_output[2 * 32 +: 32] = output_samples[output_counter + 2];
    assign exp_output[3 * 32 +: 32] = output_samples[output_counter + 3];
    
    assign s_axis_data_tdata = (modulation_samp_insert) ? (mod_index + 1) : input_samples[input_counter];
    assign s_axis_config_tvalid = ((state == TB_SYNC_WORD)) || (state == TB_TEMPLATE) || (state == TB_MAP);
    
    always@(posedge axis_aclk)
        rand_int = $random;
        
    reg [31 : 0] cnt = 0;
    
    assign s_axis_config_tdata = (state == TB_SYNC_WORD) ? output_samples[sw_counter] :
                                  (state == TB_TEMPLATE) ? template[sw_counter]:
                                  (state == TB_MAP) ? ((map[sw_counter / 32] & (1 << sw_counter % 32))
                                                 ? {31'h0000000, 1'b1} : 32'h00000000) : 32'h00000000 ;
    
    always@ (posedge axis_aclk) begin
      
      if(s_axis_config_tready && axis_aresetn) begin
        if(s_axis_config_tlast) s_axis_config_tlast <= 0;
        case(state) 
            TB_IDLE: begin
                state <= TB_SYNC_WORD;
            end
            TB_SYNC_WORD: begin
                if(sw_counter <= 1023) begin
                    if(sw_counter == 1023) begin
                        state <= TB_TEMPLATE;
                        sw_counter <= 0;
                    end
                    else if(sw_counter == 1022) begin
                        s_axis_config_tlast <= 1;
                        sw_counter <= sw_counter + 1;
                    end
                    else
                        sw_counter <= sw_counter + 1;
                end 
            end
            TB_TEMPLATE: begin
                state <= TB_MAP;
                if(sw_counter == fft_size - 1) s_axis_config_tlast <= 1;
            end
            TB_MAP: begin
                if(sw_counter < fft_size - 1) begin
                    sw_counter <= sw_counter + 1;
                    state <= TB_TEMPLATE;
                end
                else begin
                    state <= TB_FIN;
                    sw_counter <= 0;
                end
            end
            TB_NOSTATE: begin
                cnt <= cnt + 1;
                if(cnt > 2000) begin
                    state <= TB_MAP;
                    sw_counter <= 0;
                end
            end
        endcase
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
		s_axis_data_tlast,
		s_axis_data_tvalid,
		m_axis_data_tvalid,
		m_axis_data_tdata,
		m_axis_data_tlast,
		m_axis_data_tready,
		s_axis_config_tready,
		s_axis_config_tdata,
		s_axis_config_tstrb,
		s_axis_config_tlast,
		s_axis_config_tvalid
    );
    
//    always@(posedge axis_aclk) begin
//        if(axis_aresetn) begin
//            if(m_axis_data_tvalid) begin
//                if(count_m_valid % 256 == 255) begin
//                    m_axis_data_tready <= 0;
//                    count_delay <= count_delay + 1;
//                    if(count_delay == 63) begin
//                        m_axis_data_tready <= 1;
//                        count_delay <= 0;
//                        count_m_valid <= count_m_valid + 1;
//                    end
//                end
//                else
//                    count_m_valid <= count_m_valid + 1;
//            end
//        end
//    end
    
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
	       
    reg [20 : 0] ii;
    reg [20 : 0] init_cnt = 0;
    reg [20 : 0] halted = 0;
    reg [20 : 0] valid_idle_duration = 1000;
    
    initial begin
        bits_per_mod <= '{1,2,4,6,8};
        input_counter <= 0;
        output_counter <= 0;
        #100 
        @(posedge axis_aclk);
        axis_aresetn <= 1;
        
        @(posedge axis_aclk);
        s_axis_data_tvalid <= 1;
        @(posedge axis_aclk);
        m_axis_data_tready <= 1;
        
        for(ii = 0 ; ii< OUTPUT_SAMPLES * 2; ii++) begin
            @(posedge axis_aclk)
            if(halted + valid_idle_duration < ii) begin
                if(halted != 0) begin
                    halted <= 0;
                    s_axis_data_tvalid <= 1;
                    if(input_counter % 180 == 20'h0000 && modulation_samp_insert) begin
                        modulation_samp_insert <= 0;
                    end
                    else begin
                        input_counter <= input_counter + 1;
                        if((input_counter % (180 * bits_per_mod[mod_index])) == 180 * bits_per_mod[mod_index] - 1)
                            modulation_samp_insert <= 1;
                    end
                end
            end
                
            if(output_counter == OUTPUT_SAMPLES) 
                    $finish;
            if(s_axis_data_tready && s_axis_data_tvalid) begin
                if(input_counter == ((180 * bits_per_mod[mod_index]) - 1 )) begin
                    //s_axis_data_tvalid <= 0;
                    modulation_samp_insert <= 1;
                    halted <= ii;
                end
                else if(input_counter == (((180 * bits_per_mod[mod_index]) * 4 - 1))) begin
                    //s_axis_data_tvalid <= 0;
                    modulation_samp_insert <= 1;
                    halted <= ii;
                end
                else begin
                    if(input_counter % 180 == 20'h0000 && modulation_samp_insert) begin
                        modulation_samp_insert <= 0;
                    end
                    else begin
                        input_counter <= input_counter + 1;
                        if((input_counter % (180 * bits_per_mod[mod_index])) == 180 * bits_per_mod[mod_index] - 1)
                            modulation_samp_insert <= 1;
                    end
                end
            end
            if(m_axis_data_tready && m_axis_data_tvalid) begin
                    output_counter <= output_counter + 4;
            end
        end
    end
    
endmodule
