`timescale 1ns / 1ps

`define QAM16

module framer_tb #(
        parameter integer BPSK_INPUT_SAMPLES = 9000,
        parameter integer QPSK_INPUT_SAMPLES = 18000,
        parameter integer QAM16_INPUT_SAMPLES = 36000,
        parameter integer INPUT_SAMPLES = QAM16_INPUT_SAMPLES,
    
        parameter integer BPSK_OUTPUT_SAMPLES = 51200,
        parameter integer QPSK_OUTPUT_SAMPLES = 51200,
        parameter integer OUTPUT_SAMPLES = QPSK_OUTPUT_SAMPLES
    )
    ();
    
    typedef enum {IDLE, SYNC_WORD, TEMPLATE, MAP, FIN} state_t;
    state_t state = IDLE;
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
    reg [31 : 0] s_axis_config_tdata;
    wire [(32/8)-1 : 0] s_axis_config_tstrb;
    reg s_axis_config_tlast = 0;
    wire  s_axis_config_tvalid;
    wire [31 : 0] sync_word [0 : 1023];
    wire [31 : 0] template [0 : 1023];
    reg [20 : 0] count = 0; 
    reg [20 : 0] sw_counter = 0;
    reg [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
    reg [31 : 0] output_samples[0 : OUTPUT_SAMPLES - 1];
    reg [31 : 0] map[0 : 31];
    reg [20 : 0] input_counter, output_counter;
    logic [127 : 0] exp_output;
    reg [31 : 0] rand_int;
    reg i;
    
    `ifdef BPSK
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/input.txt", input_samples, 0, BPSK_INTPUT_SAMPLES - 1);
        end
        
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/output.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QPSK
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/input_qpsk.txt", input_samples, 0, QPSK_INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/output_qpsk.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QAM16
        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/input_qam16.txt", input_samples, 0, QAM16_INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/output_qam16.txt", output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `endif
    
    initial begin
        $readmemh("../../../../OFDM_Framer.srcs/sim_1/new/map.txt", map, 0, 31);
    end
    
    assign sync_word = output_samples[0 : 1023];
    assign template = output_samples[1024 : 2047];
    
    assign exp_output[0 * 32 +: 32] = output_samples[output_counter];
    assign exp_output[1 * 32 +: 32] = output_samples[output_counter + 1];
    assign exp_output[2 * 32 +: 32] = output_samples[output_counter + 2];
    assign exp_output[3 * 32 +: 32] = output_samples[output_counter + 3];
    
    assign s_axis_data_tdata = input_samples[input_counter];
    assign s_axis_config_tvalid = ((state == SYNC_WORD)) || (state == TEMPLATE) || (state == MAP);
    
    
    always@(posedge axis_aclk)
        rand_int = $random;
        
    reg [31 : 0] cnt = 0;
    
    assign s_axis_config_tdata = (state == SYNC_WORD) ? output_samples[sw_counter] :
                                  (state == TEMPLATE) ? template[sw_counter] :
                                  (state == MAP) ? map[sw_counter] : 32'h00000000 ;
    
    
    always@ (posedge axis_aclk) begin
      cnt <= cnt + 1;
      if(s_axis_config_tready && axis_aresetn) begin
        if(s_axis_config_tlast)
             s_axis_config_tlast <= 0;
        case(state) 
            IDLE: begin
                state <= SYNC_WORD;
            end
            SYNC_WORD: begin
                if(sw_counter <= 1023) begin
                    if(sw_counter == 1023) begin
                        state <= TEMPLATE;
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
            TEMPLATE: begin
                if(sw_counter <= 1023) begin
                   // s_axis_config_tdata <= template[sw_counter];
                    if(sw_counter == 1023) begin
                        state <= MAP;
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
            MAP: begin
                if(sw_counter < 32) begin
                   // s_axis_config_tdata <= map[sw_counter];
                    if(sw_counter == 31) begin
                        state <= FIN;
                        sw_counter <= 0;
                    end
                    else if(sw_counter == 30) begin
                        s_axis_config_tlast <= 1;
                        sw_counter <= sw_counter + 1;
                    end
                    else
                        sw_counter <= sw_counter + 1;
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
            if(rand_int[5 : 0] == 1 && input_counter <= 2322)
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
	       
    reg [20 : 0] ii;
    reg [20 : 0] init_cnt = 0;
    reg [20 : 0] halted = 0;
    reg [20 : 0] valid_idle_duration = 1000;
    
    initial begin
        input_counter <= 0;
        output_counter <= 0;
        #100 
        @(posedge axis_aclk);
        axis_aresetn <= 1;
        
        //s_axis_config_tdata <= output_samples[sw_counter];
        @(posedge axis_aclk);
        s_axis_data_tvalid <= 1;
        @(posedge axis_aclk);
        m_axis_data_tready <= 1;
        
        for(ii = 0 ; ii< OUTPUT_SAMPLES * 2; ii++) begin
            @(posedge axis_aclk)
            if(halted + valid_idle_duration < ii) begin
                if(halted != 0) begin
                    s_axis_data_tvalid <= 1;
                    halted <= 0;
                    input_counter <= input_counter + 1;
                end
            end
                
            if(output_counter == OUTPUT_SAMPLES) 
                    $finish;
            if(s_axis_data_tready && s_axis_data_tvalid) begin
                if(input_counter == ((180 * 4)  - 1)) begin
                    s_axis_data_tvalid <= 0;
                    halted <= ii;
                end
                else if(input_counter == (((180 * 4) * 4) - 1)) begin
                    s_axis_data_tvalid <= 0;
                    halted <= ii;
                end
                else
                    input_counter <= input_counter + 1;
            end
            if(m_axis_data_tready && m_axis_data_tvalid) begin
                    output_counter <= output_counter + 4;
            end
        end
    end
    
endmodule
