`timescale 1ns / 1ps
//import piradio_ofdm::*;

 // To run the simulation and change the modulated output of the
 // Framer, change the define to either BPSK, QPSK or QAM16.
 
`define BPSK

module framer_tb
    ();
    typedef enum {TB_IDLE, TB_SYNC_WORD, TB_TEMPLATE, TB_MAP, TB_FIN, TB_NOSTATE} state_tb_t;
    localparam OUTPUT_SAMPLES = 51200;
    localparam S_AXIS_DATA_WIDTH = 32;
    localparam integer fft_size = 1024;
    state_tb_t state = TB_IDLE;
    logic [2 : 0] mod_index;
    logic  axis_aclk = 0;
    logic  axis_aresetn = 0;
    logic  s_axis_data_tready;
    logic [31 : 0] s_axis_data_tdata;
    logic [3 : 0] s_axis_data_tstrb;
    logic  s_axis_data_tlast;
    logic  s_axis_data_tvalid = 0;
    logic  m_axis_data_tvalid;
    logic [127 : 0] m_axis_data_tdata;
    logic [3 : 0] m_axis_data_tstrb;
    logic  m_axis_data_tlast;
    logic  m_axis_data_tready;
    logic  m_axis_log_tvalid;
    logic [31 : 0] m_axis_log_tdata;
    logic [3 : 0] m_axis_log_tstrb;
    logic  m_axis_log_tlast;
    logic  m_axis_log_tready;
    
    logic  s_axis_config_tready;
    logic [S_AXIS_DATA_WIDTH - 1 : 0] s_axis_config_tdata;
    logic [(S_AXIS_DATA_WIDTH/8)-1 : 0] s_axis_config_tstrb;
    logic s_axis_config_tlast = 0;
    logic [31 : 0] sync_word [0 : 1023];
    logic [31 : 0] template [0 : 1023];
    logic [20 : 0] count = 0; 
    
    logic [31 : 0] output_samples[0 : OUTPUT_SAMPLES - 1];
    logic [31 : 0] map[0 : 31];
    logic [20 : 0] input_counter, output_counter;
    logic [127 : 0] exp_output;
    logic [31 : 0] rand_int;
    logic i;
    logic modulation_samp_insert = 1;
    logic [4 : 0] bits_per_mod [0 : 4];
    logic [20 : 0] count_m_valid = 0;
    logic [20 : 0] count_delay = 0;
    logic [31 : 0] output_array[0 : 3];
    
    logic s_axis_config_tvalid;
    
    event map_loaded;
    
    localparam string path =  "../../../../../../OFDM_Framer.srcs/sim_1/new/";

    assign sync_word = output_samples[0 : 1023];
    assign template = output_samples[1024 : 2047];
    
    localparam map_filename = { path, "map.txt" };
    
    `ifdef BPSK
    localparam INPUT_SAMPLES = 900;
    assign mod_index = 0;
    
    localparam string input_filename = { path, "input.txt" };    
    localparam string output_filename = { path, "output.txt" };    
    `endif
    
    /*
    `ifdef BPSK
        assign mod_index = 0;
        localparam INPUT_SAMPLES = 900;
        logic [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
        initial begin
            filename = { path, "input.txt" };
            $display("Reading %s", filename);
            $readmemh(filename, input_samples, 0, INPUT_SAMPLES - 1);
        end     
        initial begin
            $readmemh({ path, "output.txt" }, output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QPSK
        assign mod_index = 1;
        localparam INPUT_SAMPLES = 1800;
        logic [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
        initial begin
            $readmemh({ path, "input_qpsk.txt" }, input_samples, 0, INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh({ path, "output_qpsk.txt" }, output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `elsif QAM16
        assign mod_index = 2;
        localparam INPUT_SAMPLES = 3600;
        logic [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
        initial begin
            $readmemh({ path, "input_qam16.txt" }, input_samples, 0, INPUT_SAMPLES - 1);
        end

        initial begin
            $readmemh({ path, "output_qam16.txt" }, output_samples, 0, OUTPUT_SAMPLES - 1);
        end
    `endif
    */
    
    logic [31 : 0] input_samples[0 : INPUT_SAMPLES - 1];
    
    task read_files();
        int i = 0;
        
        $display("Reading input data from: %s", input_filename);
        $readmemh(input_filename, input_samples, 0, INPUT_SAMPLES - 1);
        
        $display("Reading output data from: %s", output_filename);  
        $readmemh(output_filename, output_samples, 0, OUTPUT_SAMPLES - 1);
              
        $display("Reading map from: %s", map_filename);
        $readmemh(map_filename, map, 0, 31);
    
        @(posedge axis_aclk);
    
        for (i = 0; i < 1024; i += 4) begin
            $display("Template %x: %0x %0x", i / 4, map[i/32][(i%32)+:4], { template[i+3], template[i+2], template[i+1], template[i] });
        end
        
    endtask
    
    assign exp_output[0 * 32 +: 32] = output_samples[output_counter];
    assign exp_output[1 * 32 +: 32] = output_samples[output_counter + 1];
    assign exp_output[2 * 32 +: 32] = output_samples[output_counter + 2];
    assign exp_output[3 * 32 +: 32] = output_samples[output_counter + 3];
    
    assign output_array[0] = output_samples[output_counter];
    assign output_array[1] = output_samples[output_counter + 1];
    assign output_array[2] = output_samples[output_counter + 2];
    assign output_array[3] = output_samples[output_counter + 3];
    

    always@(posedge axis_aclk)
        rand_int = $random;
        
    logic [31 : 0] cnt = 0;
    
    integer j;
    
    initial
    begin
        m_axis_data_tready <= 0;
        s_axis_config_tdata <= 0;
        s_axis_config_tvalid <= 0;
        s_axis_config_tstrb <= 4'hf;
        bits_per_mod <= '{1,2,4,6,8};
        input_counter <= 0;
        output_counter <= 0;
        m_axis_data_tready <= 0;
        s_axis_data_tlast <= 0;
        s_axis_data_tstrb <= 0;
        s_axis_data_tdata <= 0;

        read_files();


        repeat (10)  @(posedge axis_aclk); // Let BRAMs boot

        axis_aresetn <= 1;

        wait(axis_aresetn);
        
        // Let the BRAMs come out of reset
        repeat (30) @(posedge axis_aclk);
        
        for (j = 0; j < 1024; j++) begin
            @(posedge axis_aclk);
            s_axis_config_tdata <= sync_word[j];
            s_axis_config_tvalid <= 1;
            s_axis_config_tlast <= (j == 1023);
        end
        
        for (j = 0; j < 1024; j++) begin
            @(posedge axis_aclk);
            s_axis_config_tdata <= template[j];
            s_axis_config_tvalid <= 1;
            s_axis_config_tlast <= 0; 
            @(posedge axis_aclk);
            s_axis_config_tdata <=  ((map[j / 32] & (1 << j % 32)) ? {31'h0, 1'b1} : 32'h0);
            s_axis_config_tvalid <= 1;            
            s_axis_config_tlast <= (j == fft_size - 1); 
        end
        
        @(posedge axis_aclk);
        s_axis_config_tvalid <= 0;            
        s_axis_config_tlast <= 0; 
        
        ->map_loaded;
        
        fork
            begin
                m_axis_data_tready <= 1;

                if (0) begin
                    while (1) begin
                        wait(count_m_valid % 256 == 255);
                        m_axis_data_tready <= 0;
                        repeat (64) @(posedge axis_aclk);
                        m_axis_data_tready <= 1;
                    end
                end
            end
        join_none;
        
        @(posedge axis_aclk);
        
        for (repetitions = 0; repetitions < rep_limit; repetitions++) begin
            while (input_counter < INPUT_SAMPLES) begin
                s_axis_data_tvalid <= 1;
                s_axis_data_tdata <= mod_index + 1;
                do @(posedge axis_aclk); while(~s_axis_data_tready);
            
                for (k = 0; k < 180 * bits_per_mod[mod_index]; k++) begin
                    s_axis_data_tdata <= input_samples[input_counter];
                    input_counter <= input_counter + 1;
                    do @(posedge axis_aclk); while(~s_axis_data_tready);
                end
            end
        end
        
    end
    
    integer mismatches = 0;
    integer k;
    
    logic [31:0] recv_samples[0:3];
    
    always_comb begin
        recv_samples[0] = m_axis_data_tdata[0+:32];
        recv_samples[1] = m_axis_data_tdata[32+:32];
        recv_samples[2] = m_axis_data_tdata[64+:32];
        recv_samples[3] = m_axis_data_tdata[96+:32];
    end
    
    always@(posedge axis_aclk) begin
        if(m_axis_data_tvalid && m_axis_data_tready) begin
            if(exp_output != m_axis_data_tdata) begin
                $display("Data Missmatch at count 0x%0h exp: 0x%0h got: 0x%0h", output_counter, exp_output, m_axis_data_tdata);
                mismatches += 1;
                
                for (k = -12; k < 12; k += 4) begin
                    $display("%x: 0x%0h", (output_counter + k) / 4, 
                             { output_samples[output_counter + k + 3], output_samples[output_counter + k + 2],
                               output_samples[output_counter + k + 1], output_samples[output_counter + k + 0]  }); 
                end
                
                $stop;
            end else begin
                $display("Match (count 0x%0h): 0x%0h", output_counter, m_axis_data_tdata); 
            end
            
            output_counter += 4;
        end
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
    
    
    
    assign m_axis_log_tready = 1;

    
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
	       
    logic [20 : 0] ii;
    logic [20 : 0] init_cnt = 0;
    logic [20 : 0] halted = 0;
    logic [20 : 0] valid_idle_duration = 7000;
    logic [3 : 0] repetitions = 0;
    localparam rep_limit = 10;
    
    integer k;
    
    always @(posedge axis_aclk) begin
        if (~axis_aresetn) begin
            count_m_valid <= 0;
        end else if (m_axis_data_tvalid & m_axis_data_tready) begin
            count_m_valid <= count_m_valid + 1;
        end
    end 
endmodule
