module sync_word_module#
        ( 
        parameter integer TOTAL_CARRIERS = 1024,
        parameter integer S_AXIS_TDATA_WIDTH = 32
        )
        (
    	input wire  s_axis_config_aclk,
		input wire  s_axis_config_aresetn,
		output wire  s_axis_config_tready,
		input wire [S_AXIS_TDATA_WIDTH-1 : 0] s_axis_config_tdata,
		input wire [(S_AXIS_TDATA_WIDTH/8)-1 : 0] s_axis_config_tstrb,
		input wire  s_axis_config_tlast,
		input wire  s_axis_config_tvalid,
		output reg [31 : 0] sync_word[0 : TOTAL_CARRIERS - 1],
		output reg [31 : 0] template[0 : TOTAL_CARRIERS - 1],
		output reg [1023 : 0] map
    );
    typedef enum {IDLE, SYNC_WORD, TEMPLATE, MAP, FIN} config_state_t;
    config_state_t state = IDLE;
    reg [10 : 0] word_count = 0;
    assign s_axis_config_tready = (!(state == FIN) && s_axis_config_aresetn);

    always @(posedge s_axis_config_aclk) begin
        if ( s_axis_config_aresetn == 1'b0 ) begin
            sync_word[word_count] <= s_axis_config_tdata;
        end
        else begin
            if(s_axis_config_tvalid && s_axis_config_tready) begin
                case(state)
                    IDLE: begin
                        state <= SYNC_WORD;
                        sync_word[word_count] = s_axis_config_tdata;
                        word_count = word_count + 1;
                        
                    end
                    SYNC_WORD: begin
                        if(s_axis_config_tlast) begin
                            state <= TEMPLATE;
                            sync_word[word_count] = s_axis_config_tdata;
                            word_count = 0;
                        end
                        else begin
                            sync_word[word_count] = s_axis_config_tdata;
                            word_count = word_count + 1;
                        end
                    end
                    TEMPLATE: begin
                        if(s_axis_config_tlast) begin
                            state <= MAP;
                            template[word_count] = s_axis_config_tdata;
                            word_count = 0;
                        end
                        else begin
                            template[word_count] = s_axis_config_tdata;
                            word_count = word_count + 1;
                        end
                    end
                    MAP: begin
                        if(s_axis_config_tlast) begin
                            state <= FIN;
                            map[word_count +: 32] = s_axis_config_tdata;
                            word_count = 0;
                        end
                        else begin
                            map[word_count +: 32] = s_axis_config_tdata;
                            word_count = word_count + 32;
                        end
                    end
                endcase
            end
        end
    end
    
endmodule
