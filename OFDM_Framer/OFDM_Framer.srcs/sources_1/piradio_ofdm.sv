package piradio_ofdm;   
   
   typedef logic [7:0] ofdm_symbol_t;
   typedef logic [31:0] ofdm_sample_t;
   
   typedef struct {
      logic [7:0] bits_per_symbol;

      ofdm_sample_t constellation[0:15];
   } modulation_t;
   
   const modulation_t mod_none = { 8'd0, { 32'hADADADAD, 32'hADADADAD, 32'hADADADAD, 32'hADADADAD,
                                           32'hADADADAD, 32'hADADADAD, 32'hADADADAD, 32'hADADADAD,
                                           32'hADADADAD, 32'hADADADAD, 32'hADADADAD, 32'hADADADAD,
                                           32'hADADADAD, 32'hADADADAD, 32'hADADADAD, 32'hADADADAD  } };   
   
   const modulation_t mod_bpsk = { 8'd1, { 32'h0000c000, 32'h00003fff, 32'h00, 32'h00,
					   32'h00, 32'h00, 32'h00, 32'h00, 
					   32'h00, 32'h00, 32'h00, 32'h00, 
					   32'h00, 32'h00, 32'h00, 32'h00} };
   
   const modulation_t mod_qpsk = { 8'd2, { 32'hc000c000, 32'hc0003fff, 32'h3fffc000, 32'h3fff3fff, 
					   32'h00, 32'h00, 32'h00, 32'h00, 
					   32'h00, 32'h00, 32'h00, 32'h00, 
					   32'h00, 32'h00, 32'h00, 32'h00 }  };
   
   const modulation_t mod_qam16 = { 8'd4, { 32'h3fffc000, 32'h3fffeaaa, 32'h3fff3fff, 32'h3fff1555, 
					    32'h1555c000, 32'h1555eaaa, 32'h15553fff, 32'h15551555, 
					    32'hc000c000, 32'hc000eaaa, 32'hc0003fff, 32'hc0001555, 
					    32'heaaac000, 32'heaaaeaaa, 32'heaaa3fff, 32'heaaa1555 } };
   
   const modulation_t mod_qam64 = { 8'd6, { 32'h00, 32'h00, 32'h00008000, 32'h00003fff,
					    32'h00, 32'h00, 32'h00, 32'h00, 
					    32'h00, 32'h00, 32'h00, 32'h00,
					    32'h00, 32'h00, 32'h00, 32'h00 } };
				    
   const modulation_t mod_qam256 = { 8'd8, { 32'h00, 32'h00, 32'h00008000, 32'h00007fff,
					     32'h00, 32'h00, 32'h00, 32'h00, 
					     32'h00, 32'h00, 32'h00, 32'h00,
					     32'h00, 32'h00, 32'h00, 32'h00 } };
   
   typedef enum 	    { MOD_NONE, BPSK, QPSK, QAM16, QAM64, QAM256} mod_t;
   const modulation_t modulations[0:5] = '{ mod_none, mod_bpsk, mod_qpsk, mod_qam16, mod_qam64, mod_qam256 };
   typedef enum {TB_IDLE, TB_SYNC_WORD, TB_TEMPLATE, TB_MAP, TB_FIN, TB_NOSTATE} state_tb_t;
   typedef enum {IDLE, SYNC_WORD,MOD_SAMPLE_ON, DATA, FIFO_AFULL} state_t;
   const logic [2 : 0] ones_lut [0 : 15] = '{0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4};
  
endpackage