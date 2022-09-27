`ifndef xlConvPkgIncluded
`include "conv_pkg.v"
`endif

`timescale 1 ns / 10 ps
// Generated from Simulink block ssrFFT/I.IM
module ssrfft_i_im (
  input [16-1:0] i_im_0,
  input [16-1:0] i_im_1,
  input [16-1:0] i_im_2,
  input [16-1:0] i_im_3
);
  wire [16-1:0] i_im_3_net;
  wire [16-1:0] i_im_0_net;
  wire [16-1:0] i_im_1_net;
  wire [16-1:0] i_im_2_net;
  assign i_im_0_net = i_im_0;
  assign i_im_1_net = i_im_1;
  assign i_im_2_net = i_im_2;
  assign i_im_3_net = i_im_3;
endmodule
`timescale 1 ns / 10 ps
// Generated from Simulink block ssrFFT/I.RE
module ssrfft_i_re (
  input [16-1:0] i_re_0,
  input [16-1:0] i_re_1,
  input [16-1:0] i_re_2,
  input [16-1:0] i_re_3
);
  wire [16-1:0] i_re_1_net;
  wire [16-1:0] i_re_2_net;
  wire [16-1:0] i_re_3_net;
  wire [16-1:0] i_re_0_net;
  assign i_re_0_net = i_re_0;
  assign i_re_1_net = i_re_1;
  assign i_re_2_net = i_re_2;
  assign i_re_3_net = i_re_3;
endmodule
`timescale 1 ns / 10 ps
// Generated from Simulink block ssrFFT/Vector FFT
module ssrfft_vector_fft (
  input [16-1:0] i_re_1,
  input [16-1:0] i_im_1,
  input [1-1:0] vi,
  input [10-1:0] si,
  input [16-1:0] i_re_2,
  input [16-1:0] i_re_3,
  input [16-1:0] i_re_4,
  input [16-1:0] i_im_2,
  input [16-1:0] i_im_3,
  input [16-1:0] i_im_4,
  input clk_1,
  input ce_1,
  output [26-1:0] o_re_1,
  output [26-1:0] o_im_1,
  output vo,
  output [10-1:0] so,
  output [26-1:0] o_re_2,
  output [26-1:0] o_re_3,
  output [26-1:0] o_re_4,
  output [26-1:0] o_im_2,
  output [26-1:0] o_im_3,
  output [26-1:0] o_im_4
);
  wire [26-1:0] reinterpret8_output_port_net;
  wire [26-1:0] reinterpret12_output_port_net;
  wire test_systolicfft_vhdl_black_box_vo_net;
  wire [10-1:0] test_systolicfft_vhdl_black_box_so_net;
  wire [26-1:0] reinterpret9_output_port_net;
  wire [26-1:0] reinterpret11_output_port_net;
  wire [26-1:0] reinterpret13_output_port_net;
  wire [10-1:0] si_net;
  wire [16-1:0] i_im_1_net;
  wire [16-1:0] reinterpret5_output_port_net;
  wire [16-1:0] reinterpret0_output_port_net;
  wire [32-1:0] concat1_y_net;
  wire [32-1:0] concat2_y_net;
  wire [26-1:0] reinterpret15_output_port_net;
  wire [16-1:0] reinterpret2_output_port_net;
  wire [16-1:0] reinterpret6_output_port_net;
  wire [16-1:0] i_re_2_net;
  wire [16-1:0] i_re_0_net;
  wire [1-1:0] vi_net;
  wire [16-1:0] i_im_3_net;
  wire [32-1:0] concat0_y_net;
  wire [16-1:0] reinterpret4_output_port_net;
  wire ce_net;
  wire [26-1:0] reinterpret10_output_port_net;
  wire [26-1:0] reinterpret14_output_port_net;
  wire clk_net;
  wire [16-1:0] i_im_0_net;
  wire [16-1:0] i_im_2_net;
  wire [16-1:0] i_re_3_net;
  wire [16-1:0] reinterpret1_output_port_net;
  wire [16-1:0] i_re_1_net;
  wire [32-1:0] delay5_q_net;
  wire [16-1:0] reinterpret3_output_port_net;
  wire [32-1:0] delay2_q_net;
  wire [16-1:0] reinterpret7_output_port_net;
  wire [10-1:0] delay1_q_net;
  wire [1-1:0] delay_q_net;
  wire [32-1:0] delay3_q_net;
  wire [32-1:0] delay4_q_net;
  wire [32-1:0] concat3_y_net;
  wire [128-1:0] concat4_y_net;
  wire [26-1:0] slice10_y_net;
  wire [26-1:0] slice6_y_net;
  wire [26-1:0] slice9_y_net;
  wire [26-1:0] slice8_y_net;
  wire [26-1:0] slice11_y_net;
  wire [26-1:0] slice7_y_net;
  wire [208-1:0] test_systolicfft_vhdl_black_box_o_net;
  wire [52-1:0] slice3_y_net;
  wire [26-1:0] slice5_y_net;
  wire [26-1:0] slice4_y_net;
  wire [52-1:0] slice0_y_net;
  wire [52-1:0] slice1_y_net;
  wire [52-1:0] slice2_y_net;
  assign o_re_1 = reinterpret8_output_port_net;
  assign o_im_1 = reinterpret12_output_port_net;
  assign vo = test_systolicfft_vhdl_black_box_vo_net;
  assign so = test_systolicfft_vhdl_black_box_so_net;
  assign o_re_2 = reinterpret9_output_port_net;
  assign o_re_3 = reinterpret10_output_port_net;
  assign o_re_4 = reinterpret11_output_port_net;
  assign o_im_2 = reinterpret13_output_port_net;
  assign o_im_3 = reinterpret14_output_port_net;
  assign o_im_4 = reinterpret15_output_port_net;
  assign i_re_0_net = i_re_1;
  assign i_im_0_net = i_im_1;
  assign vi_net = vi;
  assign si_net = si;
  assign i_re_1_net = i_re_2;
  assign i_re_2_net = i_re_3;
  assign i_re_3_net = i_re_4;
  assign i_im_1_net = i_im_2;
  assign i_im_2_net = i_im_3;
  assign i_im_3_net = i_im_4;
  assign clk_net = clk_1;
  assign ce_net = ce_1;
  sysgen_concat_15d8d38fa7 concat0 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .in0(reinterpret0_output_port_net),
    .in1(reinterpret4_output_port_net),
    .y(concat0_y_net)
  );
  sysgen_concat_15d8d38fa7 concat1 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .in0(reinterpret1_output_port_net),
    .in1(reinterpret5_output_port_net),
    .y(concat1_y_net)
  );
  sysgen_concat_15d8d38fa7 concat2 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .in0(reinterpret2_output_port_net),
    .in1(reinterpret6_output_port_net),
    .y(concat2_y_net)
  );
  sysgen_concat_15d8d38fa7 concat3 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .in0(reinterpret3_output_port_net),
    .in1(reinterpret7_output_port_net),
    .y(concat3_y_net)
  );
  sysgen_concat_b148156e89 concat4 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .in0(delay5_q_net),
    .in1(delay4_q_net),
    .in2(delay3_q_net),
    .in3(delay2_q_net),
    .y(concat4_y_net)
  );
  ssrfft_xldelay #(
    .latency(4),
    .reg_retiming(0),
    .reset(0),
    .width(1)
  )
  delay (
    .en(1'b1),
    .rst(1'b0),
    .d(vi_net),
    .clk(clk_net),
    .ce(ce_net),
    .q(delay_q_net)
  );
  ssrfft_xldelay #(
    .latency(4),
    .reg_retiming(0),
    .reset(0),
    .width(10)
  )
  delay1 (
    .en(1'b1),
    .rst(1'b0),
    .d(si_net),
    .clk(clk_net),
    .ce(ce_net),
    .q(delay1_q_net)
  );
  ssrfft_xldelay #(
    .latency(4),
    .reg_retiming(0),
    .reset(0),
    .width(32)
  )
  delay2 (
    .en(1'b1),
    .rst(1'b0),
    .d(concat0_y_net),
    .clk(clk_net),
    .ce(ce_net),
    .q(delay2_q_net)
  );
  ssrfft_xldelay #(
    .latency(4),
    .reg_retiming(0),
    .reset(0),
    .width(32)
  )
  delay3 (
    .en(1'b1),
    .rst(1'b0),
    .d(concat1_y_net),
    .clk(clk_net),
    .ce(ce_net),
    .q(delay3_q_net)
  );
  ssrfft_xldelay #(
    .latency(4),
    .reg_retiming(0),
    .reset(0),
    .width(32)
  )
  delay4 (
    .en(1'b1),
    .rst(1'b0),
    .d(concat2_y_net),
    .clk(clk_net),
    .ce(ce_net),
    .q(delay4_q_net)
  );
  ssrfft_xldelay #(
    .latency(4),
    .reg_retiming(0),
    .reset(0),
    .width(32)
  )
  delay5 (
    .en(1'b1),
    .rst(1'b0),
    .d(concat3_y_net),
    .clk(clk_net),
    .ce(ce_net),
    .q(delay5_q_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret0 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_im_0_net),
    .output_port(reinterpret0_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret1 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_im_1_net),
    .output_port(reinterpret1_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret10 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice6_y_net),
    .output_port(reinterpret10_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret11 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice7_y_net),
    .output_port(reinterpret11_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret12 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice8_y_net),
    .output_port(reinterpret12_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret13 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice9_y_net),
    .output_port(reinterpret13_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret14 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice10_y_net),
    .output_port(reinterpret14_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret15 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice11_y_net),
    .output_port(reinterpret15_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret2 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_im_2_net),
    .output_port(reinterpret2_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret3 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_im_3_net),
    .output_port(reinterpret3_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret4 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_re_0_net),
    .output_port(reinterpret4_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret5 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_re_1_net),
    .output_port(reinterpret5_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret6 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_re_2_net),
    .output_port(reinterpret6_output_port_net)
  );
  sysgen_reinterpret_61ec4a008e reinterpret7 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(i_re_3_net),
    .output_port(reinterpret7_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret8 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice4_y_net),
    .output_port(reinterpret8_output_port_net)
  );
  sysgen_reinterpret_f7a4eb3665 reinterpret9 (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .input_port(slice5_y_net),
    .output_port(reinterpret9_output_port_net)
  );
  ssrfft_xlslice #(
    .new_lsb(0),
    .new_msb(51),
    .x_width(208),
    .y_width(52)
  )
  slice0 (
    .x(test_systolicfft_vhdl_black_box_o_net),
    .y(slice0_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(52),
    .new_msb(103),
    .x_width(208),
    .y_width(52)
  )
  slice1 (
    .x(test_systolicfft_vhdl_black_box_o_net),
    .y(slice1_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(26),
    .new_msb(51),
    .x_width(52),
    .y_width(26)
  )
  slice10 (
    .x(slice2_y_net),
    .y(slice10_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(26),
    .new_msb(51),
    .x_width(52),
    .y_width(26)
  )
  slice11 (
    .x(slice3_y_net),
    .y(slice11_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(104),
    .new_msb(155),
    .x_width(208),
    .y_width(52)
  )
  slice2 (
    .x(test_systolicfft_vhdl_black_box_o_net),
    .y(slice2_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(156),
    .new_msb(207),
    .x_width(208),
    .y_width(52)
  )
  slice3 (
    .x(test_systolicfft_vhdl_black_box_o_net),
    .y(slice3_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(0),
    .new_msb(25),
    .x_width(52),
    .y_width(26)
  )
  slice4 (
    .x(slice0_y_net),
    .y(slice4_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(0),
    .new_msb(25),
    .x_width(52),
    .y_width(26)
  )
  slice5 (
    .x(slice1_y_net),
    .y(slice5_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(0),
    .new_msb(25),
    .x_width(52),
    .y_width(26)
  )
  slice6 (
    .x(slice2_y_net),
    .y(slice6_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(0),
    .new_msb(25),
    .x_width(52),
    .y_width(26)
  )
  slice7 (
    .x(slice3_y_net),
    .y(slice7_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(26),
    .new_msb(51),
    .x_width(52),
    .y_width(26)
  )
  slice8 (
    .x(slice0_y_net),
    .y(slice8_y_net)
  );
  ssrfft_xlslice #(
    .new_lsb(26),
    .new_msb(51),
    .x_width(52),
    .y_width(26)
  )
  slice9 (
    .x(slice1_y_net),
    .y(slice9_y_net)
  );
  WRAPPER_VECTOR_FFT #(
    .BRAM_THRESHOLD(258),
    .DSP48E(2),
    .I_high(-9),
    .I_low(-24),
    .L2N(10),
    .N(1024),
    .O_high(1),
    .O_low(-24),
    .SSR(4),
    .W_high(1),
    .W_low(-17)
  )
  test_systolicfft_vhdl_black_box (
    .i(concat4_y_net),
    .vi(delay_q_net),
    .si(delay1_q_net),
    .CLK(clk_net),
    .CE(ce_net),
    .o(test_systolicfft_vhdl_black_box_o_net),
    .vo(test_systolicfft_vhdl_black_box_vo_net),
    .so(test_systolicfft_vhdl_black_box_so_net)
  );
endmodule
`timescale 1 ns / 10 ps
// Generated from Simulink block ssrFFT_struct
module ssrfft_struct (
  input [10-1:0] si,
  input [1-1:0] vi,
  input [16-1:0] i_im_0,
  input [16-1:0] i_im_1,
  input [16-1:0] i_im_2,
  input [16-1:0] i_im_3,
  input [16-1:0] i_re_0,
  input [16-1:0] i_re_1,
  input [16-1:0] i_re_2,
  input [16-1:0] i_re_3,
  input clk_1,
  input ce_1,
  output [1-1:0] last,
  output [10-1:0] so,
  output [1-1:0] vo,
  output [26-1:0] o_im_0,
  output [26-1:0] o_im_1,
  output [26-1:0] o_im_2,
  output [26-1:0] o_im_3,
  output [26-1:0] o_re_0,
  output [26-1:0] o_re_1,
  output [26-1:0] o_re_2,
  output [26-1:0] o_re_3
);
  wire [1-1:0] relational_op_net;
  wire [10-1:0] test_systolicfft_vhdl_black_box_so_net;
  wire [10-1:0] si_net;
  wire [1-1:0] vi_net;
  wire [8-1:0] counter_op_net;
  wire [16-1:0] i_re_1_net;
  wire [26-1:0] reinterpret14_output_port_net;
  wire [8-1:0] constant_op_net;
  wire [1-1:0] inverter_op_net;
  wire [1-1:0] test_systolicfft_vhdl_black_box_vo_net;
  wire [16-1:0] i_im_0_net;
  wire [26-1:0] reinterpret8_output_port_net;
  wire [26-1:0] reinterpret9_output_port_net;
  wire [26-1:0] reinterpret11_output_port_net;
  wire [16-1:0] i_im_2_net;
  wire ce_net;
  wire [26-1:0] reinterpret10_output_port_net;
  wire [16-1:0] i_im_3_net;
  wire [26-1:0] reinterpret12_output_port_net;
  wire [16-1:0] i_re_2_net;
  wire [16-1:0] i_im_1_net;
  wire [26-1:0] reinterpret13_output_port_net;
  wire [16-1:0] i_re_0_net;
  wire [16-1:0] i_re_3_net;
  wire clk_net;
  wire [26-1:0] reinterpret15_output_port_net;
  assign last = relational_op_net;
  assign si_net = si;
  assign so = test_systolicfft_vhdl_black_box_so_net;
  assign vi_net = vi;
  assign vo = test_systolicfft_vhdl_black_box_vo_net;
  assign i_im_0_net = i_im_0;
  assign i_im_1_net = i_im_1;
  assign i_im_2_net = i_im_2;
  assign i_im_3_net = i_im_3;
  assign i_re_0_net = i_re_0;
  assign i_re_1_net = i_re_1;
  assign i_re_2_net = i_re_2;
  assign i_re_3_net = i_re_3;
  assign o_im_0 = reinterpret12_output_port_net;
  assign o_im_1 = reinterpret13_output_port_net;
  assign o_im_2 = reinterpret14_output_port_net;
  assign o_im_3 = reinterpret15_output_port_net;
  assign o_re_0 = reinterpret8_output_port_net;
  assign o_re_1 = reinterpret9_output_port_net;
  assign o_re_2 = reinterpret10_output_port_net;
  assign o_re_3 = reinterpret11_output_port_net;
  assign clk_net = clk_1;
  assign ce_net = ce_1;
  ssrfft_i_im i_im (
    .i_im_0(i_im_0_net),
    .i_im_1(i_im_1_net),
    .i_im_2(i_im_2_net),
    .i_im_3(i_im_3_net)
  );
  ssrfft_i_re i_re (
    .i_re_0(i_re_0_net),
    .i_re_1(i_re_1_net),
    .i_re_2(i_re_2_net),
    .i_re_3(i_re_3_net)
  );
  ssrfft_vector_fft vector_fft (
    .i_re_1(i_re_0_net),
    .i_im_1(i_im_0_net),
    .vi(vi_net),
    .si(si_net),
    .i_re_2(i_re_1_net),
    .i_re_3(i_re_2_net),
    .i_re_4(i_re_3_net),
    .i_im_2(i_im_1_net),
    .i_im_3(i_im_2_net),
    .i_im_4(i_im_3_net),
    .clk_1(clk_net),
    .ce_1(ce_net),
    .o_re_1(reinterpret8_output_port_net),
    .o_im_1(reinterpret12_output_port_net),
    .vo(test_systolicfft_vhdl_black_box_vo_net),
    .so(test_systolicfft_vhdl_black_box_so_net),
    .o_re_2(reinterpret9_output_port_net),
    .o_re_3(reinterpret10_output_port_net),
    .o_re_4(reinterpret11_output_port_net),
    .o_im_2(reinterpret13_output_port_net),
    .o_im_3(reinterpret14_output_port_net),
    .o_im_4(reinterpret15_output_port_net)
  );
  sysgen_constant_35d3cbf245 constant (
    .clk(1'b0),
    .ce(1'b0),
    .clr(1'b0),
    .op(constant_op_net)
  );
  ssrfft_xlcounter_free #(
    .core_name0("ssrfft_c_counter_binary_v12_0_i0"),
    .op_arith(`xlUnsigned),
    .op_width(8)
  )
  counter (
    .en(1'b1),
    .clr(1'b0),
    .rst(inverter_op_net),
    .clk(clk_net),
    .ce(ce_net),
    .op(counter_op_net)
  );
  sysgen_inverter_27bcbc6bfc inverter (
    .clr(1'b0),
    .ip(test_systolicfft_vhdl_black_box_vo_net),
    .clk(clk_net),
    .ce(ce_net),
    .op(inverter_op_net)
  );
  sysgen_relational_1e558d276b relational (
    .clr(1'b0),
    .a(counter_op_net),
    .b(constant_op_net),
    .clk(clk_net),
    .ce(ce_net),
    .op(relational_op_net)
  );
endmodule
`timescale 1 ns / 10 ps
// Generated from Simulink block 
module ssrfft_default_clock_driver (
  input ssrfft_sysclk,
  input ssrfft_sysce,
  input ssrfft_sysclr,
  output ssrfft_clk1,
  output ssrfft_ce1
);
  xlclockdriver #(
    .period(1),
    .log_2_period(1)
  )
  clockdriver (
    .sysclk(ssrfft_sysclk),
    .sysce(ssrfft_sysce),
    .sysclr(ssrfft_sysclr),
    .clk(ssrfft_clk1),
    .ce(ssrfft_ce1)
  );
endmodule
`timescale 1 ns / 10 ps
// Generated from Simulink block 
(* core_generation_info = "ssrfft,sysgen_core_2020_2,{,compilation=IP Catalog,block_icon_display=Default,family=zynquplusRFSOC,part=xczu28dr,speed=-2-e,package=ffvg1517,synthesis_language=verilog,hdl_library=xil_defaultlib,synthesis_strategy=Vivado Synthesis Defaults,implementation_strategy=Vivado Implementation Defaults,testbench=0,interface_doc=0,ce_clr=0,clock_period=2,system_simulink_period=2e-09,waveform_viewer=0,axilite_interface=0,ip_catalog_plugin=0,hwcosim_burst_mode=0,simulation_time=4.096e-06,blackbox2=1,concat=5,constant=1,counter=1,delay=6,inv=1,reinterpret=16,relational=1,slice=12,}" *)
module ssrfft (
  input [10-1:0] si,
  input [1-1:0] vi,
  input [16-1:0] i_im_0,
  input [16-1:0] i_im_1,
  input [16-1:0] i_im_2,
  input [16-1:0] i_im_3,
  input [16-1:0] i_re_0,
  input [16-1:0] i_re_1,
  input [16-1:0] i_re_2,
  input [16-1:0] i_re_3,
  input clk,
  output [1-1:0] last,
  output [10-1:0] so,
  output [1-1:0] vo,
  output [26-1:0] o_im_0,
  output [26-1:0] o_im_1,
  output [26-1:0] o_im_2,
  output [26-1:0] o_im_3,
  output [26-1:0] o_re_0,
  output [26-1:0] o_re_1,
  output [26-1:0] o_re_2,
  output [26-1:0] o_re_3
);
  wire ce_1_net;
  wire clk_1_net;
  ssrfft_default_clock_driver ssrfft_default_clock_driver (
    .ssrfft_sysclk(clk),
    .ssrfft_sysce(1'b1),
    .ssrfft_sysclr(1'b0),
    .ssrfft_clk1(clk_1_net),
    .ssrfft_ce1(ce_1_net)
  );
  ssrfft_struct ssrfft_struct (
    .si(si),
    .vi(vi),
    .i_im_0(i_im_0),
    .i_im_1(i_im_1),
    .i_im_2(i_im_2),
    .i_im_3(i_im_3),
    .i_re_0(i_re_0),
    .i_re_1(i_re_1),
    .i_re_2(i_re_2),
    .i_re_3(i_re_3),
    .clk_1(clk_1_net),
    .ce_1(ce_1_net),
    .last(last),
    .so(so),
    .vo(vo),
    .o_im_0(o_im_0),
    .o_im_1(o_im_1),
    .o_im_2(o_im_2),
    .o_im_3(o_im_3),
    .o_re_0(o_re_0),
    .o_re_1(o_re_1),
    .o_re_2(o_re_2),
    .o_re_3(o_re_3)
  );
endmodule
