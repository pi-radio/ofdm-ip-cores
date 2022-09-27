// Copyright 1986-2021 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2021.1 (lin64) Build 3247384 Thu Jun 10 19:36:07 MDT 2021
// Date        : Mon Jun 13 10:10:35 2022
// Host        : focus running 64-bit openSUSE Tumbleweed
// Command     : write_verilog -force -mode synth_stub
//               /home/george/Documents/piradio_driver_dev/ip/ssr_FFT/ssr_FFT.srcs/sources_1/src/ssrfft_0/ssrfft_0_stub.v
// Design      : ssrfft_0
// Purpose     : Stub declaration of top-level module interface
// Device      : xczu28dr-ffvg1517-2-e
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
(* X_CORE_INFO = "ssrfft,Vivado 2021.1" *)
module ssrfft_0(si, vi, i_im_0, i_im_1, i_im_2, i_im_3, i_re_0, i_re_1, 
  i_re_2, i_re_3, clk, last, so, vo, o_im_0, o_im_1, o_im_2, o_im_3, o_re_0, o_re_1, o_re_2, o_re_3)
/* synthesis syn_black_box black_box_pad_pin="si[9:0],vi[0:0],i_im_0[15:0],i_im_1[15:0],i_im_2[15:0],i_im_3[15:0],i_re_0[15:0],i_re_1[15:0],i_re_2[15:0],i_re_3[15:0],clk,last[0:0],so[9:0],vo[0:0],o_im_0[25:0],o_im_1[25:0],o_im_2[25:0],o_im_3[25:0],o_re_0[25:0],o_re_1[25:0],o_re_2[25:0],o_re_3[25:0]" */;
  input [9:0]si;
  input [0:0]vi;
  input [15:0]i_im_0;
  input [15:0]i_im_1;
  input [15:0]i_im_2;
  input [15:0]i_im_3;
  input [15:0]i_re_0;
  input [15:0]i_re_1;
  input [15:0]i_re_2;
  input [15:0]i_re_3;
  input clk;
  output [0:0]last;
  output [9:0]so;
  output [0:0]vo;
  output [25:0]o_im_0;
  output [25:0]o_im_1;
  output [25:0]o_im_2;
  output [25:0]o_im_3;
  output [25:0]o_re_0;
  output [25:0]o_re_1;
  output [25:0]o_re_2;
  output [25:0]o_re_3;
endmodule
