// (c) Copyright 1995-2022 Xilinx, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 
// DO NOT MODIFY THIS FILE.

// IP VLNV: User_Company:SysGen:sysgenssrfft:1.0
// IP Revision: 285988280

// The following must be inserted into your Verilog file for this
// core to be instantiated. Change the instance name and port connections
// (in parentheses) to your own signal names.

//----------- Begin Cut here for INSTANTIATION Template ---// INST_TAG
sysgenssrfft_0 your_instance_name (
  .si(si),          // input wire [9 : 0] si
  .vi(vi),          // input wire [0 : 0] vi
  .i_im_0(i_im_0),  // input wire [15 : 0] i_im_0
  .i_im_1(i_im_1),  // input wire [15 : 0] i_im_1
  .i_im_2(i_im_2),  // input wire [15 : 0] i_im_2
  .i_im_3(i_im_3),  // input wire [15 : 0] i_im_3
  .i_re_0(i_re_0),  // input wire [15 : 0] i_re_0
  .i_re_1(i_re_1),  // input wire [15 : 0] i_re_1
  .i_re_2(i_re_2),  // input wire [15 : 0] i_re_2
  .i_re_3(i_re_3),  // input wire [15 : 0] i_re_3
  .clk(clk),        // input wire clk
  .last(last),      // output wire [0 : 0] last
  .so(so),          // output wire [9 : 0] so
  .vo(vo),          // output wire [0 : 0] vo
  .o_im_0(o_im_0),  // output wire [25 : 0] o_im_0
  .o_im_1(o_im_1),  // output wire [25 : 0] o_im_1
  .o_im_2(o_im_2),  // output wire [25 : 0] o_im_2
  .o_im_3(o_im_3),  // output wire [25 : 0] o_im_3
  .o_re_0(o_re_0),  // output wire [25 : 0] o_re_0
  .o_re_1(o_re_1),  // output wire [25 : 0] o_re_1
  .o_re_2(o_re_2),  // output wire [25 : 0] o_re_2
  .o_re_3(o_re_3)  // output wire [25 : 0] o_re_3
);
// INST_TAG_END ------ End INSTANTIATION Template ---------

