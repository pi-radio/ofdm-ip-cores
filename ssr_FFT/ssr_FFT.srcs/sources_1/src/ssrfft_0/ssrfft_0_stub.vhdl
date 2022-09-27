-- Copyright 1986-2021 Xilinx, Inc. All Rights Reserved.
-- --------------------------------------------------------------------------------
-- Tool Version: Vivado v.2021.1 (lin64) Build 3247384 Thu Jun 10 19:36:07 MDT 2021
-- Date        : Mon Jun 13 10:10:35 2022
-- Host        : focus running 64-bit openSUSE Tumbleweed
-- Command     : write_vhdl -force -mode synth_stub
--               /home/george/Documents/piradio_driver_dev/ip/ssr_FFT/ssr_FFT.srcs/sources_1/src/ssrfft_0/ssrfft_0_stub.vhdl
-- Design      : ssrfft_0
-- Purpose     : Stub declaration of top-level module interface
-- Device      : xczu28dr-ffvg1517-2-e
-- --------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity ssrfft_0 is
  Port ( 
    si : in STD_LOGIC_VECTOR ( 9 downto 0 );
    vi : in STD_LOGIC_VECTOR ( 0 to 0 );
    i_im_0 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_im_1 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_im_2 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_im_3 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_re_0 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_re_1 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_re_2 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    i_re_3 : in STD_LOGIC_VECTOR ( 15 downto 0 );
    clk : in STD_LOGIC;
    last : out STD_LOGIC_VECTOR ( 0 to 0 );
    so : out STD_LOGIC_VECTOR ( 9 downto 0 );
    vo : out STD_LOGIC_VECTOR ( 0 to 0 );
    o_im_0 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_im_1 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_im_2 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_im_3 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_re_0 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_re_1 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_re_2 : out STD_LOGIC_VECTOR ( 25 downto 0 );
    o_re_3 : out STD_LOGIC_VECTOR ( 25 downto 0 )
  );

end ssrfft_0;

architecture stub of ssrfft_0 is
attribute syn_black_box : boolean;
attribute black_box_pad_pin : string;
attribute syn_black_box of stub : architecture is true;
attribute black_box_pad_pin of stub : architecture is "si[9:0],vi[0:0],i_im_0[15:0],i_im_1[15:0],i_im_2[15:0],i_im_3[15:0],i_re_0[15:0],i_re_1[15:0],i_re_2[15:0],i_re_3[15:0],clk,last[0:0],so[9:0],vo[0:0],o_im_0[25:0],o_im_1[25:0],o_im_2[25:0],o_im_3[25:0],o_re_0[25:0],o_re_1[25:0],o_re_2[25:0],o_re_3[25:0]";
attribute X_CORE_INFO : string;
attribute X_CORE_INFO of stub : architecture is "ssrfft,Vivado 2021.1";
begin
end;
