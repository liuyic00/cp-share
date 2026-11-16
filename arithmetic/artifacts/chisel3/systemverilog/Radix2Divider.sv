module Radix2Divider(
  input         clock,
  input         reset,
  output        io_in_ready, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  input         io_in_valid, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  input  [63:0] io_in_bits_src_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  input  [63:0] io_in_bits_src_1, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  input  [63:0] io_in_bits_src_2, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  input         io_out_ready, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  output        io_out_valid, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  output [63:0] io_out_bits_data, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 27:14]
  input         ctrl_sign, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 37:16]
  input         ctrl_isW, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 37:16]
  input         ctrl_isHi // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 37:16]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [159:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [63:0] _RAND_5;
  reg [95:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
  reg [31:0] _RAND_13;
  reg [63:0] _RAND_14;
`endif // RANDOMIZE_REG_INIT
  reg [2:0] state; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 50:23]
  wire  _newReq_T_1 = io_in_ready & io_in_valid; // @[src/main/scala/chisel3/util/Decoupled.scala 52:35]
  wire  newReq = state == 3'h0 & _newReq_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 51:35]
  wire  divBy0 = io_in_bits_src_1 == 64'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 54:21]
  reg  divBy0Reg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 55:28]
  reg [128:0] shiftReg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 57:21]
  wire [64:0] hi = shiftReg[128:64]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 58:26]
  wire [63:0] lo = shiftReg[63:0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 59:26]
  wire  aSign = io_in_bits_src_0[63] & ctrl_sign; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 44:24]
  wire [63:0] _T_1 = 64'h0 - io_in_bits_src_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 45:16]
  wire [63:0] aVal = aSign ? _T_1 : io_in_bits_src_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 45:12]
  wire  bSign = io_in_bits_src_1[63] & ctrl_sign; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 44:24]
  wire [63:0] _T_3 = 64'h0 - io_in_bits_src_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 45:16]
  reg  aSignReg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 63:32]
  reg  qSignReg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 64:32]
  reg [63:0] bReg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 65:32]
  wire [64:0] _aValx2Reg_T = {aVal,1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 66:36]
  reg [64:0] aValx2Reg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 66:32]
  reg  ctrlReg_isW; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 67:32]
  reg  ctrlReg_isHi; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 67:32]
  reg [5:0] cnt_value; // @[src/main/scala/chisel3/util/Counter.scala 61:40]
  wire [31:0] canSkipShift_hi = bReg[63:32]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [31:0] canSkipShift_lo = bReg[31:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi = |canSkipShift_hi; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [15:0] canSkipShift_hi_1 = canSkipShift_hi[31:16]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [15:0] canSkipShift_lo_1 = canSkipShift_hi[15:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_1 = |canSkipShift_hi_1; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [7:0] canSkipShift_hi_2 = canSkipShift_hi_1[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_2 = canSkipShift_hi_1[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_2 = |canSkipShift_hi_2; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_3 = canSkipShift_hi_2[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_3 = canSkipShift_hi_2[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_3 = |canSkipShift_hi_3; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_3 = canSkipShift_hi_3[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_3[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_4 = canSkipShift_hi_3[3] ? 2'h3 : _canSkipShift_T_3; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_8 = canSkipShift_lo_3[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_3[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_9 = canSkipShift_lo_3[3] ? 2'h3 : _canSkipShift_T_8; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_10 = canSkipShift_useHi_3 ? _canSkipShift_T_4 : _canSkipShift_T_9; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_11 = {canSkipShift_useHi_3,_canSkipShift_T_10}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_4 = canSkipShift_lo_2[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_4 = canSkipShift_lo_2[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_4 = |canSkipShift_hi_4; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_15 = canSkipShift_hi_4[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_4[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_16 = canSkipShift_hi_4[3] ? 2'h3 : _canSkipShift_T_15; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_20 = canSkipShift_lo_4[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_4[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_21 = canSkipShift_lo_4[3] ? 2'h3 : _canSkipShift_T_20; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_22 = canSkipShift_useHi_4 ? _canSkipShift_T_16 : _canSkipShift_T_21; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_23 = {canSkipShift_useHi_4,_canSkipShift_T_22}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_24 = canSkipShift_useHi_2 ? _canSkipShift_T_11 : _canSkipShift_T_23; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_25 = {canSkipShift_useHi_2,_canSkipShift_T_24}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [7:0] canSkipShift_hi_5 = canSkipShift_lo_1[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_5 = canSkipShift_lo_1[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_5 = |canSkipShift_hi_5; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_6 = canSkipShift_hi_5[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_6 = canSkipShift_hi_5[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_6 = |canSkipShift_hi_6; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_29 = canSkipShift_hi_6[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_6[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_30 = canSkipShift_hi_6[3] ? 2'h3 : _canSkipShift_T_29; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_34 = canSkipShift_lo_6[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_6[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_35 = canSkipShift_lo_6[3] ? 2'h3 : _canSkipShift_T_34; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_36 = canSkipShift_useHi_6 ? _canSkipShift_T_30 : _canSkipShift_T_35; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_37 = {canSkipShift_useHi_6,_canSkipShift_T_36}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_7 = canSkipShift_lo_5[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_7 = canSkipShift_lo_5[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_7 = |canSkipShift_hi_7; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_41 = canSkipShift_hi_7[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_7[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_42 = canSkipShift_hi_7[3] ? 2'h3 : _canSkipShift_T_41; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_46 = canSkipShift_lo_7[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_7[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_47 = canSkipShift_lo_7[3] ? 2'h3 : _canSkipShift_T_46; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_48 = canSkipShift_useHi_7 ? _canSkipShift_T_42 : _canSkipShift_T_47; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_49 = {canSkipShift_useHi_7,_canSkipShift_T_48}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_50 = canSkipShift_useHi_5 ? _canSkipShift_T_37 : _canSkipShift_T_49; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_51 = {canSkipShift_useHi_5,_canSkipShift_T_50}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] _canSkipShift_T_52 = canSkipShift_useHi_1 ? _canSkipShift_T_25 : _canSkipShift_T_51; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [4:0] _canSkipShift_T_53 = {canSkipShift_useHi_1,_canSkipShift_T_52}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [15:0] canSkipShift_hi_8 = canSkipShift_lo[31:16]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [15:0] canSkipShift_lo_8 = canSkipShift_lo[15:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_8 = |canSkipShift_hi_8; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [7:0] canSkipShift_hi_9 = canSkipShift_hi_8[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_9 = canSkipShift_hi_8[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_9 = |canSkipShift_hi_9; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_10 = canSkipShift_hi_9[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_10 = canSkipShift_hi_9[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_10 = |canSkipShift_hi_10; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_57 = canSkipShift_hi_10[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_10[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_58 = canSkipShift_hi_10[3] ? 2'h3 : _canSkipShift_T_57; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_62 = canSkipShift_lo_10[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_10[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_63 = canSkipShift_lo_10[3] ? 2'h3 : _canSkipShift_T_62; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_64 = canSkipShift_useHi_10 ? _canSkipShift_T_58 : _canSkipShift_T_63; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_65 = {canSkipShift_useHi_10,_canSkipShift_T_64}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_11 = canSkipShift_lo_9[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_11 = canSkipShift_lo_9[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_11 = |canSkipShift_hi_11; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_69 = canSkipShift_hi_11[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_11[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_70 = canSkipShift_hi_11[3] ? 2'h3 : _canSkipShift_T_69; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_74 = canSkipShift_lo_11[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_11[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_75 = canSkipShift_lo_11[3] ? 2'h3 : _canSkipShift_T_74; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_76 = canSkipShift_useHi_11 ? _canSkipShift_T_70 : _canSkipShift_T_75; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_77 = {canSkipShift_useHi_11,_canSkipShift_T_76}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_78 = canSkipShift_useHi_9 ? _canSkipShift_T_65 : _canSkipShift_T_77; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_79 = {canSkipShift_useHi_9,_canSkipShift_T_78}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [7:0] canSkipShift_hi_12 = canSkipShift_lo_8[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_12 = canSkipShift_lo_8[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_12 = |canSkipShift_hi_12; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_13 = canSkipShift_hi_12[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_13 = canSkipShift_hi_12[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_13 = |canSkipShift_hi_13; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_83 = canSkipShift_hi_13[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_13[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_84 = canSkipShift_hi_13[3] ? 2'h3 : _canSkipShift_T_83; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_88 = canSkipShift_lo_13[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_13[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_89 = canSkipShift_lo_13[3] ? 2'h3 : _canSkipShift_T_88; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_90 = canSkipShift_useHi_13 ? _canSkipShift_T_84 : _canSkipShift_T_89; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_91 = {canSkipShift_useHi_13,_canSkipShift_T_90}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_14 = canSkipShift_lo_12[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_14 = canSkipShift_lo_12[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_14 = |canSkipShift_hi_14; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_95 = canSkipShift_hi_14[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_14[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_96 = canSkipShift_hi_14[3] ? 2'h3 : _canSkipShift_T_95; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_100 = canSkipShift_lo_14[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_14[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_101 = canSkipShift_lo_14[3] ? 2'h3 : _canSkipShift_T_100; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_102 = canSkipShift_useHi_14 ? _canSkipShift_T_96 : _canSkipShift_T_101; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_103 = {canSkipShift_useHi_14,_canSkipShift_T_102}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_104 = canSkipShift_useHi_12 ? _canSkipShift_T_91 : _canSkipShift_T_103; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_105 = {canSkipShift_useHi_12,_canSkipShift_T_104}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] _canSkipShift_T_106 = canSkipShift_useHi_8 ? _canSkipShift_T_79 : _canSkipShift_T_105; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [4:0] _canSkipShift_T_107 = {canSkipShift_useHi_8,_canSkipShift_T_106}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [4:0] _canSkipShift_T_108 = canSkipShift_useHi ? _canSkipShift_T_53 : _canSkipShift_T_107; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [5:0] _canSkipShift_T_109 = {canSkipShift_useHi,_canSkipShift_T_108}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [6:0] _GEN_23 = {{1'd0}, _canSkipShift_T_109}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 82:31]
  wire [6:0] _canSkipShift_T_111 = 7'h40 + _GEN_23; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 82:31]
  wire  canSkipShift_hi_15 = aValx2Reg[64]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [63:0] canSkipShift_lo_15 = aValx2Reg[63:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_15 = |canSkipShift_hi_15; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [31:0] canSkipShift_hi_16 = canSkipShift_lo_15[63:32]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [31:0] canSkipShift_lo_16 = canSkipShift_lo_15[31:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_16 = |canSkipShift_hi_16; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [15:0] canSkipShift_hi_17 = canSkipShift_hi_16[31:16]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [15:0] canSkipShift_lo_17 = canSkipShift_hi_16[15:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_17 = |canSkipShift_hi_17; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [7:0] canSkipShift_hi_18 = canSkipShift_hi_17[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_18 = canSkipShift_hi_17[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_18 = |canSkipShift_hi_18; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_19 = canSkipShift_hi_18[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_19 = canSkipShift_hi_18[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_19 = |canSkipShift_hi_19; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_115 = canSkipShift_hi_19[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_19[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_116 = canSkipShift_hi_19[3] ? 2'h3 : _canSkipShift_T_115; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_120 = canSkipShift_lo_19[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_19[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_121 = canSkipShift_lo_19[3] ? 2'h3 : _canSkipShift_T_120; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_122 = canSkipShift_useHi_19 ? _canSkipShift_T_116 : _canSkipShift_T_121; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_123 = {canSkipShift_useHi_19,_canSkipShift_T_122}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_20 = canSkipShift_lo_18[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_20 = canSkipShift_lo_18[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_20 = |canSkipShift_hi_20; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_127 = canSkipShift_hi_20[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_20[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_128 = canSkipShift_hi_20[3] ? 2'h3 : _canSkipShift_T_127; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_132 = canSkipShift_lo_20[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_20[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_133 = canSkipShift_lo_20[3] ? 2'h3 : _canSkipShift_T_132; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_134 = canSkipShift_useHi_20 ? _canSkipShift_T_128 : _canSkipShift_T_133; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_135 = {canSkipShift_useHi_20,_canSkipShift_T_134}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_136 = canSkipShift_useHi_18 ? _canSkipShift_T_123 : _canSkipShift_T_135; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_137 = {canSkipShift_useHi_18,_canSkipShift_T_136}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [7:0] canSkipShift_hi_21 = canSkipShift_lo_17[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_21 = canSkipShift_lo_17[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_21 = |canSkipShift_hi_21; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_22 = canSkipShift_hi_21[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_22 = canSkipShift_hi_21[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_22 = |canSkipShift_hi_22; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_141 = canSkipShift_hi_22[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_22[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_142 = canSkipShift_hi_22[3] ? 2'h3 : _canSkipShift_T_141; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_146 = canSkipShift_lo_22[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_22[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_147 = canSkipShift_lo_22[3] ? 2'h3 : _canSkipShift_T_146; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_148 = canSkipShift_useHi_22 ? _canSkipShift_T_142 : _canSkipShift_T_147; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_149 = {canSkipShift_useHi_22,_canSkipShift_T_148}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_23 = canSkipShift_lo_21[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_23 = canSkipShift_lo_21[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_23 = |canSkipShift_hi_23; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_153 = canSkipShift_hi_23[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_23[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_154 = canSkipShift_hi_23[3] ? 2'h3 : _canSkipShift_T_153; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_158 = canSkipShift_lo_23[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_23[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_159 = canSkipShift_lo_23[3] ? 2'h3 : _canSkipShift_T_158; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_160 = canSkipShift_useHi_23 ? _canSkipShift_T_154 : _canSkipShift_T_159; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_161 = {canSkipShift_useHi_23,_canSkipShift_T_160}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_162 = canSkipShift_useHi_21 ? _canSkipShift_T_149 : _canSkipShift_T_161; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_163 = {canSkipShift_useHi_21,_canSkipShift_T_162}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] _canSkipShift_T_164 = canSkipShift_useHi_17 ? _canSkipShift_T_137 : _canSkipShift_T_163; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [4:0] _canSkipShift_T_165 = {canSkipShift_useHi_17,_canSkipShift_T_164}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [15:0] canSkipShift_hi_24 = canSkipShift_lo_16[31:16]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [15:0] canSkipShift_lo_24 = canSkipShift_lo_16[15:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_24 = |canSkipShift_hi_24; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [7:0] canSkipShift_hi_25 = canSkipShift_hi_24[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_25 = canSkipShift_hi_24[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_25 = |canSkipShift_hi_25; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_26 = canSkipShift_hi_25[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_26 = canSkipShift_hi_25[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_26 = |canSkipShift_hi_26; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_169 = canSkipShift_hi_26[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_26[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_170 = canSkipShift_hi_26[3] ? 2'h3 : _canSkipShift_T_169; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_174 = canSkipShift_lo_26[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_26[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_175 = canSkipShift_lo_26[3] ? 2'h3 : _canSkipShift_T_174; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_176 = canSkipShift_useHi_26 ? _canSkipShift_T_170 : _canSkipShift_T_175; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_177 = {canSkipShift_useHi_26,_canSkipShift_T_176}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_27 = canSkipShift_lo_25[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_27 = canSkipShift_lo_25[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_27 = |canSkipShift_hi_27; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_181 = canSkipShift_hi_27[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_27[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_182 = canSkipShift_hi_27[3] ? 2'h3 : _canSkipShift_T_181; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_186 = canSkipShift_lo_27[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_27[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_187 = canSkipShift_lo_27[3] ? 2'h3 : _canSkipShift_T_186; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_188 = canSkipShift_useHi_27 ? _canSkipShift_T_182 : _canSkipShift_T_187; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_189 = {canSkipShift_useHi_27,_canSkipShift_T_188}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_190 = canSkipShift_useHi_25 ? _canSkipShift_T_177 : _canSkipShift_T_189; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_191 = {canSkipShift_useHi_25,_canSkipShift_T_190}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [7:0] canSkipShift_hi_28 = canSkipShift_lo_24[15:8]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [7:0] canSkipShift_lo_28 = canSkipShift_lo_24[7:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_28 = |canSkipShift_hi_28; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [3:0] canSkipShift_hi_29 = canSkipShift_hi_28[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_29 = canSkipShift_hi_28[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_29 = |canSkipShift_hi_29; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_195 = canSkipShift_hi_29[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_29[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_196 = canSkipShift_hi_29[3] ? 2'h3 : _canSkipShift_T_195; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_200 = canSkipShift_lo_29[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_29[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_201 = canSkipShift_lo_29[3] ? 2'h3 : _canSkipShift_T_200; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_202 = canSkipShift_useHi_29 ? _canSkipShift_T_196 : _canSkipShift_T_201; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_203 = {canSkipShift_useHi_29,_canSkipShift_T_202}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] canSkipShift_hi_30 = canSkipShift_lo_28[7:4]; // @[src/main/scala/chisel3/util/CircuitMath.scala 33:17]
  wire [3:0] canSkipShift_lo_30 = canSkipShift_lo_28[3:0]; // @[src/main/scala/chisel3/util/CircuitMath.scala 34:17]
  wire  canSkipShift_useHi_30 = |canSkipShift_hi_30; // @[src/main/scala/chisel3/util/CircuitMath.scala 35:22]
  wire [1:0] _canSkipShift_T_207 = canSkipShift_hi_30[2] ? 2'h2 : {{1'd0}, canSkipShift_hi_30[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_208 = canSkipShift_hi_30[3] ? 2'h3 : _canSkipShift_T_207; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_212 = canSkipShift_lo_30[2] ? 2'h2 : {{1'd0}, canSkipShift_lo_30[1]}; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_213 = canSkipShift_lo_30[3] ? 2'h3 : _canSkipShift_T_212; // @[src/main/scala/chisel3/util/CircuitMath.scala 30:10]
  wire [1:0] _canSkipShift_T_214 = canSkipShift_useHi_30 ? _canSkipShift_T_208 : _canSkipShift_T_213; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [2:0] _canSkipShift_T_215 = {canSkipShift_useHi_30,_canSkipShift_T_214}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [2:0] _canSkipShift_T_216 = canSkipShift_useHi_28 ? _canSkipShift_T_203 : _canSkipShift_T_215; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [3:0] _canSkipShift_T_217 = {canSkipShift_useHi_28,_canSkipShift_T_216}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [3:0] _canSkipShift_T_218 = canSkipShift_useHi_24 ? _canSkipShift_T_191 : _canSkipShift_T_217; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [4:0] _canSkipShift_T_219 = {canSkipShift_useHi_24,_canSkipShift_T_218}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [4:0] _canSkipShift_T_220 = canSkipShift_useHi_16 ? _canSkipShift_T_165 : _canSkipShift_T_219; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [5:0] _canSkipShift_T_221 = {canSkipShift_useHi_16,_canSkipShift_T_220}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [5:0] _canSkipShift_T_222 = canSkipShift_useHi_15 ? 6'h0 : _canSkipShift_T_221; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:21]
  wire [6:0] _canSkipShift_T_223 = {canSkipShift_useHi_15,_canSkipShift_T_222}; // @[src/main/scala/chisel3/util/CircuitMath.scala 36:10]
  wire [6:0] canSkipShift = _canSkipShift_T_111 - _canSkipShift_T_223; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 82:45]
  wire [6:0] _value_T_1 = canSkipShift >= 7'h3f ? 7'h3f : canSkipShift; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 89:10]
  wire [6:0] _value_T_2 = divBy0Reg ? 7'h0 : _value_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 86:21]
  wire  _T_5 = state == 3'h2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 92:20]
  wire [127:0] _GEN_0 = {{63'd0}, aValx2Reg}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 93:27]
  wire [127:0] _shiftReg_T = _GEN_0 << cnt_value; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 93:27]
  wire  _T_6 = state == 3'h3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 95:20]
  wire [64:0] _GEN_24 = {{1'd0}, bReg}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 96:28]
  wire  enough = hi >= _GEN_24; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 96:28]
  wire [64:0] _shiftReg_T_2 = hi - _GEN_24; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 97:36]
  wire [64:0] _shiftReg_T_3 = enough ? _shiftReg_T_2 : hi; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 97:24]
  wire [128:0] _shiftReg_T_5 = {_shiftReg_T_3[63:0],lo,enough}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 97:20]
  wire  wrap = cnt_value == 6'h3f; // @[src/main/scala/chisel3/util/Counter.scala 73:24]
  wire [5:0] _value_T_4 = cnt_value + 6'h1; // @[src/main/scala/chisel3/util/Counter.scala 77:24]
  wire [2:0] _GEN_8 = wrap ? 3'h4 : state; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 50:23 99:{37,45}]
  wire [2:0] _GEN_9 = io_out_ready ? 3'h0 : state; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 101:24 102:13 50:23]
  wire [2:0] _GEN_10 = state == 3'h4 ? _GEN_9 : state; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 100:34 50:23]
  wire [5:0] _GEN_12 = state == 3'h3 ? _value_T_4 : cnt_value; // @[src/main/scala/chisel3/util/Counter.scala 77:15 workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 95:35 src/main/scala/chisel3/util/Counter.scala 61:40]
  wire [2:0] _GEN_13 = state == 3'h3 ? _GEN_8 : _GEN_10; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 95:35]
  wire [5:0] _GEN_16 = state == 3'h2 ? cnt_value : _GEN_12; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 92:33 src/main/scala/chisel3/util/Counter.scala 61:40]
  wire [6:0] _GEN_17 = state == 3'h1 ? _value_T_2 : {{1'd0}, _GEN_16}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 72:32 86:15]
  wire [6:0] _GEN_21 = newReq ? {{1'd0}, cnt_value} : _GEN_17; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 70:16 src/main/scala/chisel3/util/Counter.scala 61:40]
  wire [63:0] r = hi[64:1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 106:16]
  wire [63:0] _resQ_T_1 = 64'h0 - lo; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 107:28]
  wire [63:0] resQ = qSignReg ? _resQ_T_1 : lo; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 107:17]
  wire [63:0] _resR_T_1 = 64'h0 - r; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 108:28]
  wire [63:0] resR = aSignReg ? _resR_T_1 : r; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 108:17]
  wire [63:0] res = ctrlReg_isHi ? resR : resQ; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 111:17]
  wire  io_out_bits_data_signBit = res[31]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 11:20]
  wire [31:0] _io_out_bits_data_T_2 = io_out_bits_data_signBit ? 32'hffffffff : 32'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 12:49]
  wire [63:0] _io_out_bits_data_T_3 = {_io_out_bits_data_T_2,res[31:0]}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 12:44]
  wire  _T_11 = ~reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 122:13]
  wire [127:0] _T_22 = lo * bReg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 126:18]
  wire [127:0] _GEN_26 = {{64'd0}, r}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 126:26]
  wire [128:0] _T_23 = _T_22 + _GEN_26; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 126:26]
  wire [128:0] _GEN_27 = {{65'd0}, aValx2Reg[64:1]}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 126:31]
  reg  historyValid; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 134:29]
  reg [2:0] previousState; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 135:30]
  reg [5:0] previousCount; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 136:30]
  wire  _T_43 = previousState == 3'h3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 140:24]
  wire  _T_44 = previousCount == 6'h3f; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 141:42]
  wire [2:0] _T_45 = previousCount == 6'h3f ? 3'h4 : 3'h3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 141:27]
  wire [5:0] _T_52 = previousCount + 6'h1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 142:82]
  wire [5:0] _T_53 = _T_44 ? 6'h0 : _T_52; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 142:31]
  reg  wasStalled; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 145:27]
  reg [63:0] previousOutput; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 146:31]
  wire [6:0] _GEN_28 = reset ? 7'h0 : _GEN_21; // @[src/main/scala/chisel3/util/Counter.scala 61:{40,40}]
  wire  _GEN_29 = io_out_valid & divBy0Reg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 122:13]
  wire  _GEN_30 = io_out_valid & divBy0Reg & ~reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 122:13]
  wire  _GEN_36 = io_out_valid & ~divBy0Reg; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 125:13]
  wire  _GEN_37 = io_out_valid & ~divBy0Reg & _T_11; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 125:13]
  wire  _GEN_56 = historyValid & _T_43; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 141:13]
  wire  _GEN_57 = historyValid & _T_43 & _T_11; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 141:13]
  wire  _GEN_62 = wasStalled & _T_11; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 148:11]
  assign io_in_ready = state == 3'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 115:25]
  assign io_out_valid = state == 3'h4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 114:25]
  assign io_out_bits_data = ctrlReg_isW ? _io_out_bits_data_T_3 : res; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 112:26]
  always @(posedge clock) begin
    if (reset) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 50:{23,23}]
      state <= 3'h0;
    end else if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 70:16 71:11]
      state <= 3'h1;
    end else if (state == 3'h1) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 72:32 91:11]
      state <= 3'h2;
    end else if (state == 3'h2) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 92:33 94:14]
      state <= 3'h3;
    end else begin
      state <= _GEN_13;
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 55:28]
      divBy0Reg <= divBy0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 55:28]
    end
    if (!(newReq)) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 70:16 57:21]
      if (!(state == 3'h1)) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 57:21 72:32]
        if (state == 3'h2) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 92:33 93:14]
          shiftReg <= {{1'd0}, _shiftReg_T};
        end else if (state == 3'h3) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 95:35]
          shiftReg <= _shiftReg_T_5; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 97:14]
        end
      end
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 63:32]
      aSignReg <= aSign; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 63:32]
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 64:32]
      qSignReg <= (aSign ^ bSign) & ~divBy0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 64:32]
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 65:32]
      if (bSign) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 45:12]
        bReg <= _T_3;
      end else begin
        bReg <= io_in_bits_src_1;
      end
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 66:32]
      aValx2Reg <= _aValx2Reg_T; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 66:32]
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 67:32]
      ctrlReg_isW <= ctrl_isW; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 67:32]
    end
    if (newReq) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 67:32]
      ctrlReg_isHi <= ctrl_isHi; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 67:32]
    end
    cnt_value <= _GEN_28[5:0]; // @[src/main/scala/chisel3/util/Counter.scala 61:{40,40}]
    if (reset) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 134:29]
      historyValid <= 1'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 134:29]
    end else begin
      historyValid <= 1'h1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 134:29]
    end
    previousState <= state; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 135:30]
    previousCount <= cnt_value; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 136:30]
    if (reset) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 145:27]
      wasStalled <= 1'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 145:27]
    end else begin
      wasStalled <= io_out_valid & ~io_out_ready; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 145:27]
    end
    previousOutput <= io_out_bits_data; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 146:31]
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (io_out_valid & divBy0Reg & ~reset & ~(lo == 64'hffffffffffffffff)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:122 assert(lo === ((BigInt(1) << len) - 1).U(len.W))\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 122:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_GEN_30 & ~(r == aValx2Reg[64:1])) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Radix2Divider.scala:123 assert(r === aValx2Reg(len, 1))\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 123:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (io_out_valid & ~divBy0Reg & _T_11 & ~(bReg != 64'h0)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Radix2Divider.scala:125 assert(bReg =/= 0.U)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 125:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_GEN_37 & ~(_T_23 == _GEN_27)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:126 assert((lo * bReg) +& r === aValx2Reg(len, 1))\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 126:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_GEN_37 & ~(r < bReg)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Radix2Divider.scala:127 assert(r < bReg)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 127:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (historyValid & previousState == 3'h1 & _T_11 & ~_T_5) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:138 when(previousState === s_log2) { assert(state === s_shift) }\n"
            ); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 138:44]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (historyValid & previousState == 3'h2 & _T_11 & ~_T_6) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:139 when(previousState === s_shift) { assert(state === s_compute) }\n"
            ); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 139:45]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (historyValid & _T_43 & _T_11 & ~(state == _T_45)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:141 assert(state === Mux(previousCount === (len - 1).U, s_finish, s_compute))\n"
            ); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 141:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_GEN_57 & ~(cnt_value == _T_53)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:142 assert(cnt.value === Mux(previousCount === (len - 1).U, 0.U, previousCount + 1.U))\n"
            ); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 142:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (wasStalled & _T_11 & ~io_out_valid) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Radix2Divider.scala:148 assert(io.out.valid)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 148:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_GEN_62 & ~(io_out_bits_data == previousOutput)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Radix2Divider.scala:149 assert(io.out.bits.data === previousOutput)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 149:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  state = _RAND_0[2:0];
  _RAND_1 = {1{`RANDOM}};
  divBy0Reg = _RAND_1[0:0];
  _RAND_2 = {5{`RANDOM}};
  shiftReg = _RAND_2[128:0];
  _RAND_3 = {1{`RANDOM}};
  aSignReg = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  qSignReg = _RAND_4[0:0];
  _RAND_5 = {2{`RANDOM}};
  bReg = _RAND_5[63:0];
  _RAND_6 = {3{`RANDOM}};
  aValx2Reg = _RAND_6[64:0];
  _RAND_7 = {1{`RANDOM}};
  ctrlReg_isW = _RAND_7[0:0];
  _RAND_8 = {1{`RANDOM}};
  ctrlReg_isHi = _RAND_8[0:0];
  _RAND_9 = {1{`RANDOM}};
  cnt_value = _RAND_9[5:0];
  _RAND_10 = {1{`RANDOM}};
  historyValid = _RAND_10[0:0];
  _RAND_11 = {1{`RANDOM}};
  previousState = _RAND_11[2:0];
  _RAND_12 = {1{`RANDOM}};
  previousCount = _RAND_12[5:0];
  _RAND_13 = {1{`RANDOM}};
  wasStalled = _RAND_13[0:0];
  _RAND_14 = {2{`RANDOM}};
  previousOutput = _RAND_14[63:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (io_out_valid & divBy0Reg & ~reset) begin
      assert(lo == 64'hffffffffffffffff); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 122:13]
    end
    //
    if (_GEN_29 & _T_11) begin
      assert(r == aValx2Reg[64:1]); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 123:13]
    end
    //
    if (io_out_valid & ~divBy0Reg & _T_11) begin
      assert(bReg != 64'h0); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 125:13]
    end
    //
    if (_GEN_36 & _T_11) begin
      assert(_T_23 == _GEN_27); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 126:13]
    end
    //
    if (_GEN_36 & _T_11) begin
      assert(r < bReg); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 127:13]
    end
    //
    if (historyValid & previousState == 3'h1 & _T_11) begin
      assert(_T_5); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 138:44]
    end
    //
    if (historyValid & previousState == 3'h2 & _T_11) begin
      assert(_T_6); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 139:45]
    end
    //
    if (historyValid & _T_43 & _T_11) begin
      assert(state == _T_45); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 141:13]
    end
    //
    if (_GEN_56 & _T_11) begin
      assert(cnt_value == _T_53); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 142:13]
    end
    //
    if (wasStalled & _T_11) begin
      assert(io_out_valid); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 148:11]
    end
    //
    if (wasStalled & _T_11) begin
      assert(io_out_bits_data == previousOutput); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Radix2Divider.scala 149:11]
    end
  end
endmodule
