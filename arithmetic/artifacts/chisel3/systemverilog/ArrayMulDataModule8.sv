module C22(
  input   clock,
  input   reset,
  input   io_in_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_1, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_1 // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
);
  wire [3:0] _inputSum_T = {{3'd0}, io_in_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_1 = {{3'd0}, io_in_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] inputSum = _inputSum_T + _inputSum_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] _outputSum_T = {{3'd0}, io_out_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:28]
  wire [3:0] _outputSum_T_1 = {{3'd0}, io_out_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
  wire [4:0] _outputSum_T_2 = {_outputSum_T_1, 1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
  wire [4:0] _GEN_0 = {{1'd0}, _outputSum_T}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] outputSum = _GEN_0 + _outputSum_T_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] _GEN_1 = {{1'd0}, inputSum}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:19]
  wire  sum = io_in_0 ^ io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 35:20]
  wire  cout = io_in_0 & io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 36:20]
  wire [1:0] temp_0 = {cout,sum}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 37:13]
  assign io_out_0 = temp_0[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 39:76]
  assign io_out_1 = temp_0[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 39:76]
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(_GEN_1 == outputSum)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Multiplier.scala:28 assert(inputSum === outputSum)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(_GEN_1 == outputSum); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    end
  end
endmodule
module C32(
  input   clock,
  input   reset,
  input   io_in_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_1, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_2, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_1 // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
);
  wire [3:0] _inputSum_T = {{3'd0}, io_in_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_1 = {{3'd0}, io_in_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_2 = {{3'd0}, io_in_2}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_4 = _inputSum_T + _inputSum_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] inputSum = _inputSum_T_4 + _inputSum_T_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] _outputSum_T = {{3'd0}, io_out_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:28]
  wire [3:0] _outputSum_T_1 = {{3'd0}, io_out_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
  wire [4:0] _outputSum_T_2 = {_outputSum_T_1, 1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
  wire [4:0] _GEN_0 = {{1'd0}, _outputSum_T}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] outputSum = _GEN_0 + _outputSum_T_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] _GEN_1 = {{1'd0}, inputSum}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:19]
  wire  a_xor_b = io_in_0 ^ io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 46:25]
  wire  a_and_b = io_in_0 & io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 47:25]
  wire  sum = a_xor_b ^ io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 48:31]
  wire  cout = a_and_b | a_xor_b & io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 49:31]
  wire [1:0] temp_0 = {cout,sum}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 50:13]
  assign io_out_0 = temp_0[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 52:76]
  assign io_out_1 = temp_0[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 52:76]
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(_GEN_1 == outputSum)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Multiplier.scala:28 assert(inputSum === outputSum)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(_GEN_1 == outputSum); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    end
  end
endmodule
module C53(
  input   clock,
  input   reset,
  input   io_in_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_1, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_2, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_3, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  input   io_in_4, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_1, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
  output  io_out_2 // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
);
  wire  CSA3_2_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire  CSA3_2_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
  wire [3:0] _inputSum_T = {{3'd0}, io_in_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_1 = {{3'd0}, io_in_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_2 = {{3'd0}, io_in_2}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_3 = {{3'd0}, io_in_3}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_4 = {{3'd0}, io_in_4}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
  wire [3:0] _inputSum_T_6 = _inputSum_T + _inputSum_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] _inputSum_T_8 = _inputSum_T_6 + _inputSum_T_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] _inputSum_T_10 = _inputSum_T_8 + _inputSum_T_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] inputSum = _inputSum_T_10 + _inputSum_T_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
  wire [3:0] _outputSum_T = {{3'd0}, io_out_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:28]
  wire [3:0] _outputSum_T_1 = {{3'd0}, io_out_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
  wire [4:0] _outputSum_T_2 = {_outputSum_T_1, 1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
  wire [3:0] _outputSum_T_3 = {{3'd0}, io_out_2}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
  wire [4:0] _outputSum_T_4 = {_outputSum_T_3, 1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
  wire [4:0] _GEN_0 = {{1'd0}, _outputSum_T}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] _outputSum_T_6 = _GEN_0 + _outputSum_T_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] outputSum = _outputSum_T_6 + _outputSum_T_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
  wire [4:0] _GEN_1 = {{1'd0}, inputSum}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:19]
  C32 CSA3_2 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
    .clock(CSA3_2_clock),
    .reset(CSA3_2_reset),
    .io_in_0(CSA3_2_io_in_0),
    .io_in_1(CSA3_2_io_in_1),
    .io_in_2(CSA3_2_io_in_2),
    .io_out_0(CSA3_2_io_out_0),
    .io_out_1(CSA3_2_io_out_1)
  );
  C32 CSA3_2_1 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
    .clock(CSA3_2_1_clock),
    .reset(CSA3_2_1_reset),
    .io_in_0(CSA3_2_1_io_in_0),
    .io_in_1(CSA3_2_1_io_in_1),
    .io_in_2(CSA3_2_1_io_in_2),
    .io_out_0(CSA3_2_1_io_out_0),
    .io_out_1(CSA3_2_1_io_out_1)
  );
  assign io_out_0 = CSA3_2_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:{26,26}]
  assign io_out_1 = CSA3_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:{26,26}]
  assign io_out_2 = CSA3_2_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:{26,26}]
  assign CSA3_2_clock = clock;
  assign CSA3_2_reset = reset;
  assign CSA3_2_io_in_0 = io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 57:16]
  assign CSA3_2_io_in_1 = io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 57:16]
  assign CSA3_2_io_in_2 = io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 57:16]
  assign CSA3_2_1_clock = clock;
  assign CSA3_2_1_reset = reset;
  assign CSA3_2_1_io_in_0 = CSA3_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:{26,26}]
  assign CSA3_2_1_io_in_1 = io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:{26,26}]
  assign CSA3_2_1_io_in_2 = io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:{26,26}]
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(_GEN_1 == outputSum)) begin
          $fwrite(32'h80000002,"Assertion failed\n    at Multiplier.scala:28 assert(inputSum === outputSum)\n"); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
  always @(posedge clock) begin
    //
    if (~reset) begin
      assert(_GEN_1 == outputSum); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    end
  end
endmodule
module ArrayMulDataModule8(
  input         clock,
  input         reset,
  input  [7:0]  io_a, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
  input  [7:0]  io_b, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
  input         io_regEnables_0, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
  input         io_regEnables_1, // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
  output [15:0] io_result // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
  reg [31:0] _RAND_13;
  reg [31:0] _RAND_14;
  reg [31:0] _RAND_15;
  reg [31:0] _RAND_16;
  reg [31:0] _RAND_17;
  reg [31:0] _RAND_18;
  reg [31:0] _RAND_19;
  reg [31:0] _RAND_20;
  reg [31:0] _RAND_21;
  reg [31:0] _RAND_22;
  reg [31:0] _RAND_23;
  reg [31:0] _RAND_24;
  reg [31:0] _RAND_25;
  reg [31:0] _RAND_26;
  reg [31:0] _RAND_27;
  reg [31:0] _RAND_28;
  reg [31:0] _RAND_29;
  reg [31:0] _RAND_30;
  reg [31:0] _RAND_31;
  reg [31:0] _RAND_32;
  reg [31:0] _RAND_33;
  reg [31:0] _RAND_34;
  reg [31:0] _RAND_35;
  reg [31:0] _RAND_36;
  reg [31:0] _RAND_37;
  reg [31:0] _RAND_38;
  reg [31:0] _RAND_39;
  reg [31:0] _RAND_40;
  reg [31:0] _RAND_41;
  reg [31:0] _RAND_42;
  reg [31:0] _RAND_43;
  reg [31:0] _RAND_44;
  reg [31:0] _RAND_45;
  reg [31:0] _RAND_46;
  reg [31:0] _RAND_47;
  reg [31:0] _RAND_48;
  reg [31:0] _RAND_49;
  reg [31:0] _RAND_50;
  reg [31:0] _RAND_51;
  reg [31:0] _RAND_52;
  reg [31:0] _RAND_53;
  reg [31:0] _RAND_54;
  reg [31:0] _RAND_55;
`endif // RANDOMIZE_REG_INIT
  wire  c22_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_1_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_1_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_1_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_1_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c32_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c53_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_1_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_2_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_3_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_4_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_5_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_6_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_in_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_in_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c53_7_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
  wire  c32_2_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_2_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_2_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_2_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_2_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c22_2_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_2_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_2_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_2_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_3_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_3_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_3_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_3_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_3_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_3_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_4_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_4_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_4_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_4_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_4_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_4_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_5_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_5_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_5_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_5_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_5_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_5_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_6_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_6_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_6_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_6_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_6_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_6_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_7_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_7_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_7_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_7_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_7_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_7_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_8_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_8_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_8_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_8_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_8_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_8_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c32_3_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_3_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_3_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_3_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_3_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_3_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_3_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_4_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c22_9_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_9_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_9_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_9_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_9_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_9_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_10_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_10_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_10_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_10_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_10_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_10_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_11_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_11_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_11_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_11_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_11_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_11_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_12_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_12_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_12_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_12_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_12_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_12_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c32_5_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_5_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_5_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_5_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_5_io_in_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_5_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c32_5_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
  wire  c22_13_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_13_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_13_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_13_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_13_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_13_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_14_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_14_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_14_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_14_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_14_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_14_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_15_clock; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_15_reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_15_io_in_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_15_io_in_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_15_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  c22_15_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
  wire  b_sext_signBit = io_b[7]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 11:20]
  wire [8:0] b_sext = {b_sext_signBit,io_b}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 12:44]
  wire [9:0] _bx2_T = {b_sext, 1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 76:21]
  wire [8:0] neg_b = ~b_sext; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 77:15]
  wire [9:0] _neg_bx2_T = {neg_b, 1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 78:20]
  wire [2:0] x = {io_a[1:0],1'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:28]
  wire [8:0] _pp_temp_T_1 = 3'h1 == x ? b_sext : 9'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_3 = 3'h2 == x ? b_sext : _pp_temp_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] bx2 = _bx2_T[8:0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 74:41 76:11]
  wire [8:0] _pp_temp_T_5 = 3'h3 == x ? bx2 : _pp_temp_T_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_6 = 3'h4 == x; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] neg_bx2 = _neg_bx2_T[8:0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 74:41 78:11]
  wire [8:0] _pp_temp_T_7 = 3'h4 == x ? neg_bx2 : _pp_temp_T_5; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_8 = 3'h5 == x; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_9 = 3'h5 == x ? neg_b : _pp_temp_T_7; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_10 = 3'h6 == x; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] pp_temp = 3'h6 == x ? neg_b : _pp_temp_T_9; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  s = pp_temp[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
  wire  _T = ~s; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 106:14]
  wire [11:0] pp = {_T,s,s,pp_temp}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 106:13]
  wire [2:0] x_1 = io_a[3:1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:101]
  wire [8:0] _pp_temp_T_12 = 3'h1 == x_1 ? b_sext : 9'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_14 = 3'h2 == x_1 ? b_sext : _pp_temp_T_12; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_16 = 3'h3 == x_1 ? bx2 : _pp_temp_T_14; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_17 = 3'h4 == x_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_18 = 3'h4 == x_1 ? neg_bx2 : _pp_temp_T_16; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_19 = 3'h5 == x_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_20 = 3'h5 == x_1 ? neg_b : _pp_temp_T_18; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_21 = 3'h6 == x_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] pp_temp_1 = 3'h6 == x_1 ? neg_b : _pp_temp_T_20; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  s_1 = pp_temp_1[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
  wire [1:0] _t_T_6 = _pp_temp_T_6 ? 2'h2 : 2'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire [1:0] _t_T_8 = _pp_temp_T_8 ? 2'h1 : _t_T_6; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire [1:0] t_1 = _pp_temp_T_10 ? 2'h1 : _t_T_8; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire  _T_13 = ~s_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:24]
  wire [12:0] pp_1 = {1'h1,_T_13,pp_temp_1,t_1}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
  wire [2:0] x_2 = io_a[5:3]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:101]
  wire [8:0] _pp_temp_T_23 = 3'h1 == x_2 ? b_sext : 9'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_25 = 3'h2 == x_2 ? b_sext : _pp_temp_T_23; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_27 = 3'h3 == x_2 ? bx2 : _pp_temp_T_25; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_28 = 3'h4 == x_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_29 = 3'h4 == x_2 ? neg_bx2 : _pp_temp_T_27; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_30 = 3'h5 == x_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_31 = 3'h5 == x_2 ? neg_b : _pp_temp_T_29; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_32 = 3'h6 == x_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] pp_temp_2 = 3'h6 == x_2 ? neg_b : _pp_temp_T_31; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  s_2 = pp_temp_2[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
  wire [1:0] _t_T_11 = _pp_temp_T_17 ? 2'h2 : 2'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire [1:0] _t_T_13 = _pp_temp_T_19 ? 2'h1 : _t_T_11; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire [1:0] t_2 = _pp_temp_T_21 ? 2'h1 : _t_T_13; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire  _T_27 = ~s_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:24]
  wire [12:0] pp_2 = {1'h1,_T_27,pp_temp_2,t_2}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
  wire [2:0] x_3 = io_a[7:5]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:101]
  wire [8:0] _pp_temp_T_34 = 3'h1 == x_3 ? b_sext : 9'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_36 = 3'h2 == x_3 ? b_sext : _pp_temp_T_34; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_38 = 3'h3 == x_3 ? bx2 : _pp_temp_T_36; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_39 = 3'h4 == x_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_40 = 3'h4 == x_3 ? neg_bx2 : _pp_temp_T_38; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_41 = 3'h5 == x_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] _pp_temp_T_42 = 3'h5 == x_3 ? neg_b : _pp_temp_T_40; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  _pp_temp_T_43 = 3'h6 == x_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire [8:0] pp_temp_3 = 3'h6 == x_3 ? neg_b : _pp_temp_T_42; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
  wire  s_3 = pp_temp_3[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
  wire [1:0] _t_T_16 = _pp_temp_T_28 ? 2'h2 : 2'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire [1:0] _t_T_18 = _pp_temp_T_30 ? 2'h1 : _t_T_16; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire [1:0] t_3 = _pp_temp_T_32 ? 2'h1 : _t_T_18; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
  wire  _T_41 = ~s_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 108:14]
  wire [11:0] pp_3 = {_T_41,pp_temp_3,t_3}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 108:13]
  wire [1:0] _finalCorrection_T_1 = _pp_temp_T_39 ? 2'h2 : 2'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
  wire [1:0] _finalCorrection_T_3 = _pp_temp_T_41 ? 2'h1 : _finalCorrection_T_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
  wire [1:0] finalCorrection = _pp_temp_T_43 ? 2'h1 : _finalCorrection_T_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
  reg  r; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_5; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_6; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_7; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_8; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_9; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_10; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_11; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_12; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_13; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_14; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_15; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_16; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_17; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_18; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_19; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_20; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_21; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_22; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_23; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_24; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_25; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_26; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_27; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_28; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_29; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_30; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_31; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_32; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_33; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_34; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_35; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_36; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_37; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_38; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_39; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_40; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_41; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_42; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_43; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_44; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_45; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_46; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_47; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_48; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_49; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_50; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  reg  r_51; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
  wire  s_0 = c22_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  s_0_15 = c22_4_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_15 = c22_4_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_16 = c22_5_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_16 = c22_5_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_17 = c22_6_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_17 = c22_6_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_18 = c22_7_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_18 = c22_7_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_19 = c22_8_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_19 = c22_8_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_20 = c32_3_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
  wire  c2_0_20 = c32_3_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
  wire  s_0_21 = c32_4_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
  wire  c2_0_21 = c32_4_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
  wire  s_0_22 = c22_9_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_22 = c22_9_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_23 = c22_10_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_23 = c22_10_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_24 = c22_11_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_24 = c22_11_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_25 = c22_12_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_25 = c22_12_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_26 = c32_5_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
  wire  c2_0_26 = c32_5_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
  wire  s_0_27 = c22_13_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_27 = c22_13_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_28 = c22_14_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire  c2_0_28 = c22_14_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  wire  s_0_29 = c22_15_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  wire [7:0] sum_lo = {s_0_21,s_0_20,s_0_19,s_0_18,s_0_17,s_0_16,s_0_15,s_0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
  wire [15:0] sum = {s_0_29,s_0_28,s_0_27,s_0_26,s_0_25,s_0_24,s_0_23,s_0_22,sum_lo}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
  wire [6:0] carry_lo = {c2_0_21,c2_0_20,c2_0_19,c2_0_18,c2_0_17,c2_0_16,c2_0_15}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
  wire [15:0] carry_1 = {c2_0_28,c2_0_27,c2_0_26,c2_0_25,c2_0_24,c2_0_23,c2_0_22,carry_lo,2'h0}; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 177:16]
  wire [15:0] _expectedFirst_T_3 = $signed(io_a) * $signed(io_b); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:61]
  reg [15:0] expectedFirst; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:32]
  reg  validFirst; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 210:27]
  wire  _GEN_53 = io_regEnables_0 | validFirst; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 211:26 210:27 211:39]
  wire  _T_58 = ~reset; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
  reg [15:0] previousResult; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 222:31]
  reg  wasHoldingKnownResult; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:38]
  C22 c22 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_clock),
    .reset(c22_reset),
    .io_in_0(c22_io_in_0),
    .io_in_1(c22_io_in_1),
    .io_out_0(c22_io_out_0),
    .io_out_1(c22_io_out_1)
  );
  C22 c22_1 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_1_clock),
    .reset(c22_1_reset),
    .io_in_0(c22_1_io_in_0),
    .io_in_1(c22_1_io_in_1),
    .io_out_0(c22_1_io_out_0),
    .io_out_1(c22_1_io_out_1)
  );
  C32 c32 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    .clock(c32_clock),
    .reset(c32_reset),
    .io_in_0(c32_io_in_0),
    .io_in_1(c32_io_in_1),
    .io_in_2(c32_io_in_2),
    .io_out_0(c32_io_out_0),
    .io_out_1(c32_io_out_1)
  );
  C32 c32_1 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    .clock(c32_1_clock),
    .reset(c32_1_reset),
    .io_in_0(c32_1_io_in_0),
    .io_in_1(c32_1_io_in_1),
    .io_in_2(c32_1_io_in_2),
    .io_out_0(c32_1_io_out_0),
    .io_out_1(c32_1_io_out_1)
  );
  C53 c53 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_clock),
    .reset(c53_reset),
    .io_in_0(c53_io_in_0),
    .io_in_1(c53_io_in_1),
    .io_in_2(c53_io_in_2),
    .io_in_3(c53_io_in_3),
    .io_in_4(c53_io_in_4),
    .io_out_0(c53_io_out_0),
    .io_out_1(c53_io_out_1),
    .io_out_2(c53_io_out_2)
  );
  C53 c53_1 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_1_clock),
    .reset(c53_1_reset),
    .io_in_0(c53_1_io_in_0),
    .io_in_1(c53_1_io_in_1),
    .io_in_2(c53_1_io_in_2),
    .io_in_3(c53_1_io_in_3),
    .io_in_4(c53_1_io_in_4),
    .io_out_0(c53_1_io_out_0),
    .io_out_1(c53_1_io_out_1),
    .io_out_2(c53_1_io_out_2)
  );
  C53 c53_2 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_2_clock),
    .reset(c53_2_reset),
    .io_in_0(c53_2_io_in_0),
    .io_in_1(c53_2_io_in_1),
    .io_in_2(c53_2_io_in_2),
    .io_in_3(c53_2_io_in_3),
    .io_in_4(c53_2_io_in_4),
    .io_out_0(c53_2_io_out_0),
    .io_out_1(c53_2_io_out_1),
    .io_out_2(c53_2_io_out_2)
  );
  C53 c53_3 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_3_clock),
    .reset(c53_3_reset),
    .io_in_0(c53_3_io_in_0),
    .io_in_1(c53_3_io_in_1),
    .io_in_2(c53_3_io_in_2),
    .io_in_3(c53_3_io_in_3),
    .io_in_4(c53_3_io_in_4),
    .io_out_0(c53_3_io_out_0),
    .io_out_1(c53_3_io_out_1),
    .io_out_2(c53_3_io_out_2)
  );
  C53 c53_4 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_4_clock),
    .reset(c53_4_reset),
    .io_in_0(c53_4_io_in_0),
    .io_in_1(c53_4_io_in_1),
    .io_in_2(c53_4_io_in_2),
    .io_in_3(c53_4_io_in_3),
    .io_in_4(c53_4_io_in_4),
    .io_out_0(c53_4_io_out_0),
    .io_out_1(c53_4_io_out_1),
    .io_out_2(c53_4_io_out_2)
  );
  C53 c53_5 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_5_clock),
    .reset(c53_5_reset),
    .io_in_0(c53_5_io_in_0),
    .io_in_1(c53_5_io_in_1),
    .io_in_2(c53_5_io_in_2),
    .io_in_3(c53_5_io_in_3),
    .io_in_4(c53_5_io_in_4),
    .io_out_0(c53_5_io_out_0),
    .io_out_1(c53_5_io_out_1),
    .io_out_2(c53_5_io_out_2)
  );
  C53 c53_6 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_6_clock),
    .reset(c53_6_reset),
    .io_in_0(c53_6_io_in_0),
    .io_in_1(c53_6_io_in_1),
    .io_in_2(c53_6_io_in_2),
    .io_in_3(c53_6_io_in_3),
    .io_in_4(c53_6_io_in_4),
    .io_out_0(c53_6_io_out_0),
    .io_out_1(c53_6_io_out_1),
    .io_out_2(c53_6_io_out_2)
  );
  C53 c53_7 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    .clock(c53_7_clock),
    .reset(c53_7_reset),
    .io_in_0(c53_7_io_in_0),
    .io_in_1(c53_7_io_in_1),
    .io_in_2(c53_7_io_in_2),
    .io_in_3(c53_7_io_in_3),
    .io_in_4(c53_7_io_in_4),
    .io_out_0(c53_7_io_out_0),
    .io_out_1(c53_7_io_out_1),
    .io_out_2(c53_7_io_out_2)
  );
  C32 c32_2 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    .clock(c32_2_clock),
    .reset(c32_2_reset),
    .io_in_0(c32_2_io_in_0),
    .io_in_1(c32_2_io_in_1),
    .io_in_2(c32_2_io_in_2),
    .io_out_0(c32_2_io_out_0),
    .io_out_1(c32_2_io_out_1)
  );
  C22 c22_2 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_2_clock),
    .reset(c22_2_reset),
    .io_in_0(c22_2_io_in_0),
    .io_in_1(c22_2_io_in_1),
    .io_out_0(c22_2_io_out_0),
    .io_out_1(c22_2_io_out_1)
  );
  C22 c22_3 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_3_clock),
    .reset(c22_3_reset),
    .io_in_0(c22_3_io_in_0),
    .io_in_1(c22_3_io_in_1),
    .io_out_0(c22_3_io_out_0),
    .io_out_1(c22_3_io_out_1)
  );
  C22 c22_4 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_4_clock),
    .reset(c22_4_reset),
    .io_in_0(c22_4_io_in_0),
    .io_in_1(c22_4_io_in_1),
    .io_out_0(c22_4_io_out_0),
    .io_out_1(c22_4_io_out_1)
  );
  C22 c22_5 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_5_clock),
    .reset(c22_5_reset),
    .io_in_0(c22_5_io_in_0),
    .io_in_1(c22_5_io_in_1),
    .io_out_0(c22_5_io_out_0),
    .io_out_1(c22_5_io_out_1)
  );
  C22 c22_6 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_6_clock),
    .reset(c22_6_reset),
    .io_in_0(c22_6_io_in_0),
    .io_in_1(c22_6_io_in_1),
    .io_out_0(c22_6_io_out_0),
    .io_out_1(c22_6_io_out_1)
  );
  C22 c22_7 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_7_clock),
    .reset(c22_7_reset),
    .io_in_0(c22_7_io_in_0),
    .io_in_1(c22_7_io_in_1),
    .io_out_0(c22_7_io_out_0),
    .io_out_1(c22_7_io_out_1)
  );
  C22 c22_8 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_8_clock),
    .reset(c22_8_reset),
    .io_in_0(c22_8_io_in_0),
    .io_in_1(c22_8_io_in_1),
    .io_out_0(c22_8_io_out_0),
    .io_out_1(c22_8_io_out_1)
  );
  C32 c32_3 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    .clock(c32_3_clock),
    .reset(c32_3_reset),
    .io_in_0(c32_3_io_in_0),
    .io_in_1(c32_3_io_in_1),
    .io_in_2(c32_3_io_in_2),
    .io_out_0(c32_3_io_out_0),
    .io_out_1(c32_3_io_out_1)
  );
  C32 c32_4 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    .clock(c32_4_clock),
    .reset(c32_4_reset),
    .io_in_0(c32_4_io_in_0),
    .io_in_1(c32_4_io_in_1),
    .io_in_2(c32_4_io_in_2),
    .io_out_0(c32_4_io_out_0),
    .io_out_1(c32_4_io_out_1)
  );
  C22 c22_9 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_9_clock),
    .reset(c22_9_reset),
    .io_in_0(c22_9_io_in_0),
    .io_in_1(c22_9_io_in_1),
    .io_out_0(c22_9_io_out_0),
    .io_out_1(c22_9_io_out_1)
  );
  C22 c22_10 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_10_clock),
    .reset(c22_10_reset),
    .io_in_0(c22_10_io_in_0),
    .io_in_1(c22_10_io_in_1),
    .io_out_0(c22_10_io_out_0),
    .io_out_1(c22_10_io_out_1)
  );
  C22 c22_11 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_11_clock),
    .reset(c22_11_reset),
    .io_in_0(c22_11_io_in_0),
    .io_in_1(c22_11_io_in_1),
    .io_out_0(c22_11_io_out_0),
    .io_out_1(c22_11_io_out_1)
  );
  C22 c22_12 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_12_clock),
    .reset(c22_12_reset),
    .io_in_0(c22_12_io_in_0),
    .io_in_1(c22_12_io_in_1),
    .io_out_0(c22_12_io_out_0),
    .io_out_1(c22_12_io_out_1)
  );
  C32 c32_5 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    .clock(c32_5_clock),
    .reset(c32_5_reset),
    .io_in_0(c32_5_io_in_0),
    .io_in_1(c32_5_io_in_1),
    .io_in_2(c32_5_io_in_2),
    .io_out_0(c32_5_io_out_0),
    .io_out_1(c32_5_io_out_1)
  );
  C22 c22_13 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_13_clock),
    .reset(c22_13_reset),
    .io_in_0(c22_13_io_in_0),
    .io_in_1(c22_13_io_in_1),
    .io_out_0(c22_13_io_out_0),
    .io_out_1(c22_13_io_out_1)
  );
  C22 c22_14 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_14_clock),
    .reset(c22_14_reset),
    .io_in_0(c22_14_io_in_0),
    .io_in_1(c22_14_io_in_1),
    .io_out_0(c22_14_io_out_0),
    .io_out_1(c22_14_io_out_1)
  );
  C22 c22_15 ( // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    .clock(c22_15_clock),
    .reset(c22_15_reset),
    .io_in_0(c22_15_io_in_0),
    .io_in_1(c22_15_io_in_1),
    .io_out_0(c22_15_io_out_0),
    .io_out_1(c22_15_io_out_1)
  );
  assign io_result = sum + carry_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 203:20]
  assign c22_clock = clock;
  assign c22_reset = reset;
  assign c22_io_in_0 = r; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_io_in_1 = r_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_1_clock = clock;
  assign c22_1_reset = reset;
  assign c22_1_io_in_0 = r_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_1_io_in_1 = r_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c32_clock = clock;
  assign c32_reset = reset;
  assign c32_io_in_0 = r_4; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_io_in_1 = r_5; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_io_in_2 = r_6; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_1_clock = clock;
  assign c32_1_reset = reset;
  assign c32_1_io_in_0 = r_7; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_1_io_in_1 = r_8; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_1_io_in_2 = r_9; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c53_clock = clock;
  assign c53_reset = reset;
  assign c53_io_in_0 = r_10; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_io_in_1 = r_11; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_io_in_2 = r_12; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_io_in_3 = r_13; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_io_in_4 = 1'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
  assign c53_1_clock = clock;
  assign c53_1_reset = reset;
  assign c53_1_io_in_0 = r_14; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_1_io_in_1 = r_15; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_1_io_in_2 = r_16; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_1_io_in_3 = r_17; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_1_io_in_4 = c53_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c53_2_clock = clock;
  assign c53_2_reset = reset;
  assign c53_2_io_in_0 = r_18; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_2_io_in_1 = r_19; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_2_io_in_2 = r_20; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_2_io_in_3 = r_21; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_2_io_in_4 = c53_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c53_3_clock = clock;
  assign c53_3_reset = reset;
  assign c53_3_io_in_0 = r_23; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_3_io_in_1 = r_24; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_3_io_in_2 = r_25; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_3_io_in_3 = r_26; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_3_io_in_4 = c53_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c53_4_clock = clock;
  assign c53_4_reset = reset;
  assign c53_4_io_in_0 = r_28; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_4_io_in_1 = r_29; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_4_io_in_2 = r_30; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_4_io_in_3 = r_31; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_4_io_in_4 = c53_3_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c53_5_clock = clock;
  assign c53_5_reset = reset;
  assign c53_5_io_in_0 = r_32; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_5_io_in_1 = r_33; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_5_io_in_2 = r_34; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_5_io_in_3 = r_35; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_5_io_in_4 = c53_4_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c53_6_clock = clock;
  assign c53_6_reset = reset;
  assign c53_6_io_in_0 = r_36; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_6_io_in_1 = r_37; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_6_io_in_2 = r_38; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_6_io_in_3 = r_39; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_6_io_in_4 = c53_5_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c53_7_clock = clock;
  assign c53_7_reset = reset;
  assign c53_7_io_in_0 = r_40; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_7_io_in_1 = r_41; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_7_io_in_2 = r_42; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_7_io_in_3 = r_43; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
  assign c53_7_io_in_4 = c53_6_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c32_2_clock = clock;
  assign c32_2_reset = reset;
  assign c32_2_io_in_0 = r_44; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_2_io_in_1 = r_45; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_2_io_in_2 = r_46; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c22_2_clock = clock;
  assign c22_2_reset = reset;
  assign c22_2_io_in_0 = r_47; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_2_io_in_1 = r_48; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_3_clock = clock;
  assign c22_3_reset = reset;
  assign c22_3_io_in_0 = r_49; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_3_io_in_1 = r_50; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_4_clock = clock;
  assign c22_4_reset = reset;
  assign c22_4_io_in_0 = c22_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  assign c22_4_io_in_1 = c22_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  assign c22_5_clock = clock;
  assign c22_5_reset = reset;
  assign c22_5_io_in_0 = c32_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
  assign c22_5_io_in_1 = c22_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  assign c22_6_clock = clock;
  assign c22_6_reset = reset;
  assign c22_6_io_in_0 = c32_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
  assign c22_6_io_in_1 = c32_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
  assign c22_7_clock = clock;
  assign c22_7_reset = reset;
  assign c22_7_io_in_0 = c53_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c22_7_io_in_1 = c32_1_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
  assign c22_8_clock = clock;
  assign c22_8_reset = reset;
  assign c22_8_io_in_0 = c53_1_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c22_8_io_in_1 = c53_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c32_3_clock = clock;
  assign c32_3_reset = reset;
  assign c32_3_io_in_0 = c53_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c32_3_io_in_1 = r_22; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_3_io_in_2 = c53_1_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c32_4_clock = clock;
  assign c32_4_reset = reset;
  assign c32_4_io_in_0 = c53_3_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c32_4_io_in_1 = r_27; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
  assign c32_4_io_in_2 = c53_2_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c22_9_clock = clock;
  assign c22_9_reset = reset;
  assign c22_9_io_in_0 = c53_4_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c22_9_io_in_1 = c53_3_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c22_10_clock = clock;
  assign c22_10_reset = reset;
  assign c22_10_io_in_0 = c53_5_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c22_10_io_in_1 = c53_4_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c22_11_clock = clock;
  assign c22_11_reset = reset;
  assign c22_11_io_in_0 = c53_6_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c22_11_io_in_1 = c53_5_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c22_12_clock = clock;
  assign c22_12_reset = reset;
  assign c22_12_io_in_0 = c53_7_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
  assign c22_12_io_in_1 = c53_6_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c32_5_clock = clock;
  assign c32_5_reset = reset;
  assign c32_5_io_in_0 = c32_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
  assign c32_5_io_in_1 = c53_7_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
  assign c32_5_io_in_2 = c53_7_io_out_2; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
  assign c22_13_clock = clock;
  assign c22_13_reset = reset;
  assign c22_13_io_in_0 = c22_2_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  assign c22_13_io_in_1 = c32_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
  assign c22_14_clock = clock;
  assign c22_14_reset = reset;
  assign c22_14_io_in_0 = c22_3_io_out_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
  assign c22_14_io_in_1 = c22_2_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  assign c22_15_clock = clock;
  assign c22_15_reset = reset;
  assign c22_15_io_in_0 = r_51; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
  assign c22_15_io_in_1 = c22_3_io_out_1; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
  always @(posedge clock) begin
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r <= pp[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_1 <= pp_1[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_2 <= pp[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_3 <= pp_1[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_4 <= pp[2]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_5 <= pp_1[2]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_6 <= pp_2[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_7 <= pp[3]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_8 <= pp_1[3]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_9 <= pp_2[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_10 <= pp[4]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_11 <= pp_1[4]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_12 <= pp_2[2]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_13 <= pp_3[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_14 <= pp[5]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_15 <= pp_1[5]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_16 <= pp_2[3]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_17 <= pp_3[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_18 <= pp[6]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_19 <= pp_1[6]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_20 <= pp_2[4]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_21 <= pp_3[2]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_22 <= finalCorrection[0]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_23 <= pp[7]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_24 <= pp_1[7]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_25 <= pp_2[5]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_26 <= pp_3[3]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_27 <= finalCorrection[1]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_28 <= pp[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_29 <= pp_1[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_30 <= pp_2[6]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_31 <= pp_3[4]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_32 <= pp[9]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_33 <= pp_1[9]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_34 <= pp_2[7]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_35 <= pp_3[5]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_36 <= pp[10]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_37 <= pp_1[10]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_38 <= pp_2[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_39 <= pp_3[6]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_40 <= pp[11]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_41 <= pp_1[11]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_42 <= pp_2[9]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_43 <= pp_3[7]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_44 <= pp_1[12]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_45 <= pp_2[10]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_46 <= pp_3[8]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_47 <= pp_2[11]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_48 <= pp_3[9]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_49 <= pp_2[12]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_50 <= pp_3[10]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
      r_51 <= pp_3[11]; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    end
    if (io_regEnables_0) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:32]
      expectedFirst <= _expectedFirst_T_3; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:32]
    end
    if (reset) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 210:{27,27}]
      validFirst <= 1'h0;
    end else begin
      validFirst <= _GEN_53;
    end
    previousResult <= io_result; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 222:31]
    if (reset) begin // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:38]
      wasHoldingKnownResult <= 1'h0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:38]
    end else begin
      wasHoldingKnownResult <= validFirst & ~io_regEnables_0; // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:38]
    end
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (validFirst & ~reset & ~(io_result == expectedFirst)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Multiplier.scala:220 when(resultKnown) { assert(io.result === expectedResult) }\n"
            ); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (wasHoldingKnownResult & _T_58 & ~(io_result == previousResult)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at Multiplier.scala:224 when(wasHoldingKnownResult) { assert(io.result === previousResult) }\n"
            ); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
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
  r = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  r_1 = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  r_2 = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  r_3 = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  r_4 = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  r_5 = _RAND_5[0:0];
  _RAND_6 = {1{`RANDOM}};
  r_6 = _RAND_6[0:0];
  _RAND_7 = {1{`RANDOM}};
  r_7 = _RAND_7[0:0];
  _RAND_8 = {1{`RANDOM}};
  r_8 = _RAND_8[0:0];
  _RAND_9 = {1{`RANDOM}};
  r_9 = _RAND_9[0:0];
  _RAND_10 = {1{`RANDOM}};
  r_10 = _RAND_10[0:0];
  _RAND_11 = {1{`RANDOM}};
  r_11 = _RAND_11[0:0];
  _RAND_12 = {1{`RANDOM}};
  r_12 = _RAND_12[0:0];
  _RAND_13 = {1{`RANDOM}};
  r_13 = _RAND_13[0:0];
  _RAND_14 = {1{`RANDOM}};
  r_14 = _RAND_14[0:0];
  _RAND_15 = {1{`RANDOM}};
  r_15 = _RAND_15[0:0];
  _RAND_16 = {1{`RANDOM}};
  r_16 = _RAND_16[0:0];
  _RAND_17 = {1{`RANDOM}};
  r_17 = _RAND_17[0:0];
  _RAND_18 = {1{`RANDOM}};
  r_18 = _RAND_18[0:0];
  _RAND_19 = {1{`RANDOM}};
  r_19 = _RAND_19[0:0];
  _RAND_20 = {1{`RANDOM}};
  r_20 = _RAND_20[0:0];
  _RAND_21 = {1{`RANDOM}};
  r_21 = _RAND_21[0:0];
  _RAND_22 = {1{`RANDOM}};
  r_22 = _RAND_22[0:0];
  _RAND_23 = {1{`RANDOM}};
  r_23 = _RAND_23[0:0];
  _RAND_24 = {1{`RANDOM}};
  r_24 = _RAND_24[0:0];
  _RAND_25 = {1{`RANDOM}};
  r_25 = _RAND_25[0:0];
  _RAND_26 = {1{`RANDOM}};
  r_26 = _RAND_26[0:0];
  _RAND_27 = {1{`RANDOM}};
  r_27 = _RAND_27[0:0];
  _RAND_28 = {1{`RANDOM}};
  r_28 = _RAND_28[0:0];
  _RAND_29 = {1{`RANDOM}};
  r_29 = _RAND_29[0:0];
  _RAND_30 = {1{`RANDOM}};
  r_30 = _RAND_30[0:0];
  _RAND_31 = {1{`RANDOM}};
  r_31 = _RAND_31[0:0];
  _RAND_32 = {1{`RANDOM}};
  r_32 = _RAND_32[0:0];
  _RAND_33 = {1{`RANDOM}};
  r_33 = _RAND_33[0:0];
  _RAND_34 = {1{`RANDOM}};
  r_34 = _RAND_34[0:0];
  _RAND_35 = {1{`RANDOM}};
  r_35 = _RAND_35[0:0];
  _RAND_36 = {1{`RANDOM}};
  r_36 = _RAND_36[0:0];
  _RAND_37 = {1{`RANDOM}};
  r_37 = _RAND_37[0:0];
  _RAND_38 = {1{`RANDOM}};
  r_38 = _RAND_38[0:0];
  _RAND_39 = {1{`RANDOM}};
  r_39 = _RAND_39[0:0];
  _RAND_40 = {1{`RANDOM}};
  r_40 = _RAND_40[0:0];
  _RAND_41 = {1{`RANDOM}};
  r_41 = _RAND_41[0:0];
  _RAND_42 = {1{`RANDOM}};
  r_42 = _RAND_42[0:0];
  _RAND_43 = {1{`RANDOM}};
  r_43 = _RAND_43[0:0];
  _RAND_44 = {1{`RANDOM}};
  r_44 = _RAND_44[0:0];
  _RAND_45 = {1{`RANDOM}};
  r_45 = _RAND_45[0:0];
  _RAND_46 = {1{`RANDOM}};
  r_46 = _RAND_46[0:0];
  _RAND_47 = {1{`RANDOM}};
  r_47 = _RAND_47[0:0];
  _RAND_48 = {1{`RANDOM}};
  r_48 = _RAND_48[0:0];
  _RAND_49 = {1{`RANDOM}};
  r_49 = _RAND_49[0:0];
  _RAND_50 = {1{`RANDOM}};
  r_50 = _RAND_50[0:0];
  _RAND_51 = {1{`RANDOM}};
  r_51 = _RAND_51[0:0];
  _RAND_52 = {1{`RANDOM}};
  expectedFirst = _RAND_52[15:0];
  _RAND_53 = {1{`RANDOM}};
  validFirst = _RAND_53[0:0];
  _RAND_54 = {1{`RANDOM}};
  previousResult = _RAND_54[15:0];
  _RAND_55 = {1{`RANDOM}};
  wasHoldingKnownResult = _RAND_55[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
  always @(posedge clock) begin
    //
    if (validFirst & ~reset) begin
      assert(io_result == expectedFirst); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
    end
    //
    if (wasHoldingKnownResult & _T_58) begin
      assert(io_result == previousResult); // @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
    end
  end
endmodule
