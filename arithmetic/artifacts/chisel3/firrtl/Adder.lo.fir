FIRRTL version 1.2.0
circuit Adder :
  module Adder :
    input clock : Clock
    input reset : UInt<1>
    input io_valid : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 6:14]
    input io_in1 : UInt<8> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 6:14]
    input io_in2 : UInt<8> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 6:14]
    output io_out : UInt<8> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 6:14]

    node _io_out_T = add(io_in1, io_in2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 14:22]
    node _io_out_T_1 = tail(_io_out_T, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 14:22]
    node _GEN_0 = mux(io_valid, _io_out_T_1, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 13:18 14:12 16:12]
    node _T = add(io_in1, io_in2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:36]
    node _T_1 = tail(_T, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:36]
    node _T_2 = eq(io_out, _T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:25]
    node _T_3 = and(io_valid, _T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:15]
    node _T_4 = eq(io_valid, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:50]
    node _T_5 = eq(io_out, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:70]
    node _T_6 = and(_T_4, _T_5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:60]
    node _T_7 = or(_T_3, _T_6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:46]
    node _T_8 = bits(reset, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
    node _T_9 = eq(_T_8, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
    node _T_10 = eq(_T_7, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
    io_out <= _GEN_0
    printf(clock, and(and(and(UInt<1>("h1"), _T_9), _T_10), UInt<1>("h1")), "Assertion failed\n    at Adder.scala:19 assert( // Modified\n") : printf @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
    assert(clock, _T_7, and(and(UInt<1>("h1"), _T_9), UInt<1>("h1")), "") : assert @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
