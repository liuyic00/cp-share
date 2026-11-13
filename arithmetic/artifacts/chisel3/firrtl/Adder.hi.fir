FIRRTL version 1.2.0
circuit Adder :
  module Adder :
    input clock : Clock
    input reset : UInt<1>
    output io : { flip valid : UInt<1>, flip in1 : UInt<8>, flip in2 : UInt<8>, out : UInt<8>} @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 6:14]

    when io.valid : @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 13:18]
      node _io_out_T = add(io.in1, io.in2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 14:22]
      node _io_out_T_1 = tail(_io_out_T, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 14:22]
      io.out <= _io_out_T_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 14:12]
    else :
      io.out <= UInt<1>("h0") @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 16:12]
    node _T = add(io.in1, io.in2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:36]
    node _T_1 = tail(_T, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:36]
    node _T_2 = eq(io.out, _T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:25]
    node _T_3 = and(io.valid, _T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:15]
    node _T_4 = eq(io.valid, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:50]
    node _T_5 = eq(io.out, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:70]
    node _T_6 = and(_T_4, _T_5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:60]
    node _T_7 = or(_T_3, _T_6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 20:46]
    node _T_8 = bits(reset, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
    node _T_9 = eq(_T_8, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
    when _T_9 : @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
      node _T_10 = eq(_T_7, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
      when _T_10 : @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
        printf(clock, UInt<1>("h1"), "Assertion failed\n    at Adder.scala:19 assert( // Modified\n") : printf @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]
      assert(clock, _T_7, UInt<1>("h1"), "") : assert @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/basic/alu/Adder.scala 19:9]

