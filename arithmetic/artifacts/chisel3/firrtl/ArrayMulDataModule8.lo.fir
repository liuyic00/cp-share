FIRRTL version 1.2.0
circuit ArrayMulDataModule8 :
  module C22 :
    input clock : Clock
    input reset : UInt<1>
    input io_in_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]

    node _inputSum_T = pad(io_in_0, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_1 = pad(io_in_1, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_2 = add(_inputSum_T, _inputSum_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node inputSum = tail(_inputSum_T_2, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _outputSum_T = pad(io_out_0, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:28]
    node _outputSum_T_1 = pad(io_out_1, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
    node _outputSum_T_2 = shl(_outputSum_T_1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
    node _outputSum_T_3 = add(_outputSum_T, _outputSum_T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node outputSum = tail(_outputSum_T_3, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node _T = eq(inputSum, outputSum) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:19]
    node _T_1 = asUInt(reset) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _T_2 = eq(_T_1, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _T_3 = eq(_T, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node a = bits(io_in_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 34:27]
    node b = bits(io_in_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 34:40]
    node sum = xor(a, b) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 35:20]
    node cout = and(a, b) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 36:20]
    node _temp_0_T = cat(cout, sum) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 37:13]
    node temp_0 = _temp_0_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 32:18 37:7]
    node _io_out_0_T = bits(temp_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 39:76]
    node _io_out_1_T = bits(temp_0, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 39:76]
    io_out_0 <= _io_out_0_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 39:50]
    io_out_1 <= _io_out_1_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 39:50]
    printf(clock, and(and(and(UInt<1>("h1"), _T_2), _T_3), UInt<1>("h1")), "Assertion failed\n    at Multiplier.scala:28 assert(inputSum === outputSum)\n") : printf @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    assert(clock, _T, and(and(UInt<1>("h1"), _T_2), UInt<1>("h1")), "") : assert @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]

  module C32 :
    input clock : Clock
    input reset : UInt<1>
    input io_in_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_2 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]

    node _inputSum_T = pad(io_in_0, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_1 = pad(io_in_1, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_2 = pad(io_in_2, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_3 = add(_inputSum_T, _inputSum_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_4 = tail(_inputSum_T_3, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_5 = add(_inputSum_T_4, _inputSum_T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node inputSum = tail(_inputSum_T_5, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _outputSum_T = pad(io_out_0, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:28]
    node _outputSum_T_1 = pad(io_out_1, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
    node _outputSum_T_2 = shl(_outputSum_T_1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
    node _outputSum_T_3 = add(_outputSum_T, _outputSum_T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node outputSum = tail(_outputSum_T_3, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node _T = eq(inputSum, outputSum) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:19]
    node _T_1 = asUInt(reset) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _T_2 = eq(_T_1, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _T_3 = eq(_T, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node a = bits(io_in_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 45:32]
    node b = bits(io_in_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 45:45]
    node cin = bits(io_in_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 45:58]
    node a_xor_b = xor(a, b) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 46:25]
    node a_and_b = and(a, b) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 47:25]
    node sum = xor(a_xor_b, cin) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 48:31]
    node _cout_T = and(a_xor_b, cin) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 49:42]
    node cout = or(a_and_b, _cout_T) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 49:31]
    node _temp_0_T = cat(cout, sum) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 50:13]
    node temp_0 = _temp_0_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 43:18 50:7]
    node _io_out_0_T = bits(temp_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 52:76]
    node _io_out_1_T = bits(temp_0, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 52:76]
    io_out_0 <= _io_out_0_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 52:50]
    io_out_1 <= _io_out_1_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 52:50]
    printf(clock, and(and(and(UInt<1>("h1"), _T_2), _T_3), UInt<1>("h1")), "Assertion failed\n    at Multiplier.scala:28 assert(inputSum === outputSum)\n") : printf @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    assert(clock, _T, and(and(UInt<1>("h1"), _T_2), UInt<1>("h1")), "") : assert @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]

  module C53 :
    input clock : Clock
    input reset : UInt<1>
    input io_in_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_2 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_3 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    input io_in_4 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]
    output io_out_2 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 17:14]

    inst CSA3_2 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
    inst CSA3_2_1 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 56:33]
    node _inputSum_T = pad(io_in_0, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_1 = pad(io_in_1, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_2 = pad(io_in_2, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_3 = pad(io_in_3, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_4 = pad(io_in_4, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:33]
    node _inputSum_T_5 = add(_inputSum_T, _inputSum_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_6 = tail(_inputSum_T_5, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_7 = add(_inputSum_T_6, _inputSum_T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_8 = tail(_inputSum_T_7, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_9 = add(_inputSum_T_8, _inputSum_T_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_10 = tail(_inputSum_T_9, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _inputSum_T_11 = add(_inputSum_T_10, _inputSum_T_4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node inputSum = tail(_inputSum_T_11, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 24:53]
    node _outputSum_T = pad(io_out_0, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:28]
    node _outputSum_T_1 = pad(io_out_1, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
    node _outputSum_T_2 = shl(_outputSum_T_1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
    node _outputSum_T_3 = pad(io_out_2, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:51]
    node _outputSum_T_4 = shl(_outputSum_T_3, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 26:61]
    node _outputSum_T_5 = add(_outputSum_T, _outputSum_T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node _outputSum_T_6 = tail(_outputSum_T_5, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node _outputSum_T_7 = add(_outputSum_T_6, _outputSum_T_4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node outputSum = tail(_outputSum_T_7, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 27:14]
    node _T = eq(inputSum, outputSum) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:19]
    node _T_1 = asUInt(reset) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _T_2 = eq(_T_1, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _T_3 = eq(_T, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    node _WIRE__0 = CSA3_2.io_out_0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:{26,26}]
    node _WIRE__1 = io_in_3 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:{26,26}]
    node _WIRE__2 = io_in_4 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:{26,26}]
    node _WIRE_1_0 = CSA3_2_1.io_out_0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:{26,26}]
    node _WIRE_1_1 = CSA3_2.io_out_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:{26,26}]
    node _WIRE_1_2 = CSA3_2_1.io_out_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:{26,26}]
    io_out_0 <= _WIRE_1_0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:16]
    io_out_1 <= _WIRE_1_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:16]
    io_out_2 <= _WIRE_1_2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 59:16]
    CSA3_2.clock <= clock
    CSA3_2.reset <= reset
    CSA3_2.io_in_0 <= io_in_0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 57:16]
    CSA3_2.io_in_1 <= io_in_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 57:16]
    CSA3_2.io_in_2 <= io_in_2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 57:16]
    CSA3_2_1.clock <= clock
    CSA3_2_1.reset <= reset
    CSA3_2_1.io_in_0 <= _WIRE__0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:16]
    CSA3_2_1.io_in_1 <= _WIRE__1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:16]
    CSA3_2_1.io_in_2 <= _WIRE__2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 58:16]
    printf(clock, and(and(and(UInt<1>("h1"), _T_2), _T_3), UInt<1>("h1")), "Assertion failed\n    at Multiplier.scala:28 assert(inputSum === outputSum)\n") : printf @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]
    assert(clock, _T, and(and(UInt<1>("h1"), _T_2), UInt<1>("h1")), "") : assert @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 28:9]

  module ArrayMulDataModule8 :
    input clock : Clock
    input reset : UInt<1>
    input io_a : UInt<8> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
    input io_b : UInt<8> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
    input io_regEnables_0 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
    input io_regEnables_1 : UInt<1> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]
    output io_result : UInt<16> @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 67:14]

    inst c22 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_1 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c32 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    inst c32_1 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    inst c53 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_1 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_2 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_3 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_4 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_5 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_6 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c53_7 of C53 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 148:25]
    inst c32_2 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    inst c22_2 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_3 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_4 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_5 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_6 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_7 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_8 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c32_3 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    inst c32_4 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    inst c22_9 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_10 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_11 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_12 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c32_5 of C32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 143:25]
    inst c22_13 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_14 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    inst c22_15 of C22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 138:25]
    node b_sext_signBit = bits(io_b, 7, 7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 11:20]
    node _b_sext_T = cat(b_sext_signBit, io_b) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 12:44]
    node b_sext = _b_sext_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 74:41 75:11]
    node _bx2_T = shl(b_sext, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 76:21]
    node _neg_b_T = not(b_sext) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 77:15]
    node neg_b = _neg_b_T @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 74:41 77:11]
    node _neg_bx2_T = shl(neg_b, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 78:20]
    node _x_T = bits(io_a, 1, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:30]
    node x = cat(_x_T, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:28]
    node _pp_temp_T = eq(UInt<1>("h1"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_1 = mux(_pp_temp_T, b_sext, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_2 = eq(UInt<2>("h2"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_3 = mux(_pp_temp_T_2, b_sext, _pp_temp_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_4 = eq(UInt<2>("h3"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node bx2 = bits(_bx2_T, 8, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 74:41 76:11]
    node _pp_temp_T_5 = mux(_pp_temp_T_4, bx2, _pp_temp_T_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_6 = eq(UInt<3>("h4"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node neg_bx2 = bits(_neg_bx2_T, 8, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 74:41 78:11]
    node _pp_temp_T_7 = mux(_pp_temp_T_6, neg_bx2, _pp_temp_T_5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_8 = eq(UInt<3>("h5"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_9 = mux(_pp_temp_T_8, neg_b, _pp_temp_T_7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_10 = eq(UInt<3>("h6"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node pp_temp = mux(_pp_temp_T_10, neg_b, _pp_temp_T_9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node s = bits(pp_temp, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
    node last_x = UInt<3>("h0") @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 82:{24,24}]
    node _t_T = eq(UInt<3>("h4"), last_x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_1 = mux(_t_T, UInt<2>("h2"), UInt<2>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_2 = eq(UInt<3>("h5"), last_x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_3 = mux(_t_T_2, UInt<2>("h1"), _t_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_4 = eq(UInt<3>("h6"), last_x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node t = mux(_t_T_4, UInt<2>("h1"), _t_T_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _T = not(s) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 106:14]
    node lo = cat(s, pp_temp) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 106:13]
    node hi = cat(_T, s) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 106:13]
    node pp = cat(hi, lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 106:13]
    node _T_1 = bits(pp, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_2 = bits(pp, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_3 = bits(pp, 2, 2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_4 = bits(pp, 3, 3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_5 = bits(pp, 4, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_6 = bits(pp, 5, 5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_7 = bits(pp, 6, 6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_8 = bits(pp, 7, 7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_9 = bits(pp, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_10 = bits(pp, 9, 9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_11 = bits(pp, 10, 10) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_12 = bits(pp, 11, 11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node x_1 = bits(io_a, 3, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:101]
    node _pp_temp_T_11 = eq(UInt<1>("h1"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_12 = mux(_pp_temp_T_11, b_sext, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_13 = eq(UInt<2>("h2"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_14 = mux(_pp_temp_T_13, b_sext, _pp_temp_T_12) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_15 = eq(UInt<2>("h3"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_16 = mux(_pp_temp_T_15, bx2, _pp_temp_T_14) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_17 = eq(UInt<3>("h4"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_18 = mux(_pp_temp_T_17, neg_bx2, _pp_temp_T_16) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_19 = eq(UInt<3>("h5"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_20 = mux(_pp_temp_T_19, neg_b, _pp_temp_T_18) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_21 = eq(UInt<3>("h6"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node pp_temp_1 = mux(_pp_temp_T_21, neg_b, _pp_temp_T_20) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node s_1 = bits(pp_temp_1, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
    node _t_T_5 = eq(UInt<3>("h4"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_6 = mux(_t_T_5, UInt<2>("h2"), UInt<2>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_7 = eq(UInt<3>("h5"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_8 = mux(_t_T_7, UInt<2>("h1"), _t_T_6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_9 = eq(UInt<3>("h6"), x) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node t_1 = mux(_t_T_9, UInt<2>("h1"), _t_T_8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _T_13 = not(s_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:24]
    node lo_1 = cat(pp_temp_1, t_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
    node hi_1 = cat(UInt<1>("h1"), _T_13) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
    node pp_1 = cat(hi_1, lo_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
    node _T_14 = bits(pp_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_15 = bits(pp_1, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_16 = bits(pp_1, 2, 2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_17 = bits(pp_1, 3, 3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_18 = bits(pp_1, 4, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_19 = bits(pp_1, 5, 5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_20 = bits(pp_1, 6, 6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_21 = bits(pp_1, 7, 7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_22 = bits(pp_1, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_23 = bits(pp_1, 9, 9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_24 = bits(pp_1, 10, 10) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_25 = bits(pp_1, 11, 11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_26 = bits(pp_1, 12, 12) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node x_2 = bits(io_a, 5, 3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:101]
    node _pp_temp_T_22 = eq(UInt<1>("h1"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_23 = mux(_pp_temp_T_22, b_sext, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_24 = eq(UInt<2>("h2"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_25 = mux(_pp_temp_T_24, b_sext, _pp_temp_T_23) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_26 = eq(UInt<2>("h3"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_27 = mux(_pp_temp_T_26, bx2, _pp_temp_T_25) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_28 = eq(UInt<3>("h4"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_29 = mux(_pp_temp_T_28, neg_bx2, _pp_temp_T_27) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_30 = eq(UInt<3>("h5"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_31 = mux(_pp_temp_T_30, neg_b, _pp_temp_T_29) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_32 = eq(UInt<3>("h6"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node pp_temp_2 = mux(_pp_temp_T_32, neg_b, _pp_temp_T_31) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node s_2 = bits(pp_temp_2, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
    node _t_T_10 = eq(UInt<3>("h4"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_11 = mux(_t_T_10, UInt<2>("h2"), UInt<2>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_12 = eq(UInt<3>("h5"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_13 = mux(_t_T_12, UInt<2>("h1"), _t_T_11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_14 = eq(UInt<3>("h6"), x_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node t_2 = mux(_t_T_14, UInt<2>("h1"), _t_T_13) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _T_27 = not(s_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:24]
    node lo_2 = cat(pp_temp_2, t_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
    node hi_2 = cat(UInt<1>("h1"), _T_27) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
    node pp_2 = cat(hi_2, lo_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 110:13]
    node _T_28 = bits(pp_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_29 = bits(pp_2, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_30 = bits(pp_2, 2, 2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_31 = bits(pp_2, 3, 3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_32 = bits(pp_2, 4, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_33 = bits(pp_2, 5, 5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_34 = bits(pp_2, 6, 6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_35 = bits(pp_2, 7, 7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_36 = bits(pp_2, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_37 = bits(pp_2, 9, 9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_38 = bits(pp_2, 10, 10) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_39 = bits(pp_2, 11, 11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_40 = bits(pp_2, 12, 12) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node x_3 = bits(io_a, 7, 5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 84:101]
    node _pp_temp_T_33 = eq(UInt<1>("h1"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_34 = mux(_pp_temp_T_33, b_sext, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_35 = eq(UInt<2>("h2"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_36 = mux(_pp_temp_T_35, b_sext, _pp_temp_T_34) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_37 = eq(UInt<2>("h3"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_38 = mux(_pp_temp_T_37, bx2, _pp_temp_T_36) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_39 = eq(UInt<3>("h4"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_40 = mux(_pp_temp_T_39, neg_bx2, _pp_temp_T_38) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_41 = eq(UInt<3>("h5"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_42 = mux(_pp_temp_T_41, neg_b, _pp_temp_T_40) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node _pp_temp_T_43 = eq(UInt<3>("h6"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node pp_temp_3 = mux(_pp_temp_T_43, neg_b, _pp_temp_T_42) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 85:36]
    node s_3 = bits(pp_temp_3, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 95:20]
    node _t_T_15 = eq(UInt<3>("h4"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_16 = mux(_t_T_15, UInt<2>("h2"), UInt<2>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_17 = eq(UInt<3>("h5"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_18 = mux(_t_T_17, UInt<2>("h1"), _t_T_16) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _t_T_19 = eq(UInt<3>("h6"), x_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node t_3 = mux(_t_T_19, UInt<2>("h1"), _t_T_18) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 96:40]
    node _T_41 = not(s_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 108:14]
    node hi_3 = cat(_T_41, pp_temp_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 108:13]
    node pp_3 = cat(hi_3, t_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 108:13]
    node _T_42 = bits(pp_3, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_43 = bits(pp_3, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_44 = bits(pp_3, 2, 2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_45 = bits(pp_3, 3, 3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_46 = bits(pp_3, 4, 4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_47 = bits(pp_3, 5, 5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_48 = bits(pp_3, 6, 6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_49 = bits(pp_3, 7, 7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_50 = bits(pp_3, 8, 8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_51 = bits(pp_3, 9, 9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_52 = bits(pp_3, 10, 10) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _T_53 = bits(pp_3, 11, 11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 114:38]
    node _finalCorrection_T = eq(UInt<3>("h4"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
    node _finalCorrection_T_1 = mux(_finalCorrection_T, UInt<2>("h2"), UInt<2>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
    node _finalCorrection_T_2 = eq(UInt<3>("h5"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
    node _finalCorrection_T_3 = mux(_finalCorrection_T_2, UInt<2>("h1"), _finalCorrection_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
    node _finalCorrection_T_4 = eq(UInt<3>("h6"), x_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
    node finalCorrection = mux(_finalCorrection_T_4, UInt<2>("h1"), _finalCorrection_T_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 122:52]
    node _T_54 = bits(finalCorrection, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 127:79]
    node _T_55 = bits(finalCorrection, 1, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 127:79]
    reg r : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_0 = mux(io_regEnables_0, _T_1, r) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_1 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_1 = mux(io_regEnables_0, _T_14, r_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_2 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_2 = mux(io_regEnables_0, _T_2, r_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_3 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_3 = mux(io_regEnables_0, _T_15, r_3) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_4 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_4 = mux(io_regEnables_0, _T_3, r_4) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_5 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_5 = mux(io_regEnables_0, _T_16, r_5) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_6 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_6 = mux(io_regEnables_0, _T_28, r_6) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_7 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_7 = mux(io_regEnables_0, _T_4, r_7) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_8 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_8 = mux(io_regEnables_0, _T_17, r_8) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_9 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_9 = mux(io_regEnables_0, _T_29, r_9) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_10 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_10) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_10 = mux(io_regEnables_0, _T_5, r_10) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_11 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_11 = mux(io_regEnables_0, _T_18, r_11) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_12 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_12) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_12 = mux(io_regEnables_0, _T_30, r_12) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_13 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_13) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_13 = mux(io_regEnables_0, _T_42, r_13) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_14 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_14) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_14 = mux(io_regEnables_0, _T_6, r_14) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_15 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_15) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_15 = mux(io_regEnables_0, _T_19, r_15) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_16 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_16) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_16 = mux(io_regEnables_0, _T_31, r_16) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_17 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_17) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_17 = mux(io_regEnables_0, _T_43, r_17) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_18 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_18) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_18 = mux(io_regEnables_0, _T_7, r_18) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_19 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_19) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_19 = mux(io_regEnables_0, _T_20, r_19) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_20 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_20) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_20 = mux(io_regEnables_0, _T_32, r_20) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_21 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_21) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_21 = mux(io_regEnables_0, _T_44, r_21) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_22 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_22) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_22 = mux(io_regEnables_0, _T_54, r_22) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_23 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_23) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_23 = mux(io_regEnables_0, _T_8, r_23) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_24 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_24) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_24 = mux(io_regEnables_0, _T_21, r_24) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_25 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_25) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_25 = mux(io_regEnables_0, _T_33, r_25) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_26 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_26) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_26 = mux(io_regEnables_0, _T_45, r_26) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_27 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_27) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_27 = mux(io_regEnables_0, _T_55, r_27) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_28 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_28) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_28 = mux(io_regEnables_0, _T_9, r_28) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_29 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_29) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_29 = mux(io_regEnables_0, _T_22, r_29) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_30 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_30) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_30 = mux(io_regEnables_0, _T_34, r_30) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_31 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_31) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_31 = mux(io_regEnables_0, _T_46, r_31) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_32 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_32) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_32 = mux(io_regEnables_0, _T_10, r_32) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_33 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_33) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_33 = mux(io_regEnables_0, _T_23, r_33) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_34 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_34) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_34 = mux(io_regEnables_0, _T_35, r_34) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_35 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_35) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_35 = mux(io_regEnables_0, _T_47, r_35) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_36 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_36) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_36 = mux(io_regEnables_0, _T_11, r_36) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_37 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_37) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_37 = mux(io_regEnables_0, _T_24, r_37) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_38 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_38) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_38 = mux(io_regEnables_0, _T_36, r_38) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_39 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_39) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_39 = mux(io_regEnables_0, _T_48, r_39) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_40 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_40) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_40 = mux(io_regEnables_0, _T_12, r_40) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_41 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_41) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_41 = mux(io_regEnables_0, _T_25, r_41) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_42 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_42) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_42 = mux(io_regEnables_0, _T_37, r_42) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_43 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_43) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_43 = mux(io_regEnables_0, _T_49, r_43) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_44 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_44) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_44 = mux(io_regEnables_0, _T_26, r_44) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_45 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_45) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_45 = mux(io_regEnables_0, _T_38, r_45) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_46 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_46) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_46 = mux(io_regEnables_0, _T_50, r_46) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_47 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_47) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_47 = mux(io_regEnables_0, _T_39, r_47) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_48 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_48) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_48 = mux(io_regEnables_0, _T_51, r_48) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_49 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_49) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_49 = mux(io_regEnables_0, _T_40, r_49) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_50 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_50) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_50 = mux(io_regEnables_0, _T_52, r_50) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    reg r_51 : UInt<1>, clock with :
      reset => (UInt<1>("h0"), r_51) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:63]
    node _GEN_51 = mux(io_regEnables_0, _T_53, r_51) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 200:{63,63,63}]
    node s_0 = bits(c22.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0 = bits(c22.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_1 = bits(c22_1.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_1 = bits(c22_1.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_2 = bits(c32.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
    node c2_0_2 = bits(c32.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
    node s_0_3 = bits(c32_1.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
    node c2_0_3 = bits(c32_1.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
    node s_0_4 = bits(c53.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0 = bits(c53.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_4 = bits(c53.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_5 = bits(c53_1.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_1 = bits(c53_1.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_5 = bits(c53_1.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_6 = bits(c53_2.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_2 = bits(c53_2.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_6 = bits(c53_2.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_7 = bits(c53_3.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_3 = bits(c53_3.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_7 = bits(c53_3.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_8 = bits(c53_4.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_4 = bits(c53_4.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_8 = bits(c53_4.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_9 = bits(c53_5.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_5 = bits(c53_5.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_9 = bits(c53_5.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_10 = bits(c53_6.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_6 = bits(c53_6.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_10 = bits(c53_6.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_11 = bits(c53_7.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 153:33]
    node c1_0_7 = bits(c53_7.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 154:35]
    node c2_0_11 = bits(c53_7.io_out_2, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 155:35]
    node s_0_12 = bits(c32_2.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
    node c2_0_12 = bits(c32_2.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
    node s_0_13 = bits(c22_2.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_13 = bits(c22_2.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_14 = bits(c22_3.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_14 = bits(c22_3.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_15 = bits(c22_4.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_15 = bits(c22_4.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_16 = bits(c22_5.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_16 = bits(c22_5.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_17 = bits(c22_6.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_17 = bits(c22_6.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_18 = bits(c22_7.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_18 = bits(c22_7.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_19 = bits(c22_8.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_19 = bits(c22_8.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_20 = bits(c32_3.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
    node c2_0_20 = bits(c32_3.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
    node s_0_21 = bits(c32_4.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
    node c2_0_21 = bits(c32_4.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
    node s_0_22 = bits(c22_9.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_22 = bits(c22_9.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_23 = bits(c22_10.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_23 = bits(c22_10.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_24 = bits(c22_11.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_24 = bits(c22_11.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_25 = bits(c22_12.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_25 = bits(c22_12.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_26 = bits(c32_5.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 145:29]
    node c2_0_26 = bits(c32_5.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 146:35]
    node s_0_27 = bits(c22_13.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_27 = bits(c22_13.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_28 = bits(c22_14.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_28 = bits(c22_14.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node s_0_29 = bits(c22_15.io_out_0, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 140:29]
    node c2_0_29 = bits(c22_15.io_out_1, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 141:35]
    node sum_lo_lo_lo = cat(s_0_15, s_0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_lo_lo_hi = cat(s_0_17, s_0_16) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_lo_lo = cat(sum_lo_lo_hi, sum_lo_lo_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_lo_hi_lo = cat(s_0_19, s_0_18) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_lo_hi_hi = cat(s_0_21, s_0_20) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_lo_hi = cat(sum_lo_hi_hi, sum_lo_hi_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_lo = cat(sum_lo_hi, sum_lo_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi_lo_lo = cat(s_0_23, s_0_22) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi_lo_hi = cat(s_0_25, s_0_24) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi_lo = cat(sum_hi_lo_hi, sum_hi_lo_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi_hi_lo = cat(s_0_27, s_0_26) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi_hi_hi = cat(s_0_29, s_0_28) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi_hi = cat(sum_hi_hi_hi, sum_hi_hi_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum_hi = cat(sum_hi_hi, sum_hi_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node sum = cat(sum_hi, sum_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 173:20]
    node carry_lo_lo_hi = cat(c2_0_17, c2_0_16) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_lo_lo = cat(carry_lo_lo_hi, c2_0_15) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_lo_hi_lo = cat(c2_0_19, c2_0_18) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_lo_hi_hi = cat(c2_0_21, c2_0_20) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_lo_hi = cat(carry_lo_hi_hi, carry_lo_hi_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_lo = cat(carry_lo_hi, carry_lo_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_hi_lo_hi = cat(c2_0_24, c2_0_23) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_hi_lo = cat(carry_hi_lo_hi, c2_0_22) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_hi_hi_lo = cat(c2_0_26, c2_0_25) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_hi_hi_hi = cat(c2_0_28, c2_0_27) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_hi_hi = cat(carry_hi_hi_hi, carry_hi_hi_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_hi = cat(carry_hi_hi, carry_hi_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry = cat(carry_hi, carry_lo) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 176:22]
    node carry_1 = cat(carry, UInt<2>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 177:16]
    node _io_result_T = add(sum, carry_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 203:20]
    node _io_result_T_1 = tail(_io_result_T, 1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 203:20]
    node _expectedFirst_T = asSInt(io_a) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:39]
    node _expectedFirst_T_1 = asSInt(io_b) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:53]
    node _expectedFirst_T_2 = mul(_expectedFirst_T, _expectedFirst_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:46]
    node _expectedFirst_T_3 = asUInt(_expectedFirst_T_2) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:61]
    reg expectedFirst : UInt<16>, clock with :
      reset => (UInt<1>("h0"), expectedFirst) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:32]
    node _GEN_52 = mux(io_regEnables_0, _expectedFirst_T_3, expectedFirst) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 209:{32,32,32}]
    reg validFirst : UInt<1>, clock with :
      reset => (UInt<1>("h0"), validFirst) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 210:27]
    node _GEN_53 = mux(io_regEnables_0, UInt<1>("h1"), validFirst) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 211:26 210:27 211:39]
    node _T_56 = eq(io_result, expectedFirst) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:40]
    node _T_57 = bits(reset, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
    node _T_58 = eq(_T_57, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
    node _T_59 = eq(_T_56, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
    reg previousResult : UInt<16>, clock with :
      reset => (UInt<1>("h0"), previousResult) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 222:31]
    node _wasHoldingKnownResult_T = eq(io_regEnables_0, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:54]
    node _wasHoldingKnownResult_T_1 = and(validFirst, _wasHoldingKnownResult_T) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:51]
    reg wasHoldingKnownResult : UInt<1>, clock with :
      reset => (UInt<1>("h0"), wasHoldingKnownResult) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:38]
    node _T_60 = eq(io_result, previousResult) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:50]
    node _T_61 = bits(reset, 0, 0) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
    node _T_62 = eq(_T_61, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
    node _T_63 = eq(_T_60, UInt<1>("h0")) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
    io_result <= _io_result_T_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 203:13]
    r <= _GEN_0
    r_1 <= _GEN_1
    r_2 <= _GEN_2
    r_3 <= _GEN_3
    r_4 <= _GEN_4
    r_5 <= _GEN_5
    r_6 <= _GEN_6
    r_7 <= _GEN_7
    r_8 <= _GEN_8
    r_9 <= _GEN_9
    r_10 <= _GEN_10
    r_11 <= _GEN_11
    r_12 <= _GEN_12
    r_13 <= _GEN_13
    r_14 <= _GEN_14
    r_15 <= _GEN_15
    r_16 <= _GEN_16
    r_17 <= _GEN_17
    r_18 <= _GEN_18
    r_19 <= _GEN_19
    r_20 <= _GEN_20
    r_21 <= _GEN_21
    r_22 <= _GEN_22
    r_23 <= _GEN_23
    r_24 <= _GEN_24
    r_25 <= _GEN_25
    r_26 <= _GEN_26
    r_27 <= _GEN_27
    r_28 <= _GEN_28
    r_29 <= _GEN_29
    r_30 <= _GEN_30
    r_31 <= _GEN_31
    r_32 <= _GEN_32
    r_33 <= _GEN_33
    r_34 <= _GEN_34
    r_35 <= _GEN_35
    r_36 <= _GEN_36
    r_37 <= _GEN_37
    r_38 <= _GEN_38
    r_39 <= _GEN_39
    r_40 <= _GEN_40
    r_41 <= _GEN_41
    r_42 <= _GEN_42
    r_43 <= _GEN_43
    r_44 <= _GEN_44
    r_45 <= _GEN_45
    r_46 <= _GEN_46
    r_47 <= _GEN_47
    r_48 <= _GEN_48
    r_49 <= _GEN_49
    r_50 <= _GEN_50
    r_51 <= _GEN_51
    c22.clock <= clock
    c22.reset <= reset
    c22.io_in_0 <= r @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22.io_in_1 <= r_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_1.clock <= clock
    c22_1.reset <= reset
    c22_1.io_in_0 <= r_2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_1.io_in_1 <= r_3 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c32.clock <= clock
    c32.reset <= reset
    c32.io_in_0 <= r_4 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32.io_in_1 <= r_5 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32.io_in_2 <= r_6 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_1.clock <= clock
    c32_1.reset <= reset
    c32_1.io_in_0 <= r_7 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_1.io_in_1 <= r_8 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_1.io_in_2 <= r_9 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c53.clock <= clock
    c53.reset <= reset
    c53.io_in_0 <= r_10 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53.io_in_1 <= r_11 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53.io_in_2 <= r_12 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53.io_in_3 <= r_13 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53.io_in_4 <= UInt<1>("h0") @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_1.clock <= clock
    c53_1.reset <= reset
    c53_1.io_in_0 <= r_14 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_1.io_in_1 <= r_15 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_1.io_in_2 <= r_16 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_1.io_in_3 <= r_17 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_1.io_in_4 <= c1_0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_2.clock <= clock
    c53_2.reset <= reset
    c53_2.io_in_0 <= r_18 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_2.io_in_1 <= r_19 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_2.io_in_2 <= r_20 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_2.io_in_3 <= r_21 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_2.io_in_4 <= c1_0_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_3.clock <= clock
    c53_3.reset <= reset
    c53_3.io_in_0 <= r_23 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_3.io_in_1 <= r_24 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_3.io_in_2 <= r_25 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_3.io_in_3 <= r_26 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_3.io_in_4 <= c1_0_2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_4.clock <= clock
    c53_4.reset <= reset
    c53_4.io_in_0 <= r_28 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_4.io_in_1 <= r_29 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_4.io_in_2 <= r_30 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_4.io_in_3 <= r_31 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_4.io_in_4 <= c1_0_3 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_5.clock <= clock
    c53_5.reset <= reset
    c53_5.io_in_0 <= r_32 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_5.io_in_1 <= r_33 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_5.io_in_2 <= r_34 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_5.io_in_3 <= r_35 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_5.io_in_4 <= c1_0_4 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_6.clock <= clock
    c53_6.reset <= reset
    c53_6.io_in_0 <= r_36 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_6.io_in_1 <= r_37 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_6.io_in_2 <= r_38 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_6.io_in_3 <= r_39 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_6.io_in_4 <= c1_0_5 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c53_7.clock <= clock
    c53_7.reset <= reset
    c53_7.io_in_0 <= r_40 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_7.io_in_1 <= r_41 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_7.io_in_2 <= r_42 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_7.io_in_3 <= r_43 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 150:13]
    c53_7.io_in_4 <= c1_0_6 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 152:24]
    c32_2.clock <= clock
    c32_2.reset <= reset
    c32_2.io_in_0 <= r_44 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_2.io_in_1 <= r_45 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_2.io_in_2 <= r_46 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c22_2.clock <= clock
    c22_2.reset <= reset
    c22_2.io_in_0 <= r_47 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_2.io_in_1 <= r_48 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_3.clock <= clock
    c22_3.reset <= reset
    c22_3.io_in_0 <= r_49 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_3.io_in_1 <= r_50 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_4.clock <= clock
    c22_4.reset <= reset
    c22_4.io_in_0 <= s_0_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_4.io_in_1 <= c2_0 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_5.clock <= clock
    c22_5.reset <= reset
    c22_5.io_in_0 <= s_0_2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_5.io_in_1 <= c2_0_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_6.clock <= clock
    c22_6.reset <= reset
    c22_6.io_in_0 <= s_0_3 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_6.io_in_1 <= c2_0_2 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_7.clock <= clock
    c22_7.reset <= reset
    c22_7.io_in_0 <= s_0_4 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_7.io_in_1 <= c2_0_3 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_8.clock <= clock
    c22_8.reset <= reset
    c22_8.io_in_0 <= s_0_5 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_8.io_in_1 <= c2_0_4 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c32_3.clock <= clock
    c32_3.reset <= reset
    c32_3.io_in_0 <= s_0_6 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_3.io_in_1 <= r_22 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_3.io_in_2 <= c2_0_5 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_4.clock <= clock
    c32_4.reset <= reset
    c32_4.io_in_0 <= s_0_7 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_4.io_in_1 <= r_27 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_4.io_in_2 <= c2_0_6 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c22_9.clock <= clock
    c22_9.reset <= reset
    c22_9.io_in_0 <= s_0_8 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_9.io_in_1 <= c2_0_7 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_10.clock <= clock
    c22_10.reset <= reset
    c22_10.io_in_0 <= s_0_9 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_10.io_in_1 <= c2_0_8 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_11.clock <= clock
    c22_11.reset <= reset
    c22_11.io_in_0 <= s_0_10 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_11.io_in_1 <= c2_0_9 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_12.clock <= clock
    c22_12.reset <= reset
    c22_12.io_in_0 <= s_0_11 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_12.io_in_1 <= c2_0_10 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c32_5.clock <= clock
    c32_5.reset <= reset
    c32_5.io_in_0 <= s_0_12 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_5.io_in_1 <= c1_0_7 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c32_5.io_in_2 <= c2_0_11 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 144:19]
    c22_13.clock <= clock
    c22_13.reset <= reset
    c22_13.io_in_0 <= s_0_13 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_13.io_in_1 <= c2_0_12 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_14.clock <= clock
    c22_14.reset <= reset
    c22_14.io_in_0 <= s_0_14 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_14.io_in_1 <= c2_0_13 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_15.clock <= clock
    c22_15.reset <= reset
    c22_15.io_in_0 <= r_51 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    c22_15.io_in_1 <= c2_0_14 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 139:19]
    expectedFirst <= _GEN_52
    validFirst <= mux(reset, UInt<1>("h0"), _GEN_53) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 210:{27,27}]
    previousResult <= io_result @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 222:31]
    wasHoldingKnownResult <= mux(reset, UInt<1>("h0"), _wasHoldingKnownResult_T_1) @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 223:{38,38,38}]
    printf(clock, and(and(and(and(UInt<1>("h1"), validFirst), _T_58), _T_59), UInt<1>("h1")), "Assertion failed\n    at Multiplier.scala:220 when(resultKnown) { assert(io.result === expectedResult) }\n") : printf @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
    assert(clock, _T_56, and(and(and(UInt<1>("h1"), validFirst), _T_58), UInt<1>("h1")), "") : assert @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 220:29]
    printf(clock, and(and(and(and(UInt<1>("h1"), wasHoldingKnownResult), _T_62), _T_63), UInt<1>("h1")), "Assertion failed\n    at Multiplier.scala:224 when(wasHoldingKnownResult) { assert(io.result === previousResult) }\n") : printf_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
    assert(clock, _T_60, and(and(and(UInt<1>("h1"), wasHoldingKnownResult), _T_62), UInt<1>("h1")), "") : assert_1 @[workspaces/cp-share/arithmetic/source/src/main/scala/singlefile/xiangshan/Multiplier.scala 224:39]
