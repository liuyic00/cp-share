FIRRTL version 1.2.0
circuit MemoryFixture :
  module Arbitrary :
    output init : UInt<8>
    init is invalid
  module MemoryFixture :
    input clock : Clock
    input reset : UInt<1>
    input addr : UInt<2>
    input data : UInt<8>
    input wen : UInt<1>
    input mask : UInt<1>
    input ren : UInt<1>
    output value : UInt<8>
    output romvalue : UInt<8>
    output sharedA : UInt<8>
    output sharedB : UInt<8>
    mem ram :
      data-type => UInt<8>
      depth => 4
      read-latency => 0
      write-latency => 1
      reader => r
      writer => w
      read-under-write => undefined
    mem rom :
      data-type => UInt<8>
      depth => 4
      read-latency => 0
      write-latency => 1
      reader => r
      read-under-write => undefined
    ram.r.addr <= addr
    ram.r.en <= ren
    ram.r.clk <= clock
    ram.w.addr <= addr
    ram.w.en <= wen
    ram.w.clk <= clock
    ram.w.data <= data
    ram.w.mask <= mask
    rom.r.addr <= addr
    rom.r.en <= ren
    rom.r.clk <= clock
    value <= ram.r.data
    romvalue <= rom.r.data
    inst seed of Arbitrary
    reg a : UInt<8>, clock with :
      reset => (reset, seed.init)
    reg b : UInt<8>, clock with :
      reset => (reset, seed.init)
    a <= a
    b <= b
    sharedA <= a
    sharedB <= b
    assert(clock, eq(a, b), not(reset), "") : shared
