circuit Aes :
  extmodule aes_core :
    input clk : Clock
    input rst : UInt<1>
    input ld : UInt<1>
    output done : UInt<1>
    input key : UInt<128>
    input text_in : UInt<128>
    output text_out : UInt<128>
    defname = aes_core

  module AesCoreModule :
    input clock : Clock
    input reset : UInt<1>
    input io_clk : Clock
    input io_rst : UInt<1>
    input io_ld : UInt<1>
    output io_done : UInt<1>
    input io_key : UInt<128>
    input io_text_in : UInt<128>
    output io_text_out : UInt<128>

    inst core of aes_core @[aes.scala 18:20]
    io_done <= core.done @[aes.scala 19:11]
    io_text_out <= core.text_out @[aes.scala 19:11]
    core.clk <= io_clk @[aes.scala 19:11]
    core.rst <= io_rst @[aes.scala 19:11]
    core.ld <= io_ld @[aes.scala 19:11]
    core.key <= io_key @[aes.scala 19:11]
    core.text_in <= io_text_in @[aes.scala 19:11]

  module Aes :
    input inj : UInt<9>
    input halt : UInt<1>
    input clock : Clock
    input reset : UInt<1>
    input io_mem_d : UInt<256>
    input io_mem_radr : UInt<8>
    input io_mem_ren : UInt<1>
    input io_mem_wen : UInt<1>
    input io_mem_wadr : UInt<8>
    output io_mem_q : UInt<256>
    output io_done : UInt<1>

    mem inmem : @[aes.scala 28:26]
      data-type => UInt<256>
      depth => 256
      read-latency => 1
      write-latency => 1
      reader => input
      writer => MPORT
      read-under-write => undefined
    mem outmem : @[aes.scala 29:27]
      data-type => UInt<128>
      depth => 256
      read-latency => 1
      write-latency => 1
      reader => io_mem_q_MPORT
      writer => MPORT_1
      read-under-write => undefined
    inst aes of AesCoreModule @[aes.scala 30:19]
    reg ctr : UInt<8>, clock with :
      reset => (UInt<1>("h0"), ctr) @[aes.scala 31:20]
    reg init_ld : UInt<1>, clock with :
      reset => (UInt<1>("h0"), init_ld) @[aes.scala 32:24]
    node _T = eq(io_mem_wen, UInt<1>("h1")) @[aes.scala 43:19]
    node _GEN_0 = validif(_T, io_mem_wadr) @[aes.scala 43:28]
    node _GEN_1 = validif(_T, clock) @[aes.scala 43:28]
    node _GEN_2 = mux(_T, UInt<1>("h1"), UInt<1>("h0")) @[aes.scala 28:26 43:28]
    node _GEN_3 = validif(_T, UInt<1>("h1")) @[aes.scala 43:28]
    node _GEN_4 = validif(_T, io_mem_d) @[aes.scala 43:28]
    node _io_done_T = eq(ctr, UInt<8>("hff")) @[aes.scala 47:18]
    node _GEN_5 = validif(UInt<1>("h1"), ctr) @[aes.scala 50:{25,25}]
    node _input_WIRE = _GEN_5 @[aes.scala 50:25]
    node _input_T = or(_input_WIRE, UInt<8>("h0")) @[aes.scala 50:25]
    node _input_T_1 = bits(_input_T, 7, 0) @[aes.scala 50:25]
    node _GEN_6 = mux(UInt<1>("h1"), UInt<1>("h1"), UInt<1>("h0")) @[aes.scala 50:{25,25} 28:26]
    node _GEN_7 = validif(UInt<1>("h1"), _input_T_1) @[aes.scala 50:{25,25}]
    node _GEN_8 = validif(UInt<1>("h1"), clock) @[aes.scala 50:{25,25}]
    node _aes_io_text_in_T = bits(inmem.input.data, 127, 0) @[aes.scala 51:26]
    node _aes_io_key_T = bits(inmem.input.data, 255, 128) @[aes.scala 52:22]
    node _ctr_T = add(ctr, UInt<1>("h1")) @[aes.scala 56:16]
    node _ctr_T_1 = tail(_ctr_T, 1) @[aes.scala 56:16]
    node _GEN_9 = validif(aes.io_done, ctr) @[aes.scala 54:21]
    node _GEN_10 = validif(aes.io_done, clock) @[aes.scala 54:21]
    node _GEN_11 = mux(aes.io_done, UInt<1>("h1"), UInt<1>("h0")) @[aes.scala 54:21 29:27]
    node _GEN_12 = validif(aes.io_done, UInt<1>("h1")) @[aes.scala 54:21]
    node _GEN_13 = validif(aes.io_done, aes.io_text_out) @[aes.scala 54:21]
    node _GEN_14 = mux(aes.io_done, _ctr_T_1, ctr) @[aes.scala 31:20 54:21 56:9]
    node _aes_io_rst_T = bits(reset, 0, 0) @[aes.scala 61:25]
    node _aes_io_rst_T_1 = eq(_aes_io_rst_T, UInt<1>("h0")) @[aes.scala 61:18]
    node _aes_io_rst_T_2 = bits(_aes_io_rst_T_1, 0, 0) @[aes.scala 61:33]
    node _aes_io_ld_T = eq(io_done, UInt<1>("h0")) @[aes.scala 62:43]
    node _aes_io_ld_T_1 = and(aes.io_done, _aes_io_ld_T) @[aes.scala 62:40]
    node _aes_io_ld_T_2 = or(init_ld, _aes_io_ld_T_1) @[aes.scala 62:24]
    io_mem_q <= pad(outmem.io_mem_q_MPORT.data, 256) @[aes.scala 46:12]
    io_done <= _io_done_T @[aes.scala 47:11]
    inmem.input.addr <= _GEN_7
    inmem.input.en <= _GEN_6
    inmem.input.clk <= _GEN_8
    inmem.MPORT.addr <= _GEN_0
    inmem.MPORT.en <= _GEN_2
    inmem.MPORT.clk <= _GEN_1
    inmem.MPORT.data <= _GEN_4
    inmem.MPORT.mask <= _GEN_3
    outmem.io_mem_q_MPORT.addr <= io_mem_radr @[aes.scala 46:26]
    outmem.io_mem_q_MPORT.en <= UInt<1>("h1") @[aes.scala 46:26]
    outmem.io_mem_q_MPORT.clk <= clock @[aes.scala 46:26]
    outmem.MPORT_1.addr <= _GEN_9
    outmem.MPORT_1.en <= _GEN_11
    outmem.MPORT_1.clk <= _GEN_10
    outmem.MPORT_1.data <= _GEN_13
    outmem.MPORT_1.mask <= _GEN_12
    aes.clock <= clock
    aes.reset <= reset
    aes.io_clk <= clock @[aes.scala 60:14]
    aes.io_rst <= _aes_io_rst_T_2 @[aes.scala 61:14]
    aes.io_ld <= _aes_io_ld_T_2 @[aes.scala 62:13]
    aes.io_key <= _aes_io_key_T @[aes.scala 52:14]
    aes.io_text_in <= _aes_io_text_in_T @[aes.scala 51:18]
    ctr <= or(and(bits(inj, 7, 0), not(ctr)), and(not(bits(inj, 7, 0)), mux(halt, ctr, mux(reset, UInt<8>("h0"), _GEN_14)))) @[aes.scala 31:{20,20}]
    init_ld <= or(and(bits(inj, 8, 8), not(init_ld)), and(not(bits(inj, 8, 8)), mux(halt, init_ld, mux(reset, UInt<1>("h1"), UInt<1>("h0"))))) @[aes.scala 32:{24,24} 33:11]
