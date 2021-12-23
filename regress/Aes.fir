;buildInfoPackage: chisel3, version: 3.4.3, scalaVersion: 2.12.12, sbtVersion: 1.3.10
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
    input reset : Reset
    output io : {flip clk : Clock, flip rst : UInt<1>, flip ld : UInt<1>, done : UInt<1>, flip key : UInt<128>, flip text_in : UInt<128>, text_out : UInt<128>}
    
    inst core of aes_core @[aes.scala 18:20]
    core.text_out is invalid
    core.text_in is invalid
    core.key is invalid
    core.done is invalid
    core.ld is invalid
    core.rst is invalid
    core.clk is invalid
    io.text_out <= core.text_out @[aes.scala 19:11]
    core.text_in <= io.text_in @[aes.scala 19:11]
    core.key <= io.key @[aes.scala 19:11]
    io.done <= core.done @[aes.scala 19:11]
    core.ld <= io.ld @[aes.scala 19:11]
    core.rst <= io.rst @[aes.scala 19:11]
    core.clk <= io.clk @[aes.scala 19:11]
    
  module Aes : 
    input clock : Clock
    input reset : UInt<1>
    output io : {mem : {flip d : UInt<256>, flip radr : UInt<8>, flip ren : UInt<1>, flip wen : UInt<1>, flip wadr : UInt<8>, q : UInt<256>}, done : UInt<1>}
    
    smem inmem : UInt<256>[256], undefined @[aes.scala 28:26]
    smem outmem : UInt<128>[256], undefined @[aes.scala 29:27]
    inst aes of AesCoreModule @[aes.scala 30:19]
    aes.clock <= clock
    aes.reset <= reset
    reg ctr : UInt<8>, clock with : (reset => (reset, UInt<8>("h00"))) @[aes.scala 31:20]
    reg init_ld : UInt<1>, clock with : (reset => (reset, UInt<1>("h01"))) @[aes.scala 32:24]
    init_ld <= UInt<1>("h00") @[aes.scala 33:11]
    node _T = eq(io.mem.wen, UInt<1>("h01")) @[aes.scala 43:19]
    when _T : @[aes.scala 43:28]
      write mport MPORT = inmem[io.mem.wadr], clock
      MPORT <= io.mem.d
      skip @[aes.scala 43:28]
    read mport io_mem_q_MPORT = outmem[io.mem.radr], clock @[aes.scala 46:26]
    io.mem.q <= io_mem_q_MPORT @[aes.scala 46:12]
    node _io_done_T = eq(ctr, UInt<8>("h0ff")) @[aes.scala 47:18]
    io.done <= _io_done_T @[aes.scala 47:11]
    wire _input_WIRE : UInt @[aes.scala 50:25]
    _input_WIRE is invalid @[aes.scala 50:25]
    when UInt<1>("h01") : @[aes.scala 50:25]
      _input_WIRE <= ctr @[aes.scala 50:25]
      node _input_T = or(_input_WIRE, UInt<8>("h00")) @[aes.scala 50:25]
      node _input_T_1 = bits(_input_T, 7, 0) @[aes.scala 50:25]
      read mport input = inmem[_input_T_1], clock @[aes.scala 50:25]
      skip @[aes.scala 50:25]
    node _aes_io_text_in_T = bits(input, 127, 0) @[aes.scala 51:26]
    aes.io.text_in <= _aes_io_text_in_T @[aes.scala 51:18]
    node _aes_io_key_T = bits(input, 255, 128) @[aes.scala 52:22]
    aes.io.key <= _aes_io_key_T @[aes.scala 52:14]
    when aes.io.done : @[aes.scala 54:21]
      write mport MPORT_1 = outmem[ctr], clock
      MPORT_1 <= aes.io.text_out
      node _ctr_T = add(ctr, UInt<1>("h01")) @[aes.scala 56:16]
      node _ctr_T_1 = tail(_ctr_T, 1) @[aes.scala 56:16]
      ctr <= _ctr_T_1 @[aes.scala 56:9]
      skip @[aes.scala 54:21]
    aes.io.clk <= clock @[aes.scala 60:14]
    node _aes_io_rst_T = bits(reset, 0, 0) @[aes.scala 61:25]
    node _aes_io_rst_T_1 = eq(_aes_io_rst_T, UInt<1>("h00")) @[aes.scala 61:18]
    node _aes_io_rst_T_2 = bits(_aes_io_rst_T_1, 0, 0) @[aes.scala 61:33]
    aes.io.rst <= _aes_io_rst_T_2 @[aes.scala 61:14]
    node _aes_io_ld_T = eq(io.done, UInt<1>("h00")) @[aes.scala 62:43]
    node _aes_io_ld_T_1 = and(aes.io.done, _aes_io_ld_T) @[aes.scala 62:40]
    node _aes_io_ld_T_2 = or(init_ld, _aes_io_ld_T_1) @[aes.scala 62:24]
    aes.io.ld <= _aes_io_ld_T_2 @[aes.scala 62:13]
    
