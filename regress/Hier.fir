; SPDX-License-Identifier: Apache-2.0
circuit Top:
  module Top:
    input a: UInt<8>
    input b: UInt<8>
    output o: UInt<9>
    input clock: Clock	
    reg a_reg: UInt<8>, clock    
    reg b_reg: UInt<8>, clock
    reg o_reg: UInt<9>, clock
    a_reg <- a
    b_reg <- b
    o <- o_reg
    inst sub of Sub
    sub.clock <- clock
    sub.a <- a_reg
    sub.b <- b_reg
    o_reg <- sub.o
  module Sub:
    input a: UInt<8>
    input b: UInt<8>
    input clock: Clock
    output o: UInt<9>
    reg a_reg: UInt<8>, clock
    a_reg <- a
    o <= add(a_reg, not(b))
