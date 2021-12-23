circuit Example :
  module Example :
    input clock : Clock
    input rst : UInt<1>
    input in : UInt<2>
    output out : UInt<2>

    reg foo : UInt<2>, clock with :
      reset => (UInt<1>("h0"), foo)
    out <= foo
    foo <= in
