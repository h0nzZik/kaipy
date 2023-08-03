module TOY-SYNTAX
    imports DOMAINS-SYNTAX

    syntax KResult
    syntax KResult ::= Int
    syntax AExp ::= Int | AExp "+" AExp | someConstant()
    syntax Stmt ::= foo(AExp) [strict]
    syntax Pgm ::= Stmt
endmodule

module TOY
    imports TOY-SYNTAX
    configuration <k> $PGM:Pgm </k>
endmodule