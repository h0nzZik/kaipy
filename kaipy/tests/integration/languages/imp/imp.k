// Taken from https://github.com/runtimeverification/k/blob/3c5e1c329dc69085ac3878583985d52cfc420a9c/k-distribution/pl-tutorial/1_k/2_imp/lesson_4/imp.k
// Changes:
// * replaced 'seqstrict' with 'seqstrict' for performance reasons.
// * sequential composition of statements is now seqstrict, with added voidVal() returned by statements.
//   This simplifies some preliminary analysis, but we will want to make our tool work even without the change/
// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module IMP-SYNTAX
  imports DOMAINS-SYNTAX
  //syntax KResult ::= Int
  syntax AExp  ::= Int | Id
                 | "-" Int                    [seqstrict(1)]
                 | AExp "/" AExp              [left, seqstrict]
                 | "(" AExp ")"               [bracket]
                 //| "getArg" "(" AExp ")"      [seqstrict(1)]
                 | "getArg" "(" Int ")"      [seqstrict(1)]
                 > AExp "+" AExp              [left, seqstrict]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [seqstrict]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, seqstrict(1)]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [seqstrict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [seqstrict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 > Stmt Stmt                  [right, seqstrict]
  syntax Pgm ::= Stmt
  syntax Ids ::= List{Id,","}
endmodule

module IMP
  imports IMP-SYNTAX
  
  imports DOMAINS

  syntax VoidVal ::= voidVal()
  syntax Value ::= Int | Bool | VoidVal
  syntax KResult ::= Value
  syntax Stmt ::= Value

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                  <args color="blue"> $ARGS:List </args>
                </T>

  rule [getArg]:
    <k> getArg(N:Int) => {ARGS[N]}:>Int ...</k>
    <args> ARGS:List </args>
    requires N >=Int 0 andBool size(ARGS) >Int N

  // TODO we should be able to write some sorts analysis which would infer that State[X] is always of sort Int
  // and transformed the rhs to say {STATE[X]}:>Int instead. That should be a semantics-level analysis/transformation.
  // <k> X:Id => STATE[X] ... </k> <state> STATE </state> requires X in_keys(STATE)
  rule [id-lookup]:
    <k> X:Id => {STATE[X]}:>Int ... </k> <state> STATE </state> requires X in_keys(STATE)

  rule [div-nonzero]:
    <k> I1 / I2 => I1 /Int I2 ... </k>  requires I2 =/=Int 0

  rule [unary-minus]:
    <k> - X:Int => 0 -Int X ... </k>

  rule [add]:
    <k> I1 + I2 => I1 +Int I2 ... </k>

  rule [less-than-or-equal-to]:
    <k> I1 <= I2   => I1 <=Int I2 ... </k>

  rule [negation]:
    <k> ! T        => notBool T   ... </k>

  rule [andb-true]:
    <k> true && B  => B           ... </k>

  rule [andb-false]:
    <k> false && _ => false       ... </k>

  // Statements
  rule [block-empty]:
    <k> {}  => voidVal() ... </k>

  rule [block-statement]:
    <k> {S} => S ... </k>

  rule [assignment]:
    <k> X = I:Int; => voidVal() ... </k> <state> STATE => STATE [ X <- I ] </state>

  //rule [stmt-sequence]:
  //  <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>
  rule [stmt-sequence]:
      <k> (voidVal() voidVal()) => voidVal() ...</k>


  rule [if-true]:
    <k> if (true)  S else _ => S ... </k>

  rule [if-false]:
    <k> if (false) _ else S => S ... </k>

  rule [while-unroll]:
    <k> while (B) S => if (B) {S while (B) S} else {} ... </k>

  rule [var-decl]:
    <k> int (X , Xs => Xs) ; ... </k> <state> STATE => STATE [ X <- 0 ] </state>
    requires notBool (X in keys(STATE))

  rule [var-decls-empty]:
    <k> int .Ids ; => voidVal() ... </k>

/*
// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
*/
endmodule

