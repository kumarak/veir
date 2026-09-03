// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The condition of cf.cond_br must be the signless i1: a signed si1 has the
// right width but the wrong type. mlir-opt reports "operand #0 must be 1-bit
// signless integer, but got 'si1'".

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (si1) -> ()}> ({
  ^bb0(%cond: si1):
    "cf.cond_br"(%cond) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (si1) -> ()
  ^bb1:
    "func.return"() : () -> ()
  ^bb2:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: cf.cond_br: Expected i1 condition
