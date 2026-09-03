// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The condition of arith.select must be the signless i1. mlir-opt reports
// "operand #0 must be bool-like, but got 'si1'".

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (si1, i8) -> i8}> ({
  ^bb0(%cond: si1, %x: i8):
    %sel = "arith.select"(%cond, %x, %x) : (si1, i8, i8) -> i8
    "func.return"(%sel) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.select: Expected i1 condition
