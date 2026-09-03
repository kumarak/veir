// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// arith.cmpi produces the signless i1, never ui1. mlir-opt reports "result #0
// must be bool-like, but got 'ui1'".

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i8) -> ()}> ({
  ^bb0(%x: i8):
    %cmp = "arith.cmpi"(%x, %x) <{ predicate = 0 : i64 }> : (i8, i8) -> ui1
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.cmpi: Expected i1 result
