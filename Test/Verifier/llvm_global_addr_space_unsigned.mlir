// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The addr_space attribute of llvm.mlir.global is a 32-bit signless integer;
// ui32 has the right width but the wrong type. mlir-opt reports "attribute
// 'addr_space' failed to satisfy constraint: 32-bit signless integer attribute
// whose value is non-negative".

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : ui32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: 'addr_space' must be a 32-bit signless integer attribute
