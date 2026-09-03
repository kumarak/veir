// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The alignment attribute of llvm.load is a 64-bit signless integer; a signed
// si64 of the same width is rejected, as mlir-opt does with the same message.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (!llvm.ptr) -> i32}> ({
  ^bb0(%p: !llvm.ptr):
    %v = "llvm.load"(%p) <{alignment = 4 : si64}> : (!llvm.ptr) -> i32
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: 'llvm.load' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute
