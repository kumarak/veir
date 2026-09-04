// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// The shape ClangIR emits at -O0 for `int x = 7; int y = 5; return (x + y) * 3;`: every
// local lives in an alloca and every use goes through memory. Expect 36.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %x = "cir.alloca"() <{alignment = 4 : i64, init, name = "x"}> : () -> !cir.ptr<!cir.int<s, 32>>
    %y = "cir.alloca"() <{alignment = 4 : i64, init, name = "y"}> : () -> !cir.ptr<!cir.int<s, 32>>
    %c7 = "cir.const"() <{value = #cir.int<7> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    "cir.store"(%c7, %x) <{alignment = 4 : i64}> : (!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> ()
    %c5 = "cir.const"() <{value = #cir.int<5> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    "cir.store"(%c5, %y) <{alignment = 4 : i64}> : (!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> ()
    %xv = "cir.load"(%x) <{alignment = 4 : i64}> : (!cir.ptr<!cir.int<s, 32>>) -> !cir.int<s, 32>
    %yv = "cir.load"(%y) <{alignment = 4 : i64}> : (!cir.ptr<!cir.int<s, 32>>) -> !cir.int<s, 32>
    %s = "cir.add"(%xv, %yv) <{no_signed_wrap = false, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %c3 = "cir.const"() <{value = #cir.int<3> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    %p = "cir.mul"(%s, %c3) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%p) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000024#32]
