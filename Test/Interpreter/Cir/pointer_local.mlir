// RUN: veir-opt %s -p=cir > %t.mlir && veir-interpret %t.mlir | filecheck %s

// `int x = 7; int *p = &x; *p = 9; return x;`: a pointer stored in and loaded from memory.
// Expect 9.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<() -> !cir.int<s, 32>>, sym_name = "main"}> ({
    %x = "cir.alloca"() <{alignment = 4 : i64, init, name = "x"}> : () -> !cir.ptr<!cir.int<s, 32>>
    %p = "cir.alloca"() <{alignment = 8 : i64, init, name = "p"}> : () -> !cir.ptr<!cir.ptr<!cir.int<s, 32>>>
    %c7 = "cir.const"() <{value = #cir.int<7> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    "cir.store"(%c7, %x) <{alignment = 4 : i64}> : (!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> ()
    "cir.store"(%x, %p) <{alignment = 8 : i64}> : (!cir.ptr<!cir.int<s, 32>>, !cir.ptr<!cir.ptr<!cir.int<s, 32>>>) -> ()
    %pv = "cir.load"(%p) <{alignment = 8 : i64}> : (!cir.ptr<!cir.ptr<!cir.int<s, 32>>>) -> !cir.ptr<!cir.int<s, 32>>
    %c9 = "cir.const"() <{value = #cir.int<9> : !cir.int<s, 32>}> : () -> !cir.int<s, 32>
    "cir.store"(%c9, %pv) <{alignment = 4 : i64}> : (!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> ()
    %xv = "cir.load"(%x) <{alignment = 4 : i64}> : (!cir.ptr<!cir.int<s, 32>>) -> !cir.int<s, 32>
    "cir.return"(%xv) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000009#32]
