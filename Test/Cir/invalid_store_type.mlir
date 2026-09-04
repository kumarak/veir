// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.store: Expected the stored value's type to match the pointee type
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<u, 8>, !cir.ptr<!cir.int<s, 32>>)>, sym_name = "f"}> ({
  ^bb0(%v : !cir.int<u, 8>, %p : !cir.ptr<!cir.int<s, 32>>):
    "cir.store"(%v, %p) : (!cir.int<u, 8>, !cir.ptr<!cir.int<s, 32>>) -> ()
    "cir.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
