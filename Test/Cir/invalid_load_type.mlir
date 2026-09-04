// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.load: Expected result type to match the pointee type
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.ptr<!cir.int<s, 32>>) -> !cir.int<u, 8>>, sym_name = "f"}> ({
  ^bb0(%p : !cir.ptr<!cir.int<s, 32>>):
    %v = "cir.load"(%p) : (!cir.ptr<!cir.int<s, 32>>) -> !cir.int<u, 8>
    "cir.return"(%v) : (!cir.int<u, 8>) -> ()
  }) : () -> ()
}) : () -> ()
