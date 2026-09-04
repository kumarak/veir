// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: cir.alloca: Expected result to have !cir.ptr type
"builtin.module"() ({
  %x = "cir.alloca"() <{alignment = 4 : i64, name = "x"}> : () -> !cir.int<s, 32>
}) : () -> ()
