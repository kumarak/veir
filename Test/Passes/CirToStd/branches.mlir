// RUN: veir-opt %s -p=cir-to-std | filecheck %s

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>) -> !cir.int<s, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>):
    %b = "cir.cast"(%a) <{kind = 28 : i32}> : (!cir.int<s, 32>) -> !cir.bool
    "cir.brcond"(%b, %a)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (!cir.bool, !cir.int<s, 32>) -> ()
  ^bb1(%x : !cir.int<s, 32>):
    "cir.br"(%x)[^bb3] : (!cir.int<s, 32>) -> ()
  ^bb2:
    "cir.unreachable"() : () -> ()
  ^bb3(%r : !cir.int<s, 32>):
    "cir.return"(%r) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "cir.func"() <{"function_type" = !cir.func<(i32) -> i32>, "sym_name" = "f"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT: %{{.*}} = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
// CHECK-NEXT: %{{.*}} = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
// CHECK-NEXT: "cf.cond_br"(%{{.*}}, %{{.*}}) [^{{.*}}, ^{{.*}}] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 1, 0>}> : (i1, i32) -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT: "cf.br"(%{{.*}}) [^{{.*}}] : (i32) -> ()
// CHECK-NEXT: ^{{.*}}():
// CHECK-NEXT: "llvm.unreachable"() : () -> ()
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i32):
// CHECK-NEXT: "cir.return"(%{{.*}}) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
