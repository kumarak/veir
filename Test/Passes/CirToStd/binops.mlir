// RUN: veir-opt %s -p=cir-to-std | filecheck %s

"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>>, sym_name = "f"}> ({
  ^bb0(%a : !cir.int<s, 32>, %b : !cir.int<u, 8>):
    %s = "cir.add"(%a, %a) <{no_signed_wrap, no_unsigned_wrap = false, saturated = false}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %d = "cir.div"(%s, %a) : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    %u = "cir.div"(%b, %b) : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.int<u, 8>
    %sh = "cir.shift"(%d, %b) : (!cir.int<s, 32>, !cir.int<u, 8>) -> !cir.int<s, 32>
    %lt = "cir.cmp"(%sh, %a) <{kind = 0 : i32}> : (!cir.int<s, 32>, !cir.int<s, 32>) -> !cir.bool
    %ult = "cir.cmp"(%u, %b) <{kind = 0 : i32}> : (!cir.int<u, 8>, !cir.int<u, 8>) -> !cir.bool
    %sel = "cir.select"(%lt, %sh, %a) : (!cir.bool, !cir.int<s, 32>, !cir.int<s, 32>) -> !cir.int<s, 32>
    "cir.return"(%sel) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "cir.func"() <{"function_type" = !cir.func<(i32, i8) -> i32>, "sym_name" = "f"}> ({
// CHECK-NEXT: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i8):
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.divsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.extui"(%{{.*}}) : (i8) -> i32
// CHECK-NEXT: %{{.*}} = "arith.shrsi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.cmpi"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
// CHECK-NEXT: %{{.*}} = "arith.select"(%{{.*}}, %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
// CHECK-NEXT: "cir.return"(%{{.*}}) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
