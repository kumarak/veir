// RUN: veir-opt %s -p=cir-to-std,reconcile-cast | filecheck %s

// Local memory lowers to the llvm memory operations: `!cir.ptr<T>` becomes the opaque
// `!llvm.ptr`, the pointee only decides the alloca's element type and the loaded or stored
// builtin type. A pointer bitcast is the identity on opaque pointers.
"builtin.module"() ({
  "cir.func"() <{function_type = !cir.func<(!cir.int<s, 32>, !cir.ptr<!cir.int<u, 8>>) -> !cir.int<s, 32>>, sym_name = "memory"}> ({
  ^bb0(%n : !cir.int<s, 32>, %q : !cir.ptr<!cir.int<u, 8>>):
    %x = "cir.alloca"() <{alignment = 4 : i64, init, name = "x"}> : () -> !cir.ptr<!cir.int<s, 32>>
    "cir.store"(%n, %x) <{alignment = 4 : i64}> : (!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> ()
    %v = "cir.load"(%x) <{alignment = 4 : i64}> : (!cir.ptr<!cir.int<s, 32>>) -> !cir.int<s, 32>
    %arr = "cir.alloca"(%n) <{alignment = 4 : i64, name = "arr"}> : (!cir.int<s, 32>) -> !cir.ptr<!cir.int<s, 32>>
    "cir.store"(%v, %arr) : (!cir.int<s, 32>, !cir.ptr<!cir.int<s, 32>>) -> ()
    %p = "cir.cast"(%q) <{kind = 1 : i32}> : (!cir.ptr<!cir.int<u, 8>>) -> !cir.ptr<!cir.int<s, 32>>
    %w = "cir.load"(%p) : (!cir.ptr<!cir.int<s, 32>>) -> !cir.int<s, 32>
    "cir.return"(%w) : (!cir.int<s, 32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "cir.func"() <{"function_type" = !cir.func<(!cir.int<s, 32>, !cir.ptr<!cir.int<u, 8>>) -> !cir.int<s, 32>>, "sym_name" = "memory"}> ({
// CHECK-NEXT: ^{{.*}}([[N:%.*]] : !cir.int<s, 32>, [[Q:%.*]] : !cir.ptr<!cir.int<u, 8>>):
// CHECK-NEXT: [[ONE:%.*]] = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: [[X:%.*]] = "llvm.alloca"([[ONE]]) <{"alignment" = 4 : i64, "elem_type" = i32}> : (i64) -> !llvm.ptr
// CHECK-NEXT: [[N0:%.*]] = "builtin.unrealized_conversion_cast"([[N]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: "llvm.store"([[N0]], [[X]]){{.*}}: (i32, !llvm.ptr) -> ()
// CHECK-NEXT: [[V:%.*]] = "llvm.load"([[X]]){{.*}}: (!llvm.ptr) -> i32
// CHECK-NEXT: [[N1:%.*]] = "builtin.unrealized_conversion_cast"([[N]]) : (!cir.int<s, 32>) -> i32
// CHECK-NEXT: [[ARR:%.*]] = "llvm.alloca"([[N1]]) <{"alignment" = 4 : i64, "elem_type" = i32}> : (i32) -> !llvm.ptr
// CHECK-NEXT: "llvm.store"([[V]], [[ARR]]){{.*}}: (i32, !llvm.ptr) -> ()
// CHECK-NEXT: [[Q0:%.*]] = "builtin.unrealized_conversion_cast"([[Q]]) : (!cir.ptr<!cir.int<u, 8>>) -> !llvm.ptr
// CHECK-NEXT: [[W:%.*]] = "llvm.load"([[Q0]]){{.*}}: (!llvm.ptr) -> i32
// CHECK-NEXT: [[WC:%.*]] = "builtin.unrealized_conversion_cast"([[W]]) : (i32) -> !cir.int<s, 32>
// CHECK-NEXT: "cir.return"([[WC]]) : (!cir.int<s, 32>) -> ()
