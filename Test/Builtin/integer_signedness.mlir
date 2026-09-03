// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// Builtin integer types carry a signedness: `i32` is signless, `si32` is
// signed and `ui32` is unsigned. The signedness is part of the type, so it
// survives a round trip through types, function types and integer attributes.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "test.test"() : () -> si32
      %1 = "test.test"() : () -> ui8
      %2 = "test.test"(%0, %1) : (si32, ui8) -> ((si64) -> ui1)
      %3 = "test.test"() {negative = -1 : si8, signed = 5 : si32, unsigned = 200 : ui8} : () -> i32
      %4 = "test.test"() {da = array<si32: 1, -2>} : () -> i32
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NEXT: "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[V0:[^ ]+]] = "test.test"() : () -> si32
// CHECK-NEXT:         %[[V1:[^ ]+]] = "test.test"() : () -> ui8
// CHECK-NEXT:         %{{.*}} = "test.test"(%[[V0]], %[[V1]]) : (si32, ui8) -> ((si64) -> ui1)
// CHECK-NEXT:         %{{.*}} = "test.test"() {"negative" = -1 : si8, "signed" = 5 : si32, "unsigned" = 200 : ui8} : () -> i32
// CHECK-NEXT:         %{{.*}} = "test.test"() {"da" = array<si32: 1, -2>} : () -> i32
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
