import Veir.Parser.MlirParser
import Veir.Verifier

open Veir
open Veir.Parser

/--
Build a well-formed IR context with one deliberately invalid CFG edge. The
source and target blocks belong to distinct regions, which cannot be expressed
through the MLIR parser because block references are region-scoped.

The resulting IR has this shape (the dashed arrow is the invalid successor):

```text
module
└─ moduleRegion
   └─ moduleBlock
      ├─ test.test op
      │  └─ sourceRegion
      │     └─ sourceBlock
      │        └─ cf.br ─ ─ ─ ┐
      └─ test.test op         │
         └─ targetRegion      │ invalid cross-region edge
            └─ targetBlock ◀─ ┘
```
-/
private def contextWithCrossRegionSuccessor :
    Except String (WfIRContext OpCode × OperationPtr) := do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let moduleRegion := moduleOp.getRegion! ctx.raw 0
  let moduleBlock := (moduleRegion.get! ctx.raw).firstBlock.get!

  let (ctx, sourceRegion) := WfRewriter.createRegion! ctx
  let (ctx, sourceBlock) :=
    WfRewriter.createBlock! ctx #[] (some (.atEnd sourceRegion))

  let (ctx, targetRegion) := WfRewriter.createRegion! ctx
  let (ctx, targetBlock) :=
    WfRewriter.createBlock! ctx #[] (some (.atEnd targetRegion))

  let (ctx, _) :=
      (WfRewriter.createOp! ctx Test.test #[] #[] #[] #[sourceRegion] ()
        (some (.atEnd moduleBlock))).get!
  let (ctx, _) :=
      (WfRewriter.createOp! ctx Test.test #[] #[] #[] #[targetRegion] ()
        (some (.atEnd moduleBlock))).get!

  let (ctx, _) :=
      (WfRewriter.createOp! ctx Cf.br #[] #[] #[targetBlock] #[] ()
        (some (.atEnd sourceBlock))).get!
  return (ctx, moduleOp)

private def verifyCrossRegionSuccessor : Except String Unit := do
  let (ctx, moduleOp) ← contextWithCrossRegionSuccessor
  ctx.verify moduleOp

#guard verifyCrossRegionSuccessor =
  .error "Block successors must belong to the same region as their predecessor"

/-! ## Signedness through the parser and the verifier

Builtin integer types compare with their signedness, so `i32`, `si32` and `ui32`
are three distinct types. These tests parse generic-form programs and run the
verifier on them, so every check goes through the existing dialect verifiers.
-/

/-- Parse a top-level operation and run the verifier on it, printing the outcome. -/
private def verifyProgram (s : String) : IO Unit := do
  let some (ctx, _) := WfIRContext.create OpCode
    | IO.println "internal error: failed to create IR context"
  let result : Except String Unit := do
    let parser ← (ParserState.fromInput s.toByteArray).mapError toString
    let (op, state, _) ← (parseTopLevelOp.run (MlirParserState.fromContext ctx) parser).mapError toString
    state.ctx.verify op
  match result with
  | .ok () => IO.println "verified"
  | .error err => IO.println s!"error: {err}"

-- Signed and unsigned integers are ordinary types for func.func and func.return.
/-- info: verified -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si32, ui8) -> si32, sym_name = "f"}> ({
  ^bb0(%a: si32, %b: ui8):
    "func.return"(%a) : (si32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- cf.br forwards an si32 operand to an si32 block argument.
/-- info: verified -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si32) -> si32, sym_name = "f"}> ({
  ^bb0(%a: si32):
    "cf.br"(%a) [^bb1] : (si32) -> ()
  ^bb1(%b: si32):
    "func.return"(%b) : (si32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- builtin.unrealized_conversion_cast bridges between signednesses of the same width.
/-- info: verified -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si32) -> i32, sym_name = "f"}> ({
  ^bb0(%a: si32):
    %b = "builtin.unrealized_conversion_cast"(%a) : (si32) -> i32
    "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- llvm.mlir.constant only asks for an integer result type, so a signed value attribute may feed an i32 result, as in MLIR.
/-- info: verified -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "f"}> ({
    %c = "llvm.mlir.constant"() <{value = 5 : si32}> : () -> i32
    "func.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- A signless i32 does not satisfy a declared si32 result.
/-- info: error: func.return operand 0 type does not match the function's declared result type -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (i32) -> si32, sym_name = "f"}> ({
  ^bb0(%a: i32):
    "func.return"(%a) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- Block arguments compare with their signedness.
/-- info: error: cf.br: successor argument 0 type mismatch: operand has type i32, block argument has type si32 -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (i32) -> si32, sym_name = "f"}> ({
  ^bb0(%a: i32):
    "cf.br"(%a) [^bb1] : (i32) -> ()
  ^bb1(%b: si32):
    "func.return"(%b) : (si32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- Mixing si32 and i32 operands is a type mismatch for arith binary operations.
/-- info: error: arith.addi: Expected operands to have the same type -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si32, i32) -> si32, sym_name = "f"}> ({
  ^bb0(%a: si32, %b: i32):
    %sum = "arith.addi"(%a, %b) : (si32, i32) -> si32
    "func.return"(%sum) : (si32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- The result must carry the operands' signedness too.
/-- info: error: arith.addi: Expected result type to match operand type -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si32) -> i32, sym_name = "f"}> ({
  ^bb0(%a: si32):
    %sum = "arith.addi"(%a, %a) : (si32, si32) -> i32
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- arith.constant requires the value attribute's type to equal the result type.
/-- info: error: arith.constant: Expected result type to be equal to the constant's type -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "f"}> ({
    %c = "arith.constant"() <{value = 5 : si32}> : () -> i32
    "func.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- arith.cmpi operands must agree on signedness.
/-- info: error: arith.cmpi: Expected operands to have the same type -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si32, ui32) -> i1, sym_name = "f"}> ({
  ^bb0(%a: si32, %b: ui32):
    %cmp = "arith.cmpi"(%a, %b) <{predicate = 0 : i64}> : (si32, ui32) -> i1
    "func.return"(%cmp) : (i1) -> ()
  }) : () -> ()
}) : () -> ()"#

-- arith.select values must agree on signedness.
/-- info: error: arith.select: Expected select values to have the same type -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (i1, si32, i32) -> si32, sym_name = "f"}> ({
  ^bb0(%c: i1, %a: si32, %b: i32):
    %sel = "arith.select"(%c, %a, %b) : (i1, si32, i32) -> si32
    "func.return"(%sel) : (si32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- A condition must be the signless i1: si1 has the width but not the type.
/-- info: error: cf.cond_br: Expected i1 condition -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si1) -> (), sym_name = "f"}> ({
  ^bb0(%c: si1):
    "cf.cond_br"(%c) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (si1) -> ()
  ^bb1:
    "func.return"() : () -> ()
  ^bb2:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

-- llvm.cond_br applies the same rule to its condition.
/-- info: error: llvm.cond_br: Expected i1 condition -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (ui1) -> (), sym_name = "f"}> ({
  ^bb0(%c: ui1):
    "llvm.cond_br"(%c) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (ui1) -> ()
  ^bb1:
    "func.return"() : () -> ()
  ^bb2:
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

-- arith.cmpi produces the signless i1, not ui1.
/-- info: error: arith.cmpi: Expected i1 result -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (i32) -> (), sym_name = "f"}> ({
  ^bb0(%a: i32):
    %cmp = "arith.cmpi"(%a, %a) <{predicate = 0 : i64}> : (i32, i32) -> ui1
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#

-- arith.select takes the signless i1 as condition.
/-- info: error: arith.select: Expected i1 condition -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (si1, i32) -> i32, sym_name = "f"}> ({
  ^bb0(%c: si1, %a: i32):
    %sel = "arith.select"(%c, %a, %a) : (si1, i32, i32) -> i32
    "func.return"(%sel) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- Attributes constrained to a signless integer type reject a signed one of the same width.
/-- info: error: llvm.load: 'llvm.load' op attribute 'alignment' failed to satisfy constraint: 64-bit signless integer attribute -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr) -> i32, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %v = "llvm.load"(%p) <{alignment = 4 : si64}> : (!llvm.ptr) -> i32
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()"#

-- llvm.mlir.global alignment must be a signless i64.
/-- info: error: llvm.mlir.global: 'alignment' must be a 64-bit signless integer attribute -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : si64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()"#

-- llvm.mlir.global addr_space must be a signless i32.
/-- info: error: llvm.mlir.global: 'addr_space' must be a 32-bit signless integer attribute -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : ui32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()"#

-- riscv_stack.alloca size must be a signless i64.
/-- info: error: riscv_stack.alloca: attribute 'size' must be a 64-bit signless integer attribute -/
#guard_msgs in #eval! verifyProgram r#""builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "f"}> ({
    %s = "riscv_stack.alloca"() <{size = 8 : ui64, alignment = 8 : i64}> : () -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()"#
