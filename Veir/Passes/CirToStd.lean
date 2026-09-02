module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.DCE.dce
import Veir.Interfaces.FunctionInterfaces

namespace Veir

/-!
  # CirToStd pass

  Lowers the `cir` dialect's integer core into the `arith`, `cf` and `llvm` dialects.
  `cir.func` and `cir.return` stay in place: the rewriter cannot change an operation's
  opcode or move its region, so the function operation keeps its `cir` spelling while its
  boundary types are converted.

  Since VeIR has no dialect-conversion framework, the pass works in four phases:
  1. each `cir` value operation is rewritten in place, casting its operands to the builtin
     type with `builtin.unrealized_conversion_cast`, emitting the `arith` operation, and
     casting the result back;
  2. function boundaries (entry-block arguments, return operands, `function_type`) are
     converted;
  3. the arguments of every other block, and the operands of the branches feeding them,
     are converted;
  4. the cast pairs that cancel are reconciled and dead casts removed.
-/

/-! ## Types -/

/-- The builtin type a `cir` type lowers to, or `none` for types this pass leaves alone. -/
def cirTypeToStd (t : TypeAttr) : Option TypeAttr :=
  match t.val with
  | .cirIntType it => some (IntegerType.mk it.width : TypeAttr)
  | .cirBoolType _ => some (IntegerType.mk 1 : TypeAttr)
  | _ => none

/-- Whether a `cir` type and a builtin type are each other's lowering. -/
def isCirRoundTrip (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .cirIntType it, .integerType i => i.bitwidth = it.width
  | .integerType i, .cirIntType it => i.bitwidth = it.width
  | .cirBoolType _, .integerType i => i.bitwidth = 1
  | .integerType i, .cirBoolType _ => i.bitwidth = 1
  | _, _ => false

/-- The signedness of a `!cir.int` type; `!cir.bool` counts as unsigned. -/
def cirIsSigned (t : TypeAttr) : Bool :=
  match t.val with
  | .cirIntType it => it.isSigned
  | _ => false

/-! ## Casts and helpers -/

/-- Emit `unrealized_conversion_cast v : !cir.* → builtin`. -/
def castToStd (rewriter : PatternRewriter OpCode) (v : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let stdType ← cirTypeToStd (v.getType! rewriter.ctx.raw)
  let (rewriter, castOp) ← rewriter.createOp! (.builtin .unrealized_conversion_cast)
    #[stdType] #[v] #[] #[] () (some ip)
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-- Emit `unrealized_conversion_cast x : builtin → ty`, where `ty` is a `cir` type. -/
def castToCir (rewriter : PatternRewriter OpCode) (x : ValuePtr) (ty : TypeAttr)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, castOp) ← rewriter.createOp! (.builtin .unrealized_conversion_cast)
    #[ty] #[x] #[] #[] () (some ip)
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-- Emit `arith.constant c : i<width>`. -/
def emitStdConstant (rewriter : PatternRewriter OpCode) (c : Int) (width : Nat)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let ty : TypeAttr := IntegerType.mk width
  let props : ArithConstantProperties := { value := IntegerAttr.mk c (IntegerType.mk width) }
  let (rewriter, c) ← rewriter.createOp! (.arith .constant) #[ty] #[] #[] #[] props (some ip)
  return (rewriter, (c.getResult 0 : ValuePtr))

/-- Emit an `arith` operation `arithOp` with result type `ty` on `operands`. -/
def emitArith (rewriter : PatternRewriter OpCode) (arithOp : Arith)
    (props : Arith.propertiesOf arithOp) (ty : TypeAttr) (operands : Array ValuePtr)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, r) ← rewriter.createOp! (.arith arithOp) #[ty] operands #[] #[] props (some ip)
  return (rewriter, (r.getResult 0 : ValuePtr))

def noOverflow : ArithIntegerOverflowFlagsProperties := { attr := { nsw := false, nuw := false } }

/-- Bring an integer value to `width` bits, zero-extending or truncating as needed. -/
def resizeUnsigned (rewriter : PatternRewriter OpCode) (v : ValuePtr) (width : Nat)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let .integerType vt := (v.getType! rewriter.ctx.raw).val | none
  let ty : TypeAttr := IntegerType.mk width
  if vt.bitwidth < width then
    emitArith rewriter .extui { nneg := false } ty #[v] ip
  else if vt.bitwidth > width then
    emitArith rewriter .trunci noOverflow ty #[v] ip
  else
    return (rewriter, v)

/-! ## Value operations

A `StdBuilder` receives the operands already cast to their builtin types, the original
`cir` operand types (for signedness), and the builtin result type, and emits the builtin
computation.
-/

abbrev StdBuilder :=
  (rewriter : PatternRewriter OpCode) → (operands : Array ValuePtr) →
  (cirOperandTypes : Array TypeAttr) → (resultType : TypeAttr) → (ip : InsertPoint) →
  Option (PatternRewriter OpCode × ValuePtr)

/--
  Lower a single-result `cir` operation `cirOp` with `numOperands` operands: cast the operands
  to builtin types, run `build`, cast the result back to the operation's `cir` result type,
  and erase the operation. `build` may inspect the properties; returning `none` from it aborts
  the pass, which is how unsupported flags are reported.
-/
def lowerValueOp (cirOp : Cir) (numOperands : Nat)
    (build : Cir.propertiesOf cirOp → StdBuilder)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx.raw cirOp numOperands
    | return rewriter
  let ip := InsertPoint.before op
  let cirResultType := (op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw
  let some stdResultType := cirTypeToStd cirResultType | none
  let cirOperandTypes := operands.map (·.getType! rewriter.ctx.raw)
  let mut rw := rewriter
  let mut stdOperands : Array ValuePtr := #[]
  for v in operands do
    let (rw', s) ← castToStd rw v ip
    rw := rw'
    stdOperands := stdOperands.push s
  let (rewriter, result) ← build props rw stdOperands cirOperandTypes stdResultType ip
  let (rewriter, back) ← castToCir rewriter result cirResultType ip
  let rewriter := rewriter.replaceValue! (op.getResult 0) back
  return rewriter.eraseOp! op

/-- `cir.const` → `arith.constant`. -/
def lowerConst := lowerValueOp .const 0 fun props rewriter _ _ resultType ip => do
  let .integerType rt := resultType.val | none
  match props.value with
  | .int attr => emitStdConstant rewriter attr.value rt.bitwidth ip
  | .bool attr => emitStdConstant rewriter (if attr.value then 1 else 0) rt.bitwidth ip

/-- `cir.add` → `arith.addi`; the saturating form is rejected. -/
def lowerAdd := lowerValueOp .add 2 fun props rewriter operands _ resultType ip => do
  if props.flagSet "saturated" then none
  emitArith rewriter .addi noOverflow resultType operands ip

/-- `cir.sub` → `arith.subi`; the saturating form is rejected. -/
def lowerSub := lowerValueOp .sub 2 fun props rewriter operands _ resultType ip => do
  if props.flagSet "saturated" then none
  emitArith rewriter .subi noOverflow resultType operands ip

/-- A binary operation whose `arith` counterpart does not depend on signedness. -/
def lowerBinOp (cirOp : Cir) (arithOp : Arith) (props : Arith.propertiesOf arithOp) :=
  lowerValueOp cirOp 2 fun _ rewriter operands _ resultType ip =>
    emitArith rewriter arithOp props resultType operands ip

def lowerMul := lowerBinOp .mul .muli noOverflow
def lowerAnd := lowerBinOp .and .andi ()
def lowerOr := lowerBinOp .or .ori { disjoint := false }
def lowerXor := lowerBinOp .xor .xori ()

/-- A binary operation whose `arith` counterpart is chosen by the operands' signedness. -/
def lowerSignedBinOp (cirOp : Cir) (signedOp unsignedOp : Arith)
    (signedProps : Arith.propertiesOf signedOp) (unsignedProps : Arith.propertiesOf unsignedOp) :=
  lowerValueOp cirOp 2 fun _ rewriter operands cirTypes resultType ip =>
    if cirIsSigned cirTypes[0]! then
      emitArith rewriter signedOp signedProps resultType operands ip
    else
      emitArith rewriter unsignedOp unsignedProps resultType operands ip

def lowerDiv := lowerSignedBinOp .div .divsi .divui { exact := false } { exact := false }
def lowerRem := lowerSignedBinOp .rem .remsi .remui () ()
def lowerMin := lowerSignedBinOp .min .minsi .minui () ()
def lowerMax := lowerSignedBinOp .max .maxsi .maxui () ()

/-- `cir.shift` → `arith.shli`, or `shrsi`/`shrui` by the value's signedness. -/
def lowerShift := lowerValueOp .shift 2 fun props rewriter operands cirTypes resultType ip => do
  let .integerType rt := resultType.val | none
  let (rewriter, amount) ← resizeUnsigned rewriter operands[1]! rt.bitwidth ip
  let operands := #[operands[0]!, amount]
  if props.isShiftleft then
    emitArith rewriter .shli noOverflow resultType operands ip
  else if cirIsSigned cirTypes[0]! then
    emitArith rewriter .shrsi { exact := false } resultType operands ip
  else
    emitArith rewriter .shrui { exact := false } resultType operands ip

/-- `cir.not` → `arith.xori` with all ones. -/
def lowerNot := lowerValueOp .not 1 fun _ rewriter operands _ resultType ip => do
  let .integerType rt := resultType.val | none
  let (rewriter, ones) ← emitStdConstant rewriter (-1) rt.bitwidth ip
  emitArith rewriter .xori () resultType #[operands[0]!, ones] ip

/-- `cir.minus` → `arith.subi` from zero. -/
def lowerMinus := lowerValueOp .minus 1 fun _ rewriter operands _ resultType ip => do
  let .integerType rt := resultType.val | none
  let (rewriter, zero) ← emitStdConstant rewriter 0 rt.bitwidth ip
  emitArith rewriter .subi noOverflow resultType #[zero, operands[0]!] ip

/-- The `arith.cmpi` predicate for a `cir.cmp` kind on operands of the given signedness. -/
def cmpPredicate (kind : CirCmpKind) (signed : Bool) : Data.LLVM.IntPred :=
  match kind, signed with
  | .eq, _ => .eq
  | .ne, _ => .ne
  | .lt, true => .slt
  | .lt, false => .ult
  | .le, true => .sle
  | .le, false => .ule
  | .gt, true => .sgt
  | .gt, false => .ugt
  | .ge, true => .sge
  | .ge, false => .uge

/-- `cir.cmp` → `arith.cmpi`. -/
def lowerCmp := lowerValueOp .cmp 2 fun props rewriter operands cirTypes resultType ip =>
  emitArith rewriter .cmpi { predicate := cmpPredicate props.kind (cirIsSigned cirTypes[0]!) }
    resultType operands ip

/-- `cir.select` → `arith.select`. -/
def lowerSelect := lowerValueOp .select 3 fun _ rewriter operands _ resultType ip =>
  emitArith rewriter .select () resultType operands ip

/-- `cir.cast` for the integral, int_to_bool and bool_to_int kinds. -/
def lowerCast := lowerValueOp .cast 1 fun props rewriter operands cirTypes resultType ip => do
  let src := operands[0]!
  let .integerType st := (src.getType! rewriter.ctx.raw).val | none
  let .integerType rt := resultType.val | none
  match props.kind with
  | .integral | .bool_to_int =>
    if st.bitwidth = rt.bitwidth then
      return (rewriter, src)
    else if st.bitwidth < rt.bitwidth then
      if cirIsSigned cirTypes[0]! then
        emitArith rewriter .extsi () resultType #[src] ip
      else
        emitArith rewriter .extui { nneg := false } resultType #[src] ip
    else
      emitArith rewriter .trunci noOverflow resultType #[src] ip
  | .int_to_bool =>
    let (rewriter, zero) ← emitStdConstant rewriter 0 st.bitwidth ip
    emitArith rewriter .cmpi { predicate := .ne } resultType #[src, zero] ip
  | .other _ => none

/-! ## Terminators -/

/-- `cir.br` → `cf.br`, forwarding the operands unchanged. -/
def lowerBr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .cir .br then return rewriter
  let (rewriter, _) ← rewriter.createOp! (.cf .br) #[] (op.getOperands! rewriter.ctx.raw)
    (op.getSuccessors! rewriter.ctx.raw) #[] () (some (InsertPoint.before op))
  return rewriter.eraseOp! op

/-- `cir.brcond` → `cf.cond_br`, casting only the condition. -/
def lowerBrCond (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .cir .brcond then return rewriter
  let props : CirBrCondProperties := op.getProperties! rewriter.ctx.raw Cir.brcond
  let operands := op.getOperands! rewriter.ctx.raw
  let ip := InsertPoint.before op
  let (rewriter, cond) ← castToStd rewriter operands[0]! ip
  let cfProps : CondBrProperties :=
    { branch_weights := { elementType := { bitwidth := 32 }, values := #[] }
      operandSegmentSizes := props.operandSegmentSizes }
  let (rewriter, _) ← rewriter.createOp! (.cf .cond_br) #[]
    (#[cond] ++ operands.extract 1 operands.size) (op.getSuccessors! rewriter.ctx.raw) #[]
    cfProps (some ip)
  return rewriter.eraseOp! op

/-- `cir.unreachable` → `llvm.unreachable`. -/
def lowerUnreachable (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.getOpType! rewriter.ctx.raw ≠ .cir .unreachable then return rewriter
  let (rewriter, _) ← rewriter.createOp! (.llvm .unreachable) #[] #[] #[] #[] ()
    (some (InsertPoint.before op))
  return rewriter.eraseOp! op

/-! ## Boundaries -/

/--
  Convert one `cir.func`'s boundary: entry-block arguments, `cir.return` operands and the
  `function_type`, bridging with casts. This mirrors `coerceFunction` in the function
  boundary coercion pass, specialised to the `cir` type map.
-/
def convertCirFunction (ctx : WfIRContext OpCode) (funcOp : OperationPtr) :
    WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let some entry := FunctionOpInterface.getEntryBlock? funcOp ctx.raw | return ctx
  let mut outputs : Array Attribute := FunctionOpInterface.getResultTypes! funcOp ctx.raw
  -- (1) Entry-block arguments: retype in place and cast back to the original type.
  let mut inputs : Array Attribute := #[]
  for i in List.range (entry.getNumArguments! ctx.raw) do
    let bap : BlockArgumentPtr := { block := entry, index := i }
    let origType := (ValuePtr.blockArgument bap).getType! ctx.raw
    match cirTypeToStd origType with
    | some newType =>
      ctx := WfRewriter.setType! ctx bap newType
      let ip := InsertPoint.atStart! entry ctx.raw
      let some (ctx', cast) := WfRewriter.createOp! ctx (OpCode.builtin .unrealized_conversion_cast)
        #[origType] #[] #[] #[] () (some ip) | return ctx
      let ctx' := WfRewriter.replaceValue! ctx' bap (cast.getResult 0)
      ctx := WfRewriter.pushOperand! ctx' cast bap
      inputs := inputs.push newType.val
    | none =>
      inputs := inputs.push origType.val
  -- (2) Return operands: cast to the builtin type before the return.
  let returnOps := ctx.raw.operations.keys.filter fun o =>
    o.getOpType! ctx.raw == .cir .return && o.getParentOp! ctx.raw == some funcOp
  for retOp in returnOps do
    for j in List.range (retOp.getNumOperands! ctx.raw) do
      let opVal := retOp.getOperand! ctx.raw j
      match cirTypeToStd (opVal.getType! ctx.raw) with
      | some newType =>
        let some (ctx', cast) := WfRewriter.createOp! ctx
          (OpCode.builtin .unrealized_conversion_cast) #[newType] #[opVal] #[] #[] ()
          (some (InsertPoint.before retOp)) | return ctx
        ctx := WfRewriter.replaceOperand! ctx' ⟨retOp, j⟩ (cast.getResult 0)
        outputs := outputs.set! j newType.val
      | none => pure ()
  -- (3) The declared function type follows the converted boundary.
  return FunctionOpInterface.setFunctionType! ctx funcOp inputs outputs

/--
  Convert the arguments of a block with predecessors: cast the forwarded operands of every
  predecessor branch, then retype the arguments and cast them back at the block start.
  This mirrors `convertBlock` in the RISC-V branch selection.
-/
def convertCirBlock (ctx : WfIRContext OpCode) (block : BlockPtr) : WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  if (block.get! ctx.raw).firstUse == none then return ctx
  let coercible := (List.range (block.getNumArguments! ctx.raw)).any fun i =>
    (cirTypeToStd ((ValuePtr.blockArgument { block, index := i }).getType! ctx.raw)).isSome
  if !coercible then return ctx
  -- Collect the predecessors first: rewriting them mutates the use chain.
  let mut predOps : Array OperationPtr := #[]
  let mut currentPredUse := (block.get! ctx.raw).firstUse
  while let some blockop := currentPredUse do
    let blockOperand := blockop.get! ctx.raw
    currentPredUse := blockOperand.nextUse
    if !predOps.contains blockOperand.owner then
      predOps := predOps.push blockOperand.owner
  for predOp in predOps do
    for j in List.range (predOp.getNumOperands! ctx.raw) do
      let opVal := predOp.getOperand! ctx.raw j
      match cirTypeToStd (opVal.getType! ctx.raw) with
      | some newType =>
        let some (ctx', cast) := WfRewriter.createOp! ctx
          (OpCode.builtin .unrealized_conversion_cast) #[newType] #[opVal] #[] #[] ()
          (some (InsertPoint.before predOp)) | return ctx
        ctx := WfRewriter.replaceOperand! ctx' ⟨predOp, j⟩ (cast.getResult 0)
      | none => pure ()
  for i in List.range (block.getNumArguments! ctx.raw) do
    let bap : BlockArgumentPtr := { block, index := i }
    let origType := (ValuePtr.blockArgument bap).getType! ctx.raw
    let some newType := cirTypeToStd origType | continue
    ctx := WfRewriter.setType! ctx bap newType
    let ip := InsertPoint.atStart! block ctx.raw
    let some (ctx', cast) := WfRewriter.createOp! ctx (OpCode.builtin .unrealized_conversion_cast)
      #[origType] #[] #[] #[] () (some ip) | return ctx
    let ctx' := WfRewriter.replaceValue! ctx' bap (cast.getResult 0)
    ctx := WfRewriter.pushOperand! ctx' cast bap
  return ctx

/-! ## Reconciliation -/

/--
  Reconcile `X → Y → X` cast round trips between `cir` and builtin types. The parent cast is
  left to DCE, as a `LocalRewritePattern` may only erase the matched operation.
-/
def reconcileCirCastLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some input := matchCastOp op ctx.raw | return (ctx, none)
  let interType := input.getType! ctx.raw
  let resultType := ((op.getResult 0).get! ctx.raw).type
  let .opResult op' := input | return (ctx, none)
  let some parentInput := matchCastOp op'.op ctx.raw | return (ctx, none)
  let inputType := parentInput.getType! ctx.raw
  if resultType ≠ inputType then return (ctx, none)
  if !isCirRoundTrip inputType interType then return (ctx, none)
  return (ctx, some (#[], #[parentInput]))

/-! ## Pass implementation -/

def CirToStdPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  -- (1) Value operations and terminators.
  let lowering := RewritePattern.GreedyRewritePattern #[
    lowerConst, lowerAdd, lowerSub, lowerMul, lowerDiv, lowerRem,
    lowerAnd, lowerOr, lowerXor, lowerShift, lowerNot, lowerMinus,
    lowerMin, lowerMax, lowerCmp, lowerSelect, lowerCast,
    lowerBr, lowerBrCond, lowerUnreachable
  ]
  let some lowered := RewritePattern.applyInContext lowering ctx
    | throw "Error while applying cir-to-std lowering (unsupported operation or flag)"
  -- (2) Function boundaries, (3) block arguments.
  let mut converted := lowered
  let funcOps := converted.raw.operations.keys.filter fun o =>
    o.getOpType! converted.raw == .cir .func
  for funcOp in funcOps do
    converted := convertCirFunction converted funcOp
  for block in converted.raw.blocks.keys do
    converted := convertCirBlock converted block
  -- (4) Cancel cast round trips and drop the dead casts they leave behind.
  let reconcile := RewritePattern.GreedyRewritePattern #[
    .fromLocalRewrite reconcileCirCastLocal, eliminateDeadOp]
  let some reconciled := RewritePattern.applyInContext reconcile converted
    | throw "Error while reconciling casts after cir-to-std lowering"
  -- Nothing but the function shell may remain.
  for o in reconciled.raw.operations.keys do
    if let .cir cirOp := o.getOpType! reconciled.raw then
      if cirOp ≠ .func && cirOp ≠ .return then
        throw s!"cir-to-std: operation '{String.fromUTF8! (IsOpCode.name cirOp)}' was not lowered"
  return reconciled

public def CirToStdPass : Pass OpCode :=
  { name := "cir-to-std"
    description := "Lower the cir dialect's integer core to the arith, cf and llvm dialects."
    run := fun _ => CirToStdPass.impl }

end Veir
