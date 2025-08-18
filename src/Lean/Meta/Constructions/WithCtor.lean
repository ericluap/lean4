/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.AddDecl
public import Lean.Meta.AppBuilder
public import Lean.Meta.CompletionName
import Lean.Meta.Constructions.ToCtorIdx
import Lean.Meta.NatTable

namespace Lean

open Meta

def deps : Array Lean.Name :=
  #[ ``cond, ``ULift, ``Eq.ndrec, ``Not, ``dite, ``Nat.decEq, ``Nat.blt ]

def canUse : MetaM Bool := deps.allM (hasConst · (skipRealize := true))

-- Right-associates the top-most `max`s to work around #5695 for prettier code
def reassocMax (l : Level) : Level :=
  let lvls := maxArgs l #[]
  let last := lvls.back!
  lvls.pop.foldr mkLevelMax last
where
  maxArgs (l : Level) (lvls : Array Level) : Array Level :=
  match l with
  | .max l1 l2 => maxArgs l2 (maxArgs l1 lvls)
  | _ => lvls.push l

def maxLevels (es : Array Expr) : MetaM Level := do
  assert! es.size > 0
  let mut maxLevel ← getLevel es[0]!
  for e in es[1...*] do
    let l ← getLevel e
    maxLevel := mkLevelMax' maxLevel l
  return reassocMax maxLevel.normalize

def mkPULift (r : Level) (t : Expr) : MetaM Expr := do
  let s ← getLevel t
  return mkApp (mkConst `PULift [r,s]) t

def withMkPULiftUp (t : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let t ← whnf t
  if t.isAppOfArity `PULift 1 then
    let t' := t.appArg!
    let e ← k t'
    return mkApp2 (mkConst `PULift.up (t.appFn!.constLevels!)) t' e
  else
    throwError "withMkPULiftUp: expected PULift type, got {t}"

def mkPULiftDown (e : Expr) : MetaM Expr := do
  let t ← whnf (← inferType e)
  if t.isAppOfArity `PULift 1 then
    let t' := t.appArg!
    return mkApp2 (mkConst `PULift.down t.appFn!.constLevels!) t' e
  else
    throwError "mkULiftDown: expected ULift type, got {t}"

def mkNatLookupTableLifting (n : Expr) (es : Array Expr) : MetaM Expr := do
  let u ← maxLevels es
  let u' := reassocMax (mkLevelMax' u 1).normalize
  let es ← es.mapM (mkPULift u)
  mkNatLookupTable n (.sort u') es

def mkToCtorIdxName (indName : Name) : Name :=
  Name.str indName "toCtorIdx"

def mkWithCtorTypeName (indName : Name) : Name :=
  Name.str indName "withCtorType"

def mkWithCtorName (indName : Name) : Name :=
  Name.str indName "withCtor"

def mkCtorWithName (indName : Name) : Name :=
  Name.str indName "with"

def mkWithCtorType (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  if info.numCtors = 0 then return
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let e ← forallTelescope casesOnInfo.type fun xs _ =>
    let params : Array Expr := xs[:info.numParams]
    let motive := xs[info.numParams]!
    -- let indices : Array Expr := xs[info.numParams + 1:info.numParams + 1 + info.numIndices]
    -- let majorArg := xs[info.numParams + 1 + info.numIndices]!
    let alts : Array Expr := xs[info.numParams + 1 + info.numIndices + 1:]
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
      let es ← alts.mapM inferType
      let e ← mkNatLookupTableLifting ctorIdx es
      mkLambdaFVars (params ++ #[motive, ctorIdx]) e

  let declName := mkWithCtorTypeName indName
  addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)
  ))
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  setReducibleAttribute declName

def mkIndWithCtor (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let withCtorTypeName := mkWithCtorTypeName indName
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let e ← forallTelescope casesOnInfo.type fun xs _ =>
    let params : Array Expr := xs[:info.numParams]
    let motive := xs[info.numParams]!
    let indices : Array Expr := xs[info.numParams + 1:info.numParams + 1 + info.numIndices]
    let majorArg := xs[info.numParams + 1 + info.numIndices]!
    let ism := indices.push majorArg
    withLocalDeclD `ctorIdx (mkConst ``Nat) fun ctorIdx => do
    let kTypeF := mkAppN (mkConst withCtorTypeName (v :: us)) (params.push motive)
    let kType := mkApp kTypeF ctorIdx
    let toCtorApp := mkAppN (mkConst (mkToCtorIdxName indName) us) (params ++ ism)
    let hType ← mkEq ctorIdx toCtorApp
    withLocalDeclD `h hType fun h => do
    withLocalDeclD `k kType fun k => do
    let motive' ← mkLambdaFVars ism <|
      (← mkArrow hType (mkAppN motive ism))
    let e := mkConst casesOnInfo.name (v :: us)
    let e := mkAppN e params
    let e := mkApp e motive'
    let e := mkAppN e ism
    let alts ← info.ctors.toArray.mapIdxM fun i ctorName => do
      let ctor := mkAppN (mkConst ctorName us) params
      let ctorType ← inferType ctor
      forallTelescope ctorType fun zs _ctorRet => do
        -- Here we let the typecheker reduce the `toCtorIdx` application
          let heq := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) ctorIdx (mkRawNatLit i)
          withLocalDeclD `h heq fun h => do
            let e ← mkEqNDRec (motive := kTypeF) k h
            let e ← mkPULiftDown e
            let e := mkAppN e zs
            -- ``Eq.ndrec
            mkLambdaFVars (zs.push h) e
    let e := mkAppN e alts
    let e := mkApp e h
    mkLambdaFVars (params ++ #[motive, ctorIdx] ++ ism ++ #[h, k]) e

  let declName := mkWithCtorName indName
  addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
    (name        := declName)
    (levelParams := casesOnInfo.levelParams)
    (type        := (← inferType e))
    (value       := e)
    (hints       := ReducibilityHints.abbrev)
  ))
  modifyEnv fun env => addToCompletionBlackList env declName
  modifyEnv fun env => addProtected env declName
  setReducibleAttribute declName

/--
Specialies `T.withCtor` for each constructor as `T.con.with`.
-/
def mkConWith (indName : Name) : MetaM Unit := do
  let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
  let casesOnName := mkCasesOnName indName
  let casesOnInfo ← getConstVal casesOnName
  let v::us := casesOnInfo.levelParams.map mkLevelParam | panic! "unexpected universe levels on `casesOn`"
  let withCtorName := mkWithCtorName indName
  let withCtorTypeName := mkWithCtorTypeName indName
  let casesOnInfo ← getConstVal casesOnName
  -- Now specialize for each constructor
  for i in [:info.numCtors] do
    let declName := mkCtorWithName info.ctors[i]!
    let e ← forallTelescope casesOnInfo.type fun xs _ => do
      let params : Array Expr := xs[:info.numParams]
      let motive := xs[info.numParams]!
      let indices : Array Expr := xs[info.numParams + 1:info.numParams + 1 + info.numIndices]
      let majorArg := xs[info.numParams + 1 + info.numIndices]!
      let ism := indices.push majorArg
      let alts := xs[info.numParams + 1 + info.numIndices + 1:]
      let alt := alts[i]!
      let toCtorApp := mkAppN (mkConst (mkToCtorIdxName indName) us) (params ++ ism)
      let hType ← mkEq toCtorApp (mkNatLit i)
      withLocalDeclD `h hType fun h => do
      let e := mkConst withCtorName (v :: us)
      let e := mkAppN e params
      let e := mkApp e motive
      let e := mkApp e (mkNatLit i)
      let e := mkAppN e ism
      let e := mkApp e (← mkEqSymm h)
      let withCtorTypeApp := mkAppN (mkConst withCtorTypeName (v :: us)) ((params.push motive).push (mkNatLit i))
      let e := mkApp e (← withMkPULiftUp withCtorTypeApp fun _ => pure alt)
      mkLambdaFVars (params ++ #[motive] ++ ism ++ #[h, alt]) e

    addAndCompile (.defnDecl (← mkDefinitionValInferringUnsafe
      (name        := declName)
      (levelParams := casesOnInfo.levelParams)
      (type        := (← inferType e))
      (value       := e)
      (hints       := ReducibilityHints.abbrev)
    ))
    modifyEnv fun env => addToCompletionBlackList env declName
    modifyEnv fun env => addProtected env declName
    setReducibleAttribute declName

public def mkWithCtor (indName : Name) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo indName | return
  -- Do not do anything if there are no constructors
  if indVal.numCtors = 0 then return
  -- Do not do anything unless can_elim_to_type.
  let recInfo ← getConstInfo (mkRecName indName)
  unless recInfo.levelParams.length > indVal.levelParams.length do return

  mkWithCtorType indName
  mkIndWithCtor indName
  mkConWith indName
