/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/

module

prelude
public import Lean.AddDecl
public import Lean.Meta.AppBuilder
public import Lean.Meta.CompletionName
public import Lean.Meta.Constructions.NoConfusionLinear

open Lean Meta

/--
For an inductive type `T` builds a function `T.toCtorIdx : T → Nat` that returns the constructor
index of the given value.  Assumes `Nat` and `T.casesOn` to be defined already.
-/
public def mkToCtorIdx (indName : Name) : MetaM Unit := do
  if (← getEnv).contains ``Nat then
    let ConstantInfo.inductInfo info ← getConstInfo indName | unreachable!
    let us := info.levelParams.map mkLevelParam
    let declName := Name.mkStr indName "toCtorIdx"
    forallBoundedTelescope info.type (info.numParams + info.numIndices) fun xs _ => do
      let params : Array Expr := xs[:info.numParams]
      let indices : Array Expr := xs[info.numParams:]
      let indType := mkAppN (mkConst indName us) xs
      let natType  := mkConst ``Nat
      let declType ← mkArrow indType natType
      let declType ← mkForallFVars xs declType
      let declValue ← withLocalDeclD `x indType fun x => do
        let motive ← mkLambdaFVars (indices.push x) natType
        let mut value := mkConst (mkCasesOnName indName) (levelOne::us)
        value := mkAppN value params
        value := mkApp value motive
        value := mkAppN value indices
        value := mkApp value x
        for c in info.ctors do
          let cInfo ← getConstInfoCtor c
          let cType ← instantiateForall cInfo.type xs
          let alt ← forallBoundedTelescope cType cInfo.numFields fun ys _ =>
            mkLambdaFVars ys <| mkNatLit cInfo.cidx
          value := mkApp value alt
        mkLambdaFVars (xs.push x) value
      addAndCompile <| Declaration.defnDecl {
        name        := declName
        levelParams := info.levelParams
        type        := declType
        value       := declValue
        safety      := DefinitionSafety.safe
        hints       := ReducibilityHints.abbrev
      }
      setReducibleAttribute declName
