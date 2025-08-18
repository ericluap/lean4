/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Command
import Lean.Meta.Injective
import Lean.Meta.Constructions.ToCtorIdx
import Lean.Meta.Constructions.WithCtor

namespace Lean.Elab.Command

@[builtin_command_elab genWithCtor] def elabWithCtor : CommandElab := fun stx => do
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo stx[1]
    mkToCtorIdx declName
    mkWithCtor declName

@[builtin_command_elab genInjectiveTheorems] def elabGenInjectiveTheorems : CommandElab := fun stx => do
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo stx[1]
    Meta.mkInjectiveTheorems declName

end Lean.Elab.Command
