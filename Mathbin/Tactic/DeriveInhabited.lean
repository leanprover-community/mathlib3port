/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Logic.Basic
import Data.Rbmap.Basic

#align_import tactic.derive_inhabited from "leanprover-community/mathlib"@"d13b3a4a392ea7273dfa4727dbd1892e26cfd518"

/-!
# Derive handler for `inhabited` instances

This file introduces a derive handler to automatically generate `inhabited`
instances for structures and inductives. We also add various `inhabited`
instances for types in the core library.
-/


namespace Tactic

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
/-- Tries to derive an `inhabited` instance for inductives and structures.

For example:
```
@[derive inhabited]
structure foo :=
(a : ℕ := 42)
(b : list ℕ)
```
Here, `@[derive inhabited]` adds the instance `foo.inhabited`, which is defined as
`⟨⟨42, default⟩⟩`.  For inductives, the default value is the first constructor.

If the structure/inductive has a type parameter `α`, then the generated instance will have an
argument `inhabited α`, even if it is not used.  (This is due to the implementation using
`instance_derive_handler`.)
-/
@[derive_handler]
unsafe def inhabited_instance : derive_handler :=
  instance_derive_handler `` Inhabited do
    applyc `` Inhabited.mk
    sorry <|> constructor >> skip
    all_goals' do
        applyc `` default <|> do
            let s ← read
            fail <| to_fmt "could not find inhabited instance for:\n" ++ to_fmt s
#align tactic.inhabited_instance tactic.inhabited_instance

end Tactic

deriving instance Inhabited for VmDeclKind, VmObjKind, Tactic.NewGoals, Tactic.Transparency,
  Tactic.ApplyCfg, SmtPreConfig, EmatchConfig, Mathlib.Tactic.CC.CCConfig, SmtConfig, Rsimp.Config,
  Tactic.DunfoldConfig, Tactic.DsimpConfig, Tactic.UnfoldProjConfig, Tactic.SimpIntrosConfig,
  Tactic.DeltaConfig, Tactic.SimpConfig, Tactic.RewriteCfg, Interactive.Loc, Tactic.UnfoldConfig,
  ParamInfo, SubsingletonInfo, FunInfo, Format.Color, Pos, Environment.ProjectionInfo,
  ReducibilityHints, CongrArgKind, ULift, PLift, StringImp, String.IteratorImp, Batteries.RBColor,
  Ordering, UnificationConstraint, PProd, UnificationHint, DocCategory, TacticDocEntry

instance {α} : Inhabited (BinTree α) :=
  ⟨BinTree.empty⟩

instance : Inhabited Unsigned :=
  ⟨0⟩

instance : Inhabited String.Iterator :=
  String.IteratorImp.inhabited

instance {α} : Inhabited (Batteries.RBNode α) :=
  ⟨Batteries.RBNode.nil⟩

instance {α lt} : Inhabited (Batteries.RBSet α lt) :=
  ⟨Batteries.mkRBSet _ _⟩

instance {α β lt} : Inhabited (Rbmap α β lt) :=
  ⟨mkRbmap _ _ _⟩

