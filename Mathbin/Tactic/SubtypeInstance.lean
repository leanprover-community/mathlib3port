/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Provides a `subtype_instance` tactic which builds instances for algebraic substructures
(sub-groups, sub-rings...).

! This file was ported from Lean 3 source module tactic.subtype_instance
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Basic

open Tactic Expr Name List

namespace Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic.Interactive (get_current_field refineStruct)

/-- makes the substructure axiom name from field name, by postfacing with `_mem`-/
def mkMemName (sub : Name) : Name → Name
  | mk_string n _ => mk_string (n ++ "_mem") sub
  | n => n
#align tactic.mk_mem_name Tactic.mkMemName

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
unsafe def derive_field_subtype : tactic Unit := do
  let field ← get_current_field
  let b ← target >>= is_prop
  if b then do
      sorry
      intros
      andthen (applyc Field) assumption
    else do
      let s ← find_local ``(Set _)
      let q(Set $(α)) ← infer_type s
      let e ← mk_const Field
      let expl_arity ← get_expl_arity <| e α
      let xs ← (iota expl_arity).mapM fun _ => intro1
      let args ← xs fun x => mk_app `subtype.val [x]
      let hyps ← xs fun x => mk_app `subtype.property [x]
      let val ← mk_app Field args
      let subname ←
        local_context >>=
            List.firstM fun h => do
              let (expr.const n _, args) ← get_app_fn_args <$> infer_type h
              is_def_eq s args reducible
              return n
      let mem_field ← resolve_constant <| mk_mem_name subname Field
      let val_mem ← mk_app mem_field hyps
      let q(coeSort $(s)) ← target >>= instantiate_mvars
      tactic.refine ``(@Subtype.mk _ $(s) $(val) $(val_mem))
#align tactic.derive_field_subtype tactic.derive_field_subtype

namespace Interactive

/-- builds instances for algebraic substructures

Example:
```lean
variables {α : Type*} [monoid α] {s : set α}

class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance
```
-/
unsafe def subtype_instance := do
  let t ← target
  let cl := t.get_app_fn.const_name
  let src ← find_ancestors cl t.app_arg
  let inst :=
    pexpr.mk_structure_instance
      { struct := cl
        field_values := []
        field_names := []
        sources := src.map to_pexpr }
  andthen (refine_struct inst) derive_field_subtype
#align tactic.interactive.subtype_instance tactic.interactive.subtype_instance

add_tactic_doc
  { Name := "subtype_instance"
    category := DocCategory.tactic
    declNames := [`` subtype_instance]
    tags := ["type class", "structures"] }

end Interactive

end Tactic

