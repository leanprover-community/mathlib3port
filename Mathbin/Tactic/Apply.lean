/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.apply
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
This file provides an alternative implementation for `apply` to fix the so-called "apply bug".

The issue arises when the goals is a Π-type -- whether it is visible or hidden behind a definition.

For instance, consider the following proof:

```
example {α β} (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
end
```

Because `x ≤ z` is definitionally equal to `∀ i, x i ≤ z i`, `apply` will fail. The alternative
definition, `apply'` fixes this. When `apply` would work, `apply` is used and otherwise,
a different strategy is deployed
-/


namespace Tactic

/-- With `gs` a list of proof goals, `reorder_goals gs new_g` will use the `new_goals` policy
`new_g` to rearrange the dependent goals to either drop them, push them to the end of the list
or leave them in place. The `bool` values in `gs` indicates whether the goal is dependent or not. -/
def reorderGoals {α} (gs : List (Bool × α)) : NewGoals → List α
  | new_goals.non_dep_first =>
    let ⟨dep, non_dep⟩ := gs.partition (coe ∘ Prod.fst)
    non_dep.map Prod.snd ++ dep.map Prod.snd
  | new_goals.non_dep_only => (gs.filter (coe ∘ not ∘ Prod.fst)).map Prod.snd
  | new_goals.all => gs.map Prod.snd
#align tactic.reorder_goals Tactic.reorderGoals

private unsafe def has_opt_auto_param_inst_for_apply (ms : List (Name × expr)) : tactic Bool :=
  ms.mfoldl
    (fun r m => do
      let type ← infer_type m.2
      let b ← is_class type
      return <| r || type `opt_param 2 || type `auto_param 2 || b)
    false
#align tactic.has_opt_auto_param_inst_for_apply tactic.has_opt_auto_param_inst_for_apply

private unsafe def try_apply_opt_auto_param_instance_for_apply (cfg : ApplyCfg)
    (ms : List (Name × expr)) : tactic Unit :=
  (whenM (has_opt_auto_param_inst_for_apply ms)) do
    let gs ← get_goals
    ms fun m =>
        whenM (not <$> is_assigned m.2) <|
          ((set_goals [m.2] >> try apply_instance) >> when cfg (try apply_opt_param)) >>
            when cfg (try apply_auto_param)
    set_goals gs
#align
  tactic.try_apply_opt_auto_param_instance_for_apply tactic.try_apply_opt_auto_param_instance_for_apply

private unsafe def retry_apply_aux :
    ∀ (e : expr) (cfg : ApplyCfg), List (Bool × Name × expr) → tactic (List (Name × expr))
  | e, cfg, gs =>
    (focus1 do
        let tgt : expr ← target
        let t ← infer_type e
        unify t tgt
        exact e
        let gs' ← get_goals
        let r := reorderGoals gs.reverse cfg.NewGoals
        set_goals (gs' ++ r Prod.snd)
        return r) <|>
      do
      let expr.pi n bi d b ← infer_type e >>= whnf |
        apply_core e cfg
      let v ← mk_meta_var d
      let b := b.has_var
      let e ← head_beta <| e v
      retry_apply_aux e cfg ((b, n, v) :: gs)
#align tactic.retry_apply_aux tactic.retry_apply_aux

private unsafe def retry_apply (e : expr) (cfg : ApplyCfg) : tactic (List (Name × expr)) :=
  apply_core e cfg <|> retry_apply_aux e cfg []
#align tactic.retry_apply tactic.retry_apply

/-- `apply'` mimics the behavior of `apply_core`. When
`apply_core` fails, it is retried by providing the term with meta
variables as additional arguments. The meta variables can then
become new goals depending on the `cfg.new_goals` policy.

`apply'` also finds instances and applies opt_params and auto_params. -/
unsafe def apply' (e : expr) (cfg : ApplyCfg := { }) : tactic (List (Name × expr)) := do
  let r ← retry_apply e cfg
  try_apply_opt_auto_param_instance_for_apply cfg r
  return r
#align tactic.apply' tactic.apply'

/-- Same as `apply'` but __all__ arguments that weren't inferred are added to goal list. -/
unsafe def fapply' (e : expr) : tactic (List (Name × expr)) :=
  apply' e { NewGoals := NewGoals.all }
#align tactic.fapply' tactic.fapply'

/-- Same as `apply'` but only goals that don't depend on other goals are added to goal list. -/
unsafe def eapply' (e : expr) : tactic (List (Name × expr)) :=
  apply' e { NewGoals := NewGoals.non_dep_only }
#align tactic.eapply' tactic.eapply'

/-- `relation_tactic` finds a proof rule for the relation found in the goal and uses `apply'`
to make one proof step. -/
private unsafe def relation_tactic (md : Transparency) (op_for : environment → Name → Option Name)
    (tac_name : String) : tactic Unit := do
  let tgt ← target >>= instantiate_mvars
  let env ← get_env
  let r := expr.get_app_fn tgt
  match op_for env (expr.const_name r) with
    | some refl => do
      let r ← mk_const refl
      retry_apply r
          { md
            NewGoals := new_goals.non_dep_only }
      return ()
    | none =>
      fail <|
        tac_name ++
          " tactic failed, target is not a relation application with the expected property."
#align tactic.relation_tactic tactic.relation_tactic

/-- Similar to `reflexivity` with the difference that `apply'` is used instead of `apply` -/
unsafe def reflexivity' (md := semireducible) : tactic Unit :=
  relation_tactic md environment.refl_for "reflexivity"
#align tactic.reflexivity' tactic.reflexivity'

/-- Similar to `symmetry` with the difference that `apply'` is used instead of `apply` -/
unsafe def symmetry' (md := semireducible) : tactic Unit :=
  relation_tactic md environment.symm_for "symmetry"
#align tactic.symmetry' tactic.symmetry'

/-- Similar to `transitivity` with the difference that `apply'` is used instead of `apply` -/
unsafe def transitivity' (md := semireducible) : tactic Unit :=
  relation_tactic md environment.trans_for "transitivity"
#align tactic.transitivity' tactic.transitivity'

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- Similarly to `apply`, the `apply'` tactic tries to match the current goal against the conclusion
of the type of term.

It differs from `apply` in that it does not unfold definition in order to find out what the
assumptions of the provided term is. It is especially useful when defining relations on function
spaces (e.g. `≤`) so that rules like transitivity on `le : (α → β) → (α → β) → (α → β)` will be
considered to have three parameters and two assumptions (i.e. `f g h : α → β`, `H₀ : f ≤ g`,
`H₁ : g ≤ h`) instead of three parameters, two assumptions and then one more parameter
(i.e. `f g h : α → β`, `H₀ : f ≤ g`, `H₁ : g ≤ h`, `x : α`). Whereas `apply` would expect the goal
`f x ≤ h x`, `apply'` will work with the goal `f ≤ h`.
-/
unsafe def apply' (q : parse texpr) : tactic Unit :=
  concat_tags do
    let h ← i_to_expr_for_apply q
    tactic.apply' h
#align tactic.interactive.apply' tactic.interactive.apply'

/-- Similar to the `apply'` tactic, but does not reorder goals.
-/
unsafe def fapply' (q : parse texpr) : tactic Unit :=
  concat_tags (i_to_expr_for_apply q >>= tactic.fapply')
#align tactic.interactive.fapply' tactic.interactive.fapply'

/--
Similar to the `apply'` tactic, but only creates subgoals for non-dependent premises that have not
been fixed by type inference or type class resolution.
-/
unsafe def eapply' (q : parse texpr) : tactic Unit :=
  concat_tags (i_to_expr_for_apply q >>= tactic.eapply')
#align tactic.interactive.eapply' tactic.interactive.eapply'

/--
Similar to the `apply'` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
unsafe def apply_with' (q : parse parser.pexpr) (cfg : ApplyCfg) : tactic Unit :=
  concat_tags do
    let e ← i_to_expr_for_apply q
    tactic.apply' e cfg
#align tactic.interactive.apply_with' tactic.interactive.apply_with'

/-- Similar to the `apply'` tactic, but uses matching instead of unification.
`mapply' t` is equivalent to `apply_with' t {unify := ff}`
-/
unsafe def mapply' (q : parse texpr) : tactic Unit :=
  concat_tags do
    let e ← i_to_expr_for_apply q
    tactic.apply' e { unify := ff }
#align tactic.interactive.mapply' tactic.interactive.mapply'

/-- Similar to `reflexivity` with the difference that `apply'` is used instead of `apply`.
-/
unsafe def reflexivity' : tactic Unit :=
  tactic.reflexivity'
#align tactic.interactive.reflexivity' tactic.interactive.reflexivity'

/-- Shorter name for the tactic `reflexivity'`.
-/
unsafe def refl' : tactic Unit :=
  tactic.reflexivity'
#align tactic.interactive.refl' tactic.interactive.refl'

/--
`symmetry'` behaves like `symmetry` but also offers the option `symmetry' at h` to apply symmetry
to assumption `h`
-/
unsafe def symmetry' : parse location → tactic Unit
  | l@loc.wildcard => l.try_apply symmetry_hyp tactic.symmetry'
  | loc.ns hs => (Loc.ns hs.reverse).apply symmetry_hyp tactic.symmetry'
#align tactic.interactive.symmetry' tactic.interactive.symmetry'

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.optional -/
/-- Similar to `transitivity` with the difference that `apply'` is used instead of `apply`.
-/
unsafe def transitivity' (q : parse (parser.optional texpr)) : tactic Unit :=
  tactic.transitivity' >>
    match q with
    | none => skip
    | some q => do
      let (r, lhs, rhs) ← target_lhs_rhs
      let t ← infer_type lhs
      i_to_expr ``(($(q) : $(t))) >>= unify rhs
#align tactic.interactive.transitivity' tactic.interactive.transitivity'

end Interactive

end Tactic

