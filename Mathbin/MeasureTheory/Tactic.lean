/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.tactic
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpaceDef
import Mathbin.Tactic.AutoCases
import Mathbin.Tactic.Tidy
import Mathbin.Tactic.WithLocalReducibility

/-!
# Tactics for measure theory

Currently we have one domain-specific tactic for measure theory: `measurability`.

This tactic is to a large extent a copy of the `continuity` tactic by Reid Barton.
-/


/-!
### `measurability` tactic

Automatically solve goals of the form `measurable f`, `ae_measurable f μ` and `measurable_set s`.

Mark lemmas with `@[measurability]` to add them to the set of lemmas
used by `measurability`. Note: `to_additive` doesn't know yet how to
copy the attribute to the additive version.
-/


/-- User attribute used to mark tactics used by `measurability`. -/
@[user_attribute]
unsafe def measurability : user_attribute
    where
  Name := `measurability
  descr := "lemmas usable to prove (ae)-measurability"
#align measurability measurability

/- Mark some measurability lemmas already defined in `measure_theory.measurable_space_def` and
`measure_theory.measure_space_def` -/
attribute [measurability]
  measurable_id measurable_id' aeMeasurableId aeMeasurableId' measurable_const aeMeasurableConst AeMeasurable.measurable_mk MeasurableSet.empty MeasurableSet.univ MeasurableSet.compl Subsingleton.measurable_set MeasurableSet.Union MeasurableSet.Inter MeasurableSet.union MeasurableSet.inter MeasurableSet.diff MeasurableSet.symm_diff MeasurableSet.ite MeasurableSet.cond MeasurableSet.disjointed MeasurableSet.const MeasurableSet.insert measurable_set_eq Finset.measurable_set MeasurableSpace.measurable_set_top

namespace Tactic

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic to apply `measurable.comp` when appropriate.

Applying `measurable.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove measurable is actually
  constant, and that constant is a function application `f z`, then
  measurable.comp would produce new goals `measurable f`, `measurable
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply `measurable_const`.

* measurable.comp will always succeed on `measurable (λ x, f x)` and
  produce new goals `measurable (λ x, x)`, `measurable f`. We detect
  this by failing if a new goal can be closed by applying
  measurable_id.
-/
unsafe def apply_measurable.comp : tactic Unit :=
  sorry
#align tactic.apply_measurable.comp tactic.apply_measurable.comp

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic to apply `measurable.comp_ae_measurable` when appropriate.

Applying `measurable.comp_ae_measurable` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove measurable is actually
  constant, and that constant is a function application `f z`, then
  `measurable.comp_ae_measurable` would produce new goals `measurable f`, `ae_measurable
  (λ _, z) μ`, which is silly. We avoid this by failing if we could
  apply `ae_measurable_const`.

* `measurable.comp_ae_measurable` will always succeed on `ae_measurable (λ x, f x) μ` and
  can produce new goals (`measurable (λ x, x)`, `ae_measurable f μ`) or
  (`measurable f`, `ae_measurable (λ x, x) μ`). We detect those by failing if a new goal can be
  closed by applying `measurable_id` or `ae_measurable_id`.
-/
unsafe def apply_measurable.comp_ae_measurable : tactic Unit :=
  sorry
#align tactic.apply_measurable.comp_ae_measurable tactic.apply_measurable.comp_ae_measurable

/--
We don't want the intro1 tactic to apply to a goal of the form `measurable f`, `ae_measurable f μ`
or `measurable_set s`. This tactic tests the target to see if it matches that form.
 -/
unsafe def goal_is_not_measurable : tactic Unit := do
  let t ← tactic.target
  match t with
    | q(Measurable $(l)) => failed
    | q(AeMeasurable $(l) $(r)) => failed
    | q(MeasurableSet $(l)) => failed
    | _ => skip
#align tactic.goal_is_not_measurable tactic.goal_is_not_measurable

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- List of tactics used by `measurability` internally. The option `use_exfalso := ff` is passed to
the tactic `apply_assumption` in order to avoid loops in the presence of negated hypotheses in
the context. -/
unsafe def measurability_tactics (md : Transparency := semireducible) : List (tactic String) :=
  [(propositional_goal >> tactic.interactive.apply_assumption none { use_exfalso := false }) >>
      pure "apply_assumption {use_exfalso := ff}",
    goal_is_not_measurable >> intro1 >>= fun ns => pure ("intro " ++ ns.toString),
    apply_rules [] [`` measurability] 50 { md } >> pure "apply_rules with measurability",
    apply_measurable.comp >> pure "refine measurable.comp _ _",
    apply_measurable.comp_ae_measurable >> pure "refine measurable.comp_ae_measurable _ _",
    sorry >> pure "refine measurable.ae_measurable _",
    sorry >> pure "refine measurable.ae_strongly_measurable _"]
#align tactic.measurability_tactics tactic.measurability_tactics

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- Solve goals of the form `measurable f`, `ae_measurable f μ`, `ae_strongly_measurable f μ` or
`measurable_set s`. `measurability?` reports back the proof term it found.
-/
unsafe def measurability (bang : parse <| optional (tk "!")) (trace : parse <| optional (tk "?"))
    (cfg : tidy.cfg := { }) : tactic Unit :=
  let md := if bang.isSome then semireducible else reducible
  let measurability_core := tactic.tidy { cfg with tactics := measurability_tactics md }
  let trace_fn := if trace.isSome then show_term else id
  trace_fn measurability_core
#align tactic.interactive.measurability tactic.interactive.measurability

/-- Version of `measurability` for use with auto_param. -/
unsafe def measurability' : tactic Unit :=
  measurability none none { }
#align tactic.interactive.measurability' tactic.interactive.measurability'

/-- `measurability` solves goals of the form `measurable f`, `ae_measurable f μ`,
`ae_strongly_measurable f μ` or `measurable_set s` by applying lemmas tagged with the
`measurability` user attribute.

You can also use `measurability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`measurability?` reports back the proof term it found.
-/
add_tactic_doc
  { Name := "measurability / measurability'"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.measurability, `tactic.interactive.measurability']
    tags := ["lemma application"] }

end Interactive

end Tactic

