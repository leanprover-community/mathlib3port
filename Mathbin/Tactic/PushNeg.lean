/-
Copyright (c) 2019 Patrick Massot All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Simon Hudon
-/
import Mathbin.Tactic.Core
import Mathbin.Logic.Basic

/-!
# A tactic pushing negations into an expression
-/


open Tactic Expr

/- Enable the option `trace.push_neg.use_distrib` in order to have `¬ (p ∧ q)` normalized to
`¬ p ∨ ¬ q`, rather than the default `p → ¬ q`. -/
initialize
  registerTraceClass.1 `push_neg.use_distrib

namespace PushNeg

section

universe u

variable {α : Sort u}

variable (p q : Prop)

variable (s : α → Prop)

attribute [local instance] Classical.propDecidable

theorem not_not_eq : (¬¬p) = p :=
  propext not_not

theorem not_and_eq : (¬(p ∧ q)) = (p → ¬q) :=
  propext not_and

theorem not_and_distrib_eq : (¬(p ∧ q)) = (¬p ∨ ¬q) :=
  propext not_and_or

theorem not_or_eq : (¬(p ∨ q)) = (¬p ∧ ¬q) :=
  propext not_or

theorem not_forall_eq : (¬∀ x, s x) = ∃ x, ¬s x :=
  propext not_forall

theorem not_exists_eq : (¬∃ x, s x) = ∀ x, ¬s x :=
  propext not_exists

theorem not_implies_eq : (¬(p → q)) = (p ∧ ¬q) :=
  propext not_imp

theorem Classical.implies_iff_not_or : p → q ↔ ¬p ∨ q :=
  imp_iff_not_or

theorem not_eq (a b : α) : ¬a = b ↔ a ≠ b :=
  Iff.rfl

variable {β : Type u}

variable [LinearOrder β]

theorem not_le_eq (a b : β) : (¬a ≤ b) = (b < a) :=
  propext not_le

theorem not_lt_eq (a b : β) : (¬a < b) = (b ≤ a) :=
  propext not_lt

end

unsafe def whnf_reducible (e : expr) : tactic expr :=
  whnf e reducible

private unsafe def transform_negation_step (e : expr) : tactic (Option (expr × expr)) := do
  let e ← whnf_reducible e
  match e with
    | quote.1 ¬%%ₓNe => do
      let ne ← whnf_reducible Ne
      match Ne with
        | quote.1 ¬%%ₓa => do
          let pr ← mk_app `` not_not_eq [a]
          return (some (a, pr))
        | quote.1 ((%%ₓa) ∧ %%ₓb) => do
          let distrib ← get_bool_option `trace.push_neg.use_distrib ff
          if distrib then do
              let pr ← mk_app `` not_and_distrib_eq [a, b]
              return (some (quote.1 (¬(%%ₓa : Prop) ∨ ¬%%ₓb), pr))
            else do
              let pr ← mk_app `` not_and_eq [a, b]
              return (some (quote.1 ((%%ₓa : Prop) → ¬%%ₓb), pr))
        | quote.1 ((%%ₓa) ∨ %%ₓb) => do
          let pr ← mk_app `` not_or_eq [a, b]
          return (some (quote.1 ((¬%%ₓa) ∧ ¬%%ₓb), pr))
        | quote.1 ((%%ₓa) ≤ %%ₓb) => do
          let e ← to_expr (pquote.1 ((%%ₓb) < %%ₓa))
          let pr ← mk_app `` not_le_eq [a, b]
          return (some (e, pr))
        | quote.1 ((%%ₓa) < %%ₓb) => do
          let e ← to_expr (pquote.1 ((%%ₓb) ≤ %%ₓa))
          let pr ← mk_app `` not_lt_eq [a, b]
          return (some (e, pr))
        | quote.1 (Exists (%%ₓp)) => do
          let pr ← mk_app `` not_exists_eq [p]
          let e ←
            match p with
              | lam n bi typ bo => do
                let body ← mk_app `` Not [bo]
                return (pi n bi typ body)
              | _ => tactic.fail "Unexpected failure negating ∃"
          return (some (e, pr))
        | pi n bi d p =>
          if p then do
            let pr ← mk_app `` not_forall_eq [lam n bi d p]
            let body ← mk_app `` Not [p]
            let e ← mk_app `` Exists [lam n bi d body]
            return (some (e, pr))
          else do
            let pr ← mk_app `` not_implies_eq [d, p]
            let quote.1 ((%%ₓ_) = %%ₓe') ← infer_type pr
            return (some (e', pr))
        | _ => return none
    | _ => return none

private unsafe def transform_negation : expr → tactic (Option (expr × expr))
  | e => do
    let some (e', pr) ← transform_negation_step e | return none
    let some (e'', pr') ← transform_negation e' | return (some (e', pr))
    let pr'' ← mk_eq_trans pr pr'
    return (some (e'', pr''))

unsafe def normalize_negations (t : expr) : tactic (expr × expr) := do
  let (_, e, pr) ←
    simplify_top_down ()
        (fun _ => fun e => do
          let oepr ← transform_negation e
          match oepr with
            | some (e', pr) => return ((), e', pr)
            | none => do
              let pr ← mk_eq_refl e
              return ((), e, pr))
        t { eta := false }
  return (e, pr)

unsafe def push_neg_at_hyp (h : Name) : tactic Unit := do
  let H ← get_local h
  let t ← infer_type H
  let (e, pr) ← normalize_negations t
  replace_hyp H e pr
  skip

unsafe def push_neg_at_goal : tactic Unit := do
  let H ← target
  let (e, pr) ← normalize_negations H
  replace_target e pr

end PushNeg

open Interactive (parse loc.ns loc.wildcard)

open Interactive.Types (location texpr)

open Lean.Parser (tk ident many)

open Interactive.Loc

-- mathport name: parser.optional
local postfix:1024 "?" => optional

-- mathport name: parser.many
local postfix:1024 "*" => many

open PushNeg

/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
/-- Push negations in the goal of some assumption.

For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variables names are conserved.

This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```

(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.
-/
unsafe def tactic.interactive.push_neg : parse location → tactic Unit
  | loc.ns loc_l =>
    loc_l.mmap' fun l =>
      match l with
      | some h => do
        push_neg_at_hyp h
        try <|
            interactive.simp_core { eta := ff } failed tt [simp_arg_type.expr (pquote.1 PushNeg.not_eq)] []
              (Interactive.Loc.ns [some h])
      | none => do
        push_neg_at_goal
        try sorry
  | loc.wildcard => do
    push_neg_at_goal
    local_context >>= mmap' fun h => push_neg_at_hyp (local_pp_name h)
    try sorry

add_tactic_doc
  { Name := "push_neg", category := DocCategory.tactic, declNames := [`tactic.interactive.push_neg], tags := ["logic"] }

theorem imp_of_not_imp_not (P Q : Prop) : (¬Q → ¬P) → P → Q := fun h hP => Classical.by_contradiction fun h' => h h' hP

/-- Matches either an identifier "h" or a pair of identifiers "h with k" -/
unsafe def name_with_opt : lean.parser (Name × Option Name) :=
  Prod.mk <$> ident <*> (some <$> (tk "with" *> ident) <|> return none)

/-- Transforms the goal into its contrapositive.

* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
  using `push_neg`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
-/
unsafe def tactic.interactive.contrapose (push : parse (tk "!")?) : parse name_with_opt ? → tactic Unit
  | some (h, h') => (((get_local h >>= revert) >> tactic.interactive.contrapose none) >> intro (h'.getOrElse h)) >> skip
  | none => do
    let quote.1 ((%%ₓP) → %%ₓQ) ← target | fail "The goal is not an implication, and you didn't specify an assumption"
    let cp ←
      mk_mapp `` imp_of_not_imp_not [P, Q] <|> fail "contrapose only applies to nondependent arrows between props"
    apply cp
    when push <| try (tactic.interactive.push_neg (loc.ns [none]))

add_tactic_doc
  { Name := "contrapose", category := DocCategory.tactic, declNames := [`tactic.interactive.contrapose],
    tags := ["logic"] }

/-!
## `#push_neg` command
A user command to run `push_neg`. Mostly copied from the `#norm_num` and `#simp` commands.
-/


namespace Tactic

open Lean.Parser

open Interactive.Types

setup_tactic_parser

/-- The syntax is `#push_neg e`, where `e` is an expression,
which will print the `push_neg` form of `e`.

`#push_neg` understands local variables, so you can use them to
introduce parameters.
-/
@[user_command]
unsafe def push_neg_cmd (_ : parse <| tk "#push_neg") : lean.parser Unit := do
  let e ← texpr
  let/- Synthesize a `tactic_state` including local variables as hypotheses under which
         `normalize_negations` may be safely called with expected behaviour given the `variables` in the
         environment. -/
    (ts, _)
    ← synthesize_tactic_state_with_variables_as_hyps [e]
  let result
    ←-- Enter the `tactic` monad, *critically* using the synthesized tactic state `ts`.
        lean.parser.of_tactic
        fun _ =>
        (/- Resolve the local variables added by the parser to `e` (when it was parsed) against the local
                 hypotheses added to the `ts : tactic_state` which we are using. -/
          do
            let e ← to_expr e
            let-- Run `push_neg` on the expression.
              (e_neg, _)
              ← normalize_negations e
            /- Run a `simp` to change any `¬ a = b` to `a ≠ b`; report the result, or, if the `simp` fails
                      (because no `¬ a = b` appear in the expression), return what `push_neg` gave. -/
                  Prod.fst <$>
                  e_neg { eta := ff } failed tt [] [simp_arg_type.expr (pquote.1 PushNeg.not_eq)] <|>
                pure e_neg)
          ts
  -- Trace the result.
      trace
      result

add_tactic_doc
  { Name := "#push_neg", category := DocCategory.cmd, declNames := [`tactic.push_neg_cmd], tags := ["logic"] }

end Tactic

