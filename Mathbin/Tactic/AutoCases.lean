/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison

! This file was ported from Lean 3 source module tactic.auto_cases
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Hint

namespace Tactic

namespace AutoCases

/-- Structure representing a tactic which can be used by `tactic.auto_cases`. -/
unsafe structure auto_cases_tac where
  Name : String
  {α : Type}
  tac : expr → tactic α
#align tactic.auto_cases.auto_cases_tac tactic.auto_cases.auto_cases_tac

/-- The `auto_cases_tac` for `tactic.cases`. -/
unsafe def tac_cases : auto_cases_tac :=
  ⟨"cases", cases⟩
#align tactic.auto_cases.tac_cases tactic.auto_cases.tac_cases

/-- The `auto_cases_tac` for `tactic.induction`. -/
unsafe def tac_induction : auto_cases_tac :=
  ⟨"induction", induction⟩
#align tactic.auto_cases.tac_induction tactic.auto_cases.tac_induction

/-- Find an `auto_cases_tac` which matches the given `type : expr`. -/
unsafe def find_tac : expr → Option auto_cases_tac
  | q(Empty) => tac_cases
  | q(PEmpty) => tac_cases
  | q(False) => tac_cases
  | q(Unit) => tac_cases
  | q(PUnit) => tac_cases
  | q(ULift _) => tac_cases
  | q(PLift _) => tac_cases
  | q(Prod _ _) => tac_cases
  | q(And _ _) => tac_cases
  | q(Sigma _) => tac_cases
  | q(PSigma _) => tac_cases
  | q(Subtype _) => tac_cases
  | q(Exists _) => tac_cases
  | q(Fin 0) => tac_cases
  | q(Sum _ _) => tac_cases
  |-- This is perhaps dangerous!
    q(Or _ _) =>
    tac_cases
  |-- This is perhaps dangerous!
    q(Iff _ _) =>
    tac_cases
  |-- This is perhaps dangerous!
    /- `cases` can be dangerous on `eq` and `quot`, producing mysterious errors during type checking.
       instead we attempt `induction`. -/
    q(Eq _ _) =>
    tac_induction
  | q(Quot _) => tac_induction
  | _ => none
#align tactic.auto_cases.find_tac tactic.auto_cases.find_tac

end AutoCases

/-- Applies `cases` or `induction` on the local_hypothesis `hyp : expr`. -/
unsafe def auto_cases_at (hyp : expr) : tactic String := do
  let t ← infer_type hyp >>= whnf
  match auto_cases.find_tac t with
    | some atac => do
      atac hyp
      let pp ← pp hyp
      return s! "{atac } {pp}"
    | none => fail "hypothesis type unsupported"
#align tactic.auto_cases_at tactic.auto_cases_at

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `results -/
/-- Applies `cases` or `induction` on certain hypotheses. -/
@[hint_tactic]
unsafe def auto_cases : tactic String := do
  let l ← local_context
  let results ← successes <| l.reverse.map auto_cases_at
  when (results results.empty) <|
      fail "`auto_cases` did not find any hypotheses to apply `cases` or `induction` to"
  return (String.intercalate ", " results)
#align tactic.auto_cases tactic.auto_cases

end Tactic

