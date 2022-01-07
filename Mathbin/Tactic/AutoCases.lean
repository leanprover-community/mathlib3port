import Mathbin.Tactic.Hint

namespace Tactic

namespace AutoCases

/-- Structure representing a tactic which can be used by `tactic.auto_cases`. -/
unsafe structure auto_cases_tac where
  Name : Stringₓ
  {α : Type}
  tac : expr → tactic α

/-- The `auto_cases_tac` for `tactic.cases`. -/
unsafe def tac_cases : auto_cases_tac :=
  ⟨"cases", cases⟩

/-- The `auto_cases_tac` for `tactic.induction`. -/
unsafe def tac_induction : auto_cases_tac :=
  ⟨"induction", induction⟩

/-- Find an `auto_cases_tac` which matches the given `type : expr`. -/
unsafe def find_tac : expr → Option auto_cases_tac
  | quote.1 Empty => tac_cases
  | quote.1 Pempty => tac_cases
  | quote.1 False => tac_cases
  | quote.1 Unit => tac_cases
  | quote.1 PUnit => tac_cases
  | quote.1 (Ulift _) => tac_cases
  | quote.1 (Plift _) => tac_cases
  | quote.1 (Prod _ _) => tac_cases
  | quote.1 (And _ _) => tac_cases
  | quote.1 (Sigma _) => tac_cases
  | quote.1 (Psigma _) => tac_cases
  | quote.1 (Subtype _) => tac_cases
  | quote.1 (Exists _) => tac_cases
  | quote.1 (Finₓ 0) => tac_cases
  | quote.1 (Sum _ _) => tac_cases
  | quote.1 (Or _ _) => tac_cases
  | quote.1 (Iff _ _) => tac_cases
  | quote.1 (Eq _ _) => tac_induction
  | quote.1 (Quot _) => tac_induction
  | _ => none

end AutoCases

/-- Applies `cases` or `induction` on the local_hypothesis `hyp : expr`. -/
unsafe def auto_cases_at (hyp : expr) : tactic Stringₓ := do
  let t ← infer_type hyp >>= whnf
  match auto_cases.find_tac t with
    | some atac => do
      atac.tac hyp
      let pp ← pp hyp
      return s! "{atac.name } {pp}"
    | none => fail "hypothesis type unsupported"

/-- Applies `cases` or `induction` on certain hypotheses. -/
@[hint_tactic]
unsafe def auto_cases : tactic Stringₓ := do
  let l ← local_context
  let results ← successes $ l.reverse.map auto_cases_at
  when results.empty $ fail "`auto_cases` did not find any hypotheses to apply `cases` or `induction` to"
  return (Stringₓ.intercalate ", " results)

end Tactic

