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
| quote Empty => tac_cases
| quote Pempty => tac_cases
| quote False => tac_cases
| quote Unit => tac_cases
| quote PUnit => tac_cases
| quote Ulift _ => tac_cases
| quote Plift _ => tac_cases
| quote Prod _ _ => tac_cases
| quote And _ _ => tac_cases
| quote Sigma _ => tac_cases
| quote Psigma _ => tac_cases
| quote Subtype _ => tac_cases
| quote Exists _ => tac_cases
| quote Finₓ 0 => tac_cases
| quote Sum _ _ => tac_cases
| quote Or _ _ => tac_cases
| quote Iff _ _ => tac_cases
| quote Eq _ _ => tac_induction
| quote Quot _ => tac_induction
| _ => none

end AutoCases

/-- Applies `cases` or `induction` on the local_hypothesis `hyp : expr`. -/
unsafe def auto_cases_at (hyp : expr) : tactic Stringₓ :=
  do 
    let t ← infer_type hyp >>= whnf 
    match auto_cases.find_tac t with 
      | some atac =>
        do 
          atac.tac hyp 
          let pp ← pp hyp 
          return s! "{atac.name } {pp}"
      | none => fail "hypothesis type unsupported"

/-- Applies `cases` or `induction` on certain hypotheses. -/
@[hintTactic]
unsafe def auto_cases : tactic Stringₓ :=
  do 
    let l ← local_context 
    let results ← successes$ l.reverse.map auto_cases_at 
    when results.empty$ fail "`auto_cases` did not find any hypotheses to apply `cases` or `induction` to"
    return (Stringₓ.intercalate ", " results)

end Tactic

