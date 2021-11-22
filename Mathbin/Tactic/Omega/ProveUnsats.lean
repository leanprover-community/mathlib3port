import Mathbin.Tactic.Omega.FindEes 
import Mathbin.Tactic.Omega.FindScalars 
import Mathbin.Tactic.Omega.LinComb

namespace Omega

open Tactic

/-- Return expr of proof that given int is negative -/
unsafe def prove_neg : Int → tactic expr
| Int.ofNat _ => failed
| -[1+ m] => return (quote Int.neg_succ_lt_zero (%%quote m))

theorem forall_mem_repeat_zero_eq_zero (m : Nat) : ∀ x _ : x ∈ List.repeat (0 : Int) m, x = (0 : Int) :=
  fun x => List.eq_of_mem_repeat

/-- Return expr of proof that elements of (repeat 0 is.length) are all 0 -/
unsafe def prove_forall_mem_eq_zero (is : List Int) : tactic expr :=
  return (quote forall_mem_repeat_zero_eq_zero is.length)

/-- Return expr of proof that the combination of linear constraints
    represented by ks and ts is unsatisfiable -/
unsafe def prove_unsat_lin_comb (ks : List Nat) (ts : List term) : tactic expr :=
  let ⟨b, as⟩ := lin_comb ks ts 
  do 
    let x1 ← prove_neg b 
    let x2 ← prove_forall_mem_eq_zero as 
    to_expr (pquote unsat_lin_comb_of (%%quote ks) (%%quote ts) (%%x1) (%%x2))

/-- Given a (([],les) : clause), return the expr of a term (t : clause.unsat ([],les)). -/
unsafe def prove_unsat_ef : clause → tactic expr
| (_ :: _, _) => failed
| ([], les) =>
  do 
    let ks ← find_scalars les 
    let x ← prove_unsat_lin_comb ks les 
    return (quote unsat_of_unsat_lin_comb (%%quote ks) (%%quote les) (%%x))

/-- Given a (c : clause), return the expr of a term (t : clause.unsat c)  -/
unsafe def prove_unsat (c : clause) : tactic expr :=
  do 
    let ee ← find_ees c 
    let x ← prove_unsat_ef (eq_elim ee c)
    return (quote unsat_of_unsat_eq_elim (%%quote ee) (%%quote c) (%%x))

/-- Given a (cs : list clause), return the expr of a term (t : clauses.unsat cs)  -/
unsafe def prove_unsats : List clause → tactic expr
| [] => return (quote clauses.unsat_nil)
| p :: ps =>
  do 
    let x ← prove_unsat p 
    let xs ← prove_unsats ps 
    to_expr (pquote clauses.unsat_cons (%%quote p) (%%quote ps) (%%x) (%%xs))

end Omega

