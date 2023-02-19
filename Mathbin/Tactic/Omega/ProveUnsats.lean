/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.prove_unsats
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.FindEes
import Mathbin.Tactic.Omega.FindScalars
import Mathbin.Tactic.Omega.LinComb

/-
A tactic which constructs exprs to discharge
goals of the form `clauses.unsat cs`.
-/
namespace Omega

open Tactic

/-- Return expr of proof that given int is negative -/
unsafe def prove_neg : Int → tactic expr
  | Int.ofNat _ => failed
  | -[m+1] => return q(Int.negSucc_lt_zero $(q(m)))
#align omega.prove_neg omega.prove_neg

theorem forall_mem_replicate_zero_eq_zero (m : Nat) :
    ∀ x ∈ List.replicate m (0 : Int), x = (0 : Int) := fun x => List.eq_of_mem_replicate
#align omega.forall_mem_replicate_zero_eq_zero Omega.forall_mem_replicate_zero_eq_zero

/-- Return expr of proof that elements of (replicate is.length 0) are all 0 -/
unsafe def prove_forall_mem_eq_zero (is : List Int) : tactic expr :=
  return q(forall_mem_replicate_zero_eq_zero is.length)
#align omega.prove_forall_mem_eq_zero omega.prove_forall_mem_eq_zero

/-- Return expr of proof that the combination of linear constraints
    represented by ks and ts is unsatisfiable -/
unsafe def prove_unsat_lin_comb (ks : List Nat) (ts : List Term) : tactic expr :=
  let ⟨b, as⟩ := linComb ks ts
  do
  let x1 ← prove_neg b
  let x2 ← prove_forall_mem_eq_zero as
  to_expr ``(unsatLinComb_of $(q(ks)) $(q(ts)) $(x1) $(x2))
#align omega.prove_unsat_lin_comb omega.prove_unsat_lin_comb

/-- Given a (([],les) : clause), return the expr of a term (t : clause.unsat ([],les)). -/
unsafe def prove_unsat_ef : Clause → tactic expr
  | (_ :: _, _) => failed
  | ([], les) => do
    let ks ← find_scalars les
    let x ← prove_unsat_lin_comb ks les
    return q(unsat_of_unsatLinComb $(q(ks)) $(q(les)) $(x))
#align omega.prove_unsat_ef omega.prove_unsat_ef

/-- Given a (c : clause), return the expr of a term (t : clause.unsat c)  -/
unsafe def prove_unsat (c : Clause) : tactic expr := do
  let ee ← find_ees c
  let x ← prove_unsat_ef (eqElim ee c)
  return q(unsat_of_unsat_eqElim $(q(ee)) $(q(c)) $(x))
#align omega.prove_unsat omega.prove_unsat

/-- Given a (cs : list clause), return the expr of a term (t : clauses.unsat cs)  -/
unsafe def prove_unsats : List Clause → tactic expr
  | [] => return q(Clauses.unsat_nil)
  | p :: ps => do
    let x ← prove_unsat p
    let xs ← prove_unsats ps
    to_expr ``(Clauses.unsat_cons $(q(p)) $(q(ps)) $(x) $(xs))
#align omega.prove_unsats omega.prove_unsats

end Omega

