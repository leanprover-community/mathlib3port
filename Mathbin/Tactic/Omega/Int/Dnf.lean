/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.int.dnf
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.ProdSigma
import Mathbin.Tactic.Omega.Clause
import Mathbin.Tactic.Omega.Int.Form

/-!
# DNF transformation
-/


namespace Omega

namespace Int

open Omega.Int

/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp]
def pushNeg : Preform → Preform
  | p ∨* q => push_neg p ∧* push_neg q
  | p ∧* q => push_neg p ∨* push_neg q
  | ¬* p => p
  | p => ¬* p
#align omega.int.push_neg Omega.Int.pushNeg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem pushNeg_equiv : ∀ {p : Preform}, Preform.Equiv (pushNeg p) (¬* p) :=
  by
  run_tac
    preform.induce sorry
  · simp only [Classical.not_not, pushNeg, Preform.Holds]
  · simp only [Preform.Holds, pushNeg, not_or, ihp v, ihq v]
  · simp only [Preform.Holds, pushNeg, not_and_or, ihp v, ihq v]
#align omega.int.push_neg_equiv Omega.Int.pushNeg_equiv

/-- NNF transformation -/
def nnf : Preform → Preform
  | ¬* p => pushNeg (nnf p)
  | p ∨* q => nnf p ∨* nnf q
  | p ∧* q => nnf p ∧* nnf q
  | a => a
#align omega.int.nnf Omega.Int.nnf

def IsNnf : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | ¬* t =* s => True
  | ¬* t ≤* s => True
  | p ∨* q => is_nnf p ∧ is_nnf q
  | p ∧* q => is_nnf p ∧ is_nnf q
  | _ => False
#align omega.int.is_nnf Omega.Int.IsNnf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem isNnf_pushNeg : ∀ p : Preform, IsNnf p → IsNnf (pushNeg p) :=
  by
  run_tac
    preform.induce sorry
  · cases p <;> try cases h1 <;> trivial
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
#align omega.int.is_nnf_push_neg Omega.Int.isNnf_pushNeg

/-- Argument is free of negations -/
def NegFree : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | p ∨* q => neg_free p ∧ neg_free q
  | p ∧* q => neg_free p ∧ neg_free q
  | _ => False
#align omega.int.neg_free Omega.Int.NegFree

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem isNnf_nnf : ∀ p : Preform, IsNnf (nnf p) :=
  by
  run_tac
    preform.induce sorry
  · apply isNnf_pushNeg _ ih
  · constructor <;> assumption
  · constructor <;> assumption
#align omega.int.is_nnf_nnf Omega.Int.isNnf_nnf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem nnf_equiv : ∀ {p : Preform}, Preform.Equiv (nnf p) p :=
  by
  run_tac
    preform.induce sorry
  · rw [pushNeg_equiv]
    apply not_congr
    apply ih
  · apply pred_mono_2' (ihp v) (ihq v)
  · apply pred_mono_2' (ihp v) (ihq v)
#align omega.int.nnf_equiv Omega.Int.nnf_equiv

/-- Eliminate all negations from preform -/
@[simp]
def negElim : Preform → Preform
  | ¬* t =* s => (t.addOne ≤* s) ∨* s.addOne ≤* t
  | ¬* t ≤* s => s.addOne ≤* t
  | p ∨* q => neg_elim p ∨* neg_elim q
  | p ∧* q => neg_elim p ∧* neg_elim q
  | p => p
#align omega.int.neg_elim Omega.Int.negElim

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem negFree_negElim : ∀ p : Preform, IsNnf p → NegFree (negElim p) :=
  by
  run_tac
    preform.induce sorry
  · cases p <;> try cases h1 <;> try trivial
    constructor <;> trivial
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
#align omega.int.neg_free_neg_elim Omega.Int.negFree_negElim

theorem le_and_le_iff_eq {α : Type} [PartialOrder α] {a b : α} : a ≤ b ∧ b ≤ a ↔ a = b :=
  by
  constructor <;> intro h1
  · cases h1
    apply le_antisymm <;> assumption
  · constructor <;> apply le_of_eq <;> rw [h1]
#align omega.int.le_and_le_iff_eq Omega.Int.le_and_le_iff_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem implies_negElim : ∀ {p : Preform}, Preform.Implies p (negElim p) :=
  by
  run_tac
    preform.induce sorry
  · cases' p with t s t s <;> try apply h
    · simp only [le_and_le_iff_eq.symm, not_and_or, not_le, Preterm.val, Preform.Holds] at h
      simp only [Int.add_one_le_iff, Preterm.addOne, Preterm.val, Preform.Holds, negElim]
      rw [or_comm']
      assumption
    · simp only [not_le, Int.add_one_le_iff, Preterm.addOne, not_le, Preterm.val, Preform.Holds,
        negElim] at *
      assumption
  · simp only [negElim]
    cases h <;>
        [·
          left
          apply ihp,
        · right
          apply ihq] <;>
      assumption
  · apply And.imp (ihp _) (ihq _) h
#align omega.int.implies_neg_elim Omega.Int.implies_negElim

@[simp]
def dnfCore : Preform → List Clause
  | p ∨* q => dnf_core p ++ dnf_core q
  | p ∧* q => (List.product (dnf_core p) (dnf_core q)).map fun pq => Clause.append pq.fst pq.snd
  | t =* s => [([Term.sub (canonize s) (canonize t)], [])]
  | t ≤* s => [([], [Term.sub (canonize s) (canonize t)])]
  | ¬* _ => []
#align omega.int.dnf_core Omega.Int.dnfCore

/-- DNF transformation -/
def dnf (p : Preform) : List Clause :=
  dnfCore <| negElim <| nnf p
#align omega.int.dnf Omega.Int.dnf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.int.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:334:4: warning: unsupported (TODO): `[tacs] -/
theorem exists_clause_holds {v : Nat → Int} :
    ∀ {p : Preform}, NegFree p → p.Holds v → ∃ c ∈ dnfCore p, Clause.Holds v c :=
  by
  run_tac
    preform.induce sorry
  · apply List.exists_mem_cons_of
    constructor
    · simp only [Preterm.val, Preform.Holds] at h2
      rw [List.forall_mem_singleton]
      simp only [h2, Omega.Int.val_canonize, Omega.Term.val_sub, sub_self]
    · apply List.forall_mem_nil
  · apply List.exists_mem_cons_of
    constructor
    · apply List.forall_mem_nil
    · simp only [Preterm.val, Preform.Holds] at h2
      rw [List.forall_mem_singleton]
      simp only [val_canonize, Preterm.val, Term.val_sub]
      rw [le_sub_comm, sub_zero]
      assumption
  · cases h1
  ·
    cases' h2 with h2 h2 <;> [· cases' ihp h1.left h2 with c h3,
              · cases' ihq h1.right h2 with c h3] <;>
            cases' h3 with h3 h4 <;>
          refine' ⟨c, list.mem_append.elim_right _, h4⟩ <;>
        [left, right] <;>
      assumption
  · rcases ihp h1.left h2.left with ⟨cp, hp1, hp2⟩
    rcases ihq h1.right h2.right with ⟨cq, hq1, hq2⟩
    refine' ⟨Clause.append cp cq, ⟨_, Clause.holds_append hp2 hq2⟩⟩
    simp only [dnfCore, List.mem_map']
    refine' ⟨(cp, cq), ⟨_, rfl⟩⟩
    rw [List.mem_product]
    constructor <;> assumption
#align omega.int.exists_clause_holds Omega.Int.exists_clause_holds

theorem clauses_sat_dnfCore {p : Preform} : NegFree p → p.Sat → Clauses.Sat (dnfCore p) :=
  by
  intro h1 h2; cases' h2 with v h2
  rcases exists_clause_holds h1 h2 with ⟨c, h3, h4⟩
  refine' ⟨c, h3, v, h4⟩
#align omega.int.clauses_sat_dnf_core Omega.Int.clauses_sat_dnfCore

theorem unsat_of_clauses_unsat {p : Preform} : Clauses.Unsat (dnf p) → p.Unsat :=
  by
  intro h1 h2; apply h1
  apply clauses_sat_dnfCore
  apply negFree_negElim _ (isNnf_nnf _)
  apply Preform.sat_of_implies_of_sat implies_negElim
  have hrw := exists_congr (@nnf_equiv p)
  apply hrw.elim_right h2
#align omega.int.unsat_of_clauses_unsat Omega.Int.unsat_of_clauses_unsat

end Int

end Omega

