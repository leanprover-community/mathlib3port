/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.nat.neg_elim
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.Nat.Form

/-
Negation elimination.
-/
namespace Omega

namespace Nat

open Omega.Nat

/-- push_neg p returns the result of normalizing ¬ p by
    pushing the outermost negation all the way down,
    until it reaches either a negation or an atom -/
@[simp]
def pushNeg : Preform → Preform
  | p ∨* q => push_neg p ∧* push_neg q
  | p ∧* q => push_neg p ∨* push_neg q
  | ¬* p => p
  | p => ¬* p
#align omega.nat.push_neg Omega.Nat.pushNeg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.nat.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
theorem pushNeg_equiv : ∀ {p : Preform}, Preform.Equiv (pushNeg p) (¬* p) :=
  by
  run_tac
    preform.induce sorry
  · simp only [Classical.not_not, preform.holds, push_neg]
  · simp only [preform.holds, push_neg, not_or, ihp v, ihq v]
  · simp only [preform.holds, push_neg, not_and_or, ihp v, ihq v]
#align omega.nat.push_neg_equiv Omega.Nat.pushNeg_equiv

/-- NNF transformation -/
def nnf : Preform → Preform
  | ¬* p => pushNeg (nnf p)
  | p ∨* q => nnf p ∨* nnf q
  | p ∧* q => nnf p ∧* nnf q
  | a => a
#align omega.nat.nnf Omega.Nat.nnf

/-- Asserts that the given preform is in NNF -/
def IsNnf : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | ¬* t =* s => True
  | ¬* t ≤* s => True
  | p ∨* q => is_nnf p ∧ is_nnf q
  | p ∧* q => is_nnf p ∧ is_nnf q
  | _ => False
#align omega.nat.is_nnf Omega.Nat.IsNnf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.nat.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
theorem isNnf_pushNeg : ∀ p : Preform, IsNnf p → IsNnf (pushNeg p) :=
  by
  run_tac
    preform.induce sorry
  · cases p <;> try cases h1 <;> trivial
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
#align omega.nat.is_nnf_push_neg Omega.Nat.isNnf_pushNeg

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.nat.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
theorem isNnf_nnf : ∀ p : Preform, IsNnf (nnf p) :=
  by
  run_tac
    preform.induce sorry
  · apply is_nnf_push_neg _ ih
  · constructor <;> assumption
  · constructor <;> assumption
#align omega.nat.is_nnf_nnf Omega.Nat.isNnf_nnf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.nat.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
theorem nnf_equiv : ∀ {p : Preform}, Preform.Equiv (nnf p) p :=
  by
  run_tac
    preform.induce sorry
  · rw [push_neg_equiv]
    apply not_congr
    apply ih
  · apply pred_mono_2' (ihp v) (ihq v)
  · apply pred_mono_2' (ihp v) (ihq v)
#align omega.nat.nnf_equiv Omega.Nat.nnf_equiv

@[simp]
def negElimCore : Preform → Preform
  | ¬* t =* s => (t.add_one ≤* s) ∨* s.add_one ≤* t
  | ¬* t ≤* s => s.add_one ≤* t
  | p ∨* q => neg_elim_core p ∨* neg_elim_core q
  | p ∧* q => neg_elim_core p ∧* neg_elim_core q
  | p => p
#align omega.nat.neg_elim_core Omega.Nat.negElimCore

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.nat.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
theorem negFree_negElimCore : ∀ p, IsNnf p → (negElimCore p).NegFree :=
  by
  run_tac
    preform.induce sorry
  · cases p <;> try cases h1 <;> try trivial
    constructor <;> trivial
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
  · cases h1
    constructor <;> [· apply ihp, · apply ihq] <;> assumption
#align omega.nat.neg_free_neg_elim_core Omega.Nat.negFree_negElimCore

theorem le_and_le_iff_eq {α : Type} [PartialOrder α] {a b : α} : a ≤ b ∧ b ≤ a ↔ a = b :=
  by
  constructor <;> intro h1
  · cases h1
    apply le_antisymm <;> assumption
  · constructor <;> apply le_of_eq <;> rw [h1]
#align omega.nat.le_and_le_iff_eq Omega.Nat.le_and_le_iff_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic omega.nat.preform.induce -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
theorem implies_negElimCore : ∀ {p : Preform}, Preform.Implies p (negElimCore p) :=
  by
  run_tac
    preform.induce sorry
  · cases' p with t s t s <;> try apply h
    · apply Or.symm
      simpa only [preform.holds, le_and_le_iff_eq.symm, not_and_or, not_le] using h
    simpa only [preform.holds, not_le, Int.add_one_le_iff] using h
  · simp only [neg_elim_core]
    cases h <;>
        [·
          left
          apply ihp,
        · right
          apply ihq] <;>
      assumption
  apply And.imp (ihp _) (ihq _) h
#align omega.nat.implies_neg_elim_core Omega.Nat.implies_negElimCore

/-- Eliminate all negations in a preform -/
def negElim : Preform → Preform :=
  negElimCore ∘ nnf
#align omega.nat.neg_elim Omega.Nat.negElim

theorem negFree_negElim {p : Preform} : (negElim p).NegFree :=
  negFree_negElimCore _ (isNnf_nnf _)
#align omega.nat.neg_free_neg_elim Omega.Nat.negFree_negElim

theorem implies_negElim {p : Preform} : Preform.Implies p (negElim p) :=
  by
  intro v h1; apply implies_neg_elim_core
  apply (nnf_equiv v).right h1
#align omega.nat.implies_neg_elim Omega.Nat.implies_negElim

end Nat

end Omega

