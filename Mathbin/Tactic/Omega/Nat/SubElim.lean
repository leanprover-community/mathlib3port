/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.nat.sub_elim
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.Nat.Form

/-
Subtraction elimination for linear natural number arithmetic.
Works by repeatedly rewriting goals of the preform `P[t-s]` into
`P[x] ∧ (t = s + x ∨ (t ≤ s ∧ x = 0))`, where `x` is fresh.
-/
namespace Omega

namespace Nat

open Omega.Nat

namespace Preterm

/-- Find subtraction inside preterm and return its operands -/
def subTerms : Preterm → Option (preterm × preterm)
  | &i => none
  | i ** n => none
  | t +* s => t.subTerms <|> s.subTerms
  | t -* s => t.subTerms <|> s.subTerms <|> some (t, s)
#align omega.nat.preterm.sub_terms Omega.Nat.Preterm.subTerms

/-- Find (t - s) inside a preterm and replace it with variable k -/
def subSubst (t s : Preterm) (k : Nat) : Preterm → Preterm
  | t@(&m) => t
  | t@(m ** n) => t
  | x +* y => x.subSubst +* y.subSubst
  | x -* y => if x = t ∧ y = s then 1 ** k else x.subSubst -* y.subSubst
#align omega.nat.preterm.sub_subst Omega.Nat.Preterm.subSubst

theorem val_sub_subst {k : Nat} {x y : Preterm} {v : Nat → Nat} :
    ∀ {t : Preterm},
      t.freshIndex ≤ k → (subSubst x y k t).val (update k (x.val v - y.val v) v) = t.val v
  | &m, h1 => rfl
  | m ** n, h1 => by 
    have h2 : n ≠ k := ne_of_lt h1
    simp only [sub_subst, preterm.val]
    rw [update_eq_of_ne _ h2]
  | t +* s, h1 => by 
    simp only [sub_subst, val_add]; apply fun_mono_2 <;> apply val_sub_subst (le_trans _ h1)
    apply le_max_left; apply le_max_right
  | t -* s, h1 => by 
    simp only [sub_subst, val_sub]
    by_cases h2 : t = x ∧ s = y
    · rw [if_pos h2]
      simp only [val_var, one_mul]
      rw [update_eq, h2.left, h2.right]
    · rw [if_neg h2]
      simp only [val_sub, sub_subst]
      apply fun_mono_2 <;> apply val_sub_subst (le_trans _ h1)
      apply le_max_left
      apply le_max_right
#align omega.nat.preterm.val_sub_subst Omega.Nat.Preterm.val_sub_subst

end Preterm

namespace Preform

/-- Find subtraction inside preform and return its operands -/
def subTerms : Preform → Option (preterm × preterm)
  | t =* s => t.subTerms <|> s.subTerms
  | t ≤* s => t.subTerms <|> s.subTerms
  | ¬* p => p.subTerms
  | p ∨* q => p.subTerms <|> q.subTerms
  | p ∧* q => p.subTerms <|> q.subTerms
#align omega.nat.preform.sub_terms Omega.Nat.Preform.subTerms

/-- Find (t - s) inside a preform and replace it with variable k -/
@[simp]
def subSubst (x y : Preterm) (k : Nat) : Preform → Preform
  | t =* s => Preterm.subSubst x y k t =* Preterm.subSubst x y k s
  | t ≤* s => Preterm.subSubst x y k t ≤* Preterm.subSubst x y k s
  | ¬* p => ¬* p.subSubst
  | p ∨* q => p.subSubst ∨* q.subSubst
  | p ∧* q => p.subSubst ∧* q.subSubst
#align omega.nat.preform.sub_subst Omega.Nat.Preform.subSubst

end Preform

/-- Preform which asserts that the value of variable k is
    the truncated difference between preterms t and s -/
def isDiff (t s : Preterm) (k : Nat) : Preform :=
  (t =* s +* 1 ** k) ∨* (t ≤* s) ∧* (1 ** k) =* &0
#align omega.nat.is_diff Omega.Nat.isDiff

theorem holds_is_diff {t s : Preterm} {k : Nat} {v : Nat → Nat} :
    v k = t.val v - s.val v → (isDiff t s k).Holds v := by
  intro h1
  simp only [preform.holds, is_diff, if_pos (Eq.refl 1), preterm.val_add, preterm.val_var,
    preterm.val_const]
  cases' le_total (t.val v) (s.val v) with h2 h2
  · right
    refine' ⟨h2, _⟩
    rw [h1, one_mul, tsub_eq_zero_iff_le]
    exact h2
  · left
    rw [h1, one_mul, add_comm, tsub_add_cancel_of_le h2]
#align omega.nat.holds_is_diff Omega.Nat.holds_is_diff

/-- Helper function for sub_elim -/
def subElimCore (t s : Preterm) (k : Nat) (p : Preform) : Preform :=
  Preform.subSubst t s k p ∧* isDiff t s k
#align omega.nat.sub_elim_core Omega.Nat.subElimCore

/-- Return de Brujin index of fresh variable that does not occur
    in any of the arguments -/
def subFreshIndex (t s : Preterm) (p : Preform) : Nat :=
  max p.freshIndex (max t.freshIndex s.freshIndex)
#align omega.nat.sub_fresh_index Omega.Nat.subFreshIndex

/-- Return a new preform with all subtractions eliminated -/
def subElim (t s : Preterm) (p : Preform) : Preform :=
  subElimCore t s (subFreshIndex t s p) p
#align omega.nat.sub_elim Omega.Nat.subElim

theorem sub_subst_equiv {k : Nat} {x y : Preterm} {v : Nat → Nat} :
    ∀ p : Preform,
      p.freshIndex ≤ k →
        ((Preform.subSubst x y k p).Holds (update k (x.val v - y.val v) v) ↔ p.Holds v)
  | t =* s, h1 => by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply preterm.val_sub_subst (le_trans _ h1)
    apply le_max_left; apply le_max_right
  | t ≤* s, h1 => by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply preterm.val_sub_subst (le_trans _ h1)
    apply le_max_left; apply le_max_right
  | ¬* p, h1 => by 
    apply not_congr
    apply sub_subst_equiv p h1
  | p ∨* q, h1 => by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply propext <;> apply sub_subst_equiv _ (le_trans _ h1)
    apply le_max_left; apply le_max_right
  | p ∧* q, h1 => by 
    simp only [preform.holds, preform.sub_subst]
    apply pred_mono_2 <;> apply propext <;> apply sub_subst_equiv _ (le_trans _ h1)
    apply le_max_left; apply le_max_right
#align omega.nat.sub_subst_equiv Omega.Nat.sub_subst_equiv

theorem sat_sub_elim {t s : Preterm} {p : Preform} : p.Sat → (subElim t s p).Sat := by
  intro h1; simp only [sub_elim, sub_elim_core]
  cases' h1 with v h1
  refine' ⟨update (sub_fresh_index t s p) (t.val v - s.val v) v, _⟩
  constructor
  · apply (sub_subst_equiv p _).elimRight h1
    apply le_max_left
  · apply holds_is_diff
    rw [update_eq]
    apply fun_mono_2 <;> apply preterm.val_constant <;> intro x h2 <;>
          rw [update_eq_of_ne _ (Ne.symm (ne_of_gt _))] <;>
        apply lt_of_lt_of_le h2 <;>
      apply le_trans _ (le_max_right _ _)
    apply le_max_left
    apply le_max_right
#align omega.nat.sat_sub_elim Omega.Nat.sat_sub_elim

theorem unsat_of_unsat_sub_elim (t s : Preterm) (p : Preform) : (subElim t s p).Unsat → p.Unsat :=
  mt sat_sub_elim
#align omega.nat.unsat_of_unsat_sub_elim Omega.Nat.unsat_of_unsat_sub_elim

end Nat

end Omega

