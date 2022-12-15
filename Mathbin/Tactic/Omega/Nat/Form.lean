/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.nat.form
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.Nat.Preterm

/-
Linear natural number arithmetic preformulas in pre-normalized preform.
-/
namespace Omega

namespace Nat

/-- Intermediate shadow syntax for LNA formulas that includes unreified exprs -/
unsafe inductive exprform
  | Eq : exprterm → exprterm → exprform
  | le : exprterm → exprterm → exprform
  | Not : exprform → exprform
  | Or : exprform → exprform → exprform
  | And : exprform → exprform → exprform
#align omega.nat.exprform omega.nat.exprform

/-- Intermediate shadow syntax for LNA formulas that includes non-canonical terms -/
inductive Preform
  | Eq : Preterm → Preterm → preform
  | le : Preterm → Preterm → preform
  | Not : preform → preform
  | Or : preform → preform → preform
  | And : preform → preform → preform
  deriving has_reflect, Inhabited
#align omega.nat.preform Omega.Nat.Preform

-- mathport name: preform.eq
scoped notation x " =* " y => Omega.Nat.Preform.eq x y

-- mathport name: preform.le
scoped notation x " ≤* " y => Omega.Nat.Preform.le x y

-- mathport name: preform.not
scoped notation "¬* " p => Omega.Nat.Preform.not p

-- mathport name: preform.or
scoped notation p " ∨* " q => Omega.Nat.Preform.or p q

-- mathport name: preform.and
scoped notation p " ∧* " q => Omega.Nat.Preform.and p q

namespace Preform

/-- Evaluate a preform into prop using the valuation `v`. -/
@[simp]
def Holds (v : Nat → Nat) : Preform → Prop
  | t =* s => t.val v = s.val v
  | t ≤* s => t.val v ≤ s.val v
  | ¬* p => ¬p.Holds
  | p ∨* q => p.Holds ∨ q.Holds
  | p ∧* q => p.Holds ∧ q.Holds
#align omega.nat.preform.holds Omega.Nat.Preform.Holds

end Preform

/-- `univ_close p n` := `p` closed by prepending `n` universal quantifiers -/
@[simp]
def UnivClose (p : Preform) : (Nat → Nat) → Nat → Prop
  | v, 0 => p.Holds v
  | v, k + 1 => ∀ i : Nat, univ_close (updateZero i v) k
#align omega.nat.univ_close Omega.Nat.UnivClose

namespace Preform

/-- Argument is free of negations -/
def NegFree : Preform → Prop
  | t =* s => True
  | t ≤* s => True
  | p ∨* q => neg_free p ∧ neg_free q
  | p ∧* q => neg_free p ∧ neg_free q
  | _ => False
#align omega.nat.preform.neg_free Omega.Nat.Preform.NegFree

/-- Return expr of proof that argument is free of subtractions -/
def SubFree : Preform → Prop
  | t =* s => t.SubFree ∧ s.SubFree
  | t ≤* s => t.SubFree ∧ s.SubFree
  | ¬* p => p.SubFree
  | p ∨* q => p.SubFree ∧ q.SubFree
  | p ∧* q => p.SubFree ∧ q.SubFree
#align omega.nat.preform.sub_free Omega.Nat.Preform.SubFree

/-- Fresh de Brujin index not used by any variable in argument -/
def freshIndex : Preform → Nat
  | t =* s => max t.freshIndex s.freshIndex
  | t ≤* s => max t.freshIndex s.freshIndex
  | ¬* p => p.freshIndex
  | p ∨* q => max p.freshIndex q.freshIndex
  | p ∧* q => max p.freshIndex q.freshIndex
#align omega.nat.preform.fresh_index Omega.Nat.Preform.freshIndex

theorem holds_constant {v w : Nat → Nat} :
    ∀ p : Preform, (∀ x < p.freshIndex, v x = w x) → (p.Holds v ↔ p.Holds w)
  | t =* s, h1 => by 
    simp only [holds]
    apply pred_mono_2 <;> apply preterm.val_constant <;> intro x h2 <;>
      apply h1 _ (lt_of_lt_of_le h2 _)
    apply le_max_left; apply le_max_right
  | t ≤* s, h1 => by 
    simp only [holds]
    apply pred_mono_2 <;> apply preterm.val_constant <;> intro x h2 <;>
      apply h1 _ (lt_of_lt_of_le h2 _)
    apply le_max_left; apply le_max_right
  | ¬* p, h1 => by 
    apply not_congr
    apply holds_constant p h1
  | p ∨* q, h1 => by 
    simp only [holds]
    apply pred_mono_2' <;> apply holds_constant <;> intro x h2 <;> apply h1 _ (lt_of_lt_of_le h2 _)
    apply le_max_left; apply le_max_right
  | p ∧* q, h1 => by 
    simp only [holds]
    apply pred_mono_2' <;> apply holds_constant <;> intro x h2 <;> apply h1 _ (lt_of_lt_of_le h2 _)
    apply le_max_left; apply le_max_right
#align omega.nat.preform.holds_constant Omega.Nat.Preform.holds_constant

/-- All valuations satisfy argument -/
def Valid (p : Preform) : Prop :=
  ∀ v, Holds v p
#align omega.nat.preform.valid Omega.Nat.Preform.Valid

/-- There exists some valuation that satisfies argument -/
def Sat (p : Preform) : Prop :=
  ∃ v, Holds v p
#align omega.nat.preform.sat Omega.Nat.Preform.Sat

/-- `implies p q` := under any valuation, `q` holds if `p` holds -/
def Implies (p q : Preform) : Prop :=
  ∀ v, Holds v p → Holds v q
#align omega.nat.preform.implies Omega.Nat.Preform.Implies

/-- `equiv p q` := under any valuation, `p` holds iff `q` holds -/
def Equiv (p q : Preform) : Prop :=
  ∀ v, Holds v p ↔ Holds v q
#align omega.nat.preform.equiv Omega.Nat.Preform.Equiv

theorem sat_of_implies_of_sat {p q : Preform} : Implies p q → Sat p → Sat q := by intro h1 h2;
  apply Exists.imp h1 h2
#align omega.nat.preform.sat_of_implies_of_sat Omega.Nat.Preform.sat_of_implies_of_sat

theorem sat_or {p q : Preform} : Sat (p ∨* q) ↔ Sat p ∨ Sat q := by
  constructor <;> intro h1
  · cases' h1 with v h1
    cases' h1 with h1 h1 <;> [left, right] <;> refine' ⟨v, _⟩ <;> assumption
  · cases' h1 with h1 h1 <;> cases' h1 with v h1 <;> refine' ⟨v, _⟩ <;> [left, right] <;> assumption
#align omega.nat.preform.sat_or Omega.Nat.Preform.sat_or

/-- There does not exist any valuation that satisfies argument -/
def Unsat (p : Preform) : Prop :=
  ¬Sat p
#align omega.nat.preform.unsat Omega.Nat.Preform.Unsat

def repr : Preform → String
  | t =* s => "(" ++ t.repr ++ " = " ++ s.repr ++ ")"
  | t ≤* s => "(" ++ t.repr ++ " ≤ " ++ s.repr ++ ")"
  | ¬* p => "¬" ++ p.repr
  | p ∨* q => "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
  | p ∧* q => "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"
#align omega.nat.preform.repr Omega.Nat.Preform.repr

instance hasRepr : Repr Preform :=
  ⟨repr⟩
#align omega.nat.preform.has_repr Omega.Nat.Preform.hasRepr

unsafe instance has_to_format : has_to_format Preform :=
  ⟨fun x => x.repr⟩
#align omega.nat.preform.has_to_format omega.nat.preform.has_to_format

end Preform

theorem univ_close_of_valid {p : Preform} : ∀ {m : Nat} {v : Nat → Nat}, p.valid → UnivClose p v m
  | 0, v, h1 => h1 _
  | m + 1, v, h1 => fun i => univ_close_of_valid h1
#align omega.nat.univ_close_of_valid Omega.Nat.univ_close_of_valid

theorem valid_of_unsat_not {p : Preform} : (¬* p).Unsat → p.valid := by
  simp only [preform.sat, preform.unsat, preform.valid, preform.holds]
  rw [not_exists_not]; intro h; assumption
#align omega.nat.valid_of_unsat_not Omega.Nat.valid_of_unsat_not

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic for setting up proof by induction over preforms. -/
unsafe def preform.induce (t : tactic Unit := tactic.skip) : tactic Unit :=
  sorry
#align omega.nat.preform.induce omega.nat.preform.induce

end Nat

end Omega

