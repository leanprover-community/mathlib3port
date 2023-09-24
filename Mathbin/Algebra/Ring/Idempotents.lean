/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Order.Basic
import Algebra.GroupPower.Basic
import Algebra.Ring.Defs
import Mathbin.Tactic.NthRewrite.Default

#align_import algebra.ring.idempotents from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Idempotents

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines idempotents for an arbitary multiplication and proves some basic results,
including:

* `is_idempotent_elem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `is_idempotent_elem.one_sub_iff`: In a (non-associative) ring, `p` is an idempotent if and only if
  `1-p` is an idempotent.
* `is_idempotent_elem.pow_succ_eq`: In a monoid `p ^ (n+1) = p` for `p` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/


variable {M N S M₀ M₁ R G G₀ : Type _}

variable [Mul M] [Monoid N] [Semigroup S] [MulZeroClass M₀] [MulOneClass M₁] [NonAssocRing R]
  [Group G] [CancelMonoidWithZero G₀]

#print IsIdempotentElem /-
/-- An element `p` is said to be idempotent if `p * p = p`
-/
def IsIdempotentElem (p : M) : Prop :=
  p * p = p
#align is_idempotent_elem IsIdempotentElem
-/

namespace IsIdempotentElem

#print IsIdempotentElem.of_isIdempotent /-
theorem of_isIdempotent [IsIdempotent M (· * ·)] (a : M) : IsIdempotentElem a :=
  IsIdempotent.idempotent a
#align is_idempotent_elem.of_is_idempotent IsIdempotentElem.of_isIdempotent
-/

#print IsIdempotentElem.eq /-
theorem eq {p : M} (h : IsIdempotentElem p) : p * p = p :=
  h
#align is_idempotent_elem.eq IsIdempotentElem.eq
-/

#print IsIdempotentElem.mul_of_commute /-
theorem mul_of_commute {p q : S} (h : Commute p q) (h₁ : IsIdempotentElem p)
    (h₂ : IsIdempotentElem q) : IsIdempotentElem (p * q) := by
  rw [IsIdempotentElem, mul_assoc, ← mul_assoc q, ← h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq]
#align is_idempotent_elem.mul_of_commute IsIdempotentElem.mul_of_commute
-/

#print IsIdempotentElem.zero /-
theorem zero : IsIdempotentElem (0 : M₀) :=
  MulZeroClass.mul_zero _
#align is_idempotent_elem.zero IsIdempotentElem.zero
-/

#print IsIdempotentElem.one /-
theorem one : IsIdempotentElem (1 : M₁) :=
  mul_one _
#align is_idempotent_elem.one IsIdempotentElem.one
-/

#print IsIdempotentElem.one_sub /-
theorem one_sub {p : R} (h : IsIdempotentElem p) : IsIdempotentElem (1 - p) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]
#align is_idempotent_elem.one_sub IsIdempotentElem.one_sub
-/

#print IsIdempotentElem.one_sub_iff /-
@[simp]
theorem one_sub_iff {p : R} : IsIdempotentElem (1 - p) ↔ IsIdempotentElem p :=
  ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, IsIdempotentElem.one_sub⟩
#align is_idempotent_elem.one_sub_iff IsIdempotentElem.one_sub_iff
-/

#print IsIdempotentElem.pow /-
theorem pow {p : N} (n : ℕ) (h : IsIdempotentElem p) : IsIdempotentElem (p ^ n) :=
  Nat.recOn n ((pow_zero p).symm ▸ one) fun n ih =>
    show p ^ n.succ * p ^ n.succ = p ^ n.succ by nth_rw 3 [← h.eq];
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']
#align is_idempotent_elem.pow IsIdempotentElem.pow
-/

#print IsIdempotentElem.pow_succ_eq /-
theorem pow_succ_eq {p : N} (n : ℕ) (h : IsIdempotentElem p) : p ^ (n + 1) = p :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one p) fun n ih => by rw [pow_succ, ih, h.eq]
#align is_idempotent_elem.pow_succ_eq IsIdempotentElem.pow_succ_eq
-/

#print IsIdempotentElem.iff_eq_one /-
@[simp]
theorem iff_eq_one {p : G} : IsIdempotentElem p ↔ p = 1 :=
  Iff.intro (fun h => mul_left_cancel ((mul_one p).symm ▸ h.Eq : p * p = p * 1)) fun h =>
    h.symm ▸ one
#align is_idempotent_elem.iff_eq_one IsIdempotentElem.iff_eq_one
-/

#print IsIdempotentElem.iff_eq_zero_or_one /-
@[simp]
theorem iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 :=
  by
  refine'
    Iff.intro (fun h => or_iff_not_imp_left.mpr fun hp => _) fun h =>
      h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one
  exact mul_left_cancel₀ hp (h.trans (mul_one p).symm)
#align is_idempotent_elem.iff_eq_zero_or_one IsIdempotentElem.iff_eq_zero_or_one
-/

/-! ### Instances on `subtype is_idempotent_elem` -/


section Instances

instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩

#print IsIdempotentElem.coe_zero /-
@[simp]
theorem coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) :=
  rfl
#align is_idempotent_elem.coe_zero IsIdempotentElem.coe_zero
-/

instance : One { p : M₁ // IsIdempotentElem p } where one := ⟨1, one⟩

#print IsIdempotentElem.coe_one /-
@[simp]
theorem coe_one : ↑(1 : { p : M₁ // IsIdempotentElem p }) = (1 : M₁) :=
  rfl
#align is_idempotent_elem.coe_one IsIdempotentElem.coe_one
-/

instance : HasCompl { p : R // IsIdempotentElem p } :=
  ⟨fun p => ⟨1 - p, p.Prop.one_sub⟩⟩

#print IsIdempotentElem.coe_compl /-
@[simp]
theorem coe_compl (p : { p : R // IsIdempotentElem p }) : ↑(pᶜ) = (1 : R) - ↑p :=
  rfl
#align is_idempotent_elem.coe_compl IsIdempotentElem.coe_compl
-/

#print IsIdempotentElem.compl_compl /-
@[simp]
theorem compl_compl (p : { p : R // IsIdempotentElem p }) : pᶜᶜ = p :=
  Subtype.ext <| sub_sub_cancel _ _
#align is_idempotent_elem.compl_compl IsIdempotentElem.compl_compl
-/

#print IsIdempotentElem.zero_compl /-
@[simp]
theorem zero_compl : (0 : { p : R // IsIdempotentElem p })ᶜ = 1 :=
  Subtype.ext <| sub_zero _
#align is_idempotent_elem.zero_compl IsIdempotentElem.zero_compl
-/

#print IsIdempotentElem.one_compl /-
@[simp]
theorem one_compl : (1 : { p : R // IsIdempotentElem p })ᶜ = 0 :=
  Subtype.ext <| sub_self _
#align is_idempotent_elem.one_compl IsIdempotentElem.one_compl
-/

end Instances

end IsIdempotentElem

