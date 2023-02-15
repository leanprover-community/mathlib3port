/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.ring.idempotents
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Basic
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Ring.Defs
import Mathbin.Tactic.NthRewrite.Default

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

/- warning: is_idempotent_elem.mul_of_commute -> IsIdempotentElem.mul_of_commute is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} [_inst_3 : Semigroup.{u1} S] {p : S} {q : S}, (Commute.{u1} S (Semigroup.toHasMul.{u1} S _inst_3) p q) -> (IsIdempotentElem.{u1} S (Semigroup.toHasMul.{u1} S _inst_3) p) -> (IsIdempotentElem.{u1} S (Semigroup.toHasMul.{u1} S _inst_3) q) -> (IsIdempotentElem.{u1} S (Semigroup.toHasMul.{u1} S _inst_3) (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (Semigroup.toHasMul.{u1} S _inst_3)) p q))
but is expected to have type
  forall {S : Type.{u1}} [_inst_3 : Semigroup.{u1} S] {p : S} {q : S}, (Commute.{u1} S (Semigroup.toMul.{u1} S _inst_3) p q) -> (IsIdempotentElem.{u1} S (Semigroup.toMul.{u1} S _inst_3) p) -> (IsIdempotentElem.{u1} S (Semigroup.toMul.{u1} S _inst_3) q) -> (IsIdempotentElem.{u1} S (Semigroup.toMul.{u1} S _inst_3) (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (Semigroup.toMul.{u1} S _inst_3)) p q))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.mul_of_commute IsIdempotentElem.mul_of_commuteₓ'. -/
theorem mul_of_commute {p q : S} (h : Commute p q) (h₁ : IsIdempotentElem p)
    (h₂ : IsIdempotentElem q) : IsIdempotentElem (p * q) := by
  rw [IsIdempotentElem, mul_assoc, ← mul_assoc q, ← h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq]
#align is_idempotent_elem.mul_of_commute IsIdempotentElem.mul_of_commute

/- warning: is_idempotent_elem.zero -> IsIdempotentElem.zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_4 : MulZeroClass.{u1} M₀], IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_4))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_4 : MulZeroClass.{u1} M₀], IsIdempotentElem.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_4) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_4)))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.zero IsIdempotentElem.zeroₓ'. -/
theorem zero : IsIdempotentElem (0 : M₀) :=
  mul_zero _
#align is_idempotent_elem.zero IsIdempotentElem.zero

/- warning: is_idempotent_elem.one -> IsIdempotentElem.one is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} [_inst_5 : MulOneClass.{u1} M₁], IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ _inst_5))))
but is expected to have type
  forall {M₁ : Type.{u1}} [_inst_5 : MulOneClass.{u1} M₁], IsIdempotentElem.{u1} M₁ (MulOneClass.toMul.{u1} M₁ _inst_5) (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (MulOneClass.toOne.{u1} M₁ _inst_5)))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.one IsIdempotentElem.oneₓ'. -/
theorem one : IsIdempotentElem (1 : M₁) :=
  mul_one _
#align is_idempotent_elem.one IsIdempotentElem.one

/- warning: is_idempotent_elem.one_sub -> IsIdempotentElem.one_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] {p : R}, (IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p) -> (IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6)))))) p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] {p : R}, (IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p) -> (IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (AddGroupWithOne.toSub.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_6))) p))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.one_sub IsIdempotentElem.one_subₓ'. -/
theorem one_sub {p : R} (h : IsIdempotentElem p) : IsIdempotentElem (1 - p) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]
#align is_idempotent_elem.one_sub IsIdempotentElem.one_sub

/- warning: is_idempotent_elem.one_sub_iff -> IsIdempotentElem.one_sub_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] {p : R}, Iff (IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6)))))) p)) (IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)
but is expected to have type
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] {p : R}, Iff (IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (AddGroupWithOne.toSub.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_6))) p)) (IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.one_sub_iff IsIdempotentElem.one_sub_iffₓ'. -/
@[simp]
theorem one_sub_iff {p : R} : IsIdempotentElem (1 - p) ↔ IsIdempotentElem p :=
  ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, IsIdempotentElem.one_sub⟩
#align is_idempotent_elem.one_sub_iff IsIdempotentElem.one_sub_iff

/- warning: is_idempotent_elem.pow -> IsIdempotentElem.pow is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_2 : Monoid.{u1} N] {p : N} (n : Nat), (IsIdempotentElem.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) p) -> (IsIdempotentElem.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (HPow.hPow.{u1, 0, u1} N Nat N (instHPow.{u1, 0} N Nat (Monoid.Pow.{u1} N _inst_2)) p n))
but is expected to have type
  forall {N : Type.{u1}} [_inst_2 : Monoid.{u1} N] {p : N} (n : Nat), (IsIdempotentElem.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) p) -> (IsIdempotentElem.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (HPow.hPow.{u1, 0, u1} N Nat N (instHPow.{u1, 0} N Nat (Monoid.Pow.{u1} N _inst_2)) p n))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.pow IsIdempotentElem.powₓ'. -/
theorem pow {p : N} (n : ℕ) (h : IsIdempotentElem p) : IsIdempotentElem (p ^ n) :=
  Nat.recOn n ((pow_zero p).symm ▸ one) fun n ih =>
    show p ^ n.succ * p ^ n.succ = p ^ n.succ
      by
      nth_rw 3 [← h.eq]
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']
#align is_idempotent_elem.pow IsIdempotentElem.pow

/- warning: is_idempotent_elem.pow_succ_eq -> IsIdempotentElem.pow_succ_eq is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_2 : Monoid.{u1} N] {p : N} (n : Nat), (IsIdempotentElem.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) p) -> (Eq.{succ u1} N (HPow.hPow.{u1, 0, u1} N Nat N (instHPow.{u1, 0} N Nat (Monoid.Pow.{u1} N _inst_2)) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) p)
but is expected to have type
  forall {N : Type.{u1}} [_inst_2 : Monoid.{u1} N] {p : N} (n : Nat), (IsIdempotentElem.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) p) -> (Eq.{succ u1} N (HPow.hPow.{u1, 0, u1} N Nat N (instHPow.{u1, 0} N Nat (Monoid.Pow.{u1} N _inst_2)) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) p)
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.pow_succ_eq IsIdempotentElem.pow_succ_eqₓ'. -/
theorem pow_succ_eq {p : N} (n : ℕ) (h : IsIdempotentElem p) : p ^ (n + 1) = p :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one p) fun n ih => by rw [pow_succ, ih, h.eq]
#align is_idempotent_elem.pow_succ_eq IsIdempotentElem.pow_succ_eq

/- warning: is_idempotent_elem.iff_eq_one -> IsIdempotentElem.iff_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_7 : Group.{u1} G] {p : G}, Iff (IsIdempotentElem.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)))) p) (Eq.{succ u1} G p (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_7 : Group.{u1} G] {p : G}, Iff (IsIdempotentElem.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)))) p) (Eq.{succ u1} G p (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_7)))))))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.iff_eq_one IsIdempotentElem.iff_eq_oneₓ'. -/
@[simp]
theorem iff_eq_one {p : G} : IsIdempotentElem p ↔ p = 1 :=
  Iff.intro (fun h => mul_left_cancel ((mul_one p).symm ▸ h.Eq : p * p = p * 1)) fun h =>
    h.symm ▸ one
#align is_idempotent_elem.iff_eq_one IsIdempotentElem.iff_eq_one

/- warning: is_idempotent_elem.iff_eq_zero_or_one -> IsIdempotentElem.iff_eq_zero_or_one is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_8 : CancelMonoidWithZero.{u1} G₀] {p : G₀}, Iff (IsIdempotentElem.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} G₀ _inst_8)))) p) (Or (Eq.{succ u1} G₀ p (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} G₀ _inst_8)))))))) (Eq.{succ u1} G₀ p (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} G₀ _inst_8)))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_8 : CancelMonoidWithZero.{u1} G₀] {p : G₀}, Iff (IsIdempotentElem.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} G₀ _inst_8)))) p) (Or (Eq.{succ u1} G₀ p (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} G₀ _inst_8))))) (Eq.{succ u1} G₀ p (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} G₀ _inst_8)))))))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.iff_eq_zero_or_one IsIdempotentElem.iff_eq_zero_or_oneₓ'. -/
@[simp]
theorem iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 :=
  by
  refine'
    Iff.intro (fun h => or_iff_not_imp_left.mpr fun hp => _) fun h =>
      h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one
  exact mul_left_cancel₀ hp (h.trans (mul_one p).symm)
#align is_idempotent_elem.iff_eq_zero_or_one IsIdempotentElem.iff_eq_zero_or_one

/-! ### Instances on `subtype is_idempotent_elem` -/


section Instances

instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩

/- warning: is_idempotent_elem.coe_zero -> IsIdempotentElem.coe_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_4 : MulZeroClass.{u1} M₀], Eq.{succ u1} M₀ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) M₀ (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) M₀ (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) M₀ (coeBase.{succ u1, succ u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) M₀ (coeSubtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p))))) (OfNat.ofNat.{u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) 0 (OfNat.mk.{u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) 0 (Zero.zero.{u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_4) p)) (IsIdempotentElem.Subtype.hasZero.{u1} M₀ _inst_4))))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_4))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_4 : MulZeroClass.{u1} M₀], Eq.{succ u1} M₀ (Subtype.val.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_4) p) (OfNat.ofNat.{u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_4) p)) 0 (Zero.toOfNat0.{u1} (Subtype.{succ u1} M₀ (fun (p : M₀) => IsIdempotentElem.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_4) p)) (IsIdempotentElem.instZeroSubtypeIsIdempotentElemToMul.{u1} M₀ _inst_4)))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_4)))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.coe_zero IsIdempotentElem.coe_zeroₓ'. -/
@[simp]
theorem coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) :=
  rfl
#align is_idempotent_elem.coe_zero IsIdempotentElem.coe_zero

instance : One { p : M₁ // IsIdempotentElem p } where one := ⟨1, one⟩

/- warning: is_idempotent_elem.coe_one -> IsIdempotentElem.coe_one is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} [_inst_5 : MulOneClass.{u1} M₁], Eq.{succ u1} M₁ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) M₁ (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) M₁ (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) M₁ (coeBase.{succ u1, succ u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) M₁ (coeSubtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p))))) (OfNat.ofNat.{u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) 1 (OfNat.mk.{u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) 1 (One.one.{u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_5) p)) (IsIdempotentElem.Subtype.hasOne.{u1} M₁ _inst_5))))) (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ _inst_5))))
but is expected to have type
  forall {M₁ : Type.{u1}} [_inst_5 : MulOneClass.{u1} M₁], Eq.{succ u1} M₁ (Subtype.val.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toMul.{u1} M₁ _inst_5) p) (OfNat.ofNat.{u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toMul.{u1} M₁ _inst_5) p)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} M₁ (fun (p : M₁) => IsIdempotentElem.{u1} M₁ (MulOneClass.toMul.{u1} M₁ _inst_5) p)) (IsIdempotentElem.instOneSubtypeIsIdempotentElemToMul.{u1} M₁ _inst_5)))) (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (MulOneClass.toOne.{u1} M₁ _inst_5)))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.coe_one IsIdempotentElem.coe_oneₓ'. -/
@[simp]
theorem coe_one : ↑(1 : { p : M₁ // IsIdempotentElem p }) = (1 : M₁) :=
  rfl
#align is_idempotent_elem.coe_one IsIdempotentElem.coe_one

instance : HasCompl { p : R // IsIdempotentElem p } :=
  ⟨fun p => ⟨1 - p, p.Prop.one_sub⟩⟩

/- warning: is_idempotent_elem.coe_compl -> IsIdempotentElem.coe_compl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] (p : Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)), Eq.{succ u1} R ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (coeBase.{succ u1, succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (coeSubtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p))))) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasCompl.{u1} R _inst_6) p)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (coeBase.{succ u1, succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) R (coeSubtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p))))) p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] (p : Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)), Eq.{succ u1} R (Subtype.val.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instHasComplSubtypeIsIdempotentElemToMulToNonUnitalNonAssocRing.{u1} R _inst_6) p)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (AddGroupWithOne.toSub.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_6))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_6))) (Subtype.val.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p) p))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.coe_compl IsIdempotentElem.coe_complₓ'. -/
@[simp]
theorem coe_compl (p : { p : R // IsIdempotentElem p }) : ↑(pᶜ) = (1 : R) - ↑p :=
  rfl
#align is_idempotent_elem.coe_compl IsIdempotentElem.coe_compl

/- warning: is_idempotent_elem.compl_compl -> IsIdempotentElem.compl_compl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] (p : Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)), Eq.{succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasCompl.{u1} R _inst_6) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasCompl.{u1} R _inst_6) p)) p
but is expected to have type
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R] (p : Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)), Eq.{succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instHasComplSubtypeIsIdempotentElemToMulToNonUnitalNonAssocRing.{u1} R _inst_6) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instHasComplSubtypeIsIdempotentElemToMulToNonUnitalNonAssocRing.{u1} R _inst_6) p)) p
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.compl_compl IsIdempotentElem.compl_complₓ'. -/
@[simp]
theorem compl_compl (p : { p : R // IsIdempotentElem p }) : pᶜᶜ = p :=
  Subtype.ext <| sub_sub_cancel _ _
#align is_idempotent_elem.compl_compl IsIdempotentElem.compl_compl

/- warning: is_idempotent_elem.zero_compl -> IsIdempotentElem.zero_compl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R], Eq.{succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasCompl.{u1} R _inst_6) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 0 (OfNat.mk.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 0 (Zero.zero.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))))))) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 1 (OfNat.mk.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 1 (One.one.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_6)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R], Eq.{succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instHasComplSubtypeIsIdempotentElemToMulToNonUnitalNonAssocRing.{u1} R _inst_6) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) 0 (Zero.toOfNat0.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instZeroSubtypeIsIdempotentElemToMul.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6))))))) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instOneSubtypeIsIdempotentElemToMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_6))))))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.zero_compl IsIdempotentElem.zero_complₓ'. -/
@[simp]
theorem zero_compl : (0 : { p : R // IsIdempotentElem p })ᶜ = 1 :=
  Subtype.ext <| sub_zero _
#align is_idempotent_elem.zero_compl IsIdempotentElem.zero_compl

/- warning: is_idempotent_elem.one_compl -> IsIdempotentElem.one_compl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R], Eq.{succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasCompl.{u1} R _inst_6) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 1 (OfNat.mk.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 1 (One.one.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_6)))))))) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 0 (OfNat.mk.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) 0 (Zero.zero.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))) p)) (IsIdempotentElem.Subtype.hasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_6 : NonAssocRing.{u1} R], Eq.{succ u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (HasCompl.compl.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instHasComplSubtypeIsIdempotentElemToMulToNonUnitalNonAssocRing.{u1} R _inst_6) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instOneSubtypeIsIdempotentElemToMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_6))))))) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) 0 (Zero.toOfNat0.{u1} (Subtype.{succ u1} R (fun (p : R) => IsIdempotentElem.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6)) p)) (IsIdempotentElem.instZeroSubtypeIsIdempotentElemToMul.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_6))))))
Case conversion may be inaccurate. Consider using '#align is_idempotent_elem.one_compl IsIdempotentElem.one_complₓ'. -/
@[simp]
theorem one_compl : (1 : { p : R // IsIdempotentElem p })ᶜ = 0 :=
  Subtype.ext <| sub_self _
#align is_idempotent_elem.one_compl IsIdempotentElem.one_compl

end Instances

end IsIdempotentElem

