/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module ring_theory.nilpotent
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Algebra.Algebra.Bilinear
import Mathbin.RingTheory.Ideal.Operations

/-!
# Nilpotent elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

  * `is_nilpotent`
  * `is_nilpotent_neg_iff`
  * `commute.is_nilpotent_add`
  * `commute.is_nilpotent_mul_left`
  * `commute.is_nilpotent_mul_right`
  * `commute.is_nilpotent_sub`

-/


universe u v

variable {R S : Type u} {x y : R}

#print IsNilpotent /-
/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0
#align is_nilpotent IsNilpotent
-/

#print IsNilpotent.mk /-
theorem IsNilpotent.mk [Zero R] [Pow R ℕ] (x : R) (n : ℕ) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩
#align is_nilpotent.mk IsNilpotent.mk
-/

/- warning: is_nilpotent.zero -> IsNilpotent.zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R], IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R], IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_nilpotent.zero IsNilpotent.zeroₓ'. -/
theorem IsNilpotent.zero [MonoidWithZero R] : IsNilpotent (0 : R) :=
  ⟨1, pow_one 0⟩
#align is_nilpotent.zero IsNilpotent.zero

/- warning: is_nilpotent.neg -> IsNilpotent.neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} [_inst_1 : Ring.{u1} R], (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) x) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x))
but is expected to have type
  forall {R : Type.{u1}} {x : R} [_inst_1 : Ring.{u1} R], (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) x) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) x))
Case conversion may be inaccurate. Consider using '#align is_nilpotent.neg IsNilpotent.negₓ'. -/
theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) :=
  by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, MulZeroClass.mul_zero]
#align is_nilpotent.neg IsNilpotent.neg

/- warning: is_nilpotent_neg_iff -> isNilpotent_neg_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} [_inst_1 : Ring.{u1} R], Iff (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1))))) x)) (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) x)
but is expected to have type
  forall {R : Type.{u1}} {x : R} [_inst_1 : Ring.{u1} R], Iff (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) x)) (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) x)
Case conversion may be inaccurate. Consider using '#align is_nilpotent_neg_iff isNilpotent_neg_iffₓ'. -/
@[simp]
theorem isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩
#align is_nilpotent_neg_iff isNilpotent_neg_iff

/- warning: is_nilpotent.map -> IsNilpotent.map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_2 : MonoidWithZero.{u1} S] {r : R} {F : Type.{u2}} [_inst_3 : MonoidWithZeroHomClass.{u2, u1, u1} F R S (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2)], (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) r) -> (forall (f : F), IsNilpotent.{u1} S (MulZeroClass.toHasZero.{u1} S (MulZeroOneClass.toMulZeroClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2))) (Monoid.Pow.{u1} S (MonoidWithZero.toMonoid.{u1} S _inst_2)) (coeFn.{succ u2, succ u1} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u2, succ u1, succ u1} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u2, u1, u1} F R S (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (MulOneClass.toHasMul.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2))) (MonoidHomClass.toMulHomClass.{u2, u1, u1} F R S (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2)) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u1, u1} F R S (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2) _inst_3)))) f r))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} R] [_inst_2 : MonoidWithZero.{u2} S] {r : R} {F : Type.{u1}} [_inst_3 : MonoidWithZeroHomClass.{u1, u2, u2} F R S (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2)], (IsNilpotent.{u2} R (MonoidWithZero.toZero.{u2} R _inst_1) (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R _inst_1)) r) -> (forall (f : F), IsNilpotent.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) r) (MonoidWithZero.toZero.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) r) _inst_2) (Monoid.Pow.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) r) (MonoidWithZero.toMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) r) _inst_2)) (FunLike.coe.{succ u1, succ u2, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{u1, u2, u2} F R S (MulOneClass.toMul.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1))) (MulOneClass.toMul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u2, u2} F R S (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u2, u2} F R S (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2) _inst_3))) f r))
Case conversion may be inaccurate. Consider using '#align is_nilpotent.map IsNilpotent.mapₓ'. -/
theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type _}
    [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) : IsNilpotent (f r) :=
  by
  use hr.some
  rw [← map_pow, hr.some_spec, map_zero]
#align is_nilpotent.map IsNilpotent.map

#print IsReduced /-
/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
class IsReduced (R : Type _) [Zero R] [Pow R ℕ] : Prop where
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
#align is_reduced IsReduced
-/

/- warning: is_reduced_of_no_zero_divisors -> isReduced_of_noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (MulZeroClass.toHasMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)))], IsReduced.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (MulZeroClass.toMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R _inst_1)], IsReduced.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align is_reduced_of_no_zero_divisors isReduced_of_noZeroDivisorsₓ'. -/
instance (priority := 900) isReduced_of_noZeroDivisors [MonoidWithZero R] [NoZeroDivisors R] :
    IsReduced R :=
  ⟨fun _ ⟨_, hn⟩ => pow_eq_zero hn⟩
#align is_reduced_of_no_zero_divisors isReduced_of_noZeroDivisors

#print isReduced_of_subsingleton /-
instance (priority := 900) isReduced_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] :
    IsReduced R :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩
#align is_reduced_of_subsingleton isReduced_of_subsingleton
-/

#print IsNilpotent.eq_zero /-
theorem IsNilpotent.eq_zero [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h
#align is_nilpotent.eq_zero IsNilpotent.eq_zero
-/

/- warning: is_nilpotent_iff_eq_zero -> isNilpotent_iff_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} [_inst_1 : MonoidWithZero.{u1} R] [_inst_2 : IsReduced.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))], Iff (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) x) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} {x : R} [_inst_1 : MonoidWithZero.{u1} R] [_inst_2 : IsReduced.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))], Iff (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) x) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_nilpotent_iff_eq_zero isNilpotent_iff_eq_zeroₓ'. -/
@[simp]
theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩
#align is_nilpotent_iff_eq_zero isNilpotent_iff_eq_zero

/- warning: is_reduced_of_injective -> isReduced_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R] [_inst_2 : MonoidWithZero.{u1} S] {F : Type.{u2}} [_inst_3 : MonoidWithZeroHomClass.{u2, u1, u1} F R S (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2)] (f : F), (Function.Injective.{succ u1, succ u1} R S (coeFn.{succ u2, succ u1} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u2, succ u1, succ u1} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u2, u1, u1} F R S (MulOneClass.toHasMul.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (MulOneClass.toHasMul.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2))) (MonoidHomClass.toMulHomClass.{u2, u1, u1} F R S (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2)) (MonoidWithZeroHomClass.toMonoidHomClass.{u2, u1, u1} F R S (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2) _inst_3)))) f)) -> (forall [_inst_4 : IsReduced.{u1} S (MulZeroClass.toHasZero.{u1} S (MulZeroOneClass.toMulZeroClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S _inst_2))) (Monoid.Pow.{u1} S (MonoidWithZero.toMonoid.{u1} S _inst_2))], IsReduced.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u2}} [_inst_1 : MonoidWithZero.{u2} R] [_inst_2 : MonoidWithZero.{u2} S] {F : Type.{u1}} [_inst_3 : MonoidWithZeroHomClass.{u1, u2, u2} F R S (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2)] (f : F), (Function.Injective.{succ u2, succ u2} R S (FunLike.coe.{succ u1, succ u2, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{u1, u2, u2} F R S (MulOneClass.toMul.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1))) (MulOneClass.toMul.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u2, u2} F R S (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2)) (MonoidWithZeroHomClass.toMonoidHomClass.{u1, u2, u2} F R S (MonoidWithZero.toMulZeroOneClass.{u2} R _inst_1) (MonoidWithZero.toMulZeroOneClass.{u2} S _inst_2) _inst_3))) f)) -> (forall [_inst_4 : IsReduced.{u2} S (MonoidWithZero.toZero.{u2} S _inst_2) (Monoid.Pow.{u2} S (MonoidWithZero.toMonoid.{u2} S _inst_2))], IsReduced.{u2} R (MonoidWithZero.toZero.{u2} R _inst_1) (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_reduced_of_injective isReduced_of_injectiveₓ'. -/
theorem isReduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type _}
    [MonoidWithZeroHomClass F R S] (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero
#align is_reduced_of_injective isReduced_of_injective

/- warning: ring_hom.ker_is_radical_iff_reduced_of_surjective -> RingHom.ker_isRadical_iff_reduced_of_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {F : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommRing.{u2} S] [_inst_3 : RingHomClass.{u3, u1, u2} F R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))] {f : F}, (Function.Surjective.{succ u1, succ u2} R S (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => R -> S) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F R (fun (_x : R) => S) (MulHomClass.toFunLike.{u3, u1, u2} F R S (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) (NonUnitalRingHomClass.toMulHomClass.{u3, u1, u2} F R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{u3, u1, u2} F R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))) _inst_3)))) f)) -> (Iff (Ideal.IsRadical.{u1} R _inst_1 (RingHom.ker.{u1, u2, u3} R S F (CommSemiring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3 f)) (IsReduced.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))) (Monoid.Pow.{u2} S (Ring.toMonoid.{u2} S (CommRing.toRing.{u2} S _inst_2)))))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} {F : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : CommRing.{u2} S] [_inst_3 : RingHomClass.{u1, u3, u2} F R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))] {f : F}, (Function.Surjective.{succ u3, succ u2} R S (FunLike.coe.{succ u1, succ u3, succ u2} F R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{u1, u3, u2} F R S (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{u1, u3, u2} F R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{u1, u3, u2} F R S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))) _inst_3))) f)) -> (Iff (Ideal.IsRadical.{u3} R _inst_1 (RingHom.ker.{u3, u2, u1} R S F (CommSemiring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3 f)) (IsReduced.{u2} S (CommMonoidWithZero.toZero.{u2} S (CommSemiring.toCommMonoidWithZero.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (Monoid.Pow.{u2} S (MonoidWithZero.toMonoid.{u2} S (Semiring.toMonoidWithZero.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align ring_hom.ker_is_radical_iff_reduced_of_surjective RingHom.ker_isRadical_iff_reduced_of_surjectiveₓ'. -/
theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [CommRing S]
    [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker] <;> rfl
#align ring_hom.ker_is_radical_iff_reduced_of_surjective RingHom.ker_isRadical_iff_reduced_of_surjective

#print IsRadical /-
/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
#align is_radical IsRadical
-/

/- warning: zero_is_radical_iff -> zero_isRadical_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R], Iff (IsRadical.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (MonoidWithZero.toSemigroupWithZero.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))))))) (IsReduced.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R], Iff (IsRadical.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (MonoidWithZero.toSemigroupWithZero.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1)))) (IsReduced.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align zero_is_radical_iff zero_isRadical_iffₓ'. -/
theorem zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R :=
  by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_swap
#align zero_is_radical_iff zero_isRadical_iff

#print isRadical_iff_span_singleton /-
theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical :=
  by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_swap.trans (forall_congr' fun r => exists_imp_distrib.symm)
#align is_radical_iff_span_singleton isRadical_iff_span_singleton
-/

#print isRadical_iff_pow_one_lt /-
theorem isRadical_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsRadical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
  ⟨fun h x => h k x, fun h =>
    k.cauchy_induction_mul (fun n h x hd => h x <| (pow_succ' x n).symm ▸ hd.mul_right x) 0 hk
      (fun x hd => pow_one x ▸ hd) fun n _ hn x hd => h x <| hn _ <| (pow_mul x k n).subst hd⟩
#align is_radical_iff_pow_one_lt isRadical_iff_pow_one_lt
-/

/- warning: is_reduced_iff_pow_one_lt -> isReduced_iff_pow_one_lt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R] (k : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) k) -> (Iff (IsReduced.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))) (forall (x : R), (Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))) x k) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1))))))) -> (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} R] (k : Nat), (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) k) -> (Iff (IsReduced.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))) (forall (x : R), (Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R _inst_1))) x k) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1)))) -> (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align is_reduced_iff_pow_one_lt isReduced_iff_pow_one_ltₓ'. -/
theorem isReduced_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsReduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 := by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]
#align is_reduced_iff_pow_one_lt isReduced_iff_pow_one_lt

namespace Commute

section Semiring

variable [Semiring R] (h_comm : Commute x y)

include h_comm

/- warning: commute.is_nilpotent_add -> Commute.isNilpotent_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Semiring.{u1} R], (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) x) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y))
but is expected to have type
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Semiring.{u1} R], (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) x) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y))
Case conversion may be inaccurate. Consider using '#align commute.is_nilpotent_add Commute.isNilpotent_addₓ'. -/
theorem isNilpotent_add (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y) :=
  by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m - 1
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, MulZeroClass.mul_zero]
  cases' Nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj
  · rw [pow_eq_zero_of_le hi hn, MulZeroClass.zero_mul]
  · rw [pow_eq_zero_of_le hj hm, MulZeroClass.mul_zero]
#align commute.is_nilpotent_add Commute.isNilpotent_add

/- warning: commute.is_nilpotent_mul_left -> Commute.isNilpotent_mul_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Semiring.{u1} R], (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) x) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y))
but is expected to have type
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Semiring.{u1} R], (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) x) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y))
Case conversion may be inaccurate. Consider using '#align commute.is_nilpotent_mul_left Commute.isNilpotent_mul_leftₓ'. -/
theorem isNilpotent_mul_left (h : IsNilpotent x) : IsNilpotent (x * y) :=
  by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, MulZeroClass.zero_mul]
#align commute.is_nilpotent_mul_left Commute.isNilpotent_mul_left

/- warning: commute.is_nilpotent_mul_right -> Commute.isNilpotent_mul_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Semiring.{u1} R], (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y))
but is expected to have type
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Semiring.{u1} R], (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y))
Case conversion may be inaccurate. Consider using '#align commute.is_nilpotent_mul_right Commute.isNilpotent_mul_rightₓ'. -/
theorem isNilpotent_mul_right (h : IsNilpotent y) : IsNilpotent (x * y) :=
  by
  rw [h_comm.eq]
  exact h_comm.symm.is_nilpotent_mul_left h
#align commute.is_nilpotent_mul_right Commute.isNilpotent_mul_right

end Semiring

section Ring

variable [Ring R] (h_comm : Commute x y)

include h_comm

/- warning: commute.is_nilpotent_sub -> Commute.isNilpotent_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Ring.{u1} R], (Commute.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) x y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) x) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) y) -> (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))) x y))
but is expected to have type
  forall {R : Type.{u1}} {x : R} {y : R} [_inst_1 : Ring.{u1} R], (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) x y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) x) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) y) -> (IsNilpotent.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R _inst_1)) x y))
Case conversion may be inaccurate. Consider using '#align commute.is_nilpotent_sub Commute.isNilpotent_subₓ'. -/
theorem isNilpotent_sub (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y) :=
  by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.is_nilpotent_add hx hy
#align commute.is_nilpotent_sub Commute.isNilpotent_sub

end Ring

end Commute

section CommSemiring

variable [CommSemiring R]

#print nilradical /-
/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type _) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
#align nilradical nilradical
-/

/- warning: mem_nilradical -> mem_nilradical is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} [_inst_1 : CommSemiring.{u1} R], Iff (Membership.Mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x (nilradical.{u1} R _inst_1)) (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x)
but is expected to have type
  forall {R : Type.{u1}} {x : R} [_inst_1 : CommSemiring.{u1} R], Iff (Membership.mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x (nilradical.{u1} R _inst_1)) (IsNilpotent.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x)
Case conversion may be inaccurate. Consider using '#align mem_nilradical mem_nilradicalₓ'. -/
theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl
#align mem_nilradical mem_nilradical

/- warning: nilradical_eq_Inf -> nilradical_eq_infₛ is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_2 : CommSemiring.{u1} R], Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (nilradical.{u1} R _inst_2) (InfSet.infₛ.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Submodule.hasInf.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (setOf.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (fun (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) => Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2) J)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_2 : CommSemiring.{u1} R], Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (nilradical.{u1} R _inst_2) (InfSet.infₛ.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Submodule.instInfSetSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (setOf.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (fun (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) => Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2) J)))
Case conversion may be inaccurate. Consider using '#align nilradical_eq_Inf nilradical_eq_infₛₓ'. -/
theorem nilradical_eq_infₛ (R : Type _) [CommSemiring R] :
    nilradical R = infₛ { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_infₛ ⊥).trans <| by simp_rw [and_iff_right bot_le]
#align nilradical_eq_Inf nilradical_eq_infₛ

/- warning: nilpotent_iff_mem_prime -> nilpotent_iff_mem_prime is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {x : R} [_inst_1 : CommSemiring.{u1} R], Iff (IsNilpotent.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x) (forall (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)), (Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) J) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x J))
but is expected to have type
  forall {R : Type.{u1}} {x : R} [_inst_1 : CommSemiring.{u1} R], Iff (IsNilpotent.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x) (forall (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)), (Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) J) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) x J))
Case conversion may be inaccurate. Consider using '#align nilpotent_iff_mem_prime nilpotent_iff_mem_primeₓ'. -/
theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J :=
  by
  rw [← mem_nilradical, nilradical_eq_infₛ, Submodule.mem_infₛ]
  rfl
#align nilpotent_iff_mem_prime nilpotent_iff_mem_prime

/- warning: nilradical_le_prime -> nilradical_le_prime is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) [H : Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) J], LE.le.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (nilradical.{u1} R _inst_1) J
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (J : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) [H : Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) J], LE.le.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))) (nilradical.{u1} R _inst_1) J
Case conversion may be inaccurate. Consider using '#align nilradical_le_prime nilradical_le_primeₓ'. -/
theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_infₛ R).symm ▸ infₛ_le H
#align nilradical_le_prime nilradical_le_prime

/- warning: nilradical_eq_zero -> nilradical_eq_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_2 : CommSemiring.{u1} R] [_inst_3 : IsReduced.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))], Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (nilradical.{u1} R _inst_2) (OfNat.ofNat.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) 0 (OfNat.mk.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) 0 (Zero.zero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (MulZeroClass.toHasZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (IdemSemiring.toSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Submodule.idemSemiring.{u1, u1} R _inst_2 R (CommSemiring.toSemiring.{u1} R _inst_2) (Algebra.id.{u1} R _inst_2))))))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_2 : CommSemiring.{u1} R] [_inst_3 : IsReduced.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_2)) (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))], Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (nilradical.{u1} R _inst_2) (OfNat.ofNat.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) 0 (Zero.toOfNat0.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (CommMonoidWithZero.toZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (CommSemiring.toCommMonoidWithZero.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (IdemCommSemiring.toCommSemiring.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R _inst_2))))))
Case conversion may be inaccurate. Consider using '#align nilradical_eq_zero nilradical_eq_zeroₓ'. -/
@[simp]
theorem nilradical_eq_zero (R : Type _) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero
#align nilradical_eq_zero nilradical_eq_zero

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/- warning: linear_map.is_nilpotent_mul_left_iff -> LinearMap.isNilpotent_mulLeft_iff is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (a : A), Iff (IsNilpotent.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (LinearMap.hasZero.{u1, u1, u2, u2} R R A A (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (Module.End.monoid.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))) (LinearMap.mulLeft.{u1, u2} R A _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.to_smulCommClass.{u1, u2} R A _inst_1 _inst_2 _inst_3) (IsScalarTower.right.{u1, u2} R A _inst_1 _inst_2 _inst_3) a)) (IsNilpotent.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (Monoid.Pow.{u2} A (MonoidWithZero.toMonoid.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2))) a)
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (a : A), Iff (IsNilpotent.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (LinearMap.instZeroLinearMap.{u1, u1, u2, u2} R R A A (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (Module.End.monoid.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))) (LinearMap.mulLeft.{u1, u2} R A _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.to_smulCommClass.{u1, u2} R A _inst_1 _inst_2 _inst_3) (IsScalarTower.right.{u1, u2} R A _inst_1 _inst_2 _inst_3) a)) (IsNilpotent.{u2} A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (Monoid.Pow.{u2} A (MonoidWithZero.toMonoid.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2))) a)
Case conversion may be inaccurate. Consider using '#align linear_map.is_nilpotent_mul_left_iff LinearMap.isNilpotent_mulLeft_iffₓ'. -/
@[simp]
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mul_left_eq_zero_iff, pow_mul_left] at hn⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_left_iff LinearMap.isNilpotent_mulLeft_iff

/- warning: linear_map.is_nilpotent_mul_right_iff -> LinearMap.isNilpotent_mulRight_iff is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (a : A), Iff (IsNilpotent.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (LinearMap.hasZero.{u1, u1, u2, u2} R R A A (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (Module.End.monoid.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))) (LinearMap.mulRight.{u1, u2} R A _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.to_smulCommClass.{u1, u2} R A _inst_1 _inst_2 _inst_3) (IsScalarTower.right.{u1, u2} R A _inst_1 _inst_2 _inst_3) a)) (IsNilpotent.{u2} A (MulZeroClass.toHasZero.{u2} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))) (Monoid.Pow.{u2} A (MonoidWithZero.toMonoid.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2))) a)
but is expected to have type
  forall (R : Type.{u1}) {A : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] (a : A), Iff (IsNilpotent.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (LinearMap.instZeroLinearMap.{u1, u1, u2, u2} R R A A (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) A A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3)) (Module.End.monoid.{u1, u2} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3))) (LinearMap.mulRight.{u1, u2} R A _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.to_smulCommClass.{u1, u2} R A _inst_1 _inst_2 _inst_3) (IsScalarTower.right.{u1, u2} R A _inst_1 _inst_2 _inst_3) a)) (IsNilpotent.{u2} A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2)) (Monoid.Pow.{u2} A (MonoidWithZero.toMonoid.{u2} A (Semiring.toMonoidWithZero.{u2} A _inst_2))) a)
Case conversion may be inaccurate. Consider using '#align linear_map.is_nilpotent_mul_right_iff LinearMap.isNilpotent_mulRight_iffₓ'. -/
@[simp]
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mul_right_eq_zero_iff, pow_mul_right] at hn⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_right_iff LinearMap.isNilpotent_mulRight_iff

end LinearMap

namespace Module.End

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

/- warning: module.End.is_nilpotent.mapq -> Module.End.IsNilpotent.mapQ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {f : Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} (hp : LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)))) p (Submodule.comap.{u1, u1, u2, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (LinearMap.semilinearMapClass.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f p)), (IsNilpotent.{u2} (Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (LinearMap.hasZero.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Module.End.monoid.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) f) -> (IsNilpotent.{u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (LinearMap.hasZero.{u1, u1, u2, u2} R R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Module.End.monoid.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))) (Submodule.mapQ.{u1, u2, u1, u2} R M _inst_1 _inst_2 _inst_3 p R M _inst_1 _inst_2 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) p f hp))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {f : Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} {p : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3} (hp : LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))))) p (Submodule.comap.{u1, u1, u2, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (LinearMap.instSemilinearMapClassLinearMap.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) f p)), (IsNilpotent.{u2} (Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (LinearMap.instZeroLinearMap.{u1, u1, u2, u2} R R M M (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (Module.End.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Module.End.monoid.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3)) f) -> (IsNilpotent.{u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (LinearMap.instZeroLinearMap.{u1, u1, u2, u2} R R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Monoid.Pow.{u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R _inst_1) (Ring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Module.End.monoid.{u1, u2} R (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} (HasQuotient.Quotient.{u2, u2} M (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (Submodule.hasQuotient.{u1, u2} R M _inst_1 _inst_2 _inst_3) p) (Submodule.Quotient.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3 p)) (Submodule.Quotient.module.{u1, u2} R M _inst_1 _inst_2 _inst_3 p))) (Submodule.mapQ.{u1, u2, u1, u2} R M _inst_1 _inst_2 _inst_3 p R M _inst_1 _inst_2 _inst_3 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) p f hp))
Case conversion may be inaccurate. Consider using '#align module.End.is_nilpotent.mapq Module.End.IsNilpotent.mapQₓ'. -/
theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) :=
  by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapq_pow, hk]
#align module.End.is_nilpotent.mapq Module.End.IsNilpotent.mapQ

end Module.End

