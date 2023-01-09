/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes

! This file was ported from Lean 3 source module ring_theory.coprime.basic
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Ring
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Coprime elements of a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `is_coprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.

See also `ring_theory.coprime.lemmas` for further development of coprime elements.
-/


open Classical

universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] (x y z : R)

#print IsCoprime /-
/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[simp]
def IsCoprime : Prop :=
  ∃ a b, a * x + b * y = 1
#align is_coprime IsCoprime
-/

variable {x y z}

#print IsCoprime.symm /-
theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
  let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩
#align is_coprime.symm IsCoprime.symm
-/

#print isCoprime_comm /-
theorem isCoprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩
#align is_coprime_comm isCoprime_comm
-/

#print isCoprime_self /-
theorem isCoprime_self : IsCoprime x x ↔ IsUnit x :=
  ⟨fun ⟨a, b, h⟩ => isUnit_of_mul_eq_one x (a + b) <| by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩
#align is_coprime_self isCoprime_self
-/

/- warning: is_coprime_zero_left -> isCoprime_zero_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, Iff (IsCoprime.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) x) (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, Iff (IsCoprime.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)))) x) (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x)
Case conversion may be inaccurate. Consider using '#align is_coprime_zero_left isCoprime_zero_leftₓ'. -/
theorem isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
  ⟨fun ⟨a, b, H⟩ => isUnit_of_mul_eq_one x b <| by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩
#align is_coprime_zero_left isCoprime_zero_left

/- warning: is_coprime_zero_right -> isCoprime_zero_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, Iff (IsCoprime.{u1} R _inst_1 x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, Iff (IsCoprime.{u1} R _inst_1 x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1))))) (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x)
Case conversion may be inaccurate. Consider using '#align is_coprime_zero_right isCoprime_zero_rightₓ'. -/
theorem isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  isCoprime_comm.trans isCoprime_zero_left
#align is_coprime_zero_right isCoprime_zero_right

/- warning: not_coprime_zero_zero -> not_isCoprime_zero_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Not (IsCoprime.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Not (IsCoprime.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align not_coprime_zero_zero not_isCoprime_zero_zeroₓ'. -/
theorem not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt isCoprime_zero_right.mp not_isUnit_zero
#align not_coprime_zero_zero not_isCoprime_zero_zero

/- warning: is_coprime.ne_zero -> IsCoprime.ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {p : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> R}, (IsCoprime.{u1} R _inst_1 (p (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZero (One.one.{0} Nat Nat.hasOne)))))) (p (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOne (One.one.{0} Nat Nat.hasOne))))))) -> (Ne.{succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> R) p (OfNat.ofNat.{u1} ((Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) -> R) 0 (OfNat.mk.{u1} ((Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) -> R) 0 (Zero.zero.{u1} ((Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) -> R) (Pi.instZero.{0, u1} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (fun (ᾰ : Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) => R) (fun (i : Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) => MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {p : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> R}, (IsCoprime.{u1} R _inst_1 (p (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) 0))) (p (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) 1)))) -> (Ne.{succ u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> R) p (OfNat.ofNat.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> R) 0 (Zero.toOfNat0.{u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> R) (Pi.instZero.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (a._@.Mathlib.RingTheory.Coprime.Basic._hyg.535 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => R) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align is_coprime.ne_zero IsCoprime.ne_zeroₓ'. -/
/-- If a 2-vector `p` satisfies `is_coprime (p 0) (p 1)`, then `p ≠ 0`. -/
theorem IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 → R} (h : IsCoprime (p 0) (p 1)) : p ≠ 0 :=
  by
  rintro rfl
  exact not_isCoprime_zero_zero h
#align is_coprime.ne_zero IsCoprime.ne_zero

#print isCoprime_one_left /-
theorem isCoprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩
#align is_coprime_one_left isCoprime_one_left
-/

#print isCoprime_one_right /-
theorem isCoprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩
#align is_coprime_one_right isCoprime_one_right
-/

/- warning: is_coprime.dvd_of_dvd_mul_right -> IsCoprime.dvd_of_dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x z) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z)) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x z) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z)) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.dvd_of_dvd_mul_right IsCoprime.dvd_of_dvd_mul_rightₓ'. -/
theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y :=
  by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
#align is_coprime.dvd_of_dvd_mul_right IsCoprime.dvd_of_dvd_mul_right

/- warning: is_coprime.dvd_of_dvd_mul_left -> IsCoprime.dvd_of_dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x y) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z)) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x y) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z)) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x z)
Case conversion may be inaccurate. Consider using '#align is_coprime.dvd_of_dvd_mul_left IsCoprime.dvd_of_dvd_mul_leftₓ'. -/
theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z :=
  by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
#align is_coprime.dvd_of_dvd_mul_left IsCoprime.dvd_of_dvd_mul_left

/- warning: is_coprime.mul_left -> IsCoprime.mul_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x z) -> (IsCoprime.{u1} R _inst_1 y z) -> (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x z) -> (IsCoprime.{u1} R _inst_1 y z) -> (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) z)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_left IsCoprime.mul_leftₓ'. -/
theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc
      a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z =
          (a * x + b * z) * (c * y + d * z) :=
        by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩
#align is_coprime.mul_left IsCoprime.mul_left

/- warning: is_coprime.mul_right -> IsCoprime.mul_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x y) -> (IsCoprime.{u1} R _inst_1 x z) -> (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x y) -> (IsCoprime.{u1} R _inst_1 x z) -> (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z))
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_right IsCoprime.mul_rightₓ'. -/
theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) :=
  by
  rw [isCoprime_comm] at H1 H2⊢
  exact H1.mul_left H2
#align is_coprime.mul_right IsCoprime.mul_right

/- warning: is_coprime.mul_dvd -> IsCoprime.mul_dvd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x y) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x z) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) y z) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x y) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) x z) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) y z) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (CommSemiring.toNonUnitalCommSemiring.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) z)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_dvd IsCoprime.mul_dvdₓ'. -/
theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
  by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z, ← h, mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _
#align is_coprime.mul_dvd IsCoprime.mul_dvd

/- warning: is_coprime.of_mul_left_left -> IsCoprime.of_mul_left_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z) -> (IsCoprime.{u1} R _inst_1 x z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) z) -> (IsCoprime.{u1} R _inst_1 x z)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_left_left IsCoprime.of_mul_left_leftₓ'. -/
theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩
#align is_coprime.of_mul_left_left IsCoprime.of_mul_left_left

/- warning: is_coprime.of_mul_left_right -> IsCoprime.of_mul_left_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z) -> (IsCoprime.{u1} R _inst_1 y z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) z) -> (IsCoprime.{u1} R _inst_1 y z)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_left_right IsCoprime.of_mul_left_rightₓ'. -/
theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z :=
  by
  rw [mul_comm] at H
  exact H.of_mul_left_left
#align is_coprime.of_mul_left_right IsCoprime.of_mul_left_right

/- warning: is_coprime.of_mul_right_left -> IsCoprime.of_mul_right_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z)) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z)) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_right_left IsCoprime.of_mul_right_leftₓ'. -/
theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y :=
  by
  rw [isCoprime_comm] at H⊢
  exact H.of_mul_left_left
#align is_coprime.of_mul_right_left IsCoprime.of_mul_right_left

/- warning: is_coprime.of_mul_right_right -> IsCoprime.of_mul_right_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z)) -> (IsCoprime.{u1} R _inst_1 x z)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z)) -> (IsCoprime.{u1} R _inst_1 x z)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_right_right IsCoprime.of_mul_right_rightₓ'. -/
theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z :=
  by
  rw [mul_comm] at H
  exact H.of_mul_right_left
#align is_coprime.of_mul_right_right IsCoprime.of_mul_right_right

/- warning: is_coprime.mul_left_iff -> IsCoprime.mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z) (And (IsCoprime.{u1} R _inst_1 x z) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) z) (And (IsCoprime.{u1} R _inst_1 x z) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_left_iff IsCoprime.mul_left_iffₓ'. -/
theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩
#align is_coprime.mul_left_iff IsCoprime.mul_left_iff

/- warning: is_coprime.mul_right_iff -> IsCoprime.mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z)) (And (IsCoprime.{u1} R _inst_1 x y) (IsCoprime.{u1} R _inst_1 x z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R _inst_1 x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z)) (And (IsCoprime.{u1} R _inst_1 x y) (IsCoprime.{u1} R _inst_1 x z))
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_right_iff IsCoprime.mul_right_iffₓ'. -/
theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [isCoprime_comm, IsCoprime.mul_left_iff, isCoprime_comm, @isCoprime_comm _ _ z]
#align is_coprime.mul_right_iff IsCoprime.mul_right_iff

#print IsCoprime.of_isCoprime_of_dvd_left /-
theorem IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z :=
  by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h
#align is_coprime.of_coprime_of_dvd_left IsCoprime.of_isCoprime_of_dvd_left
-/

#print IsCoprime.of_isCoprime_of_dvd_right /-
theorem IsCoprime.of_isCoprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x :=
  (h.symm.of_coprime_of_dvd_left hdvd).symm
#align is_coprime.of_coprime_of_dvd_right IsCoprime.of_isCoprime_of_dvd_right
-/

#print IsCoprime.isUnit_of_dvd /-
theorem IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x :=
  let ⟨k, hk⟩ := d
  isCoprime_self.1 <| IsCoprime.of_mul_right_left <| show IsCoprime x (x * k) from hk ▸ H
#align is_coprime.is_unit_of_dvd IsCoprime.isUnit_of_dvd
-/

#print IsCoprime.isUnit_of_dvd' /-
theorem IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b) :
    IsUnit x :=
  (h.of_coprime_of_dvd_left ha).is_unit_of_dvd hb
#align is_coprime.is_unit_of_dvd' IsCoprime.isUnit_of_dvd'
-/

/- warning: is_coprime.map -> IsCoprime.map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R _inst_1 x y) -> (forall {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))), IsCoprime.{u2} S _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) f y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R _inst_1 x y) -> (forall {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))), IsCoprime.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) f y))
Case conversion may be inaccurate. Consider using '#align is_coprime.map IsCoprime.mapₓ'. -/
theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R →+* S) :
    IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩
#align is_coprime.map IsCoprime.map

variable {x y z}

/- warning: is_coprime.of_add_mul_left_left -> IsCoprime.of_add_mul_left_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z)) y) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z)) y) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_add_mul_left_left IsCoprime.of_add_mul_left_leftₓ'. -/
theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩
#align is_coprime.of_add_mul_left_left IsCoprime.of_add_mul_left_left

/- warning: is_coprime.of_add_mul_right_left -> IsCoprime.of_add_mul_right_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) z y)) y) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) z y)) y) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_add_mul_right_left IsCoprime.of_add_mul_right_leftₓ'. -/
theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y :=
  by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left
#align is_coprime.of_add_mul_right_left IsCoprime.of_add_mul_right_left

/- warning: is_coprime.of_add_mul_left_right -> IsCoprime.of_add_mul_left_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x z))) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x z))) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_add_mul_left_right IsCoprime.of_add_mul_left_rightₓ'. -/
theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y :=
  by
  rw [isCoprime_comm] at h⊢
  exact h.of_add_mul_left_left
#align is_coprime.of_add_mul_left_right IsCoprime.of_add_mul_left_right

/- warning: is_coprime.of_add_mul_right_right -> IsCoprime.of_add_mul_right_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) z x))) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) z x))) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_add_mul_right_right IsCoprime.of_add_mul_right_rightₓ'. -/
theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y :=
  by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right
#align is_coprime.of_add_mul_right_right IsCoprime.of_add_mul_right_right

/- warning: is_coprime.of_mul_add_left_left -> IsCoprime.of_mul_add_left_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y z) x) y) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y z) x) y) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_add_left_left IsCoprime.of_mul_add_left_leftₓ'. -/
theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y :=
  by
  rw [add_comm] at h
  exact h.of_add_mul_left_left
#align is_coprime.of_mul_add_left_left IsCoprime.of_mul_add_left_left

/- warning: is_coprime.of_mul_add_right_left -> IsCoprime.of_mul_add_right_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) z y) x) y) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) z y) x) y) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_add_right_left IsCoprime.of_mul_add_right_leftₓ'. -/
theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y :=
  by
  rw [add_comm] at h
  exact h.of_add_mul_right_left
#align is_coprime.of_mul_add_right_left IsCoprime.of_mul_add_right_left

/- warning: is_coprime.of_mul_add_left_right -> IsCoprime.of_mul_add_left_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x z) y)) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x z) y)) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_add_left_right IsCoprime.of_mul_add_left_rightₓ'. -/
theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y :=
  by
  rw [add_comm] at h
  exact h.of_add_mul_left_right
#align is_coprime.of_mul_add_left_right IsCoprime.of_mul_add_left_right

/- warning: is_coprime.of_mul_add_right_right -> IsCoprime.of_mul_add_right_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) z x) y)) -> (IsCoprime.{u1} R _inst_1 x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R} {y : R} {z : R}, (IsCoprime.{u1} R _inst_1 x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) z x) y)) -> (IsCoprime.{u1} R _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.of_mul_add_right_right IsCoprime.of_mul_add_right_rightₓ'. -/
theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y :=
  by
  rw [add_comm] at h
  exact h.of_add_mul_right_right
#align is_coprime.of_mul_add_right_right IsCoprime.of_mul_add_right_right

end CommSemiring

section ScalarTower

variable {R G : Type _} [CommSemiring R] [Group G] [MulAction G R] [SMulCommClass G R R]
  [IsScalarTower G R R] (x : G) (y z : R)

/- warning: is_coprime_group_smul_left -> isCoprime_group_smul_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {G : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : SMulCommClass.{u2, u1, u1} G R R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))] [_inst_5 : IsScalarTower.{u2, u1, u1} G R R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (x : G) (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HasSmul.smul.{u2, u1} G R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) x y) z) (IsCoprime.{u1} R _inst_1 y z)
but is expected to have type
  forall {R : Type.{u2}} {G : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : SMulCommClass.{u1, u2, u2} G R R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (MulAction.toSMul.{u2, u2} R R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Monoid.toMulAction.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))] [_inst_5 : IsScalarTower.{u1, u2, u2} G R R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (MulAction.toSMul.{u2, u2} R R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Monoid.toMulAction.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (x : G) (y : R) (z : R), Iff (IsCoprime.{u2} R _inst_1 (HSMul.hSMul.{u1, u2, u2} G R R (instHSMul.{u1, u2} G R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x y) z) (IsCoprime.{u2} R _inst_1 y z)
Case conversion may be inaccurate. Consider using '#align is_coprime_group_smul_left isCoprime_group_smul_leftₓ'. -/
theorem isCoprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z :=
  ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul, inv_mul_self, one_smul]⟩⟩
#align is_coprime_group_smul_left isCoprime_group_smul_left

/- warning: is_coprime_group_smul_right -> isCoprime_group_smul_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {G : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : SMulCommClass.{u2, u1, u1} G R R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))] [_inst_5 : IsScalarTower.{u2, u1, u1} G R R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (x : G) (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 y (HasSmul.smul.{u2, u1} G R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) x z)) (IsCoprime.{u1} R _inst_1 y z)
but is expected to have type
  forall {R : Type.{u2}} {G : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : SMulCommClass.{u1, u2, u2} G R R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (MulAction.toSMul.{u2, u2} R R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Monoid.toMulAction.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))] [_inst_5 : IsScalarTower.{u1, u2, u2} G R R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (MulAction.toSMul.{u2, u2} R R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Monoid.toMulAction.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (x : G) (y : R) (z : R), Iff (IsCoprime.{u2} R _inst_1 y (HSMul.hSMul.{u1, u2, u2} G R R (instHSMul.{u1, u2} G R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x z)) (IsCoprime.{u2} R _inst_1 y z)
Case conversion may be inaccurate. Consider using '#align is_coprime_group_smul_right isCoprime_group_smul_rightₓ'. -/
theorem isCoprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z :=
  isCoprime_comm.trans <| (isCoprime_group_smul_left x z y).trans isCoprime_comm
#align is_coprime_group_smul_right isCoprime_group_smul_right

/- warning: is_coprime_group_smul -> isCoprime_group_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {G : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : SMulCommClass.{u2, u1, u1} G R R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))] [_inst_5 : IsScalarTower.{u2, u1, u1} G R R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (x : G) (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HasSmul.smul.{u2, u1} G R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) x y) (HasSmul.smul.{u2, u1} G R (MulAction.toHasSmul.{u2, u1} G R (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) x z)) (IsCoprime.{u1} R _inst_1 y z)
but is expected to have type
  forall {R : Type.{u2}} {G : Type.{u1}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : SMulCommClass.{u1, u2, u2} G R R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (MulAction.toSMul.{u2, u2} R R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Monoid.toMulAction.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))] [_inst_5 : IsScalarTower.{u1, u2, u2} G R R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (MulAction.toSMul.{u2, u2} R R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Monoid.toMulAction.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (x : G) (y : R) (z : R), Iff (IsCoprime.{u2} R _inst_1 (HSMul.hSMul.{u1, u2, u2} G R R (instHSMul.{u1, u2} G R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x y) (HSMul.hSMul.{u1, u2, u2} G R R (instHSMul.{u1, u2} G R (MulAction.toSMul.{u1, u2} G R (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x z)) (IsCoprime.{u2} R _inst_1 y z)
Case conversion may be inaccurate. Consider using '#align is_coprime_group_smul isCoprime_group_smulₓ'. -/
theorem isCoprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z :=
  (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)
#align is_coprime_group_smul isCoprime_group_smul

end ScalarTower

section CommSemiringUnit

variable {R : Type _} [CommSemiring R] {x : R} (hu : IsUnit x) (y z : R)

/- warning: is_coprime_mul_unit_left_left -> isCoprime_mul_unit_left_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) z) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime_mul_unit_left_left isCoprime_mul_unit_left_leftₓ'. -/
theorem isCoprime_mul_unit_left_left : IsCoprime (x * y) z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z
#align is_coprime_mul_unit_left_left isCoprime_mul_unit_left_left

/- warning: is_coprime_mul_unit_left_right -> isCoprime_mul_unit_left_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x z)) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x z)) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime_mul_unit_left_right isCoprime_mul_unit_left_rightₓ'. -/
theorem isCoprime_mul_unit_left_right : IsCoprime y (x * z) ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z
#align is_coprime_mul_unit_left_right isCoprime_mul_unit_left_right

/- warning: is_coprime_mul_unit_left -> isCoprime_mul_unit_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x z)) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x y) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x z)) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime_mul_unit_left isCoprime_mul_unit_leftₓ'. -/
theorem isCoprime_mul_unit_left : IsCoprime (x * y) (x * z) ↔ IsCoprime y z :=
  (isCoprime_mul_unit_left_left hu y (x * z)).trans (isCoprime_mul_unit_left_right hu y z)
#align is_coprime_mul_unit_left isCoprime_mul_unit_left

/- warning: is_coprime_mul_unit_right_left -> isCoprime_mul_unit_right_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y x) z) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y x) z) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime_mul_unit_right_left isCoprime_mul_unit_right_leftₓ'. -/
theorem isCoprime_mul_unit_right_left : IsCoprime (y * x) z ↔ IsCoprime y z :=
  mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z
#align is_coprime_mul_unit_right_left isCoprime_mul_unit_right_left

/- warning: is_coprime_mul_unit_right_right -> isCoprime_mul_unit_right_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) z x)) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) z x)) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime_mul_unit_right_right isCoprime_mul_unit_right_rightₓ'. -/
theorem isCoprime_mul_unit_right_right : IsCoprime y (z * x) ↔ IsCoprime y z :=
  mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z
#align is_coprime_mul_unit_right_right isCoprime_mul_unit_right_right

/- warning: is_coprime_mul_unit_right -> isCoprime_mul_unit_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) y x) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) z x)) (IsCoprime.{u1} R _inst_1 y z))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {x : R}, (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x) -> (forall (y : R) (z : R), Iff (IsCoprime.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y x) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) z x)) (IsCoprime.{u1} R _inst_1 y z))
Case conversion may be inaccurate. Consider using '#align is_coprime_mul_unit_right isCoprime_mul_unit_rightₓ'. -/
theorem isCoprime_mul_unit_right : IsCoprime (y * x) (z * x) ↔ IsCoprime y z :=
  (isCoprime_mul_unit_right_left hu y (z * x)).trans (isCoprime_mul_unit_right_right hu y z)
#align is_coprime_mul_unit_right isCoprime_mul_unit_right

end CommSemiringUnit

namespace IsCoprime

section CommRing

variable {R : Type u} [CommRing R]

/- warning: is_coprime.add_mul_left_left -> IsCoprime.add_mul_left_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y z)) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) y z)) y)
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_left_left IsCoprime.add_mul_left_leftₓ'. -/
theorem add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h
#align is_coprime.add_mul_left_left IsCoprime.add_mul_left_left

/- warning: is_coprime.add_mul_right_left -> IsCoprime.add_mul_right_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z y)) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z y)) y)
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_right_left IsCoprime.add_mul_right_leftₓ'. -/
theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y :=
  by
  rw [mul_comm]
  exact h.add_mul_left_left z
#align is_coprime.add_mul_right_left IsCoprime.add_mul_right_left

/- warning: is_coprime.add_mul_left_right -> IsCoprime.add_mul_left_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x z)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) x z)))
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_left_right IsCoprime.add_mul_left_rightₓ'. -/
theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) :=
  by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z
#align is_coprime.add_mul_left_right IsCoprime.add_mul_left_right

/- warning: is_coprime.add_mul_right_right -> IsCoprime.add_mul_right_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z x)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z x)))
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_right_right IsCoprime.add_mul_right_rightₓ'. -/
theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) :=
  by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z
#align is_coprime.add_mul_right_right IsCoprime.add_mul_right_right

/- warning: is_coprime.mul_add_left_left -> IsCoprime.mul_add_left_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y z) x) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) y z) x) y)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_left_left IsCoprime.mul_add_left_leftₓ'. -/
theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y :=
  by
  rw [add_comm]
  exact h.add_mul_left_left z
#align is_coprime.mul_add_left_left IsCoprime.mul_add_left_left

/- warning: is_coprime.mul_add_right_left -> IsCoprime.mul_add_right_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z y) x) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z y) x) y)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_right_left IsCoprime.mul_add_right_leftₓ'. -/
theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y :=
  by
  rw [add_comm]
  exact h.add_mul_right_left z
#align is_coprime.mul_add_right_left IsCoprime.mul_add_right_left

/- warning: is_coprime.mul_add_left_right -> IsCoprime.mul_add_left_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x z) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) x z) y))
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_left_right IsCoprime.mul_add_left_rightₓ'. -/
theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) :=
  by
  rw [add_comm]
  exact h.add_mul_left_right z
#align is_coprime.mul_add_left_right IsCoprime.mul_add_left_right

/- warning: is_coprime.mul_add_right_right -> IsCoprime.mul_add_right_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z x) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (forall (z : R), IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z x) y))
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_right_right IsCoprime.mul_add_right_rightₓ'. -/
theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) :=
  by
  rw [add_comm]
  exact h.add_mul_right_right z
#align is_coprime.mul_add_right_right IsCoprime.mul_add_right_right

/- warning: is_coprime.add_mul_left_left_iff -> IsCoprime.add_mul_left_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y z)) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) y z)) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_left_left_iff IsCoprime.add_mul_left_left_iffₓ'. -/
theorem add_mul_left_left_iff {x y z : R} : IsCoprime (x + y * z) y ↔ IsCoprime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩
#align is_coprime.add_mul_left_left_iff IsCoprime.add_mul_left_left_iff

/- warning: is_coprime.add_mul_right_left_iff -> IsCoprime.add_mul_right_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z y)) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z y)) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_right_left_iff IsCoprime.add_mul_right_left_iffₓ'. -/
theorem add_mul_right_left_iff {x y z : R} : IsCoprime (x + z * y) y ↔ IsCoprime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩
#align is_coprime.add_mul_right_left_iff IsCoprime.add_mul_right_left_iff

/- warning: is_coprime.add_mul_left_right_iff -> IsCoprime.add_mul_left_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x z))) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) x z))) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_left_right_iff IsCoprime.add_mul_left_right_iffₓ'. -/
theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩
#align is_coprime.add_mul_left_right_iff IsCoprime.add_mul_left_right_iff

/- warning: is_coprime.add_mul_right_right_iff -> IsCoprime.add_mul_right_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z x))) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z x))) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.add_mul_right_right_iff IsCoprime.add_mul_right_right_iffₓ'. -/
theorem add_mul_right_right_iff {x y z : R} : IsCoprime x (y + z * x) ↔ IsCoprime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩
#align is_coprime.add_mul_right_right_iff IsCoprime.add_mul_right_right_iff

/- warning: is_coprime.mul_add_left_left_iff -> IsCoprime.mul_add_left_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) y z) x) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) y z) x) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_left_left_iff IsCoprime.mul_add_left_left_iffₓ'. -/
theorem mul_add_left_left_iff {x y z : R} : IsCoprime (y * z + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩
#align is_coprime.mul_add_left_left_iff IsCoprime.mul_add_left_left_iff

/- warning: is_coprime.mul_add_right_left_iff -> IsCoprime.mul_add_right_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z y) x) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z y) x) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_right_left_iff IsCoprime.mul_add_right_left_iffₓ'. -/
theorem mul_add_right_left_iff {x y z : R} : IsCoprime (z * y + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩
#align is_coprime.mul_add_right_left_iff IsCoprime.mul_add_right_left_iff

/- warning: is_coprime.mul_add_left_right_iff -> IsCoprime.mul_add_left_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) x z) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) x z) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_left_right_iff IsCoprime.mul_add_left_right_iffₓ'. -/
theorem mul_add_left_right_iff {x y z : R} : IsCoprime x (x * z + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩
#align is_coprime.mul_add_left_right_iff IsCoprime.mul_add_left_right_iff

/- warning: is_coprime.mul_add_right_right_iff -> IsCoprime.mul_add_right_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) z x) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R} {z : R}, Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) z x) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.mul_add_right_right_iff IsCoprime.mul_add_right_right_iffₓ'. -/
theorem mul_add_right_right_iff {x y z : R} : IsCoprime x (z * x + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩
#align is_coprime.mul_add_right_right_iff IsCoprime.mul_add_right_right_iff

/- warning: is_coprime.neg_left -> IsCoprime.neg_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) x) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) x) y)
Case conversion may be inaccurate. Consider using '#align is_coprime.neg_left IsCoprime.neg_leftₓ'. -/
theorem neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y :=
  by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]
#align is_coprime.neg_left IsCoprime.neg_left

/- warning: is_coprime.neg_left_iff -> IsCoprime.neg_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) x) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) x) y) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.neg_left_iff IsCoprime.neg_left_iffₓ'. -/
theorem neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y :=
  ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩
#align is_coprime.neg_left_iff IsCoprime.neg_left_iff

/- warning: is_coprime.neg_right -> IsCoprime.neg_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) y))
Case conversion may be inaccurate. Consider using '#align is_coprime.neg_right IsCoprime.neg_rightₓ'. -/
theorem neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y) :=
  h.symm.neg_left.symm
#align is_coprime.neg_right IsCoprime.neg_right

/- warning: is_coprime.neg_right_iff -> IsCoprime.neg_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.neg_right_iff IsCoprime.neg_right_iffₓ'. -/
theorem neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y :=
  ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩
#align is_coprime.neg_right_iff IsCoprime.neg_right_iff

/- warning: is_coprime.neg_neg -> IsCoprime.neg_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) x) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {x : R} {y : R}, (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y) -> (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) x) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) y))
Case conversion may be inaccurate. Consider using '#align is_coprime.neg_neg IsCoprime.neg_negₓ'. -/
theorem neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y) :=
  h.neg_left.neg_right
#align is_coprime.neg_neg IsCoprime.neg_neg

/- warning: is_coprime.neg_neg_iff -> IsCoprime.neg_neg_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) x) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (x : R) (y : R), Iff (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) x) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) y)) (IsCoprime.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align is_coprime.neg_neg_iff IsCoprime.neg_neg_iffₓ'. -/
theorem neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)
#align is_coprime.neg_neg_iff IsCoprime.neg_neg_iff

end CommRing

/- warning: is_coprime.sq_add_sq_ne_zero -> IsCoprime.sq_add_sq_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedCommRing.{u1} R] {a : R} {b : R}, (IsCoprime.{u1} R (StrictOrderedCommSemiring.toCommSemiring.{u1} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R _inst_1))) a b) -> (Ne.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1)))))) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1)))))) b (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1))))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedCommRing.{u1} R] {a : R} {b : R}, (IsCoprime.{u1} R (StrictOrderedCommSemiring.toCommSemiring.{u1} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} R _inst_1))) a b) -> (Ne.{succ u1} R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1))))))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} R _inst_1)))))))) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} R _inst_1)))))))) b (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (StrictOrderedCommSemiring.toCommSemiring.{u1} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u1} R _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align is_coprime.sq_add_sq_ne_zero IsCoprime.sq_add_sq_ne_zeroₓ'. -/
theorem sq_add_sq_ne_zero {R : Type _} [LinearOrderedCommRing R] {a b : R} (h : IsCoprime a b) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff' (sq_nonneg a) (sq_nonneg b)).mp h'
  obtain rfl := pow_eq_zero ha
  obtain rfl := pow_eq_zero hb
  exact not_isCoprime_zero_zero h
#align is_coprime.sq_add_sq_ne_zero IsCoprime.sq_add_sq_ne_zero

end IsCoprime

