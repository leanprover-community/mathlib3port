/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson

! This file was ported from Lean 3 source module algebra.group_with_zero.divisibility
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Algebra.Divisibility.Units

/-!
# Divisibility in groups with zero.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lemmas about divisibility in groups and monoids with zero.

-/


variable {α : Type _}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

/- warning: eq_zero_of_zero_dvd -> eq_zero_of_zero_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemigroupWithZero.{u1} α] {a : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (SemigroupWithZero.toMulZeroClass.{u1} α _inst_1))))) a) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (SemigroupWithZero.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemigroupWithZero.{u1} α] {a : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α _inst_1))) a) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_zero_of_zero_dvd eq_zero_of_zero_dvdₓ'. -/
theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)
#align eq_zero_of_zero_dvd eq_zero_of_zero_dvd

/- warning: zero_dvd_iff -> zero_dvd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemigroupWithZero.{u1} α] {a : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (SemigroupWithZero.toMulZeroClass.{u1} α _inst_1))))) a) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (SemigroupWithZero.toMulZeroClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemigroupWithZero.{u1} α] {a : α}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α _inst_1))) a) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_dvd_iff zero_dvd_iffₓ'. -/
/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp]
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    use 0
    simp⟩
#align zero_dvd_iff zero_dvd_iff

/- warning: dvd_zero -> dvd_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemigroupWithZero.{u1} α] (a : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (SemigroupWithZero.toMulZeroClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemigroupWithZero.{u1} α] (a : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align dvd_zero dvd_zeroₓ'. -/
@[simp]
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by simp)
#align dvd_zero dvd_zero

end SemigroupWithZero

/- warning: mul_dvd_mul_iff_left -> mul_dvd_mul_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} α] {a : α} {b : α} {c : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) a c)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} α] {a : α} {b : α} {c : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) a c)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align mul_dvd_mul_iff_left mul_dvd_mul_iff_leftₓ'. -/
/-- Given two elements `b`, `c` of a `cancel_monoid_with_zero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [CancelMonoidWithZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]
#align mul_dvd_mul_iff_left mul_dvd_mul_iff_left

/- warning: mul_dvd_mul_iff_right -> mul_dvd_mul_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α} {b : α} {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) b c)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α} {b : α} {c : α}, (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) b c)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align mul_dvd_mul_iff_right mul_dvd_mul_iff_rightₓ'. -/
/-- Given two elements `a`, `b` of a commutative `cancel_monoid_with_zero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [CancelCommMonoidWithZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]
#align mul_dvd_mul_iff_right mul_dvd_mul_iff_right

section CommMonoidWithZero

variable [CommMonoidWithZero α]

#print DvdNotUnit /-
/-- `dvd_not_unit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x
#align dvd_not_unit DvdNotUnit
-/

#print dvdNotUnit_of_dvd_of_not_dvd /-
theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b :=
  by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine' ⟨c, _, rfl⟩
    rintro ⟨u, rfl⟩
    simpa using hnd
#align dvd_not_unit_of_dvd_of_not_dvd dvdNotUnit_of_dvd_of_not_dvd
-/

end CommMonoidWithZero

#print dvd_and_not_dvd_iff /-
theorem dvd_and_not_dvd_iff [CancelCommMonoidWithZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simpa [hx0] using hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one _
          ⟨e,
            mul_left_cancel₀ hx0 <| by
              conv =>
                  lhs
                  rw [he, hdx] <;>
                simp [mul_assoc]⟩)⟩⟩
#align dvd_and_not_dvd_iff dvd_and_not_dvd_iff
-/

section MonoidWithZero

variable [MonoidWithZero α]

/- warning: ne_zero_of_dvd_ne_zero -> ne_zero_of_dvd_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {p : α} {q : α}, (Ne.{succ u1} α q (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α _inst_1))) p q) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {p : α} {q : α}, (Ne.{succ u1} α q (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α _inst_1))) p q) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ne_zero_of_dvd_ne_zero ne_zero_of_dvd_ne_zeroₓ'. -/
theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 :=
  by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁
#align ne_zero_of_dvd_ne_zero ne_zero_of_dvd_ne_zero

end MonoidWithZero

