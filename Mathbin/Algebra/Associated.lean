/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

! This file was ported from Lean 3 source module algebra.associated
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Divisibility.Basic
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.Parity

/-!
# Associated, prime, and irreducible elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section Prime

variable [CommMonoidWithZero α]

#print Prime /-
/-- prime element of a `comm_monoid_with_zero` -/
def Prime (p : α) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b
#align prime Prime
-/

namespace Prime

variable {p : α} (hp : Prime p)

include hp

/- warning: prime.ne_zero -> Prime.ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align prime.ne_zero Prime.ne_zeroₓ'. -/
theorem ne_zero : p ≠ 0 :=
  hp.1
#align prime.ne_zero Prime.ne_zero

#print Prime.not_unit /-
theorem not_unit : ¬IsUnit p :=
  hp.2.1
#align prime.not_unit Prime.not_unit
-/

/- warning: prime.not_dvd_one -> Prime.not_dvd_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align prime.not_dvd_one Prime.not_dvd_oneₓ'. -/
theorem not_dvd_one : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one _) hp.not_unit
#align prime.not_dvd_one Prime.not_dvd_one

/- warning: prime.ne_one -> Prime.ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align prime.ne_one Prime.ne_oneₓ'. -/
theorem ne_one : p ≠ 1 := fun h => hp.2.1 (h.symm ▸ isUnit_one)
#align prime.ne_one Prime.ne_one

/- warning: prime.dvd_or_dvd -> Prime.dvd_or_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) a b)) -> (Or (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p a) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))) a b)) -> (Or (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p a) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p b)))
Case conversion may be inaccurate. Consider using '#align prime.dvd_or_dvd Prime.dvd_or_dvdₓ'. -/
theorem dvd_or_dvd (hp : Prime p) {a b : α} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h
#align prime.dvd_or_dvd Prime.dvd_or_dvd

#print Prime.dvd_of_dvd_pow /-
theorem dvd_of_dvd_pow (hp : Prime p) {a : α} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a :=
  by
  induction' n with n ih
  · rw [pow_zero] at h
    have := isUnit_of_dvd_one _ h
    have := not_unit hp
    contradiction
  rw [pow_succ] at h
  cases' dvd_or_dvd hp h with dvd_a dvd_pow
  · assumption
  exact ih dvd_pow
#align prime.dvd_of_dvd_pow Prime.dvd_of_dvd_pow
-/

end Prime

/- warning: not_prime_zero -> not_prime_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], Not (Prime.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], Not (Prime.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align not_prime_zero not_prime_zeroₓ'. -/
@[simp]
theorem not_prime_zero : ¬Prime (0 : α) := fun h => h.NeZero rfl
#align not_prime_zero not_prime_zero

/- warning: not_prime_one -> not_prime_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], Not (Prime.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], Not (Prime.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align not_prime_one not_prime_oneₓ'. -/
@[simp]
theorem not_prime_one : ¬Prime (1 : α) := fun h => h.not_unit isUnit_one
#align not_prime_one not_prime_one

section Map

variable [CommMonoidWithZero β] {F : Type _} {G : Type _} [MonoidWithZeroHomClass F α β]
  [MulHomClass G β α] (f : F) (g : G) {p : α}

/- warning: comap_prime -> comap_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : CommMonoidWithZero.{u2} β] {F : Type.{u3}} {G : Type.{u4}} [_inst_3 : MonoidWithZeroHomClass.{u3, u1, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))] [_inst_4 : MulHomClass.{u4, u2, u1} G β α (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))] (f : F) (g : G) {p : α}, (forall (a : α), Eq.{succ u1} α (coeFn.{succ u4, max (succ u2) (succ u1)} G (fun (_x : G) => β -> α) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u1} G β (fun (_x : β) => α) (MulHomClass.toFunLike.{u4, u2, u1} G β α (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) _inst_4)) g (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasMul.{u2} β (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u1, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)) _inst_3)))) f a)) a) -> (Prime.{u2} β _inst_2 (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulOneClass.toHasMul.{u2} β (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (MulZeroOneClass.toMulOneClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u1, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)) _inst_3)))) f p)) -> (Prime.{u1} α _inst_1 p)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u4} α] [_inst_2 : CommMonoidWithZero.{u2} β] {F : Type.{u3}} {G : Type.{u1}} [_inst_3 : MonoidWithZeroHomClass.{u3, u4, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))] [_inst_4 : MulHomClass.{u1, u2, u4} G β α (MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulZeroClass.toMul.{u4} α (MulZeroOneClass.toMulZeroClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1))))] (f : F) (g : G) {p : α}, (forall (a : α), Eq.{succ u4} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : β) => α) (FunLike.coe.{succ u3, succ u4, succ u2} F α (fun (a : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) a) (MulHomClass.toFunLike.{u3, u4, u2} F α β (MulOneClass.toMul.{u4} α (MulZeroOneClass.toMulOneClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)))) (MulOneClass.toMul.{u2} β (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u4, u2} F α β (MulZeroOneClass.toMulOneClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1))) (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u4, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)) _inst_3))) f a)) (FunLike.coe.{succ u1, succ u2, succ u4} G β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : β) => α) _x) (MulHomClass.toFunLike.{u1, u2, u4} G β α (MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MulZeroClass.toMul.{u4} α (MulZeroOneClass.toMulZeroClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)))) _inst_4) g (FunLike.coe.{succ u3, succ u4, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u3, u4, u2} F α β (MulOneClass.toMul.{u4} α (MulZeroOneClass.toMulOneClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)))) (MulOneClass.toMul.{u2} β (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u4, u2} F α β (MulZeroOneClass.toMulOneClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1))) (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u4, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)) _inst_3))) f a)) a) -> (Prime.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) p) _inst_2 (FunLike.coe.{succ u3, succ u4, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u3, u4, u2} F α β (MulOneClass.toMul.{u4} α (MulZeroOneClass.toMulOneClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)))) (MulOneClass.toMul.{u2} β (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u3, u4, u2} F α β (MulZeroOneClass.toMulOneClass.{u4} α (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1))) (MulZeroOneClass.toMulOneClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))) (MonoidWithZeroHomClass.toMonoidHomClass.{u3, u4, u2} F α β (MonoidWithZero.toMulZeroOneClass.{u4} α (CommMonoidWithZero.toMonoidWithZero.{u4} α _inst_1)) (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2)) _inst_3))) f p)) -> (Prime.{u4} α _inst_1 p)
Case conversion may be inaccurate. Consider using '#align comap_prime comap_primeₓ'. -/
theorem comap_prime (hinv : ∀ a, g (f a : β) = a) (hp : Prime (f p)) : Prime p :=
  ⟨fun h => hp.1 <| by simp [h], fun h => hp.2.1 <| h.map f, fun a b h => by
    refine'
        (hp.2.2 (f a) (f b) <| by
              convert map_dvd f h
              simp).imp
          _ _ <;>
      · intro h
        convert ← map_dvd g h <;> apply hinv⟩
#align comap_prime comap_prime

/- warning: mul_equiv.prime_iff -> MulEquiv.prime_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : CommMonoidWithZero.{u2} β] {p : α} (e : MulEquiv.{u1, u2} α β (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))))), Iff (Prime.{u1} α _inst_1 p) (Prime.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} α β (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))))) (fun (_x : MulEquiv.{u1, u2} α β (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))))) => α -> β) (MulEquiv.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β (CommMonoidWithZero.toMonoidWithZero.{u2} β _inst_2))))) e p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u2} α] [_inst_2 : CommMonoidWithZero.{u1} β] {p : α} (e : MulEquiv.{u2, u1} α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2))))), Iff (Prime.{u2} α _inst_1 p) (Prime.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) p) _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2))))) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2))))) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2))))) α β (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2))))) α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α (MonoidWithZero.toMulZeroOneClass.{u2} α (CommMonoidWithZero.toMonoidWithZero.{u2} α _inst_1)))) (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_2)))))))) e p))
Case conversion may be inaccurate. Consider using '#align mul_equiv.prime_iff MulEquiv.prime_iffₓ'. -/
theorem MulEquiv.prime_iff (e : α ≃* β) : Prime p ↔ Prime (e p) :=
  ⟨fun h => (comap_prime e.symm e fun a => by simp) <| (e.symm_apply_apply p).substr h,
    comap_prime e e.symm fun a => by simp⟩
#align mul_equiv.prime_iff MulEquiv.prime_iff

end Map

end Prime

/- warning: prime.left_dvd_or_dvd_right_of_dvd_mul -> Prime.left_dvd_or_dvd_right_of_dvd_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) p b)) -> (Or (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p a) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) p b)) -> (Or (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p a) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align prime.left_dvd_or_dvd_right_of_dvd_mul Prime.left_dvd_or_dvd_right_of_dvd_mulₓ'. -/
theorem Prime.left_dvd_or_dvd_right_of_dvd_mul [CancelCommMonoidWithZero α] {p : α} (hp : Prime p)
    {a b : α} : a ∣ p * b → p ∣ a ∨ a ∣ b :=
  by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
  · rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)
#align prime.left_dvd_or_dvd_right_of_dvd_mul Prime.left_dvd_or_dvd_right_of_dvd_mul

/- warning: prime.pow_dvd_of_dvd_mul_left -> Prime.pow_dvd_of_dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p a)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p a)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) b))
Case conversion may be inaccurate. Consider using '#align prime.pow_dvd_of_dvd_mul_left Prime.pow_dvd_of_dvd_mul_leftₓ'. -/
theorem Prime.pow_dvd_of_dvd_mul_left [CancelCommMonoidWithZero α] {p a b : α} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b :=
  by
  induction' n with n ih
  · rw [pow_zero]
    exact one_dvd b
  · obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ']
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ', mul_left_comm]
#align prime.pow_dvd_of_dvd_mul_left Prime.pow_dvd_of_dvd_mul_left

/- warning: prime.pow_dvd_of_dvd_mul_right -> Prime.pow_dvd_of_dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n) a))
Case conversion may be inaccurate. Consider using '#align prime.pow_dvd_of_dvd_mul_right Prime.pow_dvd_of_dvd_mul_rightₓ'. -/
theorem Prime.pow_dvd_of_dvd_mul_right [CancelCommMonoidWithZero α] {p a b : α} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a :=
  by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'
#align prime.pow_dvd_of_dvd_mul_right Prime.pow_dvd_of_dvd_mul_right

/- warning: prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd -> Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α} {n : Nat}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (Nat.succ n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a (Nat.succ n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) b n))) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α} {n : Nat}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (Nat.succ n)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a (Nat.succ n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) b n))) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p a)
Case conversion may be inaccurate. Consider using '#align prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvdₓ'. -/
theorem Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd [CancelCommMonoidWithZero α] {p a b : α}
    {n : ℕ} (hp : Prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n) (hb : ¬p ^ 2 ∣ b) : p ∣ a :=
  by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  cases' hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H hbdiv
  · exact hp.dvd_of_dvd_pow H
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can divide out a common factor of `p ^ n` from the equation `hy`.
  have : a ^ n.succ * x ^ n = p * y :=
    by
    refine' mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) _
    rw [← mul_assoc _ p, ← pow_succ', ← hy, mul_pow, ← mul_assoc (a ^ n.succ), mul_comm _ (p ^ n),
      mul_assoc]
  -- So `p ∣ a` (and we're done) or `p ∣ x`, which can't be the case since it implies `p^2 ∣ b`.
  refine' hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨_, this⟩).resolve_right fun hdvdx => hb _)
  obtain ⟨z, rfl⟩ := hp.dvd_of_dvd_pow hdvdx
  rw [pow_two, ← mul_assoc]
  exact dvd_mul_right _ _
#align prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd

/- warning: prime_pow_succ_dvd_mul -> prime_pow_succ_dvd_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {x : α} {y : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {i : Nat}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x y)) -> (Or (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) x) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {x : α} {y : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {i : Nat}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) x y)) -> (Or (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p y)))
Case conversion may be inaccurate. Consider using '#align prime_pow_succ_dvd_mul prime_pow_succ_dvd_mulₓ'. -/
theorem prime_pow_succ_dvd_mul {α : Type _} [CancelCommMonoidWithZero α] {p x y : α} (h : Prime p)
    {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y :=
  by
  rw [or_iff_not_imp_right]
  intro hy
  induction' i with i ih generalizing x
  · simp only [zero_add, pow_one] at *
    exact (h.dvd_or_dvd hxy).resolve_right hy
  rw [pow_succ] at hxy⊢
  obtain ⟨x', rfl⟩ := (h.dvd_or_dvd (dvd_of_mul_right_dvd hxy)).resolve_right hy
  rw [mul_assoc] at hxy
  exact mul_dvd_mul_left p (ih ((mul_dvd_mul_iff_left h.ne_zero).mp hxy))
#align prime_pow_succ_dvd_mul prime_pow_succ_dvd_mul

#print Irreducible /-
/-- `irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
structure Irreducible [Monoid α] (p : α) : Prop where
  not_unit : ¬IsUnit p
  is_unit_or_is_unit' : ∀ a b, p = a * b → IsUnit a ∨ IsUnit b
#align irreducible Irreducible
-/

namespace Irreducible

/- warning: irreducible.not_dvd_one -> Irreducible.not_dvd_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : α}, (Irreducible.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) p) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) p (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : α}, (Irreducible.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) p) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) p (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align irreducible.not_dvd_one Irreducible.not_dvd_oneₓ'. -/
theorem not_dvd_one [CommMonoid α] {p : α} (hp : Irreducible p) : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one _) hp.not_unit
#align irreducible.not_dvd_one Irreducible.not_dvd_one

/- warning: irreducible.is_unit_or_is_unit -> Irreducible.isUnit_or_isUnit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {p : α}, (Irreducible.{u1} α _inst_1 p) -> (forall {a : α} {b : α}, (Eq.{succ u1} α p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) -> (Or (IsUnit.{u1} α _inst_1 a) (IsUnit.{u1} α _inst_1 b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {p : α}, (Irreducible.{u1} α _inst_1 p) -> (forall {a : α} {b : α}, (Eq.{succ u1} α p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) -> (Or (IsUnit.{u1} α _inst_1 a) (IsUnit.{u1} α _inst_1 b)))
Case conversion may be inaccurate. Consider using '#align irreducible.is_unit_or_is_unit Irreducible.isUnit_or_isUnitₓ'. -/
theorem isUnit_or_isUnit [Monoid α] {p : α} (hp : Irreducible p) {a b : α} (h : p = a * b) :
    IsUnit a ∨ IsUnit b :=
  hp.is_unit_or_is_unit' a b h
#align irreducible.is_unit_or_is_unit Irreducible.isUnit_or_isUnit

end Irreducible

/- warning: irreducible_iff -> irreducible_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {p : α}, Iff (Irreducible.{u1} α _inst_1 p) (And (Not (IsUnit.{u1} α _inst_1 p)) (forall (a : α) (b : α), (Eq.{succ u1} α p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) -> (Or (IsUnit.{u1} α _inst_1 a) (IsUnit.{u1} α _inst_1 b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {p : α}, Iff (Irreducible.{u1} α _inst_1 p) (And (Not (IsUnit.{u1} α _inst_1 p)) (forall (a : α) (b : α), (Eq.{succ u1} α p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) -> (Or (IsUnit.{u1} α _inst_1 a) (IsUnit.{u1} α _inst_1 b))))
Case conversion may be inaccurate. Consider using '#align irreducible_iff irreducible_iffₓ'. -/
theorem irreducible_iff [Monoid α] {p : α} :
    Irreducible p ↔ ¬IsUnit p ∧ ∀ a b, p = a * b → IsUnit a ∨ IsUnit b :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
#align irreducible_iff irreducible_iff

/- warning: not_irreducible_one -> not_irreducible_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Not (Irreducible.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Not (Irreducible.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align not_irreducible_one not_irreducible_oneₓ'. -/
@[simp]
theorem not_irreducible_one [Monoid α] : ¬Irreducible (1 : α) := by simp [irreducible_iff]
#align not_irreducible_one not_irreducible_one

/- warning: irreducible.ne_one -> Irreducible.ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {p : α}, (Irreducible.{u1} α _inst_1 p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {p : α}, (Irreducible.{u1} α _inst_1 p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align irreducible.ne_one Irreducible.ne_oneₓ'. -/
theorem Irreducible.ne_one [Monoid α] : ∀ {p : α}, Irreducible p → p ≠ 1
  | _, hp, rfl => not_irreducible_one hp
#align irreducible.ne_one Irreducible.ne_one

/- warning: not_irreducible_zero -> not_irreducible_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α], Not (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α], Not (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align not_irreducible_zero not_irreducible_zeroₓ'. -/
@[simp]
theorem not_irreducible_zero [MonoidWithZero α] : ¬Irreducible (0 : α)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : α) ∨ IsUnit (0 : α) := h 0 0 (mul_zero 0).symm
    this.elim hn0 hn0
#align not_irreducible_zero not_irreducible_zero

/- warning: irreducible.ne_zero -> Irreducible.ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {p : α}, (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {p : α}, (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align irreducible.ne_zero Irreducible.ne_zeroₓ'. -/
theorem Irreducible.ne_zero [MonoidWithZero α] : ∀ {p : α}, Irreducible p → p ≠ 0
  | _, hp, rfl => not_irreducible_zero hp
#align irreducible.ne_zero Irreducible.ne_zero

/- warning: of_irreducible_mul -> of_irreducible_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {x : α} {y : α}, (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) x y)) -> (Or (IsUnit.{u1} α _inst_1 x) (IsUnit.{u1} α _inst_1 y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {x : α} {y : α}, (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) x y)) -> (Or (IsUnit.{u1} α _inst_1 x) (IsUnit.{u1} α _inst_1 y))
Case conversion may be inaccurate. Consider using '#align of_irreducible_mul of_irreducible_mulₓ'. -/
theorem of_irreducible_mul {α} [Monoid α] {x y : α} : Irreducible (x * y) → IsUnit x ∨ IsUnit y
  | ⟨_, h⟩ => h _ _ rfl
#align of_irreducible_mul of_irreducible_mul

#print of_irreducible_pow /-
theorem of_irreducible_pow {α} [Monoid α] {x : α} {n : ℕ} (hn : n ≠ 1) :
    Irreducible (x ^ n) → IsUnit x :=
  by
  obtain hn | hn := hn.lt_or_lt
  · simp only [nat.lt_one_iff.mp hn, IsEmpty.forall_iff, not_irreducible_one, pow_zero]
  intro h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [pow_succ, add_comm] at h
  exact (or_iff_left_of_imp is_unit_pow_succ_iff.mp).mp (of_irreducible_mul h)
#align of_irreducible_pow of_irreducible_pow
-/

/- warning: irreducible_or_factor -> irreducible_or_factor is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (x : α), (Not (IsUnit.{u1} α _inst_1 x)) -> (Or (Irreducible.{u1} α _inst_1 x) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (Not (IsUnit.{u1} α _inst_1 a)) (And (Not (IsUnit.{u1} α _inst_1 b)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) x))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (x : α), (Not (IsUnit.{u1} α _inst_1 x)) -> (Or (Irreducible.{u1} α _inst_1 x) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (Not (IsUnit.{u1} α _inst_1 a)) (And (Not (IsUnit.{u1} α _inst_1 b)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b) x))))))
Case conversion may be inaccurate. Consider using '#align irreducible_or_factor irreducible_or_factorₓ'. -/
theorem irreducible_or_factor {α} [Monoid α] (x : α) (h : ¬IsUnit x) :
    Irreducible x ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ a * b = x :=
  by
  haveI := Classical.dec
  refine' or_iff_not_imp_right.2 fun H => _
  simp [h, irreducible_iff] at H⊢
  refine' fun a b h => by_contradiction fun o => _
  simp [not_or] at o
  exact H _ o.1 _ o.2 h.symm
#align irreducible_or_factor irreducible_or_factor

#print Irreducible.dvd_symm /-
/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
theorem Irreducible.dvd_symm [Monoid α] {p q : α} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q → q ∣ p := by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_unit)]
#align irreducible.dvd_symm Irreducible.dvd_symm
-/

#print Irreducible.dvd_comm /-
theorem Irreducible.dvd_comm [Monoid α] {p q : α} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩
#align irreducible.dvd_comm Irreducible.dvd_comm
-/

section

variable [Monoid α]

/- warning: irreducible_units_mul -> irreducible_units_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : Units.{u1} α _inst_1) (b : α), Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) a) b)) (Irreducible.{u1} α _inst_1 b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : Units.{u1} α _inst_1) (b : α), Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Units.val.{u1} α _inst_1 a) b)) (Irreducible.{u1} α _inst_1 b)
Case conversion may be inaccurate. Consider using '#align irreducible_units_mul irreducible_units_mulₓ'. -/
theorem irreducible_units_mul (a : αˣ) (b : α) : Irreducible (↑a * b) ↔ Irreducible b :=
  by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine' fun hu => ⟨fun h A B HAB => _, fun h A B HAB => _⟩
  · rw [← a.is_unit_units_mul]
    apply h
    rw [mul_assoc, ← HAB]
  · rw [← a⁻¹.is_unit_units_mul]
    apply h
    rw [mul_assoc, ← HAB, Units.inv_mul_cancel_left]
#align irreducible_units_mul irreducible_units_mul

/- warning: irreducible_is_unit_mul -> irreducible_isUnit_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α}, (IsUnit.{u1} α _inst_1 a) -> (Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) (Irreducible.{u1} α _inst_1 b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α}, (IsUnit.{u1} α _inst_1 a) -> (Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) (Irreducible.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align irreducible_is_unit_mul irreducible_isUnit_mulₓ'. -/
theorem irreducible_isUnit_mul {a b : α} (h : IsUnit a) : Irreducible (a * b) ↔ Irreducible b :=
  let ⟨a, ha⟩ := h
  ha ▸ irreducible_units_mul a b
#align irreducible_is_unit_mul irreducible_isUnit_mul

/- warning: irreducible_mul_units -> irreducible_mul_units is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : Units.{u1} α _inst_1) (b : α), Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) a))) (Irreducible.{u1} α _inst_1 b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (a : Units.{u1} α _inst_1) (b : α), Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b (Units.val.{u1} α _inst_1 a))) (Irreducible.{u1} α _inst_1 b)
Case conversion may be inaccurate. Consider using '#align irreducible_mul_units irreducible_mul_unitsₓ'. -/
theorem irreducible_mul_units (a : αˣ) (b : α) : Irreducible (b * ↑a) ↔ Irreducible b :=
  by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine' fun hu => ⟨fun h A B HAB => _, fun h A B HAB => _⟩
  · rw [← Units.isUnit_mul_units B a]
    apply h
    rw [← mul_assoc, ← HAB]
  · rw [← Units.isUnit_mul_units B a⁻¹]
    apply h
    rw [← mul_assoc, ← HAB, Units.mul_inv_cancel_right]
#align irreducible_mul_units irreducible_mul_units

/- warning: irreducible_mul_is_unit -> irreducible_mul_isUnit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α}, (IsUnit.{u1} α _inst_1 a) -> (Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b a)) (Irreducible.{u1} α _inst_1 b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α}, (IsUnit.{u1} α _inst_1 a) -> (Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b a)) (Irreducible.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align irreducible_mul_is_unit irreducible_mul_isUnitₓ'. -/
theorem irreducible_mul_isUnit {a b : α} (h : IsUnit a) : Irreducible (b * a) ↔ Irreducible b :=
  let ⟨a, ha⟩ := h
  ha ▸ irreducible_mul_units a b
#align irreducible_mul_is_unit irreducible_mul_isUnit

/- warning: irreducible_mul_iff -> irreducible_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α}, Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) (Or (And (Irreducible.{u1} α _inst_1 a) (IsUnit.{u1} α _inst_1 b)) (And (Irreducible.{u1} α _inst_1 b) (IsUnit.{u1} α _inst_1 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α}, Iff (Irreducible.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a b)) (Or (And (Irreducible.{u1} α _inst_1 a) (IsUnit.{u1} α _inst_1 b)) (And (Irreducible.{u1} α _inst_1 b) (IsUnit.{u1} α _inst_1 a)))
Case conversion may be inaccurate. Consider using '#align irreducible_mul_iff irreducible_mul_iffₓ'. -/
theorem irreducible_mul_iff {a b : α} :
    Irreducible (a * b) ↔ Irreducible a ∧ IsUnit b ∨ Irreducible b ∧ IsUnit a :=
  by
  constructor
  · refine' fun h => Or.imp (fun h' => ⟨_, h'⟩) (fun h' => ⟨_, h'⟩) (h.is_unit_or_is_unit rfl).symm
    · rwa [irreducible_mul_isUnit h'] at h
    · rwa [irreducible_isUnit_mul h'] at h
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_isUnit hb]
    · rwa [irreducible_isUnit_mul ha]
#align irreducible_mul_iff irreducible_mul_iff

end

section CommMonoid

variable [CommMonoid α] {a : α}

/- warning: irreducible.not_square -> Irreducible.not_square is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, (Irreducible.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) -> (Not (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, (Irreducible.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) -> (Not (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a))
Case conversion may be inaccurate. Consider using '#align irreducible.not_square Irreducible.not_squareₓ'. -/
theorem Irreducible.not_square (ha : Irreducible a) : ¬IsSquare a :=
  by
  rintro ⟨b, rfl⟩
  simp only [irreducible_mul_iff, or_self_iff] at ha
  exact ha.1.not_unit ha.2
#align irreducible.not_square Irreducible.not_square

/- warning: is_square.not_irreducible -> IsSquare.not_irreducible is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, (IsSquare.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a) -> (Not (Irreducible.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, (IsSquare.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a) -> (Not (Irreducible.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align is_square.not_irreducible IsSquare.not_irreducibleₓ'. -/
theorem IsSquare.not_irreducible (ha : IsSquare a) : ¬Irreducible a := fun h => h.not_square ha
#align is_square.not_irreducible IsSquare.not_irreducible

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] {a p : α}

#print Prime.irreducible /-
protected theorem Prime.irreducible (hp : Prime p) : Irreducible p :=
  ⟨hp.not_unit, fun a b hab =>
    (show a * b ∣ a ∨ a * b ∣ b from hab ▸ hp.dvd_or_dvd (hab ▸ dvd_rfl)).elim
      (fun ⟨x, hx⟩ =>
        Or.inr
          (isUnit_iff_dvd_one.2
            ⟨x,
              mul_right_cancel₀ (show a ≠ 0 from fun h => by simp_all [Prime]) <| by
                conv =>
                    lhs
                    rw [hx] <;>
                  simp [mul_comm, mul_assoc, mul_left_comm]⟩))
      fun ⟨x, hx⟩ =>
      Or.inl
        (isUnit_iff_dvd_one.2
          ⟨x,
            mul_right_cancel₀ (show b ≠ 0 from fun h => by simp_all [Prime]) <| by
              conv =>
                  lhs
                  rw [hx] <;>
                simp [mul_comm, mul_assoc, mul_left_comm]⟩)⟩
#align prime.irreducible Prime.irreducible
-/

/- warning: succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul -> succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {a : α} {b : α} {k : Nat} {l : Nat}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p k) a) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p l) b) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k l) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) -> (Or (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) a) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) l (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {a : α} {b : α} {k : Nat} {l : Nat}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p k) a) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p l) b) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) -> (Or (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) a) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) l (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) b)))
Case conversion may be inaccurate. Consider using '#align succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul succ_dvd_or_succ_dvd_of_succ_sum_dvd_mulₓ'. -/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (hp : Prime p) {a b : α} {k l : ℕ} :
    p ^ k ∣ a → p ^ l ∣ b → p ^ (k + l + 1) ∣ a * b → p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz
  have hp0 : p ^ (k + l) ≠ 0 := pow_ne_zero _ hp.NeZero
  have hpd : p ∣ x * y := ⟨z, by rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_or_dvd hpd).elim
    (fun ⟨d, hd⟩ => Or.inl ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
    fun ⟨d, hd⟩ => Or.inr ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩
#align succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul

/- warning: prime.not_square -> Prime.not_square is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Not (IsSquare.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Not (IsSquare.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p))
Case conversion may be inaccurate. Consider using '#align prime.not_square Prime.not_squareₓ'. -/
theorem Prime.not_square (hp : Prime p) : ¬IsSquare p :=
  hp.Irreducible.not_square
#align prime.not_square Prime.not_square

/- warning: is_square.not_prime -> IsSquare.not_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α}, (IsSquare.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a) -> (Not (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α}, (IsSquare.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a) -> (Not (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align is_square.not_prime IsSquare.not_primeₓ'. -/
theorem IsSquare.not_prime (ha : IsSquare a) : ¬Prime a := fun h => h.not_square ha
#align is_square.not_prime IsSquare.not_prime

#print pow_not_prime /-
theorem pow_not_prime {n : ℕ} (hn : n ≠ 1) : ¬Prime (a ^ n) := fun hp =>
  hp.not_unit <| IsUnit.pow _ <| of_irreducible_pow hn <| hp.Irreducible
#align pow_not_prime pow_not_prime
-/

end CancelCommMonoidWithZero

#print Associated /-
/-- Two elements of a `monoid` are `associated` if one of them is another one
multiplied by a unit on the right. -/
def Associated [Monoid α] (x y : α) : Prop :=
  ∃ u : αˣ, x * u = y
#align associated Associated
-/

-- mathport name: «expr ~ᵤ »
local infixl:50 " ~ᵤ " => Associated

namespace Associated

#print Associated.refl /-
@[refl]
protected theorem refl [Monoid α] (x : α) : x ~ᵤ x :=
  ⟨1, by simp⟩
#align associated.refl Associated.refl
-/

instance [Monoid α] : IsRefl α Associated :=
  ⟨Associated.refl⟩

#print Associated.symm /-
@[symm]
protected theorem symm [Monoid α] : ∀ {x y : α}, x ~ᵤ y → y ~ᵤ x
  | x, _, ⟨u, rfl⟩ => ⟨u⁻¹, by rw [mul_assoc, Units.mul_inv, mul_one]⟩
#align associated.symm Associated.symm
-/

instance [Monoid α] : IsSymm α Associated :=
  ⟨fun a b => Associated.symm⟩

#print Associated.comm /-
protected theorem comm [Monoid α] {x y : α} : x ~ᵤ y ↔ y ~ᵤ x :=
  ⟨Associated.symm, Associated.symm⟩
#align associated.comm Associated.comm
-/

#print Associated.trans /-
@[trans]
protected theorem trans [Monoid α] : ∀ {x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
  | x, _, _, ⟨u, rfl⟩, ⟨v, rfl⟩ => ⟨u * v, by rw [Units.val_mul, mul_assoc]⟩
#align associated.trans Associated.trans
-/

instance [Monoid α] : IsTrans α Associated :=
  ⟨fun a b c => Associated.trans⟩

#print Associated.setoid /-
/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def setoid (α : Type _) [Monoid α] : Setoid α
    where
  R := Associated
  iseqv := ⟨Associated.refl, fun a b => Associated.symm, fun a b c => Associated.trans⟩
#align associated.setoid Associated.setoid
-/

end Associated

attribute [local instance] Associated.setoid

/- warning: unit_associated_one -> unit_associated_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {u : Units.{u1} α _inst_1}, Associated.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) u) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {u : Units.{u1} α _inst_1}, Associated.{u1} α _inst_1 (Units.val.{u1} α _inst_1 u) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align unit_associated_one unit_associated_oneₓ'. -/
theorem unit_associated_one [Monoid α] {u : αˣ} : (u : α) ~ᵤ 1 :=
  ⟨u⁻¹, Units.mul_inv u⟩
#align unit_associated_one unit_associated_one

/- warning: associated_one_iff_is_unit -> associated_one_iff_isUnit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, Iff (Associated.{u1} α _inst_1 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) (IsUnit.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, Iff (Associated.{u1} α _inst_1 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) (IsUnit.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align associated_one_iff_is_unit associated_one_iff_isUnitₓ'. -/
theorem associated_one_iff_isUnit [Monoid α] {a : α} : (a : α) ~ᵤ 1 ↔ IsUnit a :=
  Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mul _).symm⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩
#align associated_one_iff_is_unit associated_one_iff_isUnit

/- warning: associated_zero_iff_eq_zero -> associated_zero_iff_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] (a : α), Iff (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] (a : α), Iff (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align associated_zero_iff_eq_zero associated_zero_iff_eq_zeroₓ'. -/
theorem associated_zero_iff_eq_zero [MonoidWithZero α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
  Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a
#align associated_zero_iff_eq_zero associated_zero_iff_eq_zero

/- warning: associated_one_of_mul_eq_one -> associated_one_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} (b : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} (b : α), (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align associated_one_of_mul_eq_one associated_one_of_mul_eq_oneₓ'. -/
theorem associated_one_of_mul_eq_one [CommMonoid α] {a : α} (b : α) (hab : a * b = 1) : a ~ᵤ 1 :=
  show (Units.mkOfMulEqOne a b hab : α) ~ᵤ 1 from unit_associated_one
#align associated_one_of_mul_eq_one associated_one_of_mul_eq_one

/- warning: associated_one_of_associated_mul_one -> associated_one_of_associated_mul_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align associated_one_of_associated_mul_one associated_one_of_associated_mul_oneₓ'. -/
theorem associated_one_of_associated_mul_one [CommMonoid α] {a b : α} : a * b ~ᵤ 1 → a ~ᵤ 1
  | ⟨u, h⟩ => associated_one_of_mul_eq_one (b * u) <| by simpa [mul_assoc] using h
#align associated_one_of_associated_mul_one associated_one_of_associated_mul_one

/- warning: associated_mul_unit_left -> associated_mul_unit_left is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β _inst_1 u) -> (Associated.{u1} β _inst_1 (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a u) a)
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β _inst_1 u) -> (Associated.{u1} β _inst_1 (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a u) a)
Case conversion may be inaccurate. Consider using '#align associated_mul_unit_left associated_mul_unit_leftₓ'. -/
theorem associated_mul_unit_left {β : Type _} [Monoid β] (a u : β) (hu : IsUnit u) :
    Associated (a * u) a :=
  let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩
#align associated_mul_unit_left associated_mul_unit_left

/- warning: associated_unit_mul_left -> associated_unit_mul_left is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u a) a)
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u a) a)
Case conversion may be inaccurate. Consider using '#align associated_unit_mul_left associated_unit_mul_leftₓ'. -/
theorem associated_unit_mul_left {β : Type _} [CommMonoid β] (a u : β) (hu : IsUnit u) :
    Associated (u * a) a := by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu
#align associated_unit_mul_left associated_unit_mul_left

/- warning: associated_mul_unit_right -> associated_mul_unit_right is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β _inst_1 u) -> (Associated.{u1} β _inst_1 a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a u))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β _inst_1 u) -> (Associated.{u1} β _inst_1 a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a u))
Case conversion may be inaccurate. Consider using '#align associated_mul_unit_right associated_mul_unit_rightₓ'. -/
theorem associated_mul_unit_right {β : Type _} [Monoid β] (a u : β) (hu : IsUnit u) :
    Associated a (a * u) :=
  (associated_mul_unit_left a u hu).symm
#align associated_mul_unit_right associated_mul_unit_right

/- warning: associated_unit_mul_right -> associated_unit_mul_right is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u a))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (a : β) (u : β), (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u a))
Case conversion may be inaccurate. Consider using '#align associated_unit_mul_right associated_unit_mul_rightₓ'. -/
theorem associated_unit_mul_right {β : Type _} [CommMonoid β] (a u : β) (hu : IsUnit u) :
    Associated a (u * a) :=
  (associated_unit_mul_left a u hu).symm
#align associated_unit_mul_right associated_unit_mul_right

/- warning: associated_mul_is_unit_left_iff -> associated_mul_isUnit_left_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {u : β} {b : β}, (IsUnit.{u1} β _inst_1 u) -> (Iff (Associated.{u1} β _inst_1 (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a u) b) (Associated.{u1} β _inst_1 a b))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {u : β} {b : β}, (IsUnit.{u1} β _inst_1 u) -> (Iff (Associated.{u1} β _inst_1 (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a u) b) (Associated.{u1} β _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align associated_mul_is_unit_left_iff associated_mul_isUnit_left_iffₓ'. -/
theorem associated_mul_isUnit_left_iff {β : Type _} [Monoid β] {a u b : β} (hu : IsUnit u) :
    Associated (a * u) b ↔ Associated a b :=
  ⟨trans (associated_mul_unit_right _ _ hu), trans (associated_mul_unit_left _ _ hu)⟩
#align associated_mul_is_unit_left_iff associated_mul_isUnit_left_iff

/- warning: associated_is_unit_mul_left_iff -> associated_isUnit_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {u : β} {a : β} {b : β}, (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u a) b) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {u : β} {a : β} {b : β}, (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u a) b) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align associated_is_unit_mul_left_iff associated_isUnit_mul_left_iffₓ'. -/
theorem associated_isUnit_mul_left_iff {β : Type _} [CommMonoid β] {u a b : β} (hu : IsUnit u) :
    Associated (u * a) b ↔ Associated a b :=
  by
  rw [mul_comm]
  exact associated_mul_isUnit_left_iff hu
#align associated_is_unit_mul_left_iff associated_isUnit_mul_left_iff

/- warning: associated_mul_is_unit_right_iff -> associated_mul_isUnit_right_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {b : β} {u : β}, (IsUnit.{u1} β _inst_1 u) -> (Iff (Associated.{u1} β _inst_1 a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) b u)) (Associated.{u1} β _inst_1 a b))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {b : β} {u : β}, (IsUnit.{u1} β _inst_1 u) -> (Iff (Associated.{u1} β _inst_1 a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) b u)) (Associated.{u1} β _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align associated_mul_is_unit_right_iff associated_mul_isUnit_right_iffₓ'. -/
theorem associated_mul_isUnit_right_iff {β : Type _} [Monoid β] {a b u : β} (hu : IsUnit u) :
    Associated a (b * u) ↔ Associated a b :=
  Associated.comm.trans <| (associated_mul_isUnit_left_iff hu).trans Associated.comm
#align associated_mul_is_unit_right_iff associated_mul_isUnit_right_iff

/- warning: associated_is_unit_mul_right_iff -> associated_isUnit_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : β} {u : β} {b : β}, (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u b)) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : β} {u : β} {b : β}, (IsUnit.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) -> (Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) u b)) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align associated_is_unit_mul_right_iff associated_isUnit_mul_right_iffₓ'. -/
theorem associated_isUnit_mul_right_iff {β : Type _} [CommMonoid β] {a u b : β} (hu : IsUnit u) :
    Associated a (u * b) ↔ Associated a b :=
  Associated.comm.trans <| (associated_isUnit_mul_left_iff hu).trans Associated.comm
#align associated_is_unit_mul_right_iff associated_isUnit_mul_right_iff

/- warning: associated_mul_unit_left_iff -> associated_mul_unit_left_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β _inst_1}, Iff (Associated.{u1} β _inst_1 (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} β _inst_1) β (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} β _inst_1) β (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} β _inst_1) β (coeBase.{succ u1, succ u1} (Units.{u1} β _inst_1) β (Units.hasCoe.{u1} β _inst_1)))) u)) b) (Associated.{u1} β _inst_1 a b)
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β _inst_1}, Iff (Associated.{u1} β _inst_1 (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) a (Units.val.{u1} β _inst_1 u)) b) (Associated.{u1} β _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align associated_mul_unit_left_iff associated_mul_unit_left_iffₓ'. -/
@[simp]
theorem associated_mul_unit_left_iff {β : Type _} [Monoid β] {a b : β} {u : Units β} :
    Associated (a * u) b ↔ Associated a b :=
  associated_mul_isUnit_left_iff u.IsUnit
#align associated_mul_unit_left_iff associated_mul_unit_left_iff

/- warning: associated_unit_mul_left_iff -> associated_unit_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)}, Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (coeBase.{succ u1, succ u1} (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (Units.hasCoe.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) u) a) b) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b)
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)}, Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Units.val.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) a) b) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align associated_unit_mul_left_iff associated_unit_mul_left_iffₓ'. -/
@[simp]
theorem associated_unit_mul_left_iff {β : Type _} [CommMonoid β] {a b : β} {u : Units β} :
    Associated (↑u * a) b ↔ Associated a b :=
  associated_isUnit_mul_left_iff u.IsUnit
#align associated_unit_mul_left_iff associated_unit_mul_left_iff

/- warning: associated_mul_unit_right_iff -> associated_mul_unit_right_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β _inst_1}, Iff (Associated.{u1} β _inst_1 a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} β _inst_1) β (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} β _inst_1) β (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} β _inst_1) β (coeBase.{succ u1, succ u1} (Units.{u1} β _inst_1) β (Units.hasCoe.{u1} β _inst_1)))) u))) (Associated.{u1} β _inst_1 a b)
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β _inst_1}, Iff (Associated.{u1} β _inst_1 a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) b (Units.val.{u1} β _inst_1 u))) (Associated.{u1} β _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align associated_mul_unit_right_iff associated_mul_unit_right_iffₓ'. -/
@[simp]
theorem associated_mul_unit_right_iff {β : Type _} [Monoid β] {a b : β} {u : Units β} :
    Associated a (b * u) ↔ Associated a b :=
  associated_mul_isUnit_right_iff u.IsUnit
#align associated_mul_unit_right_iff associated_mul_unit_right_iff

/- warning: associated_unit_mul_right_iff -> associated_unit_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)}, Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (coeBase.{succ u1, succ u1} (Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) β (Units.hasCoe.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) u) b)) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b)
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {a : β} {b : β} {u : Units.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)}, Iff (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Units.val.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) u) b)) (Associated.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align associated_unit_mul_right_iff associated_unit_mul_right_iffₓ'. -/
@[simp]
theorem associated_unit_mul_right_iff {β : Type _} [CommMonoid β] {a b : β} {u : Units β} :
    Associated a (↑u * b) ↔ Associated a b :=
  associated_isUnit_mul_right_iff u.IsUnit
#align associated_unit_mul_right_iff associated_unit_mul_right_iff

/- warning: associated.mul_mul -> Associated.mul_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a₁ b₁) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a₂ b₂) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a₁ a₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b₁ b₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a₁ b₁) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a₂ b₂) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a₁ a₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b₁ b₂))
Case conversion may be inaccurate. Consider using '#align associated.mul_mul Associated.mul_mulₓ'. -/
theorem Associated.mul_mul [CommMonoid α] {a₁ a₂ b₁ b₂ : α} :
    a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → a₁ * a₂ ~ᵤ b₁ * b₂
  | ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ => ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩
#align associated.mul_mul Associated.mul_mul

/- warning: associated.mul_left -> Associated.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) {b : α} {c : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b c) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) {b : α} {c : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b c) -> (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c))
Case conversion may be inaccurate. Consider using '#align associated.mul_left Associated.mul_leftₓ'. -/
theorem Associated.mul_left [CommMonoid α] (a : α) {b c : α} (h : b ~ᵤ c) : a * b ~ᵤ a * c :=
  (Associated.refl a).mul_mul h
#align associated.mul_left Associated.mul_left

/- warning: associated.mul_right -> Associated.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a b) -> (forall (c : α), Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a b) -> (forall (c : α), Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align associated.mul_right Associated.mul_rightₓ'. -/
theorem Associated.mul_right [CommMonoid α] {a b : α} (h : a ~ᵤ b) (c : α) : a * c ~ᵤ b * c :=
  h.mul_mul (Associated.refl c)
#align associated.mul_right Associated.mul_right

#print Associated.pow_pow /-
theorem Associated.pow_pow [CommMonoid α] {a b : α} {n : ℕ} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n :=
  by
  induction' n with n ih; · simp [h]
  convert h.mul_mul ih <;> rw [pow_succ]
#align associated.pow_pow Associated.pow_pow
-/

#print Associated.dvd /-
protected theorem Associated.dvd [Monoid α] {a b : α} : a ~ᵤ b → a ∣ b := fun ⟨u, hu⟩ =>
  ⟨u, hu.symm⟩
#align associated.dvd Associated.dvd
-/

#print Associated.dvd_dvd /-
protected theorem Associated.dvd_dvd [Monoid α] {a b : α} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
  ⟨h.Dvd, h.symm.Dvd⟩
#align associated.dvd_dvd Associated.dvd_dvd
-/

#print associated_of_dvd_dvd /-
theorem associated_of_dvd_dvd [CancelMonoidWithZero α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    a ~ᵤ b := by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases ha0 : a = 0
  · simp_all
  have hac0 : a * c ≠ 0 := by
    intro con
    rw [Con, zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hcd : c * d = 1 := mul_left_cancel₀ ha0 this
  have : a * c * (d * c) = a * c * 1 := by rw [← mul_assoc, ← a_eq, mul_one]
  have hdc : d * c = 1 := mul_left_cancel₀ hac0 this
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩
#align associated_of_dvd_dvd associated_of_dvd_dvd
-/

#print dvd_dvd_iff_associated /-
theorem dvd_dvd_iff_associated [CancelMonoidWithZero α] {a b : α} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
  ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩
#align dvd_dvd_iff_associated dvd_dvd_iff_associated
-/

instance [CancelMonoidWithZero α] [DecidableRel ((· ∣ ·) : α → α → Prop)] :
    DecidableRel ((· ~ᵤ ·) : α → α → Prop) := fun a b => decidable_of_iff _ dvd_dvd_iff_associated

#print Associated.dvd_iff_dvd_left /-
theorem Associated.dvd_iff_dvd_left [Monoid α] {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
  let ⟨u, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm
#align associated.dvd_iff_dvd_left Associated.dvd_iff_dvd_left
-/

#print Associated.dvd_iff_dvd_right /-
theorem Associated.dvd_iff_dvd_right [Monoid α] {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
  let ⟨u, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm
#align associated.dvd_iff_dvd_right Associated.dvd_iff_dvd_right
-/

/- warning: associated.eq_zero_iff -> Associated.eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α} {b : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a b) -> (Iff (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α} {b : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a b) -> (Iff (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align associated.eq_zero_iff Associated.eq_zero_iffₓ'. -/
theorem Associated.eq_zero_iff [MonoidWithZero α] {a b : α} (h : a ~ᵤ b) : a = 0 ↔ b = 0 :=
  ⟨fun ha => by
    let ⟨u, hu⟩ := h
    simp [hu.symm, ha], fun hb => by
    let ⟨u, hu⟩ := h.symm
    simp [hu.symm, hb]⟩
#align associated.eq_zero_iff Associated.eq_zero_iff

/- warning: associated.ne_zero_iff -> Associated.ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α} {b : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a b) -> (Iff (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α} {b : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a b) -> (Iff (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align associated.ne_zero_iff Associated.ne_zero_iffₓ'. -/
theorem Associated.ne_zero_iff [MonoidWithZero α] {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
  not_congr h.eq_zero_iff
#align associated.ne_zero_iff Associated.ne_zero_iff

#print Associated.prime /-
protected theorem Associated.prime [CommMonoidWithZero α] {p q : α} (h : p ~ᵤ q) (hp : Prime p) :
    Prime q :=
  ⟨h.ne_zero_iff.1 hp.NeZero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ => hp.not_unit ⟨v * u⁻¹, by simp [hv, hu.symm]⟩,
      hu ▸ by
        simp [Units.mul_right_dvd]
        intro a b
        exact hp.dvd_or_dvd⟩⟩
#align associated.prime Associated.prime
-/

#print Irreducible.associated_of_dvd /-
theorem Irreducible.associated_of_dvd [CancelMonoidWithZero α] {p q : α} (p_irr : Irreducible p)
    (q_irr : Irreducible q) (dvd : p ∣ q) : Associated p q :=
  associated_of_dvd_dvd dvd (p_irr.dvd_symm q_irr dvd)
#align irreducible.associated_of_dvd Irreducible.associated_of_dvd
-/

#print Irreducible.dvd_irreducible_iff_associated /-
theorem Irreducible.dvd_irreducible_iff_associated [CancelMonoidWithZero α] {p q : α}
    (pp : Irreducible p) (qp : Irreducible q) : p ∣ q ↔ Associated p q :=
  ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩
#align irreducible.dvd_irreducible_iff_associated Irreducible.dvd_irreducible_iff_associated
-/

#print Prime.associated_of_dvd /-
theorem Prime.associated_of_dvd [CancelCommMonoidWithZero α] {p q : α} (p_prime : Prime p)
    (q_prime : Prime q) (dvd : p ∣ q) : Associated p q :=
  p_prime.Irreducible.associated_of_dvd q_prime.Irreducible dvd
#align prime.associated_of_dvd Prime.associated_of_dvd
-/

#print Prime.dvd_prime_iff_associated /-
theorem Prime.dvd_prime_iff_associated [CancelCommMonoidWithZero α] {p q : α} (pp : Prime p)
    (qp : Prime q) : p ∣ q ↔ Associated p q :=
  pp.Irreducible.dvd_irreducible_iff_associated qp.Irreducible
#align prime.dvd_prime_iff_associated Prime.dvd_prime_iff_associated
-/

#print Associated.prime_iff /-
theorem Associated.prime_iff [CommMonoidWithZero α] {p q : α} (h : p ~ᵤ q) : Prime p ↔ Prime q :=
  ⟨h.Prime, h.symm.Prime⟩
#align associated.prime_iff Associated.prime_iff
-/

#print Associated.isUnit /-
protected theorem Associated.isUnit [Monoid α] {a b : α} (h : a ~ᵤ b) : IsUnit a → IsUnit b :=
  let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, hu.symm]⟩
#align associated.is_unit Associated.isUnit
-/

#print Associated.isUnit_iff /-
theorem Associated.isUnit_iff [Monoid α] {a b : α} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b :=
  ⟨h.IsUnit, h.symm.IsUnit⟩
#align associated.is_unit_iff Associated.isUnit_iff
-/

#print Associated.irreducible /-
protected theorem Associated.irreducible [Monoid α] {p q : α} (h : p ~ᵤ q) (hp : Irreducible p) :
    Irreducible q :=
  ⟨mt h.symm.IsUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : αˣ)) :=
      calc
        p = p * u * (u⁻¹ : αˣ) := by simp
        _ = _ := by rw [hu] <;> simp [hab, mul_assoc]
        
    (hp.is_unit_or_is_unit hpab).elim Or.inl fun ⟨v, hv⟩ => Or.inr ⟨v * u, by simp [hv]⟩⟩
#align associated.irreducible Associated.irreducible
-/

#print Associated.irreducible_iff /-
protected theorem Associated.irreducible_iff [Monoid α] {p q : α} (h : p ~ᵤ q) :
    Irreducible p ↔ Irreducible q :=
  ⟨h.Irreducible, h.symm.Irreducible⟩
#align associated.irreducible_iff Associated.irreducible_iff
-/

/- warning: associated.of_mul_left -> Associated.of_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α} {b : α} {c : α} {d : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) c d)) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) a c) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) b d)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α} {b : α} {c : α} {d : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) c d)) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) a c) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) b d)
Case conversion may be inaccurate. Consider using '#align associated.of_mul_left Associated.of_mul_leftₓ'. -/
theorem Associated.of_mul_left [CancelCommMonoidWithZero α] {a b c d : α} (h : a * b ~ᵤ c * d)
    (h₁ : a ~ᵤ c) (ha : a ≠ 0) : b ~ᵤ d :=
  let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : αˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv, mul_assoc c (v : α) d, mul_left_comm c, ← hu]
        simp [hv.symm, mul_assoc, mul_comm, mul_left_comm])⟩
#align associated.of_mul_left Associated.of_mul_left

/- warning: associated.of_mul_right -> Associated.of_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α} {b : α} {c : α} {d : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) c d)) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) b d) -> (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : α} {b : α} {c : α} {d : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) c d)) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) b d) -> (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) a c)
Case conversion may be inaccurate. Consider using '#align associated.of_mul_right Associated.of_mul_rightₓ'. -/
theorem Associated.of_mul_right [CancelCommMonoidWithZero α] {a b c d : α} :
    a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c := by
  rw [mul_comm a, mul_comm c] <;> exact Associated.of_mul_left
#align associated.of_mul_right Associated.of_mul_right

#print Associated.of_pow_associated_of_prime /-
theorem Associated.of_pow_associated_of_prime [CancelCommMonoidWithZero α] {p₁ p₂ : α} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ :=
  by
  have : p₁ ∣ p₂ ^ k₂ := by
    rw [← h.dvd_iff_dvd_right]
    apply dvd_pow_self _ hk₁.ne'
  rw [← hp₁.dvd_prime_iff_associated hp₂]
  exact hp₁.dvd_of_dvd_pow this
#align associated.of_pow_associated_of_prime Associated.of_pow_associated_of_prime
-/

#print Associated.of_pow_associated_of_prime' /-
theorem Associated.of_pow_associated_of_prime' [CancelCommMonoidWithZero α] {p₁ p₂ : α} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₂ : 0 < k₂) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ :=
  (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm
#align associated.of_pow_associated_of_prime' Associated.of_pow_associated_of_prime'
-/

section UniqueUnits

variable [Monoid α] [Unique αˣ]

/- warning: units_eq_one -> units_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Unique.{succ u1} (Units.{u1} α _inst_1)] (u : Units.{u1} α _inst_1), Eq.{succ u1} (Units.{u1} α _inst_1) u (OfNat.ofNat.{u1} (Units.{u1} α _inst_1) 1 (OfNat.mk.{u1} (Units.{u1} α _inst_1) 1 (One.one.{u1} (Units.{u1} α _inst_1) (MulOneClass.toHasOne.{u1} (Units.{u1} α _inst_1) (Units.mulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Unique.{succ u1} (Units.{u1} α _inst_1)] (u : Units.{u1} α _inst_1), Eq.{succ u1} (Units.{u1} α _inst_1) u (OfNat.ofNat.{u1} (Units.{u1} α _inst_1) 1 (One.toOfNat1.{u1} (Units.{u1} α _inst_1) (InvOneClass.toOne.{u1} (Units.{u1} α _inst_1) (DivInvOneMonoid.toInvOneClass.{u1} (Units.{u1} α _inst_1) (DivisionMonoid.toDivInvOneMonoid.{u1} (Units.{u1} α _inst_1) (Group.toDivisionMonoid.{u1} (Units.{u1} α _inst_1) (Units.instGroupUnits.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align units_eq_one units_eq_oneₓ'. -/
theorem units_eq_one (u : αˣ) : u = 1 :=
  Subsingleton.elim u 1
#align units_eq_one units_eq_one

#print associated_iff_eq /-
theorem associated_iff_eq {x y : α} : x ~ᵤ y ↔ x = y :=
  by
  constructor
  · rintro ⟨c, rfl⟩
    rw [units_eq_one c, Units.val_one, mul_one]
  · rintro rfl
    rfl
#align associated_iff_eq associated_iff_eq
-/

#print associated_eq_eq /-
theorem associated_eq_eq : (Associated : α → α → Prop) = Eq :=
  by
  ext
  rw [associated_iff_eq]
#align associated_eq_eq associated_eq_eq
-/

#print prime_dvd_prime_iff_eq /-
theorem prime_dvd_prime_iff_eq {M : Type _} [CancelCommMonoidWithZero M] [Unique Mˣ] {p q : M}
    (pp : Prime p) (qp : Prime q) : p ∣ q ↔ p = q := by
  rw [pp.dvd_prime_iff_associated qp, ← associated_eq_eq]
#align prime_dvd_prime_iff_eq prime_dvd_prime_iff_eq
-/

end UniqueUnits

section UniqueUnits₀

variable {R : Type _} [CancelCommMonoidWithZero R] [Unique Rˣ] {p₁ p₂ : R} {k₁ k₂ : ℕ}

#print eq_of_prime_pow_eq /-
theorem eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ :=
  by
  rw [← associated_iff_eq] at h⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁
#align eq_of_prime_pow_eq eq_of_prime_pow_eq
-/

#print eq_of_prime_pow_eq' /-
theorem eq_of_prime_pow_eq' (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₂)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ :=
  by
  rw [← associated_iff_eq] at h⊢
  apply h.of_pow_associated_of_prime' hp₁ hp₂ hk₁
#align eq_of_prime_pow_eq' eq_of_prime_pow_eq'
-/

end UniqueUnits₀

#print Associates /-
/-- The quotient of a monoid by the `associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `associates α`. -/
def Associates (α : Type _) [Monoid α] : Type _ :=
  Quotient (Associated.setoid α)
#align associates Associates
-/

namespace Associates

open Associated

#print Associates.mk /-
/-- The canonical quotient map from a monoid `α` into the `associates` of `α` -/
protected def mk {α : Type _} [Monoid α] (a : α) : Associates α :=
  ⟦a⟧
#align associates.mk Associates.mk
-/

instance [Monoid α] : Inhabited (Associates α) :=
  ⟨⟦1⟧⟩

#print Associates.mk_eq_mk_iff_associated /-
theorem mk_eq_mk_iff_associated [Monoid α] {a b : α} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b :=
  Iff.intro Quotient.exact Quot.sound
#align associates.mk_eq_mk_iff_associated Associates.mk_eq_mk_iff_associated
-/

#print Associates.quotient_mk_eq_mk /-
theorem quotient_mk_eq_mk [Monoid α] (a : α) : ⟦a⟧ = Associates.mk a :=
  rfl
#align associates.quotient_mk_eq_mk Associates.quotient_mk_eq_mk
-/

#print Associates.quot_mk_eq_mk /-
theorem quot_mk_eq_mk [Monoid α] (a : α) : Quot.mk Setoid.r a = Associates.mk a :=
  rfl
#align associates.quot_mk_eq_mk Associates.quot_mk_eq_mk
-/

#print Associates.forall_associated /-
theorem forall_associated [Monoid α] {p : Associates α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (Associates.mk a) :=
  Iff.intro (fun h a => h _) fun h a => Quotient.inductionOn a h
#align associates.forall_associated Associates.forall_associated
-/

#print Associates.mk_surjective /-
theorem mk_surjective [Monoid α] : Function.Surjective (@Associates.mk α _) :=
  forall_associated.2 fun a => ⟨a, rfl⟩
#align associates.mk_surjective Associates.mk_surjective
-/

instance [Monoid α] : One (Associates α) :=
  ⟨⟦1⟧⟩

/- warning: associates.mk_one -> Associates.mk_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Associates.{u1} α _inst_1) (Associates.mk.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} (Associates.{u1} α _inst_1) 1 (OfNat.mk.{u1} (Associates.{u1} α _inst_1) 1 (One.one.{u1} (Associates.{u1} α _inst_1) (Associates.hasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Associates.{u1} α _inst_1) (Associates.mk.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (Associates.{u1} α _inst_1) 1 (One.toOfNat1.{u1} (Associates.{u1} α _inst_1) (Associates.instOneAssociates.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align associates.mk_one Associates.mk_oneₓ'. -/
@[simp]
theorem mk_one [Monoid α] : Associates.mk (1 : α) = 1 :=
  rfl
#align associates.mk_one Associates.mk_one

/- warning: associates.one_eq_mk_one -> Associates.one_eq_mk_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Associates.{u1} α _inst_1) (OfNat.ofNat.{u1} (Associates.{u1} α _inst_1) 1 (OfNat.mk.{u1} (Associates.{u1} α _inst_1) 1 (One.one.{u1} (Associates.{u1} α _inst_1) (Associates.hasOne.{u1} α _inst_1)))) (Associates.mk.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Associates.{u1} α _inst_1) (OfNat.ofNat.{u1} (Associates.{u1} α _inst_1) 1 (One.toOfNat1.{u1} (Associates.{u1} α _inst_1) (Associates.instOneAssociates.{u1} α _inst_1))) (Associates.mk.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align associates.one_eq_mk_one Associates.one_eq_mk_oneₓ'. -/
theorem one_eq_mk_one [Monoid α] : (1 : Associates α) = Associates.mk 1 :=
  rfl
#align associates.one_eq_mk_one Associates.one_eq_mk_one

instance [Monoid α] : Bot (Associates α) :=
  ⟨1⟩

/- warning: associates.bot_eq_one -> Associates.bot_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Associates.{u1} α _inst_1) (Bot.bot.{u1} (Associates.{u1} α _inst_1) (Associates.hasBot.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Associates.{u1} α _inst_1) 1 (OfNat.mk.{u1} (Associates.{u1} α _inst_1) 1 (One.one.{u1} (Associates.{u1} α _inst_1) (Associates.hasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Associates.{u1} α _inst_1) (Bot.bot.{u1} (Associates.{u1} α _inst_1) (Associates.instBotAssociates.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Associates.{u1} α _inst_1) 1 (One.toOfNat1.{u1} (Associates.{u1} α _inst_1) (Associates.instOneAssociates.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align associates.bot_eq_one Associates.bot_eq_oneₓ'. -/
theorem bot_eq_one [Monoid α] : (⊥ : Associates α) = 1 :=
  rfl
#align associates.bot_eq_one Associates.bot_eq_one

#print Associates.exists_rep /-
theorem exists_rep [Monoid α] (a : Associates α) : ∃ a0 : α, Associates.mk a0 = a :=
  Quot.exists_rep a
#align associates.exists_rep Associates.exists_rep
-/

instance [Monoid α] [Subsingleton α] : Unique (Associates α)
    where
  default := 1
  uniq a := by
    apply Quotient.recOnSubsingleton₂
    intro a b
    congr

#print Associates.mk_injective /-
theorem mk_injective [Monoid α] [Unique (Units α)] : Function.Injective (@Associates.mk α _) :=
  fun a b h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)
#align associates.mk_injective Associates.mk_injective
-/

section CommMonoid

variable [CommMonoid α]

instance : Mul (Associates α) :=
  ⟨fun a' b' =>
    Quotient.liftOn₂ a' b' (fun a b => ⟦a * b⟧) fun a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ =>
      Quotient.sound <| ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩⟩

/- warning: associates.mk_mul_mk -> Associates.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {x : α} {y : α}, Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasMul.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) x) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) y)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {x : α} {y : α}, Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instMulAssociatesToMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) x) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) y)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y))
Case conversion may be inaccurate. Consider using '#align associates.mk_mul_mk Associates.mk_mul_mkₓ'. -/
theorem mk_mul_mk {x y : α} : Associates.mk x * Associates.mk y = Associates.mk (x * y) :=
  rfl
#align associates.mk_mul_mk Associates.mk_mul_mk

instance : CommMonoid (Associates α) where
  one := 1
  mul := (· * ·)
  mul_one a' := Quotient.inductionOn a' fun a => show ⟦a * 1⟧ = ⟦a⟧ by simp
  one_mul a' := Quotient.inductionOn a' fun a => show ⟦1 * a⟧ = ⟦a⟧ by simp
  mul_assoc a' b' c' :=
    Quotient.induction_on₃ a' b' c' fun a b c => show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by rw [mul_assoc]
  mul_comm a' b' := Quotient.induction_on₂ a' b' fun a b => show ⟦a * b⟧ = ⟦b * a⟧ by rw [mul_comm]

instance : Preorder (Associates α) where
  le := Dvd.Dvd
  le_refl := dvd_refl
  le_trans a b c := dvd_trans

/- warning: associates.mk_monoid_hom -> Associates.mkMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align associates.mk_monoid_hom Associates.mkMonoidHomₓ'. -/
/-- `associates.mk` as a `monoid_hom`. -/
protected def mkMonoidHom : α →* Associates α :=
  ⟨Associates.mk, mk_one, fun x y => mk_mul_mk⟩
#align associates.mk_monoid_hom Associates.mkMonoidHom

/- warning: associates.mk_monoid_hom_apply -> Associates.mkMonoidHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α), Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))) (fun (_x : MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))) => α -> (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MonoidHom.hasCoeToFun.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))) (Associates.mkMonoidHom.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (MonoidHom.monoidHomClass.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))))) (Associates.mkMonoidHom.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align associates.mk_monoid_hom_apply Associates.mkMonoidHom_applyₓ'. -/
@[simp]
theorem mkMonoidHom_apply (a : α) : Associates.mkMonoidHom a = Associates.mk a :=
  rfl
#align associates.mk_monoid_hom_apply Associates.mkMonoidHom_apply

/- warning: associates.associated_map_mk -> Associates.associated_map_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {f : MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))}, (Function.RightInverse.{succ u1, succ u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (fun (_x : MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) => (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) -> α) (MonoidHom.hasCoeToFun.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) f) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) -> (forall (a : α), Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (fun (_x : MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) => (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) -> α) (MonoidHom.hasCoeToFun.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) f (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {f : MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))}, (Function.RightInverse.{succ u1, succ u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (fun (_x : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (MulOneClass.toMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (MonoidHom.monoidHomClass.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) f) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) -> (forall (a : α), Associated.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (fun (_x : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) => α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (MulOneClass.toMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (MonoidHom.monoidHomClass.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Monoid.toMulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) f (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)))
Case conversion may be inaccurate. Consider using '#align associates.associated_map_mk Associates.associated_map_mkₓ'. -/
theorem associated_map_mk {f : Associates α →* α} (hinv : Function.RightInverse f Associates.mk)
    (a : α) : a ~ᵤ f (Associates.mk a) :=
  Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm
#align associates.associated_map_mk Associates.associated_map_mk

/- warning: associates.mk_pow -> Associates.mk_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (n : Nat), Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a n)) (HPow.hPow.{u1, 0, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) Nat (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHPow.{u1, 0} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) Nat (Monoid.Pow.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (n : Nat), Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a n)) (HPow.hPow.{u1, 0, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) Nat (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHPow.{u1, 0} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) Nat (Monoid.Pow.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) n)
Case conversion may be inaccurate. Consider using '#align associates.mk_pow Associates.mk_powₓ'. -/
theorem mk_pow (a : α) (n : ℕ) : Associates.mk (a ^ n) = Associates.mk a ^ n := by
  induction n <;> simp [*, pow_succ, associates.mk_mul_mk.symm]
#align associates.mk_pow Associates.mk_pow

/- warning: associates.dvd_eq_le -> Associates.dvd_eq_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], Eq.{succ u1} ((Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) -> (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) -> Prop) (Dvd.Dvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (semigroupDvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toSemigroup.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))))) (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], Eq.{succ u1} ((Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) -> (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) -> Prop) (fun (x._@.Mathlib.Algebra.Associated._hyg.9340 : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (x._@.Mathlib.Algebra.Associated._hyg.9342 : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) => Dvd.dvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (semigroupDvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toSemigroup.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Associated._hyg.9340 x._@.Mathlib.Algebra.Associated._hyg.9342) (fun (x._@.Mathlib.Algebra.Associated._hyg.9355 : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (x._@.Mathlib.Algebra.Associated._hyg.9357 : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) => LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) x._@.Mathlib.Algebra.Associated._hyg.9355 x._@.Mathlib.Algebra.Associated._hyg.9357)
Case conversion may be inaccurate. Consider using '#align associates.dvd_eq_le Associates.dvd_eq_leₓ'. -/
theorem dvd_eq_le : ((· ∣ ·) : Associates α → Associates α → Prop) = (· ≤ ·) :=
  rfl
#align associates.dvd_eq_le Associates.dvd_eq_le

/- warning: associates.mul_eq_one_iff -> Associates.mul_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {x : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {y : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasMul.{u1} α _inst_1)) x y) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) (And (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) x (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) y (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {x : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {y : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instMulAssociatesToMonoid.{u1} α _inst_1)) x y) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (And (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) x (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) y (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align associates.mul_eq_one_iff Associates.mul_eq_one_iffₓ'. -/
theorem mul_eq_one_iff {x y : Associates α} : x * y = 1 ↔ x = 1 ∧ y = 1 :=
  Iff.intro
    (Quotient.induction_on₂ x y fun a b h =>
      have : a * b ~ᵤ 1 := Quotient.exact h
      ⟨Quotient.sound <| associated_one_of_associated_mul_one this,
        Quotient.sound <| associated_one_of_associated_mul_one <| by rwa [mul_comm] at this⟩)
    (by simp (config := { contextual := true }))
#align associates.mul_eq_one_iff Associates.mul_eq_one_iff

/- warning: associates.units_eq_one -> Associates.units_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (u : Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))), Eq.{succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) u (OfNat.ofNat.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) 1 (OfNat.mk.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) 1 (One.one.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Units.mulOneClass.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (u : Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))), Eq.{succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) u (OfNat.ofNat.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) 1 (One.toOfNat1.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (InvOneClass.toOne.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (DivInvOneMonoid.toInvOneClass.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (DivisionMonoid.toDivInvOneMonoid.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (DivisionCommMonoid.toDivisionMonoid.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (CommGroup.toDivisionCommMonoid.{u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))) (Units.instCommGroupUnitsToMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align associates.units_eq_one Associates.units_eq_oneₓ'. -/
theorem units_eq_one (u : (Associates α)ˣ) : u = 1 :=
  Units.ext (mul_eq_one_iff.1 u.val_inv).1
#align associates.units_eq_one Associates.units_eq_one

/- warning: associates.unique_units -> Associates.uniqueUnits is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], Unique.{succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], Unique.{succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align associates.unique_units Associates.uniqueUnitsₓ'. -/
instance uniqueUnits : Unique (Associates α)ˣ
    where
  default := 1
  uniq := Associates.units_eq_one
#align associates.unique_units Associates.uniqueUnits

/- warning: associates.coe_unit_eq_one -> Associates.coe_unit_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (u : Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))), Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (coeBase.{succ u1, succ u1} (Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1))) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Units.hasCoe.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))))) u) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (u : Units.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1))), Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Units.val.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)) u) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align associates.coe_unit_eq_one Associates.coe_unit_eq_oneₓ'. -/
theorem coe_unit_eq_one (u : (Associates α)ˣ) : (u : Associates α) = 1 := by simp
#align associates.coe_unit_eq_one Associates.coe_unit_eq_one

/- warning: associates.is_unit_iff_eq_one -> Associates.isUnit_iff_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)), Iff (IsUnit.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)) a) (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)), Iff (IsUnit.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)) a) (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align associates.is_unit_iff_eq_one Associates.isUnit_iff_eq_oneₓ'. -/
theorem isUnit_iff_eq_one (a : Associates α) : IsUnit a ↔ a = 1 :=
  Iff.intro (fun ⟨u, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ isUnit_one
#align associates.is_unit_iff_eq_one Associates.isUnit_iff_eq_one

/- warning: associates.is_unit_iff_eq_bot -> Associates.isUnit_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (IsUnit.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)) a) (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a (Bot.bot.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasBot.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (IsUnit.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)) a) (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a (Bot.bot.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instBotAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align associates.is_unit_iff_eq_bot Associates.isUnit_iff_eq_botₓ'. -/
theorem isUnit_iff_eq_bot {a : Associates α} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.isUnit_iff_eq_one, bot_eq_one]
#align associates.is_unit_iff_eq_bot Associates.isUnit_iff_eq_bot

/- warning: associates.is_unit_mk -> Associates.isUnit_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, Iff (IsUnit.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)) (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, Iff (IsUnit.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)) (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align associates.is_unit_mk Associates.isUnit_mkₓ'. -/
theorem isUnit_mk {a : α} : IsUnit (Associates.mk a) ↔ IsUnit a :=
  calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [is_unit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_isUnit
    
#align associates.is_unit_mk Associates.isUnit_mk

section Order

/- warning: associates.mul_mono -> Associates.mul_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {b : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {c : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {d : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) a b) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) c d) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasMul.{u1} α _inst_1)) a c) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasMul.{u1} α _inst_1)) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {b : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {c : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {d : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) a b) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) c d) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instMulAssociatesToMonoid.{u1} α _inst_1)) a c) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instMulAssociatesToMonoid.{u1} α _inst_1)) b d))
Case conversion may be inaccurate. Consider using '#align associates.mul_mono Associates.mul_monoₓ'. -/
theorem mul_mono {a b c d : Associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by simp [hx, hy, mul_comm, mul_assoc, mul_left_comm]⟩
#align associates.mul_mono Associates.mul_mono

/- warning: associates.one_le -> Associates.one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a
Case conversion may be inaccurate. Consider using '#align associates.one_le Associates.one_leₓ'. -/
theorem one_le {a : Associates α} : 1 ≤ a :=
  Dvd.intro _ (one_mul a)
#align associates.one_le Associates.one_le

/- warning: associates.le_mul_right -> Associates.le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {b : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasMul.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {b : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instMulAssociatesToMonoid.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align associates.le_mul_right Associates.le_mul_rightₓ'. -/
theorem le_mul_right {a b : Associates α} : a ≤ a * b :=
  ⟨b, rfl⟩
#align associates.le_mul_right Associates.le_mul_right

/- warning: associates.le_mul_left -> Associates.le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {b : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasMul.{u1} α _inst_1)) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)} {b : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (instHMul.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instMulAssociatesToMonoid.{u1} α _inst_1)) b a)
Case conversion may be inaccurate. Consider using '#align associates.le_mul_left Associates.le_mul_leftₓ'. -/
theorem le_mul_left {a b : Associates α} : a ≤ b * a := by rw [mul_comm] <;> exact le_mul_right
#align associates.le_mul_left Associates.le_mul_left

instance : OrderBot (Associates α) where
  bot := 1
  bot_le a := one_le

end Order

/- warning: associates.dvd_of_mk_le_mk -> Associates.dvd_of_mk_le_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align associates.dvd_of_mk_le_mk Associates.dvd_of_mk_le_mkₓ'. -/
theorem dvd_of_mk_le_mk {a b : α} : Associates.mk a ≤ Associates.mk b → a ∣ b
  | ⟨c', hc'⟩ =>
    (Quotient.inductionOn c' fun c hc =>
        let ⟨d, hd⟩ := (Quotient.exact hc).symm
        ⟨↑d * c,
          calc
            b = a * c * ↑d := hd.symm
            _ = a * (↑d * c) := by ac_rfl
            ⟩)
      hc'
#align associates.dvd_of_mk_le_mk Associates.dvd_of_mk_le_mk

/- warning: associates.mk_le_mk_of_dvd -> Associates.mk_le_mk_of_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align associates.mk_le_mk_of_dvd Associates.mk_le_mk_of_dvdₓ'. -/
theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → Associates.mk a ≤ Associates.mk b := fun ⟨c, hc⟩ =>
  ⟨Associates.mk c, by simp [hc] <;> rfl⟩
#align associates.mk_le_mk_of_dvd Associates.mk_le_mk_of_dvd

/- warning: associates.mk_le_mk_iff_dvd_iff -> Associates.mk_le_mk_iff_dvd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align associates.mk_le_mk_iff_dvd_iff Associates.mk_le_mk_iff_dvd_iffₓ'. -/
theorem mk_le_mk_iff_dvd_iff {a b : α} : Associates.mk a ≤ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd
#align associates.mk_le_mk_iff_dvd_iff Associates.mk_le_mk_iff_dvd_iff

/- warning: associates.mk_dvd_mk -> Associates.mk_dvd_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, Iff (Dvd.Dvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (semigroupDvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toSemigroup.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1)))) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α}, Iff (Dvd.dvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (semigroupDvd.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toSemigroup.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (CommMonoid.toMonoid.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1)))) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) b)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align associates.mk_dvd_mk Associates.mk_dvd_mkₓ'. -/
theorem mk_dvd_mk {a b : α} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd
#align associates.mk_dvd_mk Associates.mk_dvd_mk

end CommMonoid

instance [Zero α] [Monoid α] : Zero (Associates α) :=
  ⟨⟦0⟧⟩

instance [Zero α] [Monoid α] : Top (Associates α) :=
  ⟨0⟩

section MonoidWithZero

variable [MonoidWithZero α]

/- warning: associates.mk_eq_zero -> Associates.mk_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α}, Iff (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a) (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (Zero.zero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.hasZero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} α _inst_1)))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α}, Iff (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a) (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (Zero.toOfNat0.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.instZeroAssociates.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1) (MonoidWithZero.toMonoid.{u1} α _inst_1))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align associates.mk_eq_zero Associates.mk_eq_zeroₓ'. -/
@[simp]
theorem mk_eq_zero {a : α} : Associates.mk a = 0 ↔ a = 0 :=
  ⟨fun h => (associated_zero_iff_eq_zero a).1 <| Quotient.exact h, fun h => h.symm ▸ rfl⟩
#align associates.mk_eq_zero Associates.mk_eq_zero

/- warning: associates.mk_ne_zero -> Associates.mk_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α}, Iff (Ne.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a) (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (Zero.zero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.hasZero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} α _inst_1)))))) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α}, Iff (Ne.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a) (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (Zero.toOfNat0.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.instZeroAssociates.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1) (MonoidWithZero.toMonoid.{u1} α _inst_1))))) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align associates.mk_ne_zero Associates.mk_ne_zeroₓ'. -/
theorem mk_ne_zero {a : α} : Associates.mk a ≠ 0 ↔ a ≠ 0 :=
  not_congr mk_eq_zero
#align associates.mk_ne_zero Associates.mk_ne_zero

instance [Nontrivial α] : Nontrivial (Associates α) :=
  ⟨⟨0, 1, fun h =>
      have : (0 : α) ~ᵤ 1 := Quotient.exact h
      have : (0 : α) = 1 := ((associated_zero_iff_eq_zero 1).1 this.symm).symm
      zero_ne_one this⟩⟩

/- warning: associates.exists_non_zero_rep -> Associates.exists_non_zero_rep is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)}, (Ne.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (Zero.zero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.hasZero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} α _inst_1)))))) -> (Exists.{succ u1} α (fun (a0 : α) => And (Ne.{succ u1} α a0 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a0) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)}, (Ne.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) 0 (Zero.toOfNat0.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.instZeroAssociates.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1) (MonoidWithZero.toMonoid.{u1} α _inst_1))))) -> (Exists.{succ u1} α (fun (a0 : α) => And (Ne.{succ u1} α a0 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a0) a)))
Case conversion may be inaccurate. Consider using '#align associates.exists_non_zero_rep Associates.exists_non_zero_repₓ'. -/
theorem exists_non_zero_rep {a : Associates α} : a ≠ 0 → ∃ a0 : α, a0 ≠ 0 ∧ Associates.mk a0 = a :=
  Quotient.inductionOn a fun b nz => ⟨b, mt (congr_arg Quotient.mk') nz, rfl⟩
#align associates.exists_non_zero_rep Associates.exists_non_zero_rep

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero α]

instance : CommMonoidWithZero (Associates α) :=
  { Associates.commMonoid,
    Associates.hasZero with
    zero_mul := by
      rintro ⟨a⟩
      show Associates.mk (0 * a) = Associates.mk 0
      rw [zero_mul]
    mul_zero := by
      rintro ⟨a⟩
      show Associates.mk (a * 0) = Associates.mk 0
      rw [mul_zero] }

instance : OrderTop (Associates α) where
  top := 0
  le_top a := ⟨0, (mul_zero a).symm⟩

instance : BoundedOrder (Associates α) :=
  { Associates.orderTop, Associates.orderBot with }

instance [DecidableRel ((· ∣ ·) : α → α → Prop)] :
    DecidableRel ((· ∣ ·) : Associates α → Associates α → Prop) := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun a b => decidable_of_iff' _ mk_dvd_mk

/- warning: associates.prime.le_or_le -> Associates.Prime.le_or_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))}, (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1) p) -> (forall {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))} {b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))}, (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (instHMul.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.hasMul.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) a b)) -> (Or (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) p a) (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) p b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))}, (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1) p) -> (forall {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))} {b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))}, (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (instHMul.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instMulAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) a b)) -> (Or (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) p a) (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) p b)))
Case conversion may be inaccurate. Consider using '#align associates.prime.le_or_le Associates.Prime.le_or_leₓ'. -/
theorem Prime.le_or_le {p : Associates α} (hp : Prime p) {a b : Associates α} (h : p ≤ a * b) :
    p ≤ a ∨ p ≤ b :=
  hp.2.2 a b h
#align associates.prime.le_or_le Associates.Prime.le_or_le

/- warning: associates.prime_mk -> Associates.prime_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] (p : α), Iff (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) p)) (Prime.{u1} α _inst_1 p)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] (p : α), Iff (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) p)) (Prime.{u1} α _inst_1 p)
Case conversion may be inaccurate. Consider using '#align associates.prime_mk Associates.prime_mkₓ'. -/
theorem prime_mk (p : α) : Prime (Associates.mk p) ↔ Prime p :=
  by
  rw [Prime, _root_.prime, forall_associated]
  trans
  · apply and_congr
    rfl
    apply and_congr
    rfl
    apply forall_congr'
    intro a
    exact forall_associated
  apply and_congr mk_ne_zero
  apply and_congr
  · rw [is_unit_mk]
  refine' forall₂_congr fun a b => _
  rw [mk_mul_mk, mk_dvd_mk, mk_dvd_mk, mk_dvd_mk]
#align associates.prime_mk Associates.prime_mk

/- warning: associates.irreducible_mk -> Associates.irreducible_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] (a : α), Iff (Irreducible.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1))) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a)) (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] (a : α), Iff (Irreducible.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1))) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a)) (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align associates.irreducible_mk Associates.irreducible_mkₓ'. -/
theorem irreducible_mk (a : α) : Irreducible (Associates.mk a) ↔ Irreducible a :=
  by
  simp only [irreducible_iff, is_unit_mk]
  apply and_congr Iff.rfl
  constructor
  · rintro h x y rfl
    simpa [is_unit_mk] using h (Associates.mk x) (Associates.mk y) rfl
  · intro h x y
    refine' Quotient.induction_on₂ x y fun x y a_eq => _
    rcases Quotient.exact a_eq.symm with ⟨u, a_eq⟩
    rw [mul_assoc] at a_eq
    show IsUnit (Associates.mk x) ∨ IsUnit (Associates.mk y)
    simpa [is_unit_mk] using h _ _ a_eq.symm
#align associates.irreducible_mk Associates.irreducible_mk

/- warning: associates.mk_dvd_not_unit_mk_iff -> Associates.mk_dvdNotUnit_mk_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {a : α} {b : α}, Iff (DvdNotUnit.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) b)) (DvdNotUnit.{u1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {a : α} {b : α}, Iff (DvdNotUnit.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) b)) (DvdNotUnit.{u1} α _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align associates.mk_dvd_not_unit_mk_iff Associates.mk_dvdNotUnit_mk_iffₓ'. -/
theorem mk_dvdNotUnit_mk_iff {a b : α} :
    DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b :=
  by
  rw [DvdNotUnit, DvdNotUnit, mk_ne_zero]
  apply and_congr_right; intro ane0
  constructor
  · contrapose!
    rw [forall_associated]
    intro h x hx hbax
    rw [mk_mul_mk, mk_eq_mk_iff_associated] at hbax
    cases' hbax with u hu
    apply h (x * ↑u⁻¹)
    · rw [is_unit_mk] at hx
      rw [Associated.isUnit_iff]
      apply hx
      use u
      simp
    simp [← mul_assoc, ← hu]
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use Associates.mk x
    simp [is_unit_mk, mk_mul_mk, hx]
#align associates.mk_dvd_not_unit_mk_iff Associates.mk_dvdNotUnit_mk_iff

/- warning: associates.dvd_not_unit_of_lt -> Associates.dvdNotUnit_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))} {b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))}, (LT.lt.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLT.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) a b) -> (DvdNotUnit.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))} {b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))}, (LT.lt.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Preorder.toLT.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1))) a b) -> (DvdNotUnit.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align associates.dvd_not_unit_of_lt Associates.dvdNotUnit_of_ltₓ'. -/
theorem dvdNotUnit_of_lt {a b : Associates α} (hlt : a < b) : DvdNotUnit a b :=
  by
  constructor;
  · rintro rfl
    apply not_lt_of_le _ hlt
    apply dvd_zero
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine' ⟨x, _, rfl⟩
  contrapose! ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp
#align associates.dvd_not_unit_of_lt Associates.dvdNotUnit_of_lt

/- warning: associates.irreducible_iff_prime_iff -> Associates.irreducible_iff_prime_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], Iff (forall (a : α), Iff (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a) (Prime.{u1} α _inst_1 a)) (forall (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))), Iff (Irreducible.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1))) a) (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α], Iff (forall (a : α), Iff (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a) (Prime.{u1} α _inst_1 a)) (forall (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))), Iff (Irreducible.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1))) a) (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align associates.irreducible_iff_prime_iff Associates.irreducible_iff_prime_iffₓ'. -/
theorem irreducible_iff_prime_iff :
    (∀ a : α, Irreducible a ↔ Prime a) ↔ ∀ a : Associates α, Irreducible a ↔ Prime a := by
  simp_rw [forall_associated, irreducible_mk, prime_mk]
#align associates.irreducible_iff_prime_iff Associates.irreducible_iff_prime_iff

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

instance : PartialOrder (Associates α) :=
  { Associates.preorder with
    le_antisymm := fun a' b' =>
      Quotient.induction_on₂ a' b' fun a b hab hba =>
        Quot.sound <| associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba) }

instance : OrderedCommMonoid (Associates α) :=
  { Associates.commMonoid, Associates.partialOrder with
    mul_le_mul_left := fun a b ⟨d, hd⟩ c => hd.symm ▸ mul_assoc c a d ▸ le_mul_right }

instance : NoZeroDivisors (Associates α) :=
  ⟨fun x y =>
    Quotient.induction_on₂ x y fun a b h =>
      have : a * b = 0 := (associated_zero_iff_eq_zero _).1 (Quotient.exact h)
      have : a = 0 ∨ b = 0 := mul_eq_zero.1 this
      this.imp (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl⟩

instance : CancelCommMonoidWithZero (Associates α) :=
  { (inferInstance : CommMonoidWithZero (Associates α)) with
    mul_left_cancel_of_ne_zero := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h
      rcases Quotient.exact' h with ⟨u, hu⟩
      rw [mul_assoc] at hu
      exact Quotient.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩ }

/- warning: associates.le_of_mul_le_mul_left -> Associates.le_of_mul_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (c : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))), (Ne.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 0 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 0 (Zero.zero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.hasZero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (instHMul.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.hasMul.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (instHMul.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.hasMul.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a c)) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (c : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))), (Ne.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 0 (Zero.toOfNat0.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instZeroAssociates.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (instHMul.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instMulAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (instHMul.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instMulAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a c)) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) b c)
Case conversion may be inaccurate. Consider using '#align associates.le_of_mul_le_mul_left Associates.le_of_mul_le_mul_leftₓ'. -/
theorem le_of_mul_le_mul_left (a b c : Associates α) (ha : a ≠ 0) : a * b ≤ a * c → b ≤ c
  | ⟨d, hd⟩ => ⟨d, mul_left_cancel₀ ha <| by rwa [← mul_assoc]⟩
#align associates.le_of_mul_le_mul_left Associates.le_of_mul_le_mul_left

/- warning: associates.one_or_eq_of_le_of_prime -> Associates.one_or_eq_of_le_of_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] (p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (m : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))), (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.commMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) p) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) m p) -> (Or (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) m (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (One.one.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.hasOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))) (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) m p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] (p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (m : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))), (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) p) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) m p) -> (Or (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) m (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instOneAssociates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) m p))
Case conversion may be inaccurate. Consider using '#align associates.one_or_eq_of_le_of_prime Associates.one_or_eq_of_le_of_primeₓ'. -/
theorem one_or_eq_of_le_of_prime : ∀ p m : Associates α, Prime p → m ≤ p → m = 1 ∨ m = p
  | _, m, ⟨hp0, hp1, h⟩, ⟨d, rfl⟩ =>
    match h m d dvd_rfl with
    | Or.inl h =>
      by_cases (fun this : m = 0 => by simp [this]) fun this : m ≠ 0 =>
        by
        have : m * d ≤ m * 1 := by simpa using h
        have : d ≤ 1 := Associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this
        have : d = 1 := bot_unique this
        simp [this]
    | Or.inr h =>
      by_cases (fun this : d = 0 => by simp [this] at hp0 <;> contradiction) fun this : d ≠ 0 =>
        have : d * m ≤ d * 1 := by simpa [mul_comm] using h
        Or.inl <| bot_unique <| Associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this
#align associates.one_or_eq_of_le_of_prime Associates.one_or_eq_of_le_of_prime

instance : CanonicallyOrderedMonoid (Associates α) :=
  { Associates.cancelCommMonoidWithZero, Associates.boundedOrder,
    Associates.orderedCommMonoid with
    exists_mul_of_le := fun a b => id
    le_self_mul := fun a b => ⟨b, rfl⟩ }

/- warning: associates.dvd_not_unit_iff_lt -> Associates.dvdNotUnit_iff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))} {b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))}, Iff (DvdNotUnit.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.commMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) a b) (LT.lt.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLT.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))} {b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))}, Iff (DvdNotUnit.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) a b) (LT.lt.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLT.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align associates.dvd_not_unit_iff_lt Associates.dvdNotUnit_iff_ltₓ'. -/
theorem dvdNotUnit_iff_lt {a b : Associates α} : DvdNotUnit a b ↔ a < b :=
  dvd_and_not_dvd_iff.symm
#align associates.dvd_not_unit_iff_lt Associates.dvdNotUnit_iff_lt

/- warning: associates.le_one_iff -> Associates.le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))}, Iff (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (One.one.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.hasOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))) (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (One.one.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.hasOne.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))}, Iff (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instOneAssociates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))) (Eq.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p (OfNat.ofNat.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instOneAssociates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align associates.le_one_iff Associates.le_one_iffₓ'. -/
theorem le_one_iff {p : Associates α} : p ≤ 1 ↔ p = 1 := by rw [← Associates.bot_eq_one, le_bot_iff]
#align associates.le_one_iff Associates.le_one_iff

end CancelCommMonoidWithZero

end Associates

section CommMonoidWithZero

#print DvdNotUnit.isUnit_of_irreducible_right /-
theorem DvdNotUnit.isUnit_of_irreducible_right [CommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q)
    (hq : Irreducible q) : IsUnit p :=
  by
  obtain ⟨hp', x, hx, hx'⟩ := h
  exact Or.resolve_right ((irreducible_iff.1 hq).right p x hx') hx
#align dvd_not_unit.is_unit_of_irreducible_right DvdNotUnit.isUnit_of_irreducible_right
-/

#print not_irreducible_of_not_unit_dvdNotUnit /-
theorem not_irreducible_of_not_unit_dvdNotUnit [CommMonoidWithZero α] {p q : α} (hp : ¬IsUnit p)
    (h : DvdNotUnit p q) : ¬Irreducible q :=
  mt h.is_unit_of_irreducible_right hp
#align not_irreducible_of_not_unit_dvd_not_unit not_irreducible_of_not_unit_dvdNotUnit
-/

#print DvdNotUnit.not_unit /-
theorem DvdNotUnit.not_unit [CommMonoidWithZero α] {p q : α} (hp : DvdNotUnit p q) : ¬IsUnit q :=
  by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (is_unit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (is_unit_iff_dvd_one.mp hc)))
#align dvd_not_unit.not_unit DvdNotUnit.not_unit
-/

#print dvdNotUnit_of_dvdNotUnit_associated /-
theorem dvdNotUnit_of_dvdNotUnit_associated [CommMonoidWithZero α] [Nontrivial α] {p q r : α}
    (h : DvdNotUnit p q) (h' : Associated q r) : DvdNotUnit p r :=
  by
  obtain ⟨u, rfl⟩ := Associated.symm h'
  obtain ⟨hp, x, hx⟩ := h
  refine' ⟨hp, x * ↑u⁻¹, DvdNotUnit.not_unit ⟨u⁻¹.NeZero, x, hx.left, mul_comm _ _⟩, _⟩
  rw [← mul_assoc, ← hx.right, mul_assoc, Units.mul_inv, mul_one]
#align dvd_not_unit_of_dvd_not_unit_associated dvdNotUnit_of_dvdNotUnit_associated
-/

end CommMonoidWithZero

section CancelCommMonoidWithZero

/- warning: is_unit_of_associated_mul -> isUnit_of_associated_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {b : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) p b) p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {b : α}, (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) p b) p) -> (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align is_unit_of_associated_mul isUnit_of_associated_mulₓ'. -/
theorem isUnit_of_associated_mul [CancelCommMonoidWithZero α] {p b : α} (h : Associated (p * b) p)
    (hp : p ≠ 0) : IsUnit b := by
  cases' h with a ha
  refine' isUnit_of_mul_eq_one b a ((mul_right_inj' hp).mp _)
  rwa [← mul_assoc, mul_one]
#align is_unit_of_associated_mul isUnit_of_associated_mul

#print DvdNotUnit.not_associated /-
theorem DvdNotUnit.not_associated [CancelCommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q) :
    ¬Associated p q := by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases(mul_right_inj' hp).mp hx' with rfl
  exact hx a.is_unit
#align dvd_not_unit.not_associated DvdNotUnit.not_associated
-/

#print DvdNotUnit.ne /-
theorem DvdNotUnit.ne [CancelCommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q) : p ≠ q :=
  by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  conv_lhs at hx'' => rw [← hcontra, ← mul_one p]
  rw [(mul_left_cancel₀ hp hx'').symm] at hx'
  exact hx' isUnit_one
#align dvd_not_unit.ne DvdNotUnit.ne
-/

/- warning: pow_injective_of_not_unit -> pow_injective_of_not_unit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {q : α}, (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) q)) -> (Ne.{succ u1} α q (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Function.Injective.{1, succ u1} Nat α (fun (n : Nat) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) q n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {q : α}, (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) q)) -> (Ne.{succ u1} α q (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Function.Injective.{1, succ u1} Nat α (fun (n : Nat) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) q n))
Case conversion may be inaccurate. Consider using '#align pow_injective_of_not_unit pow_injective_of_not_unitₓ'. -/
theorem pow_injective_of_not_unit [CancelCommMonoidWithZero α] {q : α} (hq : ¬IsUnit q)
    (hq' : q ≠ 0) : Function.Injective fun n : ℕ => q ^ n :=
  by
  refine' injective_of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), _, _⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm
#align pow_injective_of_not_unit pow_injective_of_not_unit

/- warning: dvd_prime_pow -> dvd_prime_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {q : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) q (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n)) (Exists.{1} Nat (fun (i : Nat) => Exists.{0} (LE.le.{0} Nat Nat.hasLe i n) (fun (H : LE.le.{0} Nat Nat.hasLe i n) => Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) q (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p i)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {q : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) q (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n)) (Exists.{1} Nat (fun (i : Nat) => And (LE.le.{0} Nat instLENat i n) (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) q (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p i)))))
Case conversion may be inaccurate. Consider using '#align dvd_prime_pow dvd_prime_powₓ'. -/
theorem dvd_prime_pow [CancelCommMonoidWithZero α] {p q : α} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n ↔ ∃ i ≤ n, Associated q (p ^ i) :=
  by
  induction' n with n ih generalizing q
  · simp [← isUnit_iff_dvd_one, associated_one_iff_isUnit]
  refine' ⟨fun h => _, fun ⟨i, hi, hq⟩ => hq.dvd.trans (pow_dvd_pow p hi)⟩
  rw [pow_succ] at h
  rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno)
  · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
    rcases h with ⟨i, hi, hq⟩
    refine' ⟨i + 1, Nat.succ_le_succ hi, (hq.mul_left p).trans _⟩
    rw [pow_succ]
  · obtain ⟨i, hi, hq⟩ := ih.mp hno
    exact ⟨i, hi.trans n.le_succ, hq⟩
#align dvd_prime_pow dvd_prime_pow

end CancelCommMonoidWithZero

assert_not_exists Multiset

