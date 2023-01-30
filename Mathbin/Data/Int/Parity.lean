/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Benjamin Davidson

! This file was ported from Lean 3 source module data.int.parity
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Parity

/-!
# Parity of integers

This file contains theorems about the `even` and `odd` predicates on the integers.

## Tags

even, odd
-/


namespace Int

variable {m n : ℤ}

#print Int.emod_two_ne_one /-
@[simp]
theorem emod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
#align int.mod_two_ne_one Int.emod_two_ne_one
-/

#print Int.emod_two_ne_zero /-
-- euclidean_domain.mod_eq_zero uses (2 ∣ n) as normal form
@[local simp]
theorem emod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' mod_two_eq_zero_or_one n with h h <;> simp [h]
#align int.mod_two_ne_zero Int.emod_two_ne_zero
-/

#print Int.even_iff /-
theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨fun ⟨m, hm⟩ => by simp [← two_mul, hm], fun h =>
    ⟨n / 2, (emod_add_ediv n 2).symm.trans (by simp [← two_mul, h])⟩⟩
#align int.even_iff Int.even_iff
-/

/- warning: int.odd_iff -> Int.odd_iff is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (Odd.{0} Int Int.semiring n) (Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.hasMod) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt n) (Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.instModInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.odd_iff Int.odd_iffₓ'. -/
theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨fun ⟨m, hm⟩ => by
    rw [hm, add_mod]
    norm_num, fun h =>
    ⟨n / 2,
      (emod_add_ediv n 2).symm.trans
        (by
          rw [h]
          abel)⟩⟩
#align int.odd_iff Int.odd_iff

#print Int.not_even_iff /-
theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, mod_two_ne_zero]
#align int.not_even_iff Int.not_even_iff
-/

/- warning: int.not_odd_iff -> Int.not_odd_iff is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (Not (Odd.{0} Int Int.semiring n)) (Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.hasMod) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {n : Int}, Iff (Not (Odd.{0} Int Int.instSemiringInt n)) (Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.instModInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.not_odd_iff Int.not_odd_iffₓ'. -/
theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, mod_two_ne_one]
#align int.not_odd_iff Int.not_odd_iff

/- warning: int.even_iff_not_odd -> Int.even_iff_not_odd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (Even.{0} Int Int.hasAdd n) (Not (Odd.{0} Int Int.semiring n))
but is expected to have type
  forall {n : Int}, Iff (Even.{0} Int Int.instAddInt n) (Not (Odd.{0} Int Int.instSemiringInt n))
Case conversion may be inaccurate. Consider using '#align int.even_iff_not_odd Int.even_iff_not_oddₓ'. -/
theorem even_iff_not_odd : Even n ↔ ¬Odd n := by rw [not_odd_iff, even_iff]
#align int.even_iff_not_odd Int.even_iff_not_odd

/- warning: int.odd_iff_not_even -> Int.odd_iff_not_even is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (Odd.{0} Int Int.semiring n) (Not (Even.{0} Int Int.hasAdd n))
but is expected to have type
  forall {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt n) (Not (Even.{0} Int Int.instAddInt n))
Case conversion may be inaccurate. Consider using '#align int.odd_iff_not_even Int.odd_iff_not_evenₓ'. -/
@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]
#align int.odd_iff_not_even Int.odd_iff_not_even

/- warning: int.is_compl_even_odd -> Int.isCompl_even_odd is a dubious translation:
lean 3 declaration is
  IsCompl.{0} (Set.{0} Int) (SemilatticeInf.toPartialOrder.{0} (Set.{0} Int) (Lattice.toSemilatticeInf.{0} (Set.{0} Int) (GeneralizedCoheytingAlgebra.toLattice.{0} (Set.{0} Int) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{0} (Set.{0} Int) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} (Set.{0} Int) (Set.booleanAlgebra.{0} Int)))))) (BooleanAlgebra.toBoundedOrder.{0} (Set.{0} Int) (Set.booleanAlgebra.{0} Int)) (setOf.{0} Int (fun (n : Int) => Even.{0} Int Int.hasAdd n)) (setOf.{0} Int (fun (n : Int) => Odd.{0} Int Int.semiring n))
but is expected to have type
  IsCompl.{0} (Set.{0} Int) (SemilatticeInf.toPartialOrder.{0} (Set.{0} Int) (Lattice.toSemilatticeInf.{0} (Set.{0} Int) (GeneralizedCoheytingAlgebra.toLattice.{0} (Set.{0} Int) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{0} (Set.{0} Int) (BiheytingAlgebra.toCoheytingAlgebra.{0} (Set.{0} Int) (BooleanAlgebra.toBiheytingAlgebra.{0} (Set.{0} Int) (Set.instBooleanAlgebraSet.{0} Int))))))) (BooleanAlgebra.toBoundedOrder.{0} (Set.{0} Int) (Set.instBooleanAlgebraSet.{0} Int)) (setOf.{0} Int (fun (n : Int) => Even.{0} Int Int.instAddInt n)) (setOf.{0} Int (fun (n : Int) => Odd.{0} Int Int.instSemiringInt n))
Case conversion may be inaccurate. Consider using '#align int.is_compl_even_odd Int.isCompl_even_oddₓ'. -/
theorem isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← Set.compl_setOf, isCompl_compl]
#align int.is_compl_even_odd Int.isCompl_even_odd

/- warning: int.even_or_odd -> Int.even_or_odd is a dubious translation:
lean 3 declaration is
  forall (n : Int), Or (Even.{0} Int Int.hasAdd n) (Odd.{0} Int Int.semiring n)
but is expected to have type
  forall (n : Int), Or (Even.{0} Int Int.instAddInt n) (Odd.{0} Int Int.instSemiringInt n)
Case conversion may be inaccurate. Consider using '#align int.even_or_odd Int.even_or_oddₓ'. -/
theorem even_or_odd (n : ℤ) : Even n ∨ Odd n :=
  Or.imp_right odd_iff_not_even.2 <| em <| Even n
#align int.even_or_odd Int.even_or_odd

#print Int.even_or_odd' /-
theorem even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by
  simpa only [← two_mul, exists_or, ← Odd, ← Even] using even_or_odd n
#align int.even_or_odd' Int.even_or_odd'
-/

/- warning: int.even_xor_odd -> Int.even_xor'_odd is a dubious translation:
lean 3 declaration is
  forall (n : Int), Xor' (Even.{0} Int Int.hasAdd n) (Odd.{0} Int Int.semiring n)
but is expected to have type
  forall (n : Int), Xor' (Even.{0} Int Int.instAddInt n) (Odd.{0} Int Int.instSemiringInt n)
Case conversion may be inaccurate. Consider using '#align int.even_xor_odd Int.even_xor'_oddₓ'. -/
theorem even_xor'_odd (n : ℤ) : Xor' (Even n) (Odd n) :=
  by
  cases' even_or_odd n with h
  · exact Or.inl ⟨h, even_iff_not_odd.mp h⟩
  · exact Or.inr ⟨h, odd_iff_not_even.mp h⟩
#align int.even_xor_odd Int.even_xor'_odd

#print Int.even_xor'_odd' /-
theorem even_xor'_odd' (n : ℤ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) :=
  by
  rcases even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> use k
  ·
    simpa only [← two_mul, Xor', true_and_iff, eq_self_iff_true, not_true, or_false_iff,
      and_false_iff] using (succ_ne_self (2 * k)).symm
  ·
    simp only [Xor', add_right_eq_self, false_or_iff, eq_self_iff_true, not_true, not_false_iff,
      one_ne_zero, and_self_iff]
#align int.even_xor_odd' Int.even_xor'_odd'
-/

/- warning: int.two_dvd_ne_zero -> Int.two_dvd_ne_zero is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (Not (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))) n)) (Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.hasMod) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {n : Int}, Iff (Not (Dvd.dvd.{0} Int Int.instDvdInt (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)) n)) (Eq.{1} Int (HMod.hMod.{0, 0, 0} Int Int Int (instHMod.{0} Int Int.instModInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.two_dvd_ne_zero Int.two_dvd_ne_zeroₓ'. -/
@[simp]
theorem two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  even_iff_two_dvd.symm.Not.trans not_even_iff
#align int.two_dvd_ne_zero Int.two_dvd_ne_zero

instance : DecidablePred (Even : ℤ → Prop) := fun n => decidable_of_iff _ even_iff.symm

instance : DecidablePred (Odd : ℤ → Prop) := fun n => decidable_of_iff _ odd_iff_not_even.symm

#print Int.not_even_one /-
@[simp]
theorem not_even_one : ¬Even (1 : ℤ) := by rw [even_iff] <;> norm_num
#align int.not_even_one Int.not_even_one
-/

#print Int.even_add /-
@[parity_simps]
theorem even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;> cases' mod_two_eq_zero_or_one n with h₂ h₂ <;>
      simp [even_iff, h₁, h₂, Int.add_emod] <;>
    norm_num
#align int.even_add Int.even_add
-/

/- warning: int.even_add' -> Int.even_add' is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Even.{0} Int Int.hasAdd (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (Iff (Odd.{0} Int Int.semiring m) (Odd.{0} Int Int.semiring n))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Even.{0} Int Int.instAddInt (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (Iff (Odd.{0} Int Int.instSemiringInt m) (Odd.{0} Int Int.instSemiringInt n))
Case conversion may be inaccurate. Consider using '#align int.even_add' Int.even_add'ₓ'. -/
theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by
  rw [even_add, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align int.even_add' Int.even_add'

#print Int.not_even_bit1 /-
@[simp]
theorem not_even_bit1 (n : ℤ) : ¬Even (bit1 n) := by simp [bit1, parity_simps]
#align int.not_even_bit1 Int.not_even_bit1
-/

/- warning: int.two_not_dvd_two_mul_add_one -> Int.two_not_dvd_two_mul_add_one is a dubious translation:
lean 3 declaration is
  forall (n : Int), Not (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))) n) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))
but is expected to have type
  forall (n : Int), Not (Dvd.dvd.{0} Int Int.instDvdInt (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)) n) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))
Case conversion may be inaccurate. Consider using '#align int.two_not_dvd_two_mul_add_one Int.two_not_dvd_two_mul_add_oneₓ'. -/
theorem two_not_dvd_two_mul_add_one (n : ℤ) : ¬2 ∣ 2 * n + 1 :=
  by
  simp [add_mod]
  rfl
#align int.two_not_dvd_two_mul_add_one Int.two_not_dvd_two_mul_add_one

#print Int.even_sub /-
@[parity_simps]
theorem even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by simp [sub_eq_add_neg, parity_simps]
#align int.even_sub Int.even_sub
-/

/- warning: int.even_sub' -> Int.even_sub' is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Even.{0} Int Int.hasAdd (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) m n)) (Iff (Odd.{0} Int Int.semiring m) (Odd.{0} Int Int.semiring n))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Even.{0} Int Int.instAddInt (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) m n)) (Iff (Odd.{0} Int Int.instSemiringInt m) (Odd.{0} Int Int.instSemiringInt n))
Case conversion may be inaccurate. Consider using '#align int.even_sub' Int.even_sub'ₓ'. -/
theorem even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub, even_iff_not_odd, even_iff_not_odd, not_iff_not]
#align int.even_sub' Int.even_sub'

#print Int.even_add_one /-
@[parity_simps]
theorem even_add_one : Even (n + 1) ↔ ¬Even n := by simp [even_add]
#align int.even_add_one Int.even_add_one
-/

#print Int.even_mul /-
@[parity_simps]
theorem even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  cases' mod_two_eq_zero_or_one m with h₁ h₁ <;> cases' mod_two_eq_zero_or_one n with h₂ h₂ <;>
      simp [even_iff, h₁, h₂, Int.mul_emod] <;>
    norm_num
#align int.even_mul Int.even_mul
-/

/- warning: int.odd_mul -> Int.odd_mul is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.semiring (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) (And (Odd.{0} Int Int.semiring m) (Odd.{0} Int Int.semiring n))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) (And (Odd.{0} Int Int.instSemiringInt m) (Odd.{0} Int Int.instSemiringInt n))
Case conversion may be inaccurate. Consider using '#align int.odd_mul Int.odd_mulₓ'. -/
theorem odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [not_or, parity_simps]
#align int.odd_mul Int.odd_mul

/- warning: int.odd.of_mul_left -> Int.Odd.of_mul_left is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, (Odd.{0} Int Int.semiring (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) -> (Odd.{0} Int Int.semiring m)
but is expected to have type
  forall {m : Int} {n : Int}, (Odd.{0} Int Int.instSemiringInt (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) -> (Odd.{0} Int Int.instSemiringInt m)
Case conversion may be inaccurate. Consider using '#align int.odd.of_mul_left Int.Odd.of_mul_leftₓ'. -/
theorem Odd.of_mul_left (h : Odd (m * n)) : Odd m :=
  (odd_mul.mp h).1
#align int.odd.of_mul_left Int.Odd.of_mul_left

/- warning: int.odd.of_mul_right -> Int.Odd.of_mul_right is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, (Odd.{0} Int Int.semiring (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) -> (Odd.{0} Int Int.semiring n)
but is expected to have type
  forall {m : Int} {n : Int}, (Odd.{0} Int Int.instSemiringInt (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) -> (Odd.{0} Int Int.instSemiringInt n)
Case conversion may be inaccurate. Consider using '#align int.odd.of_mul_right Int.Odd.of_mul_rightₓ'. -/
theorem Odd.of_mul_right (h : Odd (m * n)) : Odd n :=
  (odd_mul.mp h).2
#align int.odd.of_mul_right Int.Odd.of_mul_right

/- warning: int.even_pow -> Int.even_pow is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Nat}, Iff (Even.{0} Int Int.hasAdd (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) m n)) (And (Even.{0} Int Int.hasAdd m) (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {m : Int} {n : Nat}, Iff (Even.{0} Int Int.instAddInt (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat m n)) (And (Even.{0} Int Int.instAddInt m) (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align int.even_pow Int.even_powₓ'. -/
@[parity_simps]
theorem even_pow {n : ℕ} : Even (m ^ n) ↔ Even m ∧ n ≠ 0 :=
  by
  induction' n with n ih <;> simp [*, even_mul, pow_succ]
  tauto
#align int.even_pow Int.even_pow

/- warning: int.even_pow' -> Int.even_pow' is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (Even.{0} Int Int.hasAdd (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) m n)) (Even.{0} Int Int.hasAdd m))
but is expected to have type
  forall {m : Int} {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (Even.{0} Int Int.instAddInt (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat m n)) (Even.{0} Int Int.instAddInt m))
Case conversion may be inaccurate. Consider using '#align int.even_pow' Int.even_pow'ₓ'. -/
theorem even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m :=
  even_pow.trans <| and_iff_left h
#align int.even_pow' Int.even_pow'

/- warning: int.odd_add -> Int.odd_add is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.semiring (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (Iff (Odd.{0} Int Int.semiring m) (Even.{0} Int Int.hasAdd n))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (Iff (Odd.{0} Int Int.instSemiringInt m) (Even.{0} Int Int.instAddInt n))
Case conversion may be inaccurate. Consider using '#align int.odd_add Int.odd_addₓ'. -/
@[parity_simps]
theorem odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_add, not_iff, odd_iff_not_even]
#align int.odd_add Int.odd_add

/- warning: int.odd_add' -> Int.odd_add' is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.semiring (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) (Iff (Odd.{0} Int Int.semiring n) (Even.{0} Int Int.hasAdd m))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) (Iff (Odd.{0} Int Int.instSemiringInt n) (Even.{0} Int Int.instAddInt m))
Case conversion may be inaccurate. Consider using '#align int.odd_add' Int.odd_add'ₓ'. -/
theorem odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by rw [add_comm, odd_add]
#align int.odd_add' Int.odd_add'

/- warning: int.ne_of_odd_add -> Int.ne_of_odd_add is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, (Odd.{0} Int Int.semiring (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) m n)) -> (Ne.{1} Int m n)
but is expected to have type
  forall {m : Int} {n : Int}, (Odd.{0} Int Int.instSemiringInt (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) m n)) -> (Ne.{1} Int m n)
Case conversion may be inaccurate. Consider using '#align int.ne_of_odd_add Int.ne_of_odd_addₓ'. -/
theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n := fun hnot => by simpa [hnot, parity_simps] using h
#align int.ne_of_odd_add Int.ne_of_odd_add

/- warning: int.odd_sub -> Int.odd_sub is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.semiring (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) m n)) (Iff (Odd.{0} Int Int.semiring m) (Even.{0} Int Int.hasAdd n))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) m n)) (Iff (Odd.{0} Int Int.instSemiringInt m) (Even.{0} Int Int.instAddInt n))
Case conversion may be inaccurate. Consider using '#align int.odd_sub Int.odd_subₓ'. -/
@[parity_simps]
theorem odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [odd_iff_not_even, even_sub, not_iff, odd_iff_not_even]
#align int.odd_sub Int.odd_sub

/- warning: int.odd_sub' -> Int.odd_sub' is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.semiring (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) m n)) (Iff (Odd.{0} Int Int.semiring n) (Even.{0} Int Int.hasAdd m))
but is expected to have type
  forall {m : Int} {n : Int}, Iff (Odd.{0} Int Int.instSemiringInt (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) m n)) (Iff (Odd.{0} Int Int.instSemiringInt n) (Even.{0} Int Int.instAddInt m))
Case conversion may be inaccurate. Consider using '#align int.odd_sub' Int.odd_sub'ₓ'. -/
theorem odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by
  rw [odd_iff_not_even, even_sub, not_iff, not_iff_comm, odd_iff_not_even]
#align int.odd_sub' Int.odd_sub'

#print Int.even_mul_succ_self /-
theorem even_mul_succ_self (n : ℤ) : Even (n * (n + 1)) :=
  by
  rw [even_mul]
  convert n.even_or_odd
  simp [parity_simps]
#align int.even_mul_succ_self Int.even_mul_succ_self
-/

#print Int.even_coe_nat /-
@[simp, norm_cast]
theorem even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by rw_mod_cast [even_iff, Nat.even_iff]
#align int.even_coe_nat Int.even_coe_nat
-/

/- warning: int.odd_coe_nat -> Int.odd_coe_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Iff (Odd.{0} Int Int.semiring ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (Odd.{0} Nat Nat.semiring n)
but is expected to have type
  forall (n : Nat), Iff (Odd.{0} Int Int.instSemiringInt (Nat.cast.{0} Int Int.instNatCastInt n)) (Odd.{0} Nat Nat.semiring n)
Case conversion may be inaccurate. Consider using '#align int.odd_coe_nat Int.odd_coe_natₓ'. -/
@[simp, norm_cast]
theorem odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, even_coe_nat]
#align int.odd_coe_nat Int.odd_coe_nat

#print Int.natAbs_even /-
@[simp]
theorem natAbs_even : Even n.natAbs ↔ Even n := by
  simp [even_iff_two_dvd, dvd_nat_abs, coe_nat_dvd_left.symm]
#align int.nat_abs_even Int.natAbs_even
-/

/- warning: int.nat_abs_odd -> Int.natAbs_odd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (Odd.{0} Nat Nat.semiring (Int.natAbs n)) (Odd.{0} Int Int.semiring n)
but is expected to have type
  forall {n : Int}, Iff (Odd.{0} Nat Nat.semiring (Int.natAbs n)) (Odd.{0} Int Int.instSemiringInt n)
Case conversion may be inaccurate. Consider using '#align int.nat_abs_odd Int.natAbs_oddₓ'. -/
@[simp]
theorem natAbs_odd : Odd n.natAbs ↔ Odd n := by
  rw [odd_iff_not_even, Nat.odd_iff_not_even, nat_abs_even]
#align int.nat_abs_odd Int.natAbs_odd

alias nat_abs_even ↔ _ _root_.even.nat_abs
#align even.nat_abs Even.natAbs

/- warning: odd.nat_abs -> Odd.natAbs is a dubious translation:
lean 3 declaration is
  forall {n : Int}, (Odd.{0} Int Int.semiring n) -> (Odd.{0} Nat Nat.semiring (Int.natAbs n))
but is expected to have type
  forall {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (Odd.{0} Nat Nat.semiring (Int.natAbs n))
Case conversion may be inaccurate. Consider using '#align odd.nat_abs Odd.natAbsₓ'. -/
alias nat_abs_odd ↔ _ _root_.odd.nat_abs
#align odd.nat_abs Odd.natAbs

attribute [protected] Even.natAbs Odd.natAbs

/- warning: int.four_dvd_add_or_sub_of_odd -> Int.four_dvd_add_or_sub_of_odd is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (Odd.{0} Int Int.semiring a) -> (Odd.{0} Int Int.semiring b) -> (Or (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (OfNat.ofNat.{0} Int 4 (OfNat.mk.{0} Int 4 (bit0.{0} Int Int.hasAdd (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) a b)) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (OfNat.ofNat.{0} Int 4 (OfNat.mk.{0} Int 4 (bit0.{0} Int Int.hasAdd (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) a b)))
but is expected to have type
  forall {a : Int} {b : Int}, (Odd.{0} Int Int.instSemiringInt a) -> (Odd.{0} Int Int.instSemiringInt b) -> (Or (Dvd.dvd.{0} Int Int.instDvdInt (OfNat.ofNat.{0} Int 4 (instOfNatInt 4)) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) a b)) (Dvd.dvd.{0} Int Int.instDvdInt (OfNat.ofNat.{0} Int 4 (instOfNatInt 4)) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) a b)))
Case conversion may be inaccurate. Consider using '#align int.four_dvd_add_or_sub_of_odd Int.four_dvd_add_or_sub_of_oddₓ'. -/
theorem four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) : 4 ∣ a + b ∨ 4 ∣ a - b :=
  by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  obtain h | h := Int.even_or_odd (m + n)
  · right
    rw [Int.even_add, ← Int.even_sub] at h
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 k
    rw [eq_add_of_sub_eq hk, mul_add, add_assoc, add_sub_cancel, ← two_mul, ← mul_assoc]
    rfl
  · left
    obtain ⟨k, hk⟩ := h
    convert dvd_mul_right 4 (k + 1)
    rw [eq_sub_of_add_eq hk, add_right_comm, ← add_sub, mul_add, mul_sub, add_assoc, add_assoc,
      sub_add, add_assoc, ← sub_sub (2 * n), sub_self, zero_sub, sub_neg_eq_add, ← mul_assoc,
      mul_add]
    rfl
#align int.four_dvd_add_or_sub_of_odd Int.four_dvd_add_or_sub_of_odd

#print Int.two_mul_ediv_two_of_even /-
theorem two_mul_ediv_two_of_even : Even n → 2 * (n / 2) = n := fun h =>
  Int.mul_ediv_cancel' (even_iff_two_dvd.mp h)
#align int.two_mul_div_two_of_even Int.two_mul_ediv_two_of_even
-/

#print Int.ediv_two_mul_two_of_even /-
theorem ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun
    --int.div_mul_cancel
    h =>
  Int.ediv_mul_cancel (even_iff_two_dvd.mp h)
#align int.div_two_mul_two_of_even Int.ediv_two_mul_two_of_even
-/

/- warning: int.two_mul_div_two_add_one_of_odd -> Int.two_mul_ediv_two_add_one_of_odd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, (Odd.{0} Int Int.semiring n) -> (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) n)
but is expected to have type
  forall {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) n)
Case conversion may be inaccurate. Consider using '#align int.two_mul_div_two_add_one_of_odd Int.two_mul_ediv_two_add_one_of_oddₓ'. -/
theorem two_mul_ediv_two_add_one_of_odd : Odd n → 2 * (n / 2) + 1 = n :=
  by
  rintro ⟨c, rfl⟩
  rw [mul_comm]
  convert Int.div_add_mod' _ _
  simpa [Int.add_emod]
#align int.two_mul_div_two_add_one_of_odd Int.two_mul_ediv_two_add_one_of_odd

/- warning: int.div_two_mul_two_add_one_of_odd -> Int.ediv_two_mul_two_add_one_of_odd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, (Odd.{0} Int Int.semiring n) -> (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) n)
but is expected to have type
  forall {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) n)
Case conversion may be inaccurate. Consider using '#align int.div_two_mul_two_add_one_of_odd Int.ediv_two_mul_two_add_one_of_oddₓ'. -/
theorem ediv_two_mul_two_add_one_of_odd : Odd n → n / 2 * 2 + 1 = n :=
  by
  rintro ⟨c, rfl⟩
  convert Int.div_add_mod' _ _
  simpa [Int.add_emod]
#align int.div_two_mul_two_add_one_of_odd Int.ediv_two_mul_two_add_one_of_odd

/- warning: int.add_one_div_two_mul_two_of_odd -> Int.add_one_ediv_two_mul_two_of_odd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, (Odd.{0} Int Int.semiring n) -> (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne))))) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))))) n)
but is expected to have type
  forall {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2))) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)))) n)
Case conversion may be inaccurate. Consider using '#align int.add_one_div_two_mul_two_of_odd Int.add_one_ediv_two_mul_two_of_oddₓ'. -/
theorem add_one_ediv_two_mul_two_of_odd : Odd n → 1 + n / 2 * 2 = n :=
  by
  rintro ⟨c, rfl⟩
  rw [add_comm]
  convert Int.div_add_mod' _ _
  simpa [Int.add_emod]
#align int.add_one_div_two_mul_two_of_odd Int.add_one_ediv_two_mul_two_of_odd

/- warning: int.two_mul_div_two_of_odd -> Int.two_mul_ediv_two_of_odd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, (Odd.{0} Int Int.semiring n) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) n (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))))
but is expected to have type
  forall {n : Int}, (Odd.{0} Int Int.instSemiringInt n) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) n (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)))) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))))
Case conversion may be inaccurate. Consider using '#align int.two_mul_div_two_of_odd Int.two_mul_ediv_two_of_oddₓ'. -/
theorem two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 :=
  eq_sub_of_add_eq (two_mul_ediv_two_add_one_of_odd h)
#align int.two_mul_div_two_of_odd Int.two_mul_ediv_two_of_odd

-- Here are examples of how `parity_simps` can be used with `int`.
example (m n : ℤ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, (by decide : ¬2 = 0), parity_simps]

example : ¬Even (25394535 : ℤ) := by simp

end Int

