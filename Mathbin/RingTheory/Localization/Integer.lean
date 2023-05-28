/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.integer
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.Basic

/-!
# Integer elements of a localization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

 * `is_localization.is_integer` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRing R] {M : Submonoid R} {S : Type _} [CommRing S]

variable [Algebra R S] {P : Type _} [CommRing P]

open Function

open BigOperators

namespace IsLocalization

section

variable (R) {M S}

#print IsLocalization.IsInteger /-
-- TODO: define a subalgebra of `is_integer`s
/-- Given `a : S`, `S` a localization of `R`, `is_integer R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).range
#align is_localization.is_integer IsLocalization.IsInteger
-/

end

/- warning: is_localization.is_integer_zero -> IsLocalization.isInteger_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))], IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))], IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 (OfNat.ofNat.{u1} S 0 (Zero.toOfNat0.{u1} S (CommMonoidWithZero.toZero.{u1} S (CommSemiring.toCommMonoidWithZero.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_localization.is_integer_zero IsLocalization.isInteger_zeroₓ'. -/
theorem isInteger_zero : IsInteger R (0 : S) :=
  Subring.zero_mem _
#align is_localization.is_integer_zero IsLocalization.isInteger_zero

/- warning: is_localization.is_integer_one -> IsLocalization.isInteger_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))], IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S (AddMonoidWithOne.toOne.{u2} S (AddGroupWithOne.toAddMonoidWithOne.{u2} S (AddCommGroupWithOne.toAddGroupWithOne.{u2} S (Ring.toAddCommGroupWithOne.{u2} S (CommRing.toRing.{u2} S _inst_2))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))], IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 (OfNat.ofNat.{u1} S 1 (One.toOfNat1.{u1} S (Semiring.toOne.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_localization.is_integer_one IsLocalization.isInteger_oneₓ'. -/
theorem isInteger_one : IsInteger R (1 : S) :=
  Subring.one_mem _
#align is_localization.is_integer_one IsLocalization.isInteger_one

/- warning: is_localization.is_integer_add -> IsLocalization.isInteger_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] {a : S} {b : S}, (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 a) -> (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 b) -> (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 (HAdd.hAdd.{u2, u2, u2} S S S (instHAdd.{u2} S (Distrib.toHasAdd.{u2} S (Ring.toDistrib.{u2} S (CommRing.toRing.{u2} S _inst_2)))) a b))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] {a : S} {b : S}, (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 a) -> (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 b) -> (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 (HAdd.hAdd.{u1, u1, u1} S S S (instHAdd.{u1} S (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S (CommRing.toRing.{u1} S _inst_2))))))) a b))
Case conversion may be inaccurate. Consider using '#align is_localization.is_integer_add IsLocalization.isInteger_addₓ'. -/
theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subring.add_mem _ ha hb
#align is_localization.is_integer_add IsLocalization.isInteger_add

/- warning: is_localization.is_integer_mul -> IsLocalization.isInteger_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] {a : S} {b : S}, (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 a) -> (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 b) -> (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 (HMul.hMul.{u2, u2, u2} S S S (instHMul.{u2} S (Distrib.toHasMul.{u2} S (Ring.toDistrib.{u2} S (CommRing.toRing.{u2} S _inst_2)))) a b))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] {a : S} {b : S}, (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 a) -> (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 b) -> (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (NonUnitalNonAssocRing.toMul.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S (CommRing.toRing.{u1} S _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align is_localization.is_integer_mul IsLocalization.isInteger_mulₓ'. -/
theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subring.mul_mem _ ha hb
#align is_localization.is_integer_mul IsLocalization.isInteger_mul

/- warning: is_localization.is_integer_smul -> IsLocalization.isInteger_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] {a : R} {b : S}, (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 b) -> (IsLocalization.IsInteger.{u1, u2} R _inst_1 S _inst_2 _inst_3 (SMul.smul.{u1, u2} R S (SMulZeroClass.toHasSmul.{u1, u2} R S (AddZeroClass.toHasZero.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R S (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R S (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))) (Module.toMulActionWithZero.{u1, u2} R S (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))))) (Algebra.toModule.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3))))) a b))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] {a : R} {b : S}, (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 b) -> (IsLocalization.IsInteger.{u2, u1} R _inst_1 S _inst_2 _inst_3 (HSMul.hSMul.{u2, u1, u1} R S S (instHSMul.{u2, u1} R S (Algebra.toSMul.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)) _inst_3)) a b))
Case conversion may be inaccurate. Consider using '#align is_localization.is_integer_smul IsLocalization.isInteger_smulₓ'. -/
theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) :=
  by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]
#align is_localization.is_integer_smul IsLocalization.isInteger_smul

variable (M) {S} [IsLocalization M S]

/- warning: is_localization.exists_integer_multiple' -> IsLocalization.exists_integer_multiple' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.exists_integer_multiple' IsLocalization.exists_integer_multiple'ₓ'. -/
/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
theorem exists_integer_multiple' (a : S) : ∃ b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩
#align is_localization.exists_integer_multiple' IsLocalization.exists_integer_multiple'

/- warning: is_localization.exists_integer_multiple -> IsLocalization.exists_integer_multiple is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.exists_integer_multiple IsLocalization.exists_integer_multipleₓ'. -/
/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_smul` instance.
-/
theorem exists_integer_multiple (a : S) : ∃ b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]; apply exists_integer_multiple'
#align is_localization.exists_integer_multiple IsLocalization.exists_integer_multiple

/- warning: is_localization.exist_integer_multiples -> IsLocalization.exist_integer_multiples is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.exist_integer_multiples IsLocalization.exist_integer_multiplesₓ'. -/
/-- We can clear the denominators of a `finset`-indexed family of fractions. -/
theorem exist_integer_multiples {ι : Type _} (s : Finset ι) (f : ι → S) :
    ∃ b : M, ∀ i ∈ s, IsLocalization.IsInteger R ((b : R) • f i) :=
  by
  haveI := Classical.propDecidable
  refine' ⟨∏ i in s, (sec M (f i)).2, fun i hi => ⟨_, _⟩⟩
  · exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [RingHom.map_mul, sec_spec', ← mul_assoc, ← (algebraMap R S).map_mul, ← Algebra.smul_def]
  congr 2
  refine' trans _ ((Submonoid.subtype M).map_prod _ _).symm
  rw [mul_comm, ← Finset.prod_insert (s.not_mem_erase i), Finset.insert_erase hi]
  rfl
#align is_localization.exist_integer_multiples IsLocalization.exist_integer_multiples

/- warning: is_localization.exist_integer_multiples_of_finite -> IsLocalization.exist_integer_multiples_of_finite is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.exist_integer_multiples_of_finite IsLocalization.exist_integer_multiples_of_finiteₓ'. -/
/-- We can clear the denominators of a finite indexed family of fractions. -/
theorem exist_integer_multiples_of_finite {ι : Type _} [Finite ι] (f : ι → S) :
    ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) :=
  by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩
#align is_localization.exist_integer_multiples_of_finite IsLocalization.exist_integer_multiples_of_finite

/- warning: is_localization.exist_integer_multiples_of_finset -> IsLocalization.exist_integer_multiples_of_finset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.exist_integer_multiples_of_finset IsLocalization.exist_integer_multiples_of_finsetₓ'. -/
/-- We can clear the denominators of a finite set of fractions. -/
theorem exist_integer_multiples_of_finset (s : Finset S) :
    ∃ b : M, ∀ a ∈ s, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id
#align is_localization.exist_integer_multiples_of_finset IsLocalization.exist_integer_multiples_of_finset

/- warning: is_localization.common_denom -> IsLocalization.commonDenom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] {ι : Type.{u3}}, (Finset.{u3} ι) -> (ι -> S) -> (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) M)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] {ι : Type.{u3}}, (Finset.{u3} ι) -> (ι -> S) -> (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) x M))
Case conversion may be inaccurate. Consider using '#align is_localization.common_denom IsLocalization.commonDenomₓ'. -/
/-- A choice of a common multiple of the denominators of a `finset`-indexed family of fractions. -/
noncomputable def commonDenom {ι : Type _} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).some
#align is_localization.common_denom IsLocalization.commonDenom

#print IsLocalization.integerMultiple /-
/-- The numerator of a fraction after clearing the denominators
of a `finset`-indexed family of fractions. -/
noncomputable def integerMultiple {ι : Type _} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.Prop).some
#align is_localization.integer_multiple IsLocalization.integerMultiple
-/

/- warning: is_localization.map_integer_multiple -> IsLocalization.map_integerMultiple is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_integer_multiple IsLocalization.map_integerMultipleₓ'. -/
@[simp]
theorem map_integerMultiple {ι : Type _} (s : Finset ι) (f : ι → S) (i : s) :
    algebraMap R S (integerMultiple M s f i) = commonDenom M s f • f i :=
  ((exist_integer_multiples M s f).choose_spec _ i.Prop).choose_spec
#align is_localization.map_integer_multiple IsLocalization.map_integerMultiple

/- warning: is_localization.common_denom_of_finset -> IsLocalization.commonDenomOfFinset is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], (Finset.{u2} S) -> (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) M)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], (Finset.{u2} S) -> (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))) x M))
Case conversion may be inaccurate. Consider using '#align is_localization.common_denom_of_finset IsLocalization.commonDenomOfFinsetₓ'. -/
/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable def commonDenomOfFinset (s : Finset S) : M :=
  commonDenom M s id
#align is_localization.common_denom_of_finset IsLocalization.commonDenomOfFinset

#print IsLocalization.finsetIntegerMultiple /-
/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable def finsetIntegerMultiple [DecidableEq R] (s : Finset S) : Finset R :=
  s.attach.image fun t => integerMultiple M s id t
#align is_localization.finset_integer_multiple IsLocalization.finsetIntegerMultiple
-/

open Pointwise

/- warning: is_localization.finset_integer_multiple_image -> IsLocalization.finsetIntegerMultiple_image is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.finset_integer_multiple_image IsLocalization.finsetIntegerMultiple_imageₓ'. -/
theorem finsetIntegerMultiple_image [DecidableEq R] (s : Finset S) :
    algebraMap R S '' finsetIntegerMultiple M s = commonDenomOfFinset M s • s :=
  by
  delta finset_integer_multiple common_denom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integer_multiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integer_multiple M s id _⟩
#align is_localization.finset_integer_multiple_image IsLocalization.finsetIntegerMultiple_image

end IsLocalization

