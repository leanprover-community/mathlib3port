/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.module
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer

/-!
# Modules / vector spaces over localizations / fraction fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `linear_independent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `basis.localization_localization`: promote an `R`-basis `b` of `A` to an `Rₛ`-basis of `Aₛ`,
   where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s` respectively
 * `linear_independent.iff_fraction_ring`: `b` is linear independent over `R` iff it is
   linear independent over `Frac(R)`
-/


open BigOperators

open nonZeroDivisors

section Localization

variable {R : Type _} (Rₛ : Type _) [CommRing R] [CommRing Rₛ] [Algebra R Rₛ]

variable (S : Submonoid R) [hT : IsLocalization S Rₛ]

include hT

section AddCommMonoid

variable {M : Type _} [AddCommMonoid M] [Module R M] [Module Rₛ M] [IsScalarTower R Rₛ M]

/- warning: linear_independent.localization -> LinearIndependent.localization is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} (Rₛ : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : CommRing.{u2} Rₛ] [_inst_3 : Algebra.{u1, u2} R Rₛ (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2))] (S : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) [hT : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) S Rₛ (CommRing.toCommSemiring.{u2} Rₛ _inst_2) _inst_3] {M : Type.{u3}} [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_4] [_inst_6 : Module.{u2, u3} Rₛ M (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)) _inst_4] [_inst_7 : IsScalarTower.{u1, u2, u3} R Rₛ M (SMulZeroClass.toHasSmul.{u1, u2} R Rₛ (AddZeroClass.toHasZero.{u2} Rₛ (AddMonoid.toAddZeroClass.{u2} Rₛ (AddCommMonoid.toAddMonoid.{u2} Rₛ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} Rₛ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} Rₛ (Semiring.toNonAssocSemiring.{u2} Rₛ (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R Rₛ (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} Rₛ (AddMonoid.toAddZeroClass.{u2} Rₛ (AddCommMonoid.toAddMonoid.{u2} Rₛ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} Rₛ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} Rₛ (Semiring.toNonAssocSemiring.{u2} Rₛ (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R Rₛ (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} Rₛ (AddMonoid.toAddZeroClass.{u2} Rₛ (AddCommMonoid.toAddMonoid.{u2} Rₛ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} Rₛ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} Rₛ (Semiring.toNonAssocSemiring.{u2} Rₛ (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)))))))) (Module.toMulActionWithZero.{u1, u2} R Rₛ (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} Rₛ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} Rₛ (Semiring.toNonAssocSemiring.{u2} Rₛ (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2))))) (Algebra.toModule.{u1, u2} R Rₛ (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)) _inst_3))))) (SMulZeroClass.toHasSmul.{u2, u3} Rₛ M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} Rₛ M (MulZeroClass.toHasZero.{u2} Rₛ (MulZeroOneClass.toMulZeroClass.{u2} Rₛ (MonoidWithZero.toMulZeroOneClass.{u2} Rₛ (Semiring.toMonoidWithZero.{u2} Rₛ (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} Rₛ M (Semiring.toMonoidWithZero.{u2} Rₛ (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} Rₛ M (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)) _inst_4 _inst_6)))) (SMulZeroClass.toHasSmul.{u1, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_4 _inst_5))))] {ι : Type.{u4}} {b : ι -> M}, (LinearIndependent.{u4, u1, u3} ι R M b (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_4 _inst_5) -> (LinearIndependent.{u4, u2, u3} ι Rₛ M b (Ring.toSemiring.{u2} Rₛ (CommRing.toRing.{u2} Rₛ _inst_2)) _inst_4 _inst_6)
but is expected to have type
  forall {R : Type.{u3}} (Rₛ : Type.{u1}) [_inst_1 : CommRing.{u3} R] [_inst_2 : CommRing.{u1} Rₛ] [_inst_3 : Algebra.{u3, u1} R Rₛ (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2))] (S : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)))))) [hT : IsLocalization.{u3, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) S Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2) _inst_3] {M : Type.{u2}} [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) _inst_4] [_inst_6 : Module.{u1, u2} Rₛ M (CommSemiring.toSemiring.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2)) _inst_4] [_inst_7 : IsScalarTower.{u3, u1, u2} R Rₛ M (Algebra.toSMul.{u3, u1} R Rₛ (CommRing.toCommSemiring.{u3} R _inst_1) (CommSemiring.toSemiring.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2)) _inst_3) (SMulZeroClass.toSMul.{u1, u2} Rₛ M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u1, u2} Rₛ M (CommMonoidWithZero.toZero.{u1} Rₛ (CommSemiring.toCommMonoidWithZero.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2))) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u1, u2} Rₛ M (Semiring.toMonoidWithZero.{u1} Rₛ (CommSemiring.toSemiring.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2))) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (Module.toMulActionWithZero.{u1, u2} Rₛ M (CommSemiring.toSemiring.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2)) _inst_4 _inst_6)))) (SMulZeroClass.toSMul.{u3, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (CommMonoidWithZero.toZero.{u3} R (CommSemiring.toCommMonoidWithZero.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (Module.toMulActionWithZero.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) _inst_4 _inst_5))))] {ι : Type.{u4}} {b : ι -> M}, (LinearIndependent.{u4, u3, u2} ι R M b (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) _inst_4 _inst_5) -> (LinearIndependent.{u4, u1, u2} ι Rₛ M b (CommSemiring.toSemiring.{u1} Rₛ (CommRing.toCommSemiring.{u1} Rₛ _inst_2)) _inst_4 _inst_6)
Case conversion may be inaccurate. Consider using '#align linear_independent.localization LinearIndependent.localizationₓ'. -/
theorem LinearIndependent.localization {ι : Type _} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by
  rw [linearIndependent_iff'] at hli⊢
  intro s g hg i hi
  choose! a g' hg' using IsLocalization.exist_integer_multiples S s g
  specialize hli s g' _ i hi
  · rw [← @smul_zero _ M _ _ (a : R), ← hg, Finset.smul_sum]
    refine' Finset.sum_congr rfl fun i hi => _
    rw [← IsScalarTower.algebraMap_smul Rₛ, hg' i hi, smul_assoc]
    infer_instance
  refine' (IsLocalization.map_units Rₛ a).mul_right_eq_zero.mp _
  rw [← Algebra.smul_def, ← map_zero (algebraMap R Rₛ), ← hli, hg' i hi]
#align linear_independent.localization LinearIndependent.localization

end AddCommMonoid

section LocalizationLocalization

variable {A : Type _} [CommRing A] [Algebra R A]

variable (Aₛ : Type _) [CommRing Aₛ] [Algebra A Aₛ]

variable [Algebra Rₛ Aₛ] [Algebra R Aₛ] [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]

variable [hA : IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]

include hA

open Submodule

/- warning: linear_independent.localization_localization -> LinearIndependent.localization_localization is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_independent.localization_localization LinearIndependent.localization_localizationₓ'. -/
theorem LinearIndependent.localization_localization {ι : Type _} {v : ι → A}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (algebraMap A Aₛ ∘ v) :=
  by
  rw [linearIndependent_iff'] at hv⊢
  intro s g hg i hi
  choose! a g' hg' using IsLocalization.exist_integer_multiples S s g
  have h0 : algebraMap A Aₛ (∑ i in s, g' i • v i) = 0 :=
    by
    apply_fun (· • ·) (a : R)  at hg
    rw [smul_zero, Finset.smul_sum] at hg
    rw [map_sum, ← hg]
    refine' Finset.sum_congr rfl fun i hi => _
    rw [← smul_assoc, ← hg' i hi, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ←
      Algebra.smul_def, algebraMap_smul]
  obtain ⟨⟨_, r, hrS, rfl⟩, hr : algebraMap R A r * _ = 0⟩ :=
    (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid A S) _ _).1 h0
  simp_rw [Finset.mul_sum, ← Algebra.smul_def, smul_smul] at hr
  specialize hv s _ hr i hi
  rw [← (IsLocalization.map_units Rₛ a).mul_right_eq_zero, ← Algebra.smul_def, ← hg' i hi]
  exact (IsLocalization.map_eq_zero_iff S _ _).2 ⟨⟨r, hrS⟩, hv⟩
#align linear_independent.localization_localization LinearIndependent.localization_localization

/- warning: span_eq_top.localization_localization -> SpanEqTop.localization_localization is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align span_eq_top.localization_localization SpanEqTop.localization_localizationₓ'. -/
theorem SpanEqTop.localization_localization {v : Set A} (hv : span R v = ⊤) :
    span Rₛ (algebraMap A Aₛ '' v) = ⊤ := by
  rw [eq_top_iff]
  rintro a' -
  obtain ⟨a, ⟨_, s, hs, rfl⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid A S) a'
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm, ← map_one (algebraMap R A)]
  erw [← IsLocalization.algebraMap_mk' A Rₛ Aₛ (1 : R) ⟨s, hs⟩]
  -- `erw` needed to unify `⟨s, hs⟩`
  rw [← Algebra.smul_def]
  refine' smul_mem _ _ (span_subset_span R _ _ _)
  rw [← Algebra.coe_linearMap, ← LinearMap.coe_restrictScalars R, ← LinearMap.map_span]
  exact mem_map_of_mem (hv.symm ▸ mem_top)
  · infer_instance
#align span_eq_top.localization_localization SpanEqTop.localization_localization

#print Basis.localizationLocalization /-
/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[algebra A Aₛ]` is `localization_algebra`.
-/
noncomputable def Basis.localizationLocalization {ι : Type _} (b : Basis ι R A) : Basis ι Rₛ Aₛ :=
  Basis.mk (b.LinearIndependent.localization_localization _ S _)
    (by
      rw [Set.range_comp, SpanEqTop.localization_localization Rₛ S Aₛ b.span_eq]
      exact le_rfl)
#align basis.localization_localization Basis.localizationLocalization
-/

/- warning: basis.localization_localization_apply -> Basis.localizationLocalization_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.localization_localization_apply Basis.localizationLocalization_applyₓ'. -/
@[simp]
theorem Basis.localizationLocalization_apply {ι : Type _} (b : Basis ι R A) (i) :
    b.localization_localization Rₛ S Aₛ i = algebraMap A Aₛ (b i) :=
  Basis.mk_apply _ _ _
#align basis.localization_localization_apply Basis.localizationLocalization_apply

/- warning: basis.localization_localization_repr_algebra_map -> Basis.localizationLocalization_repr_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.localization_localization_repr_algebra_map Basis.localizationLocalization_repr_algebraMapₓ'. -/
@[simp]
theorem Basis.localizationLocalization_repr_algebraMap {ι : Type _} (b : Basis ι R A) (x i) :
    (b.localization_localization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
      algebraMap R Rₛ (b.repr x i) :=
  calc
    (b.localization_localization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
        (b.localization_localization Rₛ S Aₛ).repr
          ((b.repr x).Sum fun j c => algebraMap R Rₛ c • algebraMap A Aₛ (b j)) i :=
      by
      simp_rw [IsScalarTower.algebraMap_smul, Algebra.smul_def,
        IsScalarTower.algebraMap_apply R A Aₛ, ← _root_.map_mul, ← map_finsupp_sum, ←
        Algebra.smul_def, ← Finsupp.total_apply, Basis.total_repr]
    _ = (b.repr x).Sum fun j c => algebraMap R Rₛ c • Finsupp.single j 1 i := by
      simp_rw [← b.localization_localization_apply Rₛ S Aₛ, map_finsupp_sum, LinearEquiv.map_smul,
        Basis.repr_self, Finsupp.sum_apply, Finsupp.smul_apply]
    _ = _ :=
      (Finset.sum_eq_single i (fun j _ hj => by simp [hj]) fun hi => by
        simp [finsupp.not_mem_support_iff.mp hi])
    _ = algebraMap R Rₛ (b.repr x i) := by simp [Algebra.smul_def]
    
#align basis.localization_localization_repr_algebra_map Basis.localizationLocalization_repr_algebraMap

end LocalizationLocalization

end Localization

section FractionRing

variable (R K : Type _) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable {V : Type _} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/- warning: linear_independent.iff_fraction_ring -> LinearIndependent.iff_fractionRing is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (K : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : Field.{u2} K] [_inst_3 : Algebra.{u1, u2} R K (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2)))] [_inst_4 : IsFractionRing.{u1, u2} R _inst_1 K (Field.toCommRing.{u2} K _inst_2) _inst_3] {V : Type.{u3}} [_inst_5 : AddCommGroup.{u3} V] [_inst_6 : Module.{u1, u3} R V (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)] [_inst_7 : Module.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)] [_inst_8 : IsScalarTower.{u1, u2, u3} R K V (SMulZeroClass.toHasSmul.{u1, u2} R K (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R K (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R K (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))))))))) (Module.toMulActionWithZero.{u1, u2} R K (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2)))))) (Algebra.toModule.{u1, u2} R K (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))) _inst_3))))) (SMulZeroClass.toHasSmul.{u2, u3} K V (AddZeroClass.toHasZero.{u3} V (AddMonoid.toAddZeroClass.{u3} V (AddCommMonoid.toAddMonoid.{u3} V (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)))) (SMulWithZero.toSmulZeroClass.{u2, u3} K V (MulZeroClass.toHasZero.{u2} K (MulZeroOneClass.toMulZeroClass.{u2} K (MonoidWithZero.toMulZeroOneClass.{u2} K (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))))))) (AddZeroClass.toHasZero.{u3} V (AddMonoid.toAddZeroClass.{u3} V (AddCommMonoid.toAddMonoid.{u3} V (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)))) (MulActionWithZero.toSMulWithZero.{u2, u3} K V (Semiring.toMonoidWithZero.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2)))) (AddZeroClass.toHasZero.{u3} V (AddMonoid.toAddZeroClass.{u3} V (AddCommMonoid.toAddMonoid.{u3} V (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)))) (Module.toMulActionWithZero.{u2, u3} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_5) _inst_7)))) (SMulZeroClass.toHasSmul.{u1, u3} R V (AddZeroClass.toHasZero.{u3} V (AddMonoid.toAddZeroClass.{u3} V (AddCommMonoid.toAddMonoid.{u3} V (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)))) (SMulWithZero.toSmulZeroClass.{u1, u3} R V (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u3} V (AddMonoid.toAddZeroClass.{u3} V (AddCommMonoid.toAddMonoid.{u3} V (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)))) (MulActionWithZero.toSMulWithZero.{u1, u3} R V (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u3} V (AddMonoid.toAddZeroClass.{u3} V (AddCommMonoid.toAddMonoid.{u3} V (AddCommGroup.toAddCommMonoid.{u3} V _inst_5)))) (Module.toMulActionWithZero.{u1, u3} R V (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} V _inst_5) _inst_6))))] {ι : Type.{u4}} {b : ι -> V}, Iff (LinearIndependent.{u4, u1, u3} ι R V b (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} V _inst_5) _inst_6) (LinearIndependent.{u4, u2, u3} ι K V b (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_2))) (AddCommGroup.toAddCommMonoid.{u3} V _inst_5) _inst_7)
but is expected to have type
  forall (R : Type.{u3}) (K : Type.{u1}) [_inst_1 : CommRing.{u3} R] [_inst_2 : Field.{u1} K] [_inst_3 : Algebra.{u3, u1} R K (CommRing.toCommSemiring.{u3} R _inst_1) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2)))] [_inst_4 : IsFractionRing.{u3, u1} R _inst_1 K (Field.toCommRing.{u1} K _inst_2) _inst_3] {V : Type.{u2}} [_inst_5 : AddCommGroup.{u2} V] [_inst_6 : Module.{u3, u2} R V (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_5)] [_inst_7 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_5)] [_inst_8 : IsScalarTower.{u3, u1, u2} R K V (Algebra.toSMul.{u3, u1} R K (CommRing.toCommSemiring.{u3} R _inst_1) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2))) _inst_3) (SMulZeroClass.toSMul.{u1, u2} K V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_5))))) (SMulWithZero.toSMulZeroClass.{u1, u2} K V (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (Field.toSemifield.{u1} K _inst_2)))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_5))))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2)))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_5))))) (Module.toMulActionWithZero.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_5) _inst_7)))) (SMulZeroClass.toSMul.{u3, u2} R V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_5))))) (SMulWithZero.toSMulZeroClass.{u3, u2} R V (CommMonoidWithZero.toZero.{u3} R (CommSemiring.toCommMonoidWithZero.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_5))))) (MulActionWithZero.toSMulWithZero.{u3, u2} R V (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_5))))) (Module.toMulActionWithZero.{u3, u2} R V (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_5) _inst_6))))] {ι : Type.{u4}} {b : ι -> V}, Iff (LinearIndependent.{u4, u3, u2} ι R V b (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_5) _inst_6) (LinearIndependent.{u4, u1, u2} ι K V b (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_2))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_5) _inst_7)
Case conversion may be inaccurate. Consider using '#align linear_independent.iff_fraction_ring LinearIndependent.iff_fractionRingₓ'. -/
theorem LinearIndependent.iff_fractionRing {ι : Type _} {b : ι → V} :
    LinearIndependent R b ↔ LinearIndependent K b :=
  ⟨LinearIndependent.localization K R⁰,
    LinearIndependent.restrict_scalars (smul_left_injective R one_ne_zero)⟩
#align linear_independent.iff_fraction_ring LinearIndependent.iff_fractionRing

end FractionRing

