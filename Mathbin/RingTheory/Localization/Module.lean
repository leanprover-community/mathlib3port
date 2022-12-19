/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.module
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `linear_independent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `basis.localization`: promote an `R`-basis `b` to an `Rₛ`-basis,
   where `Rₛ` is a localization of `R`
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

theorem LinearIndependent.localization {ι : Type _} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by 
  rw [linear_independent_iff'] at hli⊢
  intro s g hg i hi
  choose a g' hg' using IsLocalization.exist_integer_multiples S s g
  letI := fun i => Classical.propDecidable (i ∈ s)
  specialize hli s (fun i => if hi : i ∈ s then g' i hi else 0) _ i hi
  · rw [← @smul_zero _ M _ _ (a : R), ← hg, Finset.smul_sum]
    refine' Finset.sum_congr rfl fun i hi => _
    dsimp only
    rw [dif_pos hi, ← IsScalarTower.algebra_map_smul Rₛ, hg' i hi, smul_assoc]
    infer_instance
  refine' (IsLocalization.map_units Rₛ a).mul_right_eq_zero.mp _
  rw [← Algebra.smul_def, ← map_zero (algebraMap R Rₛ), ← hli]
  simp [hi, hg']
#align linear_independent.localization LinearIndependent.localization

end AddCommMonoid

section AddCommGroup

variable {M : Type _} [AddCommGroup M] [Module R M] [Module Rₛ M] [IsScalarTower R Rₛ M]

/-- Promote a basis for `M` over `R` to a basis for `M` over the localization `Rₛ` -/
noncomputable def Basis.localization {ι : Type _} (b : Basis ι R M) : Basis ι Rₛ M :=
  Basis.mk (b.LinearIndependent.Localization Rₛ S) <| by
    rw [← eq_top_iff, ← @Submodule.restrict_scalars_eq_top_iff Rₛ R, eq_top_iff, ← b.span_eq]
    apply Submodule.span_le_restrict_scalars
#align basis.localization Basis.localization

end AddCommGroup

end Localization

section FractionRing

variable (R K : Type _) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable {V : Type _} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem LinearIndependent.iff_fraction_ring {ι : Type _} {b : ι → V} :
    LinearIndependent R b ↔ LinearIndependent K b :=
  ⟨LinearIndependent.localization K R⁰,
    LinearIndependent.restrict_scalars (smul_left_injective R one_ne_zero)⟩
#align linear_independent.iff_fraction_ring LinearIndependent.iff_fraction_ring

end FractionRing

