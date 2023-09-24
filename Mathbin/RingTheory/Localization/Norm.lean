/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import RingTheory.Localization.Module
import RingTheory.Norm

#align_import ring_theory.localization.norm from "leanprover-community/mathlib"@"e8e130de9dba4ed6897183c3193c752ffadbcc77"

/-!

# Field/algebra norm and localization

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results on the combination of `algebra.norm` and `is_localization`.

## Main results

 * `algebra.norm_localization`: let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M`
  of `R S` respectively. Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R`
  if `S` is free as `R`-module

## Tags

field norm, algebra norm, localization

-/


open scoped nonZeroDivisors

variable (R : Type _) {S : Type _} [CommRing R] [CommRing S] [Algebra R S]

variable {Rₘ Sₘ : Type _} [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]

variable (M : Submonoid R)

variable [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

#print Algebra.norm_localization /-
/-- Let `S` be an extension of `R` and `Rₘ Sₘ` be localizations at `M` of `R S` respectively.
Then the norm of `a : Sₘ` over `Rₘ` is the norm of `a : S` over `R` if `S` is free as `R`-module.
-/
theorem Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a : S) :
    Algebra.norm Rₘ (algebraMap S Sₘ a) = algebraMap R Rₘ (Algebra.norm R a) :=
  by
  cases subsingleton_or_nontrivial R
  · haveI : Subsingleton Rₘ := Module.subsingleton R Rₘ
    simp
  let b := Module.Free.chooseBasis R S
  letI := Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localization_localization Rₘ M Sₘ),
    Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr
  ext i j
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Basis.localizationLocalization_apply, ← _root_.map_mul]
  apply Basis.localizationLocalization_repr_algebraMap
#align algebra.norm_localization Algebra.norm_localization
-/

