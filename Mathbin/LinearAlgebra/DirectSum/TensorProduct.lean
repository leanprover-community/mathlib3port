/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro

! This file was ported from Lean 3 source module linear_algebra.direct_sum.tensor_product
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.TensorProduct
import Mathbin.Algebra.DirectSum.Module

/-!
# Tensor products of direct sums

This file shows that taking `tensor_product`s commutes with taking `direct_sum`s in both arguments.
-/


section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type _) [CommRing R]

variable (ι₁ : Type _) (ι₂ : Type _)

variable [DecidableEq ι₁] [DecidableEq ι₂]

variable (M₁ : ι₁ → Type _) (M₂ : ι₂ → Type _)

variable [∀ i₁, AddCommGroup (M₁ i₁)] [∀ i₂, AddCommGroup (M₂ i₂)]

variable [∀ i₁, Module R (M₁ i₁)] [∀ i₂, Module R (M₂ i₂)]

/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
def directSum : ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[R] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 :=
  by
  refine'
      LinearEquiv.ofLinear
        (lift <|
          DirectSum.toModule R _ _ fun i₁ =>
            flip <|
              DirectSum.toModule R _ _ fun i₂ =>
                flip <| curry <| DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))
        (DirectSum.toModule R _ _ fun i => map (DirectSum.lof R _ _ _) (DirectSum.lof R _ _ _)) _
        _ <;>
    [ext (⟨i₁, i₂⟩x₁ x₂) : 4, ext (i₁ i₂ x₁ x₂) : 5]
  repeat'
    first
      |rw [compr₂_apply]|rw [comp_apply]|rw [id_apply]|rw [mk_apply]|rw [DirectSum.toModule_lof]|rw [map_tmul]|rw [lift.tmul]|rw [flip_apply]|rw [curry_apply]
#align tensor_product.direct_sum TensorProduct.directSum

@[simp]
theorem directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    directSum R ι₁ ι₂ M₁ M₂ (DirectSum.lof R ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
      DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) :=
  by simp [DirectSum]
#align tensor_product.direct_sum_lof_tmul_lof TensorProduct.directSum_lof_tmul_lof

end TensorProduct

end Ring

