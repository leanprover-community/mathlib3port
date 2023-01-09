/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.matrix.rank
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `matrix.rank_eq_finrank_range_to_lin`.

## Main declarations

* `matrix.rank`: the rank of a matrix

## TODO

* Show that `matrix.rank` is equal to the row-rank and column-rank
* Generalize away from fields

-/


open Matrix

namespace Matrix

open FiniteDimensional

variable {m n o K : Type _} [m_fin : Fintype m] [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o] [Field K]

variable (A : Matrix m n K)

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank : ℕ :=
  finrank K A.toLin'.range
#align matrix.rank Matrix.rank

@[simp]
theorem rank_one : rank (1 : Matrix n n K) = Fintype.card n := by
  rw [rank, to_lin'_one, LinearMap.range_id, finrank_top, Module.Free.finrank_pi]
#align matrix.rank_one Matrix.rank_one

@[simp]
theorem rank_zero : rank (0 : Matrix n n K) = 0 := by
  rw [rank, LinearEquiv.map_zero, LinearMap.range_zero, finrank_bot]
#align matrix.rank_zero Matrix.rank_zero

theorem rank_le_card_width : A.rank ≤ Fintype.card n :=
  by
  convert le_of_add_le_left A.to_lin'.finrank_range_add_finrank_ker.le
  exact (Module.Free.finrank_pi K).symm
#align matrix.rank_le_card_width Matrix.rank_le_card_width

theorem rank_le_width {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : A.rank ≤ n :=
  A.rank_le_card_width.trans <| (Fintype.card_fin n).le
#align matrix.rank_le_width Matrix.rank_le_width

theorem rank_mul_le (B : Matrix n o K) : (A ⬝ B).rank ≤ A.rank :=
  by
  refine' LinearMap.finrank_le_finrank_of_injective (Submodule.of_le_injective _)
  rw [to_lin'_mul]
  exact LinearMap.range_comp_le_range _ _
#align matrix.rank_mul_le Matrix.rank_mul_le

theorem rank_unit (A : (Matrix n n K)ˣ) : (A : Matrix n n K).rank = Fintype.card n :=
  by
  refine' le_antisymm (rank_le_card_width A) _
  have := rank_mul_le (A : Matrix n n K) (↑A⁻¹ : Matrix n n K)
  rwa [← mul_eq_mul, ← Units.val_mul, mul_inv_self, Units.val_one, rank_one] at this
#align matrix.rank_unit Matrix.rank_unit

theorem rank_of_is_unit (A : Matrix n n K) (h : IsUnit A) : A.rank = Fintype.card n :=
  by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A
#align matrix.rank_of_is_unit Matrix.rank_of_is_unit

include m_fin

theorem rank_eq_finrank_range_to_lin {M₁ M₂ : Type _} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module K M₁] [Module K M₂] (v₁ : Basis m K M₁) (v₂ : Basis n K M₂) :
    A.rank = finrank K (toLin v₂ v₁ A).range :=
  by
  let e₁ := (Pi.basisFun K m).Equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun K n).Equiv v₂ (Equiv.refl _)
  have range_e₂ : (e₂ : (n → K) →ₗ[K] M₂).range = ⊤ :=
    by
    rw [LinearMap.range_eq_top]
    exact e₂.surjective
  refine' LinearEquiv.finrank_eq (e₁.of_submodules _ _ _)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (to_lin v₂ v₁ A) range_e₂]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := to_lin_self (Pi.basisFun K n) (Pi.basisFun K m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun K n) i v₂
  rw [to_lin_eq_to_lin'] at aux₁
  rw [Pi.basis_fun_apply, LinearMap.coe_std_basis] at aux₁ aux₂
  simp only [LinearMap.comp_apply, e₁, e₂, LinearEquiv.coe_coe, Equiv.refl_apply, aux₁, aux₂,
    LinearMap.coe_single, to_lin_self, LinearEquiv.map_sum, LinearEquiv.map_smul, Basis.equiv_apply]
#align matrix.rank_eq_finrank_range_to_lin Matrix.rank_eq_finrank_range_to_lin

theorem rank_le_card_height : A.rank ≤ Fintype.card m :=
  (Submodule.finrank_le _).trans (Module.Free.finrank_pi K).le
#align matrix.rank_le_card_height Matrix.rank_le_card_height

omit m_fin

theorem rank_le_height {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : A.rank ≤ m :=
  A.rank_le_card_height.trans <| (Fintype.card_fin m).le
#align matrix.rank_le_height Matrix.rank_le_height

end Matrix

