/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.matrix.rank
! leanprover-community/mathlib commit 45ce3929e3bf9a086a216feea3b1ab6c14bf0e67
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

-/


open Matrix

namespace Matrix

open FiniteDimensional

variable {m n o R : Type _} [m_fin : Fintype m] [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o] [CommRing R]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank (A : Matrix m n R) : ℕ :=
  finrank R A.toLin'.range
#align matrix.rank Matrix.rank

@[simp]
theorem rank_one [StrongRankCondition R] : rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank, to_lin'_one, LinearMap.range_id, finrank_top, finrank_pi]
#align matrix.rank_one Matrix.rank_one

@[simp]
theorem rank_zero [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank, LinearEquiv.map_zero, LinearMap.range_zero, finrank_bot]
#align matrix.rank_zero Matrix.rank_zero

theorem rank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.rank ≤ Fintype.card n :=
  by
  haveI : Module.Finite R (n → R) := Module.Finite.pi
  haveI : Module.Free R (n → R) := Module.Free.pi _ _
  exact A.to_lin'.finrank_range_le.trans_eq (finrank_pi _)
#align matrix.rank_le_card_width Matrix.rank_le_card_width

theorem rank_le_width [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ n :=
  A.rank_le_card_width.trans <| (Fintype.card_fin n).le
#align matrix.rank_le_width Matrix.rank_le_width

theorem rank_mul_le [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A ⬝ B).rank ≤ A.rank := by
  rw [rank, rank, to_lin'_mul]
  refine' Cardinal.toNat_le_of_le_of_lt_aleph0 _ (LinearMap.rank_comp_le_left _ _)
  rw [← Cardinal.lift_lt_aleph0]
  have := lift_rank_range_le A.to_lin'
  rw [rank_fun', Cardinal.lift_natCast] at this
  exact this.trans_lt (Cardinal.nat_lt_aleph0 (Fintype.card n))
#align matrix.rank_mul_le Matrix.rank_mul_le

theorem rank_unit [StrongRankCondition R] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n :=
  by
  refine' le_antisymm (rank_le_card_width A) _
  have := rank_mul_le (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← mul_eq_mul, ← Units.val_mul, mul_inv_self, Units.val_one, rank_one] at this
#align matrix.rank_unit Matrix.rank_unit

theorem rank_of_isUnit [StrongRankCondition R] (A : Matrix n n R) (h : IsUnit A) :
    A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A
#align matrix.rank_of_is_unit Matrix.rank_of_isUnit

include m_fin

theorem rank_eq_finrank_range_toLin {M₁ M₂ : Type _} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂] (A : Matrix m n R) (v₁ : Basis m R M₁) (v₂ : Basis n R M₂) :
    A.rank = finrank R (toLin v₂ v₁ A).range :=
  by
  let e₁ := (Pi.basisFun R m).Equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).Equiv v₂ (Equiv.refl _)
  have range_e₂ : (e₂ : (n → R) →ₗ[R] M₂).range = ⊤ :=
    by
    rw [LinearMap.range_eq_top]
    exact e₂.surjective
  refine' LinearEquiv.finrank_eq (e₁.of_submodules _ _ _)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (to_lin v₂ v₁ A) range_e₂]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := to_lin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [to_lin_eq_to_lin'] at aux₁
  rw [Pi.basisFun_apply, LinearMap.coe_stdBasis] at aux₁ aux₂
  simp only [LinearMap.comp_apply, e₁, e₂, LinearEquiv.coe_coe, Equiv.refl_apply, aux₁, aux₂,
    LinearMap.coe_single, to_lin_self, LinearEquiv.map_sum, LinearEquiv.map_smul, Basis.equiv_apply]
#align matrix.rank_eq_finrank_range_to_lin Matrix.rank_eq_finrank_range_toLin

theorem rank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.rank ≤ Fintype.card m :=
  by
  haveI : Module.Finite R (m → R) := Module.Finite.pi
  haveI : Module.Free R (m → R) := Module.Free.pi _ _
  exact (Submodule.finrank_le _).trans (finrank_pi R).le
#align matrix.rank_le_card_height Matrix.rank_le_card_height

omit m_fin

theorem rank_le_height [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ m :=
  A.rank_le_card_height.trans <| (Fintype.card_fin m).le
#align matrix.rank_le_height Matrix.rank_le_height

end Matrix

