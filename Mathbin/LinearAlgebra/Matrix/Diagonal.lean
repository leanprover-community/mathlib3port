/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear_map
-/


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

namespace Matrix

section CommRing

variable {n : Type _} [Fintype n] [DecidableEq n] {R : Type v} [CommRing R]

theorem proj_diagonal (i : n) (w : n → R) : (proj i).comp (toLin' (diagonal w)) = w i • proj i :=
  LinearMap.ext fun j => mul_vec_diagonal _ _ _

theorem diagonal_comp_std_basis (w : n → R) (i : n) :
    (diagonal w).toLin'.comp (LinearMap.stdBasis R (fun _ : n => R) i) =
      w i • LinearMap.stdBasis R (fun _ : n => R) i :=
  LinearMap.ext fun x => (diagonal_mul_vec_single w _ _).trans (Pi.single_smul' i (w i) x)

theorem diagonal_to_lin' (w : n → R) : (diagonal w).toLin' = LinearMap.pi fun i => w i • LinearMap.proj i :=
  LinearMap.ext fun v => funext fun i => mul_vec_diagonal _ _ _

end CommRing

section Field

variable {m n : Type _} [Fintype m] [Fintype n]

variable {K : Type u} [Field K]

-- maybe try to relax the universe constraint
theorem ker_diagonal_to_lin' [DecidableEq m] (w : m → K) :
    ker (diagonal w).toLin' = ⨆ i ∈ { i | w i = 0 }, Range (LinearMap.stdBasis K (fun i => K) i) := by
  rw [← comap_bot, ← infi_ker_proj, comap_infi]
  have := fun i : m => ker_comp (to_lin' (diagonal w)) (proj i)
  simp only [comap_infi, ← this, proj_diagonal, ker_smul']
  have : univ ⊆ { i : m | w i = 0 } ∪ { i : m | w i = 0 }ᶜ := by rw [Set.union_compl_self]
  exact (supr_range_std_basis_eq_infi_ker_proj K (fun i : m => K) disjointComplRight this (Set.to_finite _)).symm

theorem range_diagonal [DecidableEq m] (w : m → K) :
    (diagonal w).toLin'.range = ⨆ i ∈ { i | w i ≠ 0 }, (LinearMap.stdBasis K (fun i => K) i).range := by
  dsimp only [mem_set_of_eq]
  rw [← map_top, ← supr_range_std_basis, map_supr]
  congr
  funext i
  rw [← LinearMap.range_comp, diagonal_comp_std_basis, ← range_smul']

theorem rank_diagonal [DecidableEq m] [DecidableEq K] (w : m → K) :
    rank (diagonal w).toLin' = Fintype.card { i // w i ≠ 0 } := by
  have hu : univ ⊆ { i : m | w i = 0 }ᶜ ∪ { i : m | w i = 0 } := by rw [Set.compl_union_self]
  have hd : Disjoint { i : m | w i ≠ 0 } { i : m | w i = 0 } := disjointComplLeft
  have B₁ := supr_range_std_basis_eq_infi_ker_proj K (fun i : m => K) hd hu (Set.to_finite _)
  have B₂ := @infi_ker_proj_equiv K _ _ (fun i : m => K) _ _ _ _ (by simp <;> infer_instance) hd hu
  rw [rank, range_diagonal, B₁, ← @dim_fun' K]
  apply LinearEquiv.dim_eq
  apply B₂

end Field

end Matrix

