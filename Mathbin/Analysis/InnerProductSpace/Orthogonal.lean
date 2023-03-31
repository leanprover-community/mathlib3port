/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.orthogonal
! leanprover-community/mathlib commit 6e272cd89fa32c72a25dbefd319394c48dce1576
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.Convex.Uniform
import Mathbin.Analysis.NormedSpace.Completion
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.LinearAlgebra.BilinearForm
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
Some of the more subtle results about the orthogonal complement are delayed to
`analysis.inner_product_space.projection`.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.
-/


variable {𝕜 E F : Type _} [IsROrC 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace Submodule

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def orthogonal : Submodule 𝕜 E
    where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' x y hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, MulZeroClass.mul_zero]
#align submodule.orthogonal Submodule.orthogonal

-- mathport name: «expr ᗮ»
notation:1200 K "ᗮ" => orthogonal K

/-- When a vector is in `Kᗮ`. -/
theorem mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl
#align submodule.mem_orthogonal Submodule.mem_orthogonal

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 := by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]
#align submodule.mem_orthogonal' Submodule.mem_orthogonal'

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu
#align submodule.inner_right_of_mem_orthogonal Submodule.inner_right_of_mem_orthogonal

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 := by
  rw [inner_eq_zero_symm] <;> exact inner_right_of_mem_orthogonal hu hv
#align submodule.inner_left_of_mem_orthogonal Submodule.inner_left_of_mem_orthogonal

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
theorem mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 :=
  by
  refine' ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), _⟩
  intro hv w hw
  rw [mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]
#align submodule.mem_orthogonal_singleton_iff_inner_right Submodule.mem_orthogonal_singleton_iff_inner_right

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 := by
  rw [mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]
#align submodule.mem_orthogonal_singleton_iff_inner_left Submodule.mem_orthogonal_singleton_iff_inner_left

theorem sub_mem_orthogonal_of_inner_left {x y : E} (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ :=
  by
  rw [mem_orthogonal']
  intro u hu
  rw [inner_sub_left, sub_eq_zero]
  exact h ⟨u, hu⟩
#align submodule.sub_mem_orthogonal_of_inner_left Submodule.sub_mem_orthogonal_of_inner_left

theorem sub_mem_orthogonal_of_inner_right {x y : E} (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) :
    x - y ∈ Kᗮ := by
  intro u hu
  rw [inner_sub_right, sub_eq_zero]
  exact h ⟨u, hu⟩
#align submodule.sub_mem_orthogonal_of_inner_right Submodule.sub_mem_orthogonal_of_inner_right

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ :=
  by
  rw [eq_bot_iff]
  intro x
  rw [mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)
#align submodule.inf_orthogonal_eq_bot Submodule.inf_orthogonal_eq_bot

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem orthogonal_disjoint : Disjoint K Kᗮ := by simp [disjoint_iff, K.inf_orthogonal_eq_bot]
#align submodule.orthogonal_disjoint Submodule.orthogonal_disjoint

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL 𝕜 (v : E)) :=
  by
  apply le_antisymm
  · rw [le_infᵢ_iff]
    rintro ⟨v, hv⟩ w hw
    simpa using hw _ hv
  · intro v hv w hw
    simp only [mem_infi] at hv
    exact hv ⟨w, hw⟩
#align submodule.orthogonal_eq_inter Submodule.orthogonal_eq_inter

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem isClosed_orthogonal : IsClosed (Kᗮ : Set E) :=
  by
  rw [orthogonal_eq_inter K]
  have := fun v : K => ContinuousLinearMap.isClosed_ker (innerSL 𝕜 (v : E))
  convert isClosed_interᵢ this
  simp only [infi_coe]
#align submodule.is_closed_orthogonal Submodule.isClosed_orthogonal

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.isClosed_orthogonal.completeSpace_coe

variable (𝕜 E)

/-- `orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
theorem orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ orthogonal orthogonal := fun K₁ K₂ =>
  ⟨fun h v hv u hu => inner_left_of_mem_orthogonal hv (h hu), fun h v hv u hu =>
    inner_left_of_mem_orthogonal hv (h hu)⟩
#align submodule.orthogonal_gc Submodule.orthogonal_gc

variable {𝕜 E}

/-- `orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (orthogonal_gc 𝕜 E).monotone_l h
#align submodule.orthogonal_le Submodule.orthogonal_le

/-- `orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  orthogonal_le (orthogonal_le h)
#align submodule.orthogonal_orthogonal_monotone Submodule.orthogonal_orthogonal_monotone

/-- `K` is contained in `Kᗮᗮ`. -/
theorem le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (orthogonal_gc 𝕜 E).le_u_l _
#align submodule.le_orthogonal_orthogonal Submodule.le_orthogonal_orthogonal

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (orthogonal_gc 𝕜 E).l_sup.symm
#align submodule.inf_orthogonal Submodule.inf_orthogonal

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem infᵢ_orthogonal {ι : Type _} (K : ι → Submodule 𝕜 E) : (⨅ i, (K i)ᗮ) = (supᵢ K)ᗮ :=
  (orthogonal_gc 𝕜 E).l_supᵢ.symm
#align submodule.infi_orthogonal Submodule.infᵢ_orthogonal

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem Inf_orthogonal (s : Set <| Submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (supₛ s)ᗮ :=
  (orthogonal_gc 𝕜 E).l_supₛ.symm
#align submodule.Inf_orthogonal Submodule.Inf_orthogonal

@[simp]
theorem top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ :=
  by
  ext
  rw [mem_bot, mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x mem_top),
      by
      rintro rfl
      simp⟩
#align submodule.top_orthogonal_eq_bot Submodule.top_orthogonal_eq_bot

@[simp]
theorem bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ :=
  by
  rw [← top_orthogonal_eq_bot, eq_top_iff]
  exact le_orthogonal_orthogonal ⊤
#align submodule.bot_orthogonal_eq_top Submodule.bot_orthogonal_eq_top

@[simp]
theorem orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ :=
  by
  refine'
    ⟨_, by
      rintro rfl
      exact bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this
#align submodule.orthogonal_eq_top_iff Submodule.orthogonal_eq_top_iff

theorem orthogonalFamily_self :
    OrthogonalFamily 𝕜 (fun b => ↥(cond b K Kᗮ)) fun b => (cond b K Kᗮ).subtypeₗᵢ
  | tt, tt => absurd rfl
  | tt, ff => fun _ x y => inner_right_of_mem_orthogonal x.Prop y.Prop
  | ff, tt => fun _ x y => inner_left_of_mem_orthogonal y.Prop x.Prop
  | ff, ff => absurd rfl
#align submodule.orthogonal_family_self Submodule.orthogonalFamily_self

end Submodule

