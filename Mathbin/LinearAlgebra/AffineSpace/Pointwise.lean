/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import LinearAlgebra.AffineSpace.AffineSubspace

#align_import linear_algebra.affine_space.pointwise from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-! # Pointwise instances on `affine_subspace`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the additive action `affine_subspace.pointwise_add_action` in the
`pointwise` locale.

-/


open scoped Affine Pointwise

open Set

namespace AffineSubspace

variable {k : Type _} [Ring k]

variable {V P V₁ P₁ V₂ P₂ : Type _}

variable [AddCommGroup V] [Module k V] [affine_space V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

#print AffineSubspace.pointwiseAddAction /-
/-- The additive action on an affine subspace corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseAddAction : AddAction V (AffineSubspace k P)
    where
  vadd x S := S.map (AffineEquiv.constVAdd k P x)
  zero_vadd p := ((congr_arg fun f => p.map f) <| AffineMap.ext <| zero_vadd _).trans p.map_id
  add_vadd x y p :=
    ((congr_arg fun f => p.map f) <| AffineMap.ext <| add_vadd _ _).trans (p.map_map _ _).symm
#align affine_subspace.pointwise_add_action AffineSubspace.pointwiseAddAction
-/

scoped[Pointwise] attribute [instance] AffineSubspace.pointwiseAddAction

open scoped Pointwise

#print AffineSubspace.coe_pointwise_vadd /-
@[simp]
theorem coe_pointwise_vadd (v : V) (s : AffineSubspace k P) :
    ((v +ᵥ s : AffineSubspace k P) : Set P) = v +ᵥ s :=
  rfl
#align affine_subspace.coe_pointwise_vadd AffineSubspace.coe_pointwise_vadd
-/

#print AffineSubspace.vadd_mem_pointwise_vadd_iff /-
theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s :=
  vadd_mem_vadd_set_iff
#align affine_subspace.vadd_mem_pointwise_vadd_iff AffineSubspace.vadd_mem_pointwise_vadd_iff
-/

#print AffineSubspace.pointwise_vadd_bot /-
theorem pointwise_vadd_bot (v : V) : v +ᵥ (⊥ : AffineSubspace k P) = ⊥ := by simp [SetLike.ext'_iff]
#align affine_subspace.pointwise_vadd_bot AffineSubspace.pointwise_vadd_bot
-/

#print AffineSubspace.pointwise_vadd_direction /-
theorem pointwise_vadd_direction (v : V) (s : AffineSubspace k P) :
    (v +ᵥ s).direction = s.direction := by
  unfold VAdd.vadd
  rw [map_direction]
  exact Submodule.map_id _
#align affine_subspace.pointwise_vadd_direction AffineSubspace.pointwise_vadd_direction
-/

#print AffineSubspace.pointwise_vadd_span /-
theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) :=
  map_span _ s
#align affine_subspace.pointwise_vadd_span AffineSubspace.pointwise_vadd_span
-/

#print AffineSubspace.map_pointwise_vadd /-
theorem map_pointwise_vadd (f : P₁ →ᵃ[k] P₂) (v : V₁) (s : AffineSubspace k P₁) :
    (v +ᵥ s).map f = f.linear v +ᵥ s.map f :=
  by
  unfold VAdd.vadd
  rw [map_map, map_map]
  congr 1
  ext
  exact f.map_vadd _ _
#align affine_subspace.map_pointwise_vadd AffineSubspace.map_pointwise_vadd
-/

end AffineSubspace

