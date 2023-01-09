/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module analysis.convex.side
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Between
import Mathbin.Analysis.Convex.Topology
import Mathbin.Analysis.Normed.Group.AddTorsor

/-!
# Sides of affine subspaces

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.w_same_side x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.s_same_side x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.w_opp_side x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.s_opp_side x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/


variable {R V V' P P' : Type _}

open AffineEquiv AffineMap

namespace AffineSubspace

section StrictOrderedCommRing

variable [StrictOrderedCommRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

include V

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (p₁ p₂ «expr ∈ » s) -/
/-- The points `x` and `y` are weakly on the same side of `s`. -/
def WSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ (p₁ : _)(_ : p₁ ∈ s)(p₂ : _)(_ : p₂ ∈ s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
#align affine_subspace.w_same_side AffineSubspace.WSameSide

/-- The points `x` and `y` are strictly on the same side of `s`. -/
def SSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WSameSide x y ∧ x ∉ s ∧ y ∉ s
#align affine_subspace.s_same_side AffineSubspace.SSameSide

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (p₁ p₂ «expr ∈ » s) -/
/-- The points `x` and `y` are weakly on opposite sides of `s`. -/
def WOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ (p₁ : _)(_ : p₁ ∈ s)(p₂ : _)(_ : p₂ ∈ s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
#align affine_subspace.w_opp_side AffineSubspace.WOppSide

/-- The points `x` and `y` are strictly on opposite sides of `s`. -/
def SOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WOppSide x y ∧ x ∉ s ∧ y ∉ s
#align affine_subspace.s_opp_side AffineSubspace.SOppSide

include V'

theorem WSameSide.map {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WSameSide (f x) (f y) :=
  by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine' ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩
  simp_rw [← linear_map_vsub]
  exact h.map f.linear
#align affine_subspace.w_same_side.map AffineSubspace.WSameSide.map

theorem Function.Injective.w_same_side_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  by
  refine' ⟨fun h => _, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine' ⟨p₁, hp₁, p₂, hp₂, _⟩
  simp_rw [← linear_map_vsub, (f.linear_injective_iff.2 hf).same_ray_map_iff] at h
  exact h
#align function.injective.w_same_side_map_iff Function.Injective.w_same_side_map_iff

theorem Function.Injective.s_same_side_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).SSameSide (f x) (f y) ↔ s.SSameSide x y := by
  simp_rw [s_same_side, hf.w_same_side_map_iff, mem_map_iff_mem_of_injective hf]
#align function.injective.s_same_side_map_iff Function.Injective.s_same_side_map_iff

@[simp]
theorem AffineEquiv.w_same_side_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).w_same_side_map_iff
#align affine_equiv.w_same_side_map_iff AffineEquiv.w_same_side_map_iff

@[simp]
theorem AffineEquiv.s_same_side_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SSameSide (f x) (f y) ↔ s.SSameSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).s_same_side_map_iff
#align affine_equiv.s_same_side_map_iff AffineEquiv.s_same_side_map_iff

theorem WOppSide.map {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WOppSide (f x) (f y) :=
  by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine' ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩
  simp_rw [← linear_map_vsub]
  exact h.map f.linear
#align affine_subspace.w_opp_side.map AffineSubspace.WOppSide.map

theorem Function.Injective.w_opp_side_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  by
  refine' ⟨fun h => _, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine' ⟨p₁, hp₁, p₂, hp₂, _⟩
  simp_rw [← linear_map_vsub, (f.linear_injective_iff.2 hf).same_ray_map_iff] at h
  exact h
#align function.injective.w_opp_side_map_iff Function.Injective.w_opp_side_map_iff

theorem Function.Injective.s_opp_side_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).SOppSide (f x) (f y) ↔ s.SOppSide x y := by
  simp_rw [s_opp_side, hf.w_opp_side_map_iff, mem_map_iff_mem_of_injective hf]
#align function.injective.s_opp_side_map_iff Function.Injective.s_opp_side_map_iff

@[simp]
theorem AffineEquiv.w_opp_side_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).w_opp_side_map_iff
#align affine_equiv.w_opp_side_map_iff AffineEquiv.w_opp_side_map_iff

@[simp]
theorem AffineEquiv.s_opp_side_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SOppSide (f x) (f y) ↔ s.SOppSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).s_opp_side_map_iff
#align affine_equiv.s_opp_side_map_iff AffineEquiv.s_opp_side_map_iff

omit V'

theorem WSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.some, h.some_spec.some⟩
#align affine_subspace.w_same_side.nonempty AffineSubspace.WSameSide.nonempty

theorem SSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.some, h.1.some_spec.some⟩
#align affine_subspace.s_same_side.nonempty AffineSubspace.SSameSide.nonempty

theorem WOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.some, h.some_spec.some⟩
#align affine_subspace.w_opp_side.nonempty AffineSubspace.WOppSide.nonempty

theorem SOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.some, h.1.some_spec.some⟩
#align affine_subspace.s_opp_side.nonempty AffineSubspace.SOppSide.nonempty

theorem SSameSide.wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    s.WSameSide x y :=
  h.1
#align affine_subspace.s_same_side.w_same_side AffineSubspace.SSameSide.wSameSide

theorem SSameSide.left_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : x ∉ s :=
  h.2.1
#align affine_subspace.s_same_side.left_not_mem AffineSubspace.SSameSide.left_not_mem

theorem SSameSide.right_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : y ∉ s :=
  h.2.2
#align affine_subspace.s_same_side.right_not_mem AffineSubspace.SSameSide.right_not_mem

theorem SOppSide.wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    s.WOppSide x y :=
  h.1
#align affine_subspace.s_opp_side.w_opp_side AffineSubspace.SOppSide.wOppSide

theorem SOppSide.left_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : x ∉ s :=
  h.2.1
#align affine_subspace.s_opp_side.left_not_mem AffineSubspace.SOppSide.left_not_mem

theorem SOppSide.right_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : y ∉ s :=
  h.2.2
#align affine_subspace.s_opp_side.right_not_mem AffineSubspace.SOppSide.right_not_mem

theorem w_same_side_comm {s : AffineSubspace R P} {x y : P} : s.WSameSide x y ↔ s.WSameSide y x :=
  ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩, fun ⟨p₁, hp₁, p₂, hp₂, h⟩ =>
    ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩
#align affine_subspace.w_same_side_comm AffineSubspace.w_same_side_comm

alias w_same_side_comm ↔ w_same_side.symm _

theorem s_same_side_comm {s : AffineSubspace R P} {x y : P} : s.SSameSide x y ↔ s.SSameSide y x :=
  by rw [s_same_side, s_same_side, w_same_side_comm, and_comm' (x ∉ s)]
#align affine_subspace.s_same_side_comm AffineSubspace.s_same_side_comm

alias s_same_side_comm ↔ s_same_side.symm _

theorem w_opp_side_comm {s : AffineSubspace R P} {x y : P} : s.WOppSide x y ↔ s.WOppSide y x :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
    rwa [same_ray_comm, ← same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
    rwa [same_ray_comm, ← same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
#align affine_subspace.w_opp_side_comm AffineSubspace.w_opp_side_comm

alias w_opp_side_comm ↔ w_opp_side.symm _

theorem s_opp_side_comm {s : AffineSubspace R P} {x y : P} : s.SOppSide x y ↔ s.SOppSide y x := by
  rw [s_opp_side, s_opp_side, w_opp_side_comm, and_comm' (x ∉ s)]
#align affine_subspace.s_opp_side_comm AffineSubspace.s_opp_side_comm

alias s_opp_side_comm ↔ s_opp_side.symm _

theorem not_w_same_side_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WSameSide x y := by
  simp [w_same_side, not_mem_bot]
#align affine_subspace.not_w_same_side_bot AffineSubspace.not_w_same_side_bot

theorem not_s_same_side_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SSameSide x y := fun h =>
  not_w_same_side_bot x y h.WSameSide
#align affine_subspace.not_s_same_side_bot AffineSubspace.not_s_same_side_bot

theorem not_w_opp_side_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WOppSide x y := by
  simp [w_opp_side, not_mem_bot]
#align affine_subspace.not_w_opp_side_bot AffineSubspace.not_w_opp_side_bot

theorem not_s_opp_side_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SOppSide x y := fun h =>
  not_w_opp_side_bot x y h.WOppSide
#align affine_subspace.not_s_opp_side_bot AffineSubspace.not_s_opp_side_bot

@[simp]
theorem w_same_side_self_iff {s : AffineSubspace R P} {x : P} :
    s.WSameSide x x ↔ (s : Set P).Nonempty :=
  ⟨fun h => h.Nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩
#align affine_subspace.w_same_side_self_iff AffineSubspace.w_same_side_self_iff

theorem s_same_side_self_iff {s : AffineSubspace R P} {x : P} :
    s.SSameSide x x ↔ (s : Set P).Nonempty ∧ x ∉ s :=
  ⟨fun ⟨h, hx, _⟩ => ⟨w_same_side_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ =>
    ⟨w_same_side_self_iff.2 h, hx, hx⟩⟩
#align affine_subspace.s_same_side_self_iff AffineSubspace.s_same_side_self_iff

theorem wSameSideOfLeftMem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WSameSide x y := by
  refine' ⟨x, hx, x, hx, _⟩
  simp
#align affine_subspace.w_same_side_of_left_mem AffineSubspace.wSameSideOfLeftMem

theorem wSameSideOfRightMem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WSameSide x y :=
  (wSameSideOfLeftMem x hy).symm
#align affine_subspace.w_same_side_of_right_mem AffineSubspace.wSameSideOfRightMem

theorem wOppSideOfLeftMem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) : s.WOppSide x y :=
  by
  refine' ⟨x, hx, x, hx, _⟩
  simp
#align affine_subspace.w_opp_side_of_left_mem AffineSubspace.wOppSideOfLeftMem

theorem wOppSideOfRightMem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) : s.WOppSide x y :=
  (wOppSideOfLeftMem x hy).symm
#align affine_subspace.w_opp_side_of_right_mem AffineSubspace.wOppSideOfRightMem

theorem w_same_side_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V}
    (hv : v ∈ s.direction) : s.WSameSide (v +ᵥ x) y ↔ s.WSameSide x y :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine'
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩
    rwa [vadd_vsub_vadd_cancel_left]
#align affine_subspace.w_same_side_vadd_left_iff AffineSubspace.w_same_side_vadd_left_iff

theorem w_same_side_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V}
    (hv : v ∈ s.direction) : s.WSameSide x (v +ᵥ y) ↔ s.WSameSide x y := by
  rw [w_same_side_comm, w_same_side_vadd_left_iff hv, w_same_side_comm]
#align affine_subspace.w_same_side_vadd_right_iff AffineSubspace.w_same_side_vadd_right_iff

theorem s_same_side_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V}
    (hv : v ∈ s.direction) : s.SSameSide (v +ᵥ x) y ↔ s.SSameSide x y := by
  rw [s_same_side, s_same_side, w_same_side_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
#align affine_subspace.s_same_side_vadd_left_iff AffineSubspace.s_same_side_vadd_left_iff

theorem s_same_side_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V}
    (hv : v ∈ s.direction) : s.SSameSide x (v +ᵥ y) ↔ s.SSameSide x y := by
  rw [s_same_side_comm, s_same_side_vadd_left_iff hv, s_same_side_comm]
#align affine_subspace.s_same_side_vadd_right_iff AffineSubspace.s_same_side_vadd_right_iff

theorem w_opp_side_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide (v +ᵥ x) y ↔ s.WOppSide x y :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine'
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩
    rwa [vadd_vsub_vadd_cancel_left]
#align affine_subspace.w_opp_side_vadd_left_iff AffineSubspace.w_opp_side_vadd_left_iff

theorem w_opp_side_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V}
    (hv : v ∈ s.direction) : s.WOppSide x (v +ᵥ y) ↔ s.WOppSide x y := by
  rw [w_opp_side_comm, w_opp_side_vadd_left_iff hv, w_opp_side_comm]
#align affine_subspace.w_opp_side_vadd_right_iff AffineSubspace.w_opp_side_vadd_right_iff

theorem s_opp_side_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide (v +ᵥ x) y ↔ s.SOppSide x y := by
  rw [s_opp_side, s_opp_side, w_opp_side_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
#align affine_subspace.s_opp_side_vadd_left_iff AffineSubspace.s_opp_side_vadd_left_iff

theorem s_opp_side_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V}
    (hv : v ∈ s.direction) : s.SOppSide x (v +ᵥ y) ↔ s.SOppSide x y := by
  rw [s_opp_side_comm, s_opp_side_vadd_left_iff hv, s_opp_side_comm]
#align affine_subspace.s_opp_side_vadd_right_iff AffineSubspace.s_opp_side_vadd_right_iff

theorem wSameSideSmulVsubVaddLeft {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
  rw [vadd_vsub]
  exact same_ray_nonneg_smul_left _ ht
#align affine_subspace.w_same_side_smul_vsub_vadd_left AffineSubspace.wSameSideSmulVsubVaddLeft

theorem wSameSideSmulVsubVaddRight {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wSameSideSmulVsubVaddLeft x hp₁ hp₂ ht).symm
#align affine_subspace.w_same_side_smul_vsub_vadd_right AffineSubspace.wSameSideSmulVsubVaddRight

theorem wSameSideLineMapLeft {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide (lineMap x y t) y :=
  wSameSideSmulVsubVaddLeft y h h ht
#align affine_subspace.w_same_side_line_map_left AffineSubspace.wSameSideLineMapLeft

theorem wSameSideLineMapRight {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide y (lineMap x y t) :=
  (wSameSideLineMapLeft y h ht).symm
#align affine_subspace.w_same_side_line_map_right AffineSubspace.wSameSideLineMapRight

theorem wOppSideSmulVsubVaddLeft {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
  rw [vadd_vsub, ← neg_neg t, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
  exact same_ray_nonneg_smul_left _ (neg_nonneg.2 ht)
#align affine_subspace.w_opp_side_smul_vsub_vadd_left AffineSubspace.wOppSideSmulVsubVaddLeft

theorem wOppSideSmulVsubVaddRight {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wOppSideSmulVsubVaddLeft x hp₁ hp₂ ht).symm
#align affine_subspace.w_opp_side_smul_vsub_vadd_right AffineSubspace.wOppSideSmulVsubVaddRight

theorem wOppSideLineMapLeft {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide (lineMap x y t) y :=
  wOppSideSmulVsubVaddLeft y h h ht
#align affine_subspace.w_opp_side_line_map_left AffineSubspace.wOppSideLineMapLeft

theorem wOppSideLineMapRight {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide y (lineMap x y t) :=
  (wOppSideLineMapLeft y h ht).symm
#align affine_subspace.w_opp_side_line_map_right AffineSubspace.wOppSideLineMapRight

theorem Wbtw.wSameSide₂₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hx : x ∈ s) :
    s.WSameSide y z := by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  exact w_same_side_line_map_left z hx ht0
#align wbtw.w_same_side₂₃ Wbtw.wSameSide₂₃

theorem Wbtw.wSameSide₃₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hx : x ∈ s) :
    s.WSameSide z y :=
  (h.wSameSide₂₃ hx).symm
#align wbtw.w_same_side₃₂ Wbtw.wSameSide₃₂

theorem Wbtw.wSameSide₁₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hz : z ∈ s) :
    s.WSameSide x y :=
  h.symm.wSameSide₃₂ hz
#align wbtw.w_same_side₁₂ Wbtw.wSameSide₁₂

theorem Wbtw.wSameSide₂₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hz : z ∈ s) :
    s.WSameSide y x :=
  h.symm.wSameSide₂₃ hz
#align wbtw.w_same_side₂₁ Wbtw.wSameSide₂₁

theorem Wbtw.wOppSide₁₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hy : y ∈ s) :
    s.WOppSide x z := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine' ⟨_, hy, _, hy, _⟩
  rcases ht1.lt_or_eq with (ht1' | rfl); swap; · simp
  rcases ht0.lt_or_eq with (ht0' | rfl); swap; · simp
  refine' Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', _⟩)
  simp_rw [line_map_apply, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev z x,
    vsub_self, zero_sub, ← neg_one_smul R (z -ᵥ x), ← add_smul, smul_neg, ← neg_smul, smul_smul]
  ring_nf
#align wbtw.w_opp_side₁₃ Wbtw.wOppSide₁₃

theorem Wbtw.wOppSide₃₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hy : y ∈ s) :
    s.WOppSide z x :=
  h.symm.wOppSide₁₃ hy
#align wbtw.w_opp_side₃₁ Wbtw.wOppSide₃₁

end StrictOrderedCommRing

section LinearOrderedField

variable [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

include V

variable {R}

@[simp]
theorem w_opp_side_self_iff {s : AffineSubspace R P} {x : P} : s.WOppSide x x ↔ x ∈ s :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    rw [add_comm, vsub_add_vsub_cancel, ← eq_vadd_iff_vsub_eq] at h₁
    rw [h₁]
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩
#align affine_subspace.w_opp_side_self_iff AffineSubspace.w_opp_side_self_iff

theorem not_s_opp_side_self (s : AffineSubspace R P) (x : P) : ¬s.SOppSide x x := by
  simp [s_opp_side]
#align affine_subspace.not_s_opp_side_self AffineSubspace.not_s_opp_side_self

theorem w_same_side_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WSameSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine' Or.inr ⟨p₂', hp₂', _⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine'
        Or.inr
          ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
            Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩
      rw [vsub_vadd_eq_vsub_sub, smul_sub, ← hr, smul_smul, mul_div_cancel' _ hr₂.ne.symm, ←
        smul_sub, vsub_sub_vsub_cancel_right]
  · rintro (h' | h')
    · exact w_same_side_of_left_mem y h'
    · exact ⟨p₁, h, h'⟩
#align affine_subspace.w_same_side_iff_exists_left AffineSubspace.w_same_side_iff_exists_left

theorem w_same_side_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WSameSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  rw [w_same_side_comm, w_same_side_iff_exists_left h]
  simp_rw [same_ray_comm]
#align affine_subspace.w_same_side_iff_exists_right AffineSubspace.w_same_side_iff_exists_right

theorem s_same_side_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  rw [s_same_side, and_comm', w_same_side_iff_exists_left h, and_assoc', and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]
#align affine_subspace.s_same_side_iff_exists_left AffineSubspace.s_same_side_iff_exists_left

theorem s_same_side_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  rw [s_same_side_comm, s_same_side_iff_exists_left h, ← and_assoc', and_comm' (y ∉ s), and_assoc']
  simp_rw [same_ray_comm]
#align affine_subspace.s_same_side_iff_exists_right AffineSubspace.s_same_side_iff_exists_right

theorem w_opp_side_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WOppSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine' Or.inr ⟨p₂', hp₂', _⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine'
        Or.inr
          ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
            Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩
      rw [vadd_vsub_assoc, smul_add, ← hr, smul_smul, neg_div, mul_neg,
        mul_div_cancel' _ hr₂.ne.symm, neg_smul, neg_add_eq_sub, ← smul_sub,
        vsub_sub_vsub_cancel_right]
  · rintro (h' | h')
    · exact w_opp_side_of_left_mem y h'
    · exact ⟨p₁, h, h'⟩
#align affine_subspace.w_opp_side_iff_exists_left AffineSubspace.w_opp_side_iff_exists_left

theorem w_opp_side_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WOppSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  rw [w_opp_side_comm, w_opp_side_iff_exists_left h]
  constructor
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine' Or.inr ⟨p, hp, _⟩
    rwa [same_ray_comm, ← same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine' Or.inr ⟨p, hp, _⟩
    rwa [same_ray_comm, ← same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
#align affine_subspace.w_opp_side_iff_exists_right AffineSubspace.w_opp_side_iff_exists_right

theorem s_opp_side_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  rw [s_opp_side, and_comm', w_opp_side_iff_exists_left h, and_assoc', and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]
#align affine_subspace.s_opp_side_iff_exists_left AffineSubspace.s_opp_side_iff_exists_left

theorem s_opp_side_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  rw [s_opp_side, and_comm', w_opp_side_iff_exists_right h, and_assoc', and_congr_right_iff,
    and_congr_right_iff]
  rintro hx hy
  rw [or_iff_right hy]
#align affine_subspace.s_opp_side_iff_exists_right AffineSubspace.s_opp_side_iff_exists_right

theorem WSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WSameSide x z :=
  by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [w_same_side_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  refine' fun h => False.elim _
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)
#align affine_subspace.w_same_side.trans AffineSubspace.WSameSide.trans

theorem WSameSide.transSSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SSameSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
#align affine_subspace.w_same_side.trans_s_same_side AffineSubspace.WSameSide.transSSameSide

theorem WSameSide.transWOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [w_opp_side_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  refine' fun h => False.elim _
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)
#align affine_subspace.w_same_side.trans_w_opp_side AffineSubspace.WSameSide.transWOppSide

theorem WSameSide.transSOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SOppSide y z) : s.WOppSide x z :=
  hxy.transWOppSide hyz.1 hyz.2.1
#align affine_subspace.w_same_side.trans_s_opp_side AffineSubspace.WSameSide.transSOppSide

theorem SSameSide.transWSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WSameSide y z) : s.WSameSide x z :=
  (hyz.symm.transSSameSide hxy.symm).symm
#align affine_subspace.s_same_side.trans_w_same_side AffineSubspace.SSameSide.transWSameSide

theorem SSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SSameSide y z) : s.SSameSide x z :=
  ⟨hxy.WSameSide.transSSameSide hyz, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_same_side.trans AffineSubspace.SSameSide.trans

theorem SSameSide.transWOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WOppSide y z) : s.WOppSide x z :=
  hxy.WSameSide.transWOppSide hyz hxy.2.2
#align affine_subspace.s_same_side.trans_w_opp_side AffineSubspace.SSameSide.transWOppSide

theorem SSameSide.transSOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SOppSide y z) : s.SOppSide x z :=
  ⟨hxy.transWOppSide hyz.1, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_same_side.trans_s_opp_side AffineSubspace.SSameSide.transSOppSide

theorem WOppSide.transWSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  (hyz.symm.transWOppSide hxy.symm hy).symm
#align affine_subspace.w_opp_side.trans_w_same_side AffineSubspace.WOppSide.transWSameSide

theorem WOppSide.transSSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SSameSide y z) : s.WOppSide x z :=
  hxy.transWSameSide hyz.1 hyz.2.1
#align affine_subspace.w_opp_side.trans_s_same_side AffineSubspace.WOppSide.transSSameSide

theorem WOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WSameSide x z :=
  by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [w_opp_side_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  rw [← same_ray_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hyz
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  refine' fun h => False.elim _
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h ▸ hp₂)
#align affine_subspace.w_opp_side.trans AffineSubspace.WOppSide.trans

theorem WOppSide.transSOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SOppSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
#align affine_subspace.w_opp_side.trans_s_opp_side AffineSubspace.WOppSide.transSOppSide

theorem SOppSide.transWSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WSameSide y z) : s.WOppSide x z :=
  (hyz.symm.transSOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_w_same_side AffineSubspace.SOppSide.transWSameSide

theorem SOppSide.transSSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SSameSide y z) : s.SOppSide x z :=
  (hyz.symm.transSOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_s_same_side AffineSubspace.SOppSide.transSSameSide

theorem SOppSide.transWOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WOppSide y z) : s.WSameSide x z :=
  (hyz.symm.transSOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_w_opp_side AffineSubspace.SOppSide.transWOppSide

theorem SOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SOppSide y z) : s.SSameSide x z :=
  ⟨hxy.transWOppSide hyz.1, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_opp_side.trans AffineSubspace.SOppSide.trans

theorem w_same_side_and_w_opp_side_iff {s : AffineSubspace R P} {x y : P} :
    s.WSameSide x y ∧ s.WOppSide x y ↔ x ∈ s ∨ y ∈ s :=
  by
  constructor
  · rintro ⟨hs, ho⟩
    rw [w_opp_side_comm] at ho
    by_contra h
    rw [not_or] at h
    exact h.1 (w_opp_side_self_iff.1 (hs.trans_w_opp_side ho h.2))
  · rintro (h | h)
    · exact ⟨w_same_side_of_left_mem y h, w_opp_side_of_left_mem y h⟩
    · exact ⟨w_same_side_of_right_mem x h, w_opp_side_of_right_mem x h⟩
#align affine_subspace.w_same_side_and_w_opp_side_iff AffineSubspace.w_same_side_and_w_opp_side_iff

theorem WSameSide.not_s_opp_side {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    ¬s.SOppSide x y := by
  intro ho
  have hxy := w_same_side_and_w_opp_side_iff.1 ⟨h, ho.1⟩
  rcases hxy with (hx | hy)
  · exact ho.2.1 hx
  · exact ho.2.2 hy
#align affine_subspace.w_same_side.not_s_opp_side AffineSubspace.WSameSide.not_s_opp_side

theorem SSameSide.not_w_opp_side {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.WOppSide x y := by
  intro ho
  have hxy := w_same_side_and_w_opp_side_iff.1 ⟨h.1, ho⟩
  rcases hxy with (hx | hy)
  · exact h.2.1 hx
  · exact h.2.2 hy
#align affine_subspace.s_same_side.not_w_opp_side AffineSubspace.SSameSide.not_w_opp_side

theorem SSameSide.not_s_opp_side {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.SOppSide x y := fun ho => h.not_w_opp_side ho.1
#align affine_subspace.s_same_side.not_s_opp_side AffineSubspace.SSameSide.not_s_opp_side

theorem WOppSide.not_s_same_side {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    ¬s.SSameSide x y := fun hs => hs.not_w_opp_side h
#align affine_subspace.w_opp_side.not_s_same_side AffineSubspace.WOppSide.not_s_same_side

theorem SOppSide.not_w_same_side {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.WSameSide x y := fun hs => hs.not_s_opp_side h
#align affine_subspace.s_opp_side.not_w_same_side AffineSubspace.SOppSide.not_w_same_side

theorem SOppSide.not_s_same_side {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.SSameSide x y := fun hs => h.not_w_same_side hs.1
#align affine_subspace.s_opp_side.not_s_same_side AffineSubspace.SOppSide.not_s_same_side

theorem w_opp_side_iff_exists_wbtw {s : AffineSubspace R P} {x y : P} :
    s.WOppSide x y ↔ ∃ p ∈ s, Wbtw R x p y :=
  by
  refine' ⟨fun h => _, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [h]
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [← h]
    exact ⟨p₂, hp₂, wbtw_self_right _ _ _⟩
  · refine' ⟨line_map x y (r₂ / (r₁ + r₂)), _, _⟩
    · rw [line_map_apply, ← vsub_vadd x p₁, ← vsub_vadd y p₂, vsub_vadd_eq_vsub_sub,
        vadd_vsub_assoc, ← vadd_assoc, vadd_eq_add]
      convert s.smul_vsub_vadd_mem (r₂ / (r₁ + r₂)) hp₂ hp₁ hp₁
      rw [add_comm (y -ᵥ p₂), smul_sub, smul_add, add_sub_assoc, add_assoc, add_right_eq_self,
        div_eq_inv_mul, ← neg_vsub_eq_vsub_rev, smul_neg, ← smul_smul, ← h, smul_smul, ← neg_smul, ←
        sub_smul, ← div_eq_inv_mul, ← div_eq_inv_mul, ← neg_div, ← sub_div, sub_eq_add_neg, ←
        neg_add, neg_div, div_self (Left.add_pos hr₁ hr₂).Ne.symm, neg_one_smul, neg_add_self]
    ·
      exact
        Set.mem_image_of_mem _
          ⟨div_nonneg hr₂.le (Left.add_pos hr₁ hr₂).le,
            div_le_one_of_le (le_add_of_nonneg_left hr₁.le) (Left.add_pos hr₁ hr₂).le⟩
#align affine_subspace.w_opp_side_iff_exists_wbtw AffineSubspace.w_opp_side_iff_exists_wbtw

theorem SOppSide.exists_sbtw {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ∃ p ∈ s, Sbtw R x p y :=
  by
  obtain ⟨p, hp, hw⟩ := w_opp_side_iff_exists_wbtw.1 h.w_opp_side
  refine' ⟨p, hp, hw, _, _⟩
  · rintro rfl
    exact h.2.1 hp
  · rintro rfl
    exact h.2.2 hp
#align affine_subspace.s_opp_side.exists_sbtw AffineSubspace.SOppSide.exists_sbtw

theorem Sbtw.sOppSideOfNotMemOfMem {s : AffineSubspace R P} {x y z : P} (h : Sbtw R x y z)
    (hx : x ∉ s) (hy : y ∈ s) : s.SOppSide x z :=
  by
  refine' ⟨h.wbtw.w_opp_side₁₃ hy, hx, fun hz => hx _⟩
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  rw [line_map_apply] at hy
  have ht : t ≠ 1 := by
    rintro rfl
    simpa [line_map_apply] using hyz
  have hy' := vsub_mem_direction hy hz
  rw [vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev z, ← neg_one_smul R (z -ᵥ x), ← add_smul, ←
    sub_eq_add_neg, s.direction.smul_mem_iff (sub_ne_zero_of_ne ht)] at hy'
  rwa [vadd_mem_iff_mem_of_mem_direction (Submodule.smul_mem _ _ hy')] at hy
#align sbtw.s_opp_side_of_not_mem_of_mem Sbtw.sOppSideOfNotMemOfMem

theorem sSameSideSmulVsubVaddLeft {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨w_same_side_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx _, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h
#align affine_subspace.s_same_side_smul_vsub_vadd_left AffineSubspace.sSameSideSmulVsubVaddLeft

theorem sSameSideSmulVsubVaddRight {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sSameSideSmulVsubVaddLeft hx hp₁ hp₂ ht).symm
#align affine_subspace.s_same_side_smul_vsub_vadd_right AffineSubspace.sSameSideSmulVsubVaddRight

theorem sSameSideLineMapLeft {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide (lineMap x y t) y :=
  sSameSideSmulVsubVaddLeft hy hx hx ht
#align affine_subspace.s_same_side_line_map_left AffineSubspace.sSameSideLineMapLeft

theorem sSameSideLineMapRight {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide y (lineMap x y t) :=
  (sSameSideLineMapLeft hx hy ht).symm
#align affine_subspace.s_same_side_line_map_right AffineSubspace.sSameSideLineMapRight

theorem sOppSideSmulVsubVaddLeft {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨w_opp_side_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx _, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h
#align affine_subspace.s_opp_side_smul_vsub_vadd_left AffineSubspace.sOppSideSmulVsubVaddLeft

theorem sOppSideSmulVsubVaddRight {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sOppSideSmulVsubVaddLeft hx hp₁ hp₂ ht).symm
#align affine_subspace.s_opp_side_smul_vsub_vadd_right AffineSubspace.sOppSideSmulVsubVaddRight

theorem sOppSideLineMapLeft {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide (lineMap x y t) y :=
  sOppSideSmulVsubVaddLeft hy hx hx ht
#align affine_subspace.s_opp_side_line_map_left AffineSubspace.sOppSideLineMapLeft

theorem sOppSideLineMapRight {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide y (lineMap x y t) :=
  (sOppSideLineMapLeft hx hy ht).symm
#align affine_subspace.s_opp_side_line_map_right AffineSubspace.sOppSideLineMapRight

theorem set_of_w_same_side_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ici 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Ici, mem_coe]
  constructor
  · rw [w_same_side_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine' ⟨0, p₂, le_refl _, hp₂, _⟩
      simp [h]
    · refine' ⟨r₁ / r₂, p₂, (div_pos hr₁ hr₂).le, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact w_same_side_smul_vsub_vadd_right x hp hp' ht
#align affine_subspace.set_of_w_same_side_eq_image2 AffineSubspace.set_of_w_same_side_eq_image2

theorem set_of_s_same_side_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ioi 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Ioi, mem_coe]
  constructor
  · rw [s_same_side_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h.symm ▸ hp₂))
    · refine' ⟨r₁ / r₂, p₂, div_pos hr₁ hr₂, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact s_same_side_smul_vsub_vadd_right hx hp hp' ht
#align affine_subspace.set_of_s_same_side_eq_image2 AffineSubspace.set_of_s_same_side_eq_image2

theorem set_of_w_opp_side_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iic 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Iic, mem_coe]
  constructor
  · rw [w_opp_side_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine' ⟨0, p₂, le_refl _, hp₂, _⟩
      simp [h]
    · refine' ⟨-r₁ / r₂, p₂, (div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂).le, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul, inv_mul_cancel hr₂.ne.symm,
        one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact w_opp_side_smul_vsub_vadd_right x hp hp' ht
#align affine_subspace.set_of_w_opp_side_eq_image2 AffineSubspace.set_of_w_opp_side_eq_image2

theorem set_of_s_opp_side_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iio 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Iio, mem_coe]
  constructor
  · rw [s_opp_side_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h ▸ hp₂))
    · refine' ⟨-r₁ / r₂, p₂, div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul, inv_mul_cancel hr₂.ne.symm,
        one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact s_opp_side_smul_vsub_vadd_right hx hp hp' ht
#align affine_subspace.set_of_s_opp_side_eq_image2 AffineSubspace.set_of_s_opp_side_eq_image2

theorem wOppSidePointReflection {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide y (pointReflection R x y) :=
  (wbtw_point_reflection R _ _).wOppSide₁₃ hx
#align affine_subspace.w_opp_side_point_reflection AffineSubspace.wOppSidePointReflection

theorem sOppSidePointReflection {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) :
    s.SOppSide y (pointReflection R x y) :=
  by
  refine' (sbtw_point_reflection_of_ne R fun h => hy _).sOppSideOfNotMemOfMem hy hx
  rwa [← h]
#align affine_subspace.s_opp_side_point_reflection AffineSubspace.sOppSidePointReflection

end LinearOrderedField

section Normed

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]

variable [NormedAddTorsor V P]

include V

theorem is_connected_set_of_w_same_side {s : AffineSubspace ℝ P} (x : P)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.WSameSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x ∈ s
  · convert is_connected_univ
    · simp [w_same_side_of_left_mem, hx]
    · exact AddTorsor.connected_space V P
  · rw [set_of_w_same_side_eq_image2 hx hp, ← Set.image_prod]
    refine'
      (is_connected_Ici.prod (is_connected_iff_connected_space.2 _)).image _
        ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
    convert AddTorsor.connected_space s.direction s
#align
  affine_subspace.is_connected_set_of_w_same_side AffineSubspace.is_connected_set_of_w_same_side

theorem is_preconnected_set_of_w_same_side (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WSameSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert is_preconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_w_same_side_bot]
    rfl
  · exact (is_connected_set_of_w_same_side x h).IsPreconnected
#align
  affine_subspace.is_preconnected_set_of_w_same_side AffineSubspace.is_preconnected_set_of_w_same_side

theorem is_connected_set_of_s_same_side {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SSameSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [set_of_s_same_side_eq_image2 hx hp, ← Set.image_prod]
  refine'
    (is_connected_Ioi.prod (is_connected_iff_connected_space.2 _)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
  convert AddTorsor.connected_space s.direction s
#align
  affine_subspace.is_connected_set_of_s_same_side AffineSubspace.is_connected_set_of_s_same_side

theorem is_preconnected_set_of_s_same_side (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SSameSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert is_preconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_s_same_side_bot]
    rfl
  · by_cases hx : x ∈ s
    · convert is_preconnected_empty
      simp only [hx, s_same_side, not_true, false_and_iff, and_false_iff]
      rfl
    · exact (is_connected_set_of_s_same_side hx h).IsPreconnected
#align
  affine_subspace.is_preconnected_set_of_s_same_side AffineSubspace.is_preconnected_set_of_s_same_side

theorem is_connected_set_of_w_opp_side {s : AffineSubspace ℝ P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WOppSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x ∈ s
  · convert is_connected_univ
    · simp [w_opp_side_of_left_mem, hx]
    · exact AddTorsor.connected_space V P
  · rw [set_of_w_opp_side_eq_image2 hx hp, ← Set.image_prod]
    refine'
      (is_connected_Iic.prod (is_connected_iff_connected_space.2 _)).image _
        ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
    convert AddTorsor.connected_space s.direction s
#align affine_subspace.is_connected_set_of_w_opp_side AffineSubspace.is_connected_set_of_w_opp_side

theorem is_preconnected_set_of_w_opp_side (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WOppSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert is_preconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_w_opp_side_bot]
    rfl
  · exact (is_connected_set_of_w_opp_side x h).IsPreconnected
#align
  affine_subspace.is_preconnected_set_of_w_opp_side AffineSubspace.is_preconnected_set_of_w_opp_side

theorem is_connected_set_of_s_opp_side {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SOppSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [set_of_s_opp_side_eq_image2 hx hp, ← Set.image_prod]
  refine'
    (is_connected_Iio.prod (is_connected_iff_connected_space.2 _)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
  convert AddTorsor.connected_space s.direction s
#align affine_subspace.is_connected_set_of_s_opp_side AffineSubspace.is_connected_set_of_s_opp_side

theorem is_preconnected_set_of_s_opp_side (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SOppSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert is_preconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_s_opp_side_bot]
    rfl
  · by_cases hx : x ∈ s
    · convert is_preconnected_empty
      simp only [hx, s_opp_side, not_true, false_and_iff, and_false_iff]
      rfl
    · exact (is_connected_set_of_s_opp_side hx h).IsPreconnected
#align
  affine_subspace.is_preconnected_set_of_s_opp_side AffineSubspace.is_preconnected_set_of_s_opp_side

end Normed

end AffineSubspace

