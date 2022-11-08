/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Data.Set.Intervals.Group
import Mathbin.Analysis.Convex.Segment
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathbin.Tactic.FieldSimp

/-!
# Betweenness in affine spaces

This file defines notions of a point in an affine space being between two given points.

## Main definitions

* `affine_segment R x y`: The segment of points weakly between `x` and `y`.
* `wbtw R x y z`: The point `y` is weakly between `x` and `z`.
* `sbtw R x y z`: The point `y` is strictly between `x` and `z`.

-/


variable (R : Type _) {V V' P P' : Type _}

open AffineEquiv AffineMap

section OrderedRing

variable [OrderedRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

include V

/-- The segment of points weakly between `x` and `y`. When convexity is refactored to support
abstract affine combination spaces, this will no longer need to be a separate definition from
`segment`. However, lemmas involving `+ᵥ` or `-ᵥ` will still be relevant after such a
refactoring, as distinct from versions involving `+` or `-` in a module. -/
def AffineSegment (x y : P) :=
  lineMap x y '' Set.IccCat (0 : R) 1

theorem affine_segment_eq_segment (x y : V) : AffineSegment R x y = Segment R x y := by
  rw [segment_eq_image_line_map, AffineSegment]

theorem affine_segment_comm (x y : P) : AffineSegment R x y = AffineSegment R y x := by
  refine' Set.ext fun z => _
  constructor <;>
    · rintro ⟨t, ht, hxy⟩
      refine' ⟨1 - t, _, _⟩
      · rwa [Set.sub_mem_Icc_iff_right, sub_self, sub_zero]
        
      · rwa [line_map_apply_one_sub]
        
      

theorem left_mem_affine_segment (x y : P) : x ∈ AffineSegment R x y :=
  ⟨0, Set.left_mem_Icc.2 zero_le_one, line_map_apply_zero _ _⟩

theorem right_mem_affine_segment (x y : P) : y ∈ AffineSegment R x y :=
  ⟨1, Set.right_mem_Icc.2 zero_le_one, line_map_apply_one _ _⟩

include V'

variable {R}

@[simp]
theorem affine_segment_image (f : P →ᵃ[R] P') (x y : P) : f '' AffineSegment R x y = AffineSegment R (f x) (f y) := by
  rw [AffineSegment, AffineSegment, Set.image_image, ← comp_line_map]
  rfl

omit V'

variable (R)

@[simp]
theorem affine_segment_const_vadd_image (x y : P) (v : V) :
    (· +ᵥ ·) v '' AffineSegment R x y = AffineSegment R (v +ᵥ x) (v +ᵥ y) :=
  affine_segment_image (AffineEquiv.constVadd R P v : P →ᵃ[R] P) x y

@[simp]
theorem affine_segment_vadd_const_image (x y : V) (p : P) :
    (· +ᵥ p) '' AffineSegment R x y = AffineSegment R (x +ᵥ p) (y +ᵥ p) :=
  affine_segment_image (AffineEquiv.vaddConst R p : V →ᵃ[R] P) x y

@[simp]
theorem affine_segment_const_vsub_image (x y p : P) :
    (· -ᵥ ·) p '' AffineSegment R x y = AffineSegment R (p -ᵥ x) (p -ᵥ y) :=
  affine_segment_image (AffineEquiv.constVsub R p : P →ᵃ[R] V) x y

@[simp]
theorem affine_segment_vsub_const_image (x y p : P) :
    (· -ᵥ p) '' AffineSegment R x y = AffineSegment R (x -ᵥ p) (y -ᵥ p) :=
  affine_segment_image ((AffineEquiv.vaddConst R p).symm : P →ᵃ[R] V) x y

variable {R}

@[simp]
theorem mem_const_vadd_affine_segment {x y z : P} (v : V) :
    v +ᵥ z ∈ AffineSegment R (v +ᵥ x) (v +ᵥ y) ↔ z ∈ AffineSegment R x y := by
  rw [← affine_segment_const_vadd_image, (AddAction.injective v).mem_set_image]

@[simp]
theorem mem_vadd_const_affine_segment {x y z : V} (p : P) :
    z +ᵥ p ∈ AffineSegment R (x +ᵥ p) (y +ᵥ p) ↔ z ∈ AffineSegment R x y := by
  rw [← affine_segment_vadd_const_image, (vadd_right_injective p).mem_set_image]

variable {R}

@[simp]
theorem mem_const_vsub_affine_segment {x y z : P} (p : P) :
    p -ᵥ z ∈ AffineSegment R (p -ᵥ x) (p -ᵥ y) ↔ z ∈ AffineSegment R x y := by
  rw [← affine_segment_const_vsub_image, (vsub_right_injective p).mem_set_image]

@[simp]
theorem mem_vsub_const_affine_segment {x y z : P} (p : P) :
    z -ᵥ p ∈ AffineSegment R (x -ᵥ p) (y -ᵥ p) ↔ z ∈ AffineSegment R x y := by
  rw [← affine_segment_vsub_const_image, (vsub_left_injective p).mem_set_image]

variable (R)

/-- The point `y` is weakly between `x` and `z`. -/
def Wbtw (x y z : P) : Prop :=
  y ∈ AffineSegment R x z

/-- The point `y` is strictly between `x` and `z`. -/
def Sbtw (x y z : P) : Prop :=
  Wbtw R x y z ∧ y ≠ x ∧ y ≠ z

variable {R}

include V'

theorem Wbtw.map {x y z : P} (h : Wbtw R x y z) (f : P →ᵃ[R] P') : Wbtw R (f x) (f y) (f z) := by
  rw [Wbtw, ← affine_segment_image]
  exact Set.mem_image_of_mem _ h

theorem Function.Injective.wbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  refine' ⟨fun h => _, fun h => h.map _⟩
  rwa [Wbtw, ← affine_segment_image, hf.mem_set_image] at h

theorem Function.Injective.sbtw_map_iff {x y z : P} {f : P →ᵃ[R] P'} (hf : Function.Injective f) :
    Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by simp_rw [Sbtw, hf.wbtw_map_iff, hf.ne_iff]

@[simp]
theorem AffineEquiv.wbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') : Wbtw R (f x) (f y) (f z) ↔ Wbtw R x y z := by
  refine' Function.Injective.wbtw_map_iff (_ : Function.Injective f.to_affine_map)
  exact f.injective

@[simp]
theorem AffineEquiv.sbtw_map_iff {x y z : P} (f : P ≃ᵃ[R] P') : Sbtw R (f x) (f y) (f z) ↔ Sbtw R x y z := by
  refine' Function.Injective.sbtw_map_iff (_ : Function.Injective f.to_affine_map)
  exact f.injective

omit V'

@[simp]
theorem wbtw_const_vadd_iff {x y z : P} (v : V) : Wbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Wbtw R x y z :=
  mem_const_vadd_affine_segment _

@[simp]
theorem wbtw_vadd_const_iff {x y z : V} (p : P) : Wbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Wbtw R x y z :=
  mem_vadd_const_affine_segment _

@[simp]
theorem wbtw_const_vsub_iff {x y z : P} (p : P) : Wbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Wbtw R x y z :=
  mem_const_vsub_affine_segment _

@[simp]
theorem wbtw_vsub_const_iff {x y z : P} (p : P) : Wbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Wbtw R x y z :=
  mem_vsub_const_affine_segment _

@[simp]
theorem sbtw_const_vadd_iff {x y z : P} (v : V) : Sbtw R (v +ᵥ x) (v +ᵥ y) (v +ᵥ z) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, wbtw_const_vadd_iff, (AddAction.injective v).ne_iff]

@[simp]
theorem sbtw_vadd_const_iff {x y z : V} (p : P) : Sbtw R (x +ᵥ p) (y +ᵥ p) (z +ᵥ p) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, wbtw_vadd_const_iff, (vadd_right_injective p).ne_iff]

@[simp]
theorem sbtw_const_vsub_iff {x y z : P} (p : P) : Sbtw R (p -ᵥ x) (p -ᵥ y) (p -ᵥ z) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, wbtw_const_vsub_iff, (vsub_right_injective p).ne_iff]

@[simp]
theorem sbtw_vsub_const_iff {x y z : P} (p : P) : Sbtw R (x -ᵥ p) (y -ᵥ p) (z -ᵥ p) ↔ Sbtw R x y z := by
  simp_rw [Sbtw, wbtw_vsub_const_iff, (vsub_left_injective p).ne_iff]

theorem Sbtw.wbtw {x y z : P} (h : Sbtw R x y z) : Wbtw R x y z :=
  h.1

theorem Sbtw.ne_left {x y z : P} (h : Sbtw R x y z) : y ≠ x :=
  h.2.1

theorem Sbtw.left_ne {x y z : P} (h : Sbtw R x y z) : x ≠ y :=
  h.2.1.symm

theorem Sbtw.ne_right {x y z : P} (h : Sbtw R x y z) : y ≠ z :=
  h.2.2

theorem Sbtw.right_ne {x y z : P} (h : Sbtw R x y z) : z ≠ y :=
  h.2.2.symm

theorem Sbtw.mem_image_Ioo {x y z : P} (h : Sbtw R x y z) : y ∈ lineMap x z '' Set.IooCat (0 : R) 1 := by
  rcases h with ⟨⟨t, ht, rfl⟩, hyx, hyz⟩
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ho)
  · exfalso
    simpa using hyx
    
  · exfalso
    simpa using hyz
    
  · exact ⟨t, ho, rfl⟩
    

theorem wbtw_comm {x y z : P} : Wbtw R x y z ↔ Wbtw R z y x := by rw [Wbtw, Wbtw, affine_segment_comm]

alias wbtw_comm ↔ Wbtw.symm _

theorem sbtw_comm {x y z : P} : Sbtw R x y z ↔ Sbtw R z y x := by
  rw [Sbtw, Sbtw, wbtw_comm, ← and_assoc', ← and_assoc', and_right_comm]

alias sbtw_comm ↔ Sbtw.symm _

variable (R)

@[simp]
theorem wbtw_self_left (x y : P) : Wbtw R x x y :=
  left_mem_affine_segment _ _ _

@[simp]
theorem wbtw_self_right (x y : P) : Wbtw R x y y :=
  right_mem_affine_segment _ _ _

@[simp]
theorem wbtw_self_iff {x y : P} : Wbtw R x y x ↔ y = x := by
  refine' ⟨fun h => _, fun h => _⟩
  · simpa [Wbtw, AffineSegment] using h
    
  · rw [h]
    exact wbtw_self_left R x x
    

@[simp]
theorem not_sbtw_self_left (x y : P) : ¬Sbtw R x x y := fun h => h.ne_left rfl

@[simp]
theorem not_sbtw_self_right (x y : P) : ¬Sbtw R x y y := fun h => h.ne_right rfl

variable {R}

theorem Wbtw.left_ne_right_of_ne_left {x y z : P} (h : Wbtw R x y z) (hne : y ≠ x) : x ≠ z := by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

theorem Wbtw.left_ne_right_of_ne_right {x y z : P} (h : Wbtw R x y z) (hne : y ≠ z) : x ≠ z := by
  rintro rfl
  rw [wbtw_self_iff] at h
  exact hne h

theorem Sbtw.left_ne_right {x y z : P} (h : Sbtw R x y z) : x ≠ z :=
  h.Wbtw.left_ne_right_of_ne_left h.2.1

theorem sbtw_iff_mem_image_Ioo_and_ne [NoZeroSmulDivisors R V] {x y z : P} :
    Sbtw R x y z ↔ y ∈ lineMap x z '' Set.IooCat (0 : R) 1 ∧ x ≠ z := by
  refine' ⟨fun h => ⟨h.mem_image_Ioo, h.left_ne_right⟩, fun h => _⟩
  rcases h with ⟨⟨t, ht, rfl⟩, hxz⟩
  refine' ⟨⟨t, Set.mem_Icc_of_Ioo ht, rfl⟩, _⟩
  rw [line_map_apply, ← @vsub_ne_zero V, ← @vsub_ne_zero V _ _ _ _ z, vadd_vsub_assoc, vadd_vsub_assoc, ←
    neg_vsub_eq_vsub_rev z x, ← @neg_one_smul R, ← add_smul, ← sub_eq_add_neg]
  simp [smul_ne_zero, hxz.symm, sub_eq_zero, ht.1.Ne.symm, ht.2.Ne]

variable (R)

@[simp]
theorem not_sbtw_self (x y : P) : ¬Sbtw R x y x := fun h => h.left_ne_right rfl

theorem wbtw_swap_left_iff [NoZeroSmulDivisors R V] {x y : P} (z : P) : Wbtw R x y z ∧ Wbtw R y x z ↔ x = y := by
  constructor
  · rintro ⟨hxyz, hyxz⟩
    rcases hxyz with ⟨ty, hty, rfl⟩
    rcases hyxz with ⟨tx, htx, hx⟩
    simp_rw [line_map_apply, ← add_vadd] at hx
    rw [← @vsub_eq_zero_iff_eq V, vadd_vsub, vsub_vadd_eq_vsub_sub, smul_sub, smul_smul, ← sub_smul, ← add_smul,
      smul_eq_zero] at hx
    rcases hx with (h | h)
    · nth_rw 0 [← mul_one tx]  at h
      rw [← mul_sub, add_eq_zero_iff_neg_eq] at h
      have h' : ty = 0 := by
        refine' le_antisymm _ hty.1
        rw [← h, Left.neg_nonpos_iff]
        exact mul_nonneg htx.1 (sub_nonneg.2 hty.2)
      simp [h']
      
    · rw [vsub_eq_zero_iff_eq] at h
      simp [h]
      
    
  · rintro rfl
    exact ⟨wbtw_self_left _ _ _, wbtw_self_left _ _ _⟩
    

theorem wbtw_swap_right_iff [NoZeroSmulDivisors R V] (x : P) {y z : P} : Wbtw R x y z ∧ Wbtw R x z y ↔ y = z := by
  nth_rw 0 [wbtw_comm]
  nth_rw 1 [wbtw_comm]
  rw [eq_comm]
  exact wbtw_swap_left_iff R x

theorem wbtw_rotate_iff [NoZeroSmulDivisors R V] (x : P) {y z : P} : Wbtw R x y z ∧ Wbtw R z x y ↔ x = y := by
  rw [wbtw_comm, wbtw_swap_right_iff, eq_comm]

variable {R}

theorem Wbtw.swap_left_iff [NoZeroSmulDivisors R V] {x y z : P} (h : Wbtw R x y z) : Wbtw R y x z ↔ x = y := by
  rw [← wbtw_swap_left_iff R z, and_iff_right h]

theorem Wbtw.swap_right_iff [NoZeroSmulDivisors R V] {x y z : P} (h : Wbtw R x y z) : Wbtw R x z y ↔ y = z := by
  rw [← wbtw_swap_right_iff R x, and_iff_right h]

theorem Wbtw.rotate_iff [NoZeroSmulDivisors R V] {x y z : P} (h : Wbtw R x y z) : Wbtw R z x y ↔ x = y := by
  rw [← wbtw_rotate_iff R x, and_iff_right h]

theorem Sbtw.not_swap_left [NoZeroSmulDivisors R V] {x y z : P} (h : Sbtw R x y z) : ¬Wbtw R y x z := fun hs =>
  h.left_ne (h.Wbtw.swap_left_iff.1 hs)

theorem Sbtw.not_swap_right [NoZeroSmulDivisors R V] {x y z : P} (h : Sbtw R x y z) : ¬Wbtw R x z y := fun hs =>
  h.ne_right (h.Wbtw.swap_right_iff.1 hs)

theorem Sbtw.not_rotate [NoZeroSmulDivisors R V] {x y z : P} (h : Sbtw R x y z) : ¬Wbtw R z x y := fun hs =>
  h.left_ne (h.Wbtw.rotate_iff.1 hs)

theorem Wbtw.trans_left {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) : Wbtw R w x z := by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine' ⟨t₂ * t₁, ⟨mul_nonneg ht₂.1 ht₁.1, mul_le_one ht₂.2 ht₁.1 ht₁.2⟩, _⟩
  simp [line_map_apply, smul_smul]

theorem Wbtw.trans_right {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) : Wbtw R w y z := by
  rw [wbtw_comm] at *
  exact h₁.trans_left h₂

theorem Wbtw.trans_sbtw_left [NoZeroSmulDivisors R V] {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Sbtw R w x y) :
    Sbtw R w x z := by
  refine' ⟨h₁.trans_left h₂.wbtw, h₂.ne_left, _⟩
  rintro rfl
  exact h₂.right_ne ((wbtw_swap_right_iff R w).1 ⟨h₁, h₂.wbtw⟩)

theorem Wbtw.trans_sbtw_right [NoZeroSmulDivisors R V] {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Sbtw R x y z) :
    Sbtw R w y z := by
  rw [wbtw_comm] at *
  rw [sbtw_comm] at *
  exact h₁.trans_sbtw_left h₂

theorem Sbtw.trans_left [NoZeroSmulDivisors R V] {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R w x z :=
  h₁.Wbtw.trans_sbtw_left h₂

theorem Sbtw.trans_right [NoZeroSmulDivisors R V] {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) :
    Sbtw R w y z :=
  h₁.Wbtw.trans_sbtw_right h₂

end OrderedRing

section StrictOrderedCommRing

variable [StrictOrderedCommRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

include V

variable {R}

theorem Wbtw.same_ray_vsub {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -ᵥ y) := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  simp_rw [line_map_apply]
  rcases ht0.lt_or_eq with (ht0' | rfl)
  swap
  · simp
    
  rcases ht1.lt_or_eq with (ht1' | rfl)
  swap
  · simp
    
  refine' Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', _⟩)
  simp [vsub_vadd_eq_vsub_sub, smul_sub, smul_smul, ← sub_smul]
  ring_nf

theorem Wbtw.same_ray_vsub_left {x y z : P} (h : Wbtw R x y z) : SameRay R (y -ᵥ x) (z -ᵥ x) := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  simpa [line_map_apply] using same_ray_nonneg_smul_left (z -ᵥ x) ht0

theorem Wbtw.same_ray_vsub_right {x y z : P} (h : Wbtw R x y z) : SameRay R (z -ᵥ x) (z -ᵥ y) := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  simpa [line_map_apply, vsub_vadd_eq_vsub_sub, sub_smul] using same_ray_nonneg_smul_right (z -ᵥ x) (sub_nonneg.2 ht1)

end StrictOrderedCommRing

section LinearOrderedField

variable [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]

include V

variable {R}

theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁) (hr₂ : r₁ ≤ r₂) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) := by
  refine' ⟨r₁ / r₂, ⟨div_nonneg hr₁ (hr₁.trans hr₂), div_le_one_of_le hr₂ (hr₁.trans hr₂)⟩, _⟩
  by_cases h:r₁ = 0
  · simp [h]
    
  simp [line_map_apply, smul_smul, ((hr₁.lt_of_ne' h).trans_le hr₂).Ne.symm]

theorem wbtw_or_wbtw_smul_vadd_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) := by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₁ h)
    
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x v hr₂ h)
    

theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_le (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0) (hr₂ : r₂ ≤ r₁) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) := by
  convert wbtw_smul_vadd_smul_vadd_of_nonneg_of_le x (-v) (Left.nonneg_neg_iff.2 hr₁) (neg_le_neg_iff.2 hr₂) using 1 <;>
    rw [neg_smul_neg]

theorem wbtw_or_wbtw_smul_vadd_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0) (hr₂ : r₂ ≤ 0) :
    Wbtw R x (r₁ • v +ᵥ x) (r₂ • v +ᵥ x) ∨ Wbtw R x (r₂ • v +ᵥ x) (r₁ • v +ᵥ x) := by
  rcases le_total r₁ r₂ with (h | h)
  · exact Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₂ h)
    
  · exact Or.inl (wbtw_smul_vadd_smul_vadd_of_nonpos_of_le x v hr₁ h)
    

theorem wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg (x : P) (v : V) {r₁ r₂ : R} (hr₁ : r₁ ≤ 0) (hr₂ : 0 ≤ r₂) :
    Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) := by
  convert
      wbtw_smul_vadd_smul_vadd_of_nonneg_of_le (r₁ • v +ᵥ x) v (Left.nonneg_neg_iff.2 hr₁)
        (neg_le_sub_iff_le_add.2 ((le_add_iff_nonneg_left r₁).2 hr₂)) using
      1 <;>
    simp [sub_smul, ← add_vadd]

theorem wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos (x : P) (v : V) {r₁ r₂ : R} (hr₁ : 0 ≤ r₁) (hr₂ : r₂ ≤ 0) :
    Wbtw R (r₁ • v +ᵥ x) x (r₂ • v +ᵥ x) := by
  rw [wbtw_comm]
  exact wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg x v hr₂ hr₁

theorem Wbtw.trans_left_right {w x y z : P} (h₁ : Wbtw R w y z) (h₂ : Wbtw R w x y) : Wbtw R x y z := by
  rcases h₁ with ⟨t₁, ht₁, rfl⟩
  rcases h₂ with ⟨t₂, ht₂, rfl⟩
  refine'
    ⟨(t₁ - t₂ * t₁) / (1 - t₂ * t₁),
      ⟨div_nonneg (sub_nonneg.2 (mul_le_of_le_one_left ht₁.1 ht₂.2)) (sub_nonneg.2 (mul_le_one ht₂.2 ht₁.1 ht₁.2)),
        div_le_one_of_le (sub_le_sub_right ht₁.2 _) (sub_nonneg.2 (mul_le_one ht₂.2 ht₁.1 ht₁.2))⟩,
      _⟩
  simp only [line_map_apply, smul_smul, ← add_vadd, vsub_vadd_eq_vsub_sub, smul_sub, ← sub_smul, ← add_smul, vadd_vsub,
    vadd_right_cancel_iff, div_mul_eq_mul_div, div_sub_div_same]
  nth_rw 0 [← mul_one (t₁ - t₂ * t₁)]
  rw [← mul_sub, mul_div_assoc]
  by_cases h:1 - t₂ * t₁ = 0
  · rw [sub_eq_zero, eq_comm] at h
    rw [h]
    suffices t₁ = 1 by simp [this]
    exact eq_of_le_of_not_lt ht₁.2 fun ht₁lt => (mul_lt_one_of_nonneg_of_lt_one_right ht₂.2 ht₁.1 ht₁lt).Ne h
    
  · rw [div_self h]
    ring_nf
    

theorem Wbtw.trans_right_left {w x y z : P} (h₁ : Wbtw R w x z) (h₂ : Wbtw R x y z) : Wbtw R w x y := by
  rw [wbtw_comm] at *
  exact h₁.trans_left_right h₂

theorem Sbtw.trans_left_right {w x y z : P} (h₁ : Sbtw R w y z) (h₂ : Sbtw R w x y) : Sbtw R x y z :=
  ⟨h₁.Wbtw.trans_left_right h₂.Wbtw, h₂.right_ne, h₁.ne_right⟩

theorem Sbtw.trans_right_left {w x y z : P} (h₁ : Sbtw R w x z) (h₂ : Sbtw R x y z) : Sbtw R w x y :=
  ⟨h₁.Wbtw.trans_right_left h₂.Wbtw, h₁.ne_left, h₂.left_ne⟩

theorem Wbtw.collinear {x y z : P} (h : Wbtw R x y z) : Collinear R ({x, y, z} : Set P) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine' ⟨x, z -ᵥ x, _⟩
  intro p hp
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with (rfl | rfl | rfl)
  · refine' ⟨0, _⟩
    simp
    
  · rcases h with ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
    
  · refine' ⟨1, _⟩
    simp
    

theorem Collinear.wbtw_or_wbtw_or_wbtw {x y z : P} (h : Collinear R ({x, y, z} : Set P)) :
    Wbtw R x y z ∨ Wbtw R y z x ∨ Wbtw R z x y := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  rcases h with ⟨v, h⟩
  simp_rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have hy := h y (Or.inr (Or.inl rfl))
  have hz := h z (Or.inr (Or.inr rfl))
  rcases hy with ⟨ty, rfl⟩
  rcases hz with ⟨tz, rfl⟩
  rcases lt_trichotomy ty 0 with (hy0 | rfl | hy0)
  · rcases lt_trichotomy tz 0 with (hz0 | rfl | hz0)
    · nth_rw 1 [wbtw_comm]
      rw [← or_assoc']
      exact Or.inl (wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hy0.le hz0.le)
      
    · simp
      
    · exact Or.inr (Or.inr (wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos _ _ hz0.le hy0.le))
      
    
  · simp
    
  · rcases lt_trichotomy tz 0 with (hz0 | rfl | hz0)
    · refine' Or.inr (Or.inr (wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg _ _ hz0.le hy0.le))
      
    · simp
      
    · nth_rw 1 [wbtw_comm]
      rw [← or_assoc']
      exact Or.inl (wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hy0.le hz0.le)
      
    

theorem wbtw_iff_same_ray_vsub {x y z : P} : Wbtw R x y z ↔ SameRay R (y -ᵥ x) (z -ᵥ y) := by
  refine' ⟨Wbtw.same_ray_vsub, fun h => _⟩
  rcases h with (h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rw [vsub_eq_zero_iff_eq] at h
    simp [h]
    
  · rw [vsub_eq_zero_iff_eq] at h
    simp [h]
    
  · refine'
      ⟨r₂ / (r₁ + r₂),
        ⟨div_nonneg hr₂.le (add_nonneg hr₁.le hr₂.le),
          div_le_one_of_le (le_add_of_nonneg_left hr₁.le) (add_nonneg hr₁.le hr₂.le)⟩,
        _⟩
    have h' : z = r₂⁻¹ • r₁ • (y -ᵥ x) +ᵥ y := by simp [h, hr₂.ne']
    rw [eq_comm]
    simp only [line_map_apply, h', vadd_vsub_assoc, smul_smul, ← add_smul, eq_vadd_iff_vsub_eq, smul_add]
    convert (one_smul _ _).symm
    field_simp [(add_pos hr₁ hr₂).ne', hr₂.ne']
    ring
    

variable (R)

theorem wbtw_point_reflection (x y : P) : Wbtw R y x (pointReflection R x y) := by
  refine' ⟨2⁻¹, ⟨by norm_num, by norm_num⟩, _⟩
  rw [line_map_apply, point_reflection_apply, vadd_vsub_assoc, ← two_smul R (x -ᵥ y)]
  simp

theorem sbtw_point_reflection_of_ne {x y : P} (h : x ≠ y) : Sbtw R y x (pointReflection R x y) := by
  refine' ⟨wbtw_point_reflection _ _ _, h, _⟩
  nth_rw 0 [← point_reflection_self R x]
  exact (point_reflection_involutive R x).Injective.Ne h

end LinearOrderedField

