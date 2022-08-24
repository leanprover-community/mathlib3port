/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import Mathbin.Algebra.Order.Invertible
import Mathbin.Algebra.Order.Smul
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.LinearAlgebra.Ray
import Mathbin.Tactic.Positivity

/-!
# Segments in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `open_segment 𝕜 x y`: Open segment joining `x` and `y`.

## Notations

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in locale `convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/


variable {𝕜 E F : Type _}

open Set

section OrderedSemiring

variable [OrderedSemiring 𝕜] [AddCommMonoidₓ E]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E] {s : Set E} {x y : E}

/-- Segments in a vector space. -/
def Segment (x y : E) : Set E :=
  { z : E | ∃ (a b : 𝕜)(ha : 0 ≤ a)(hb : 0 ≤ b)(hab : a + b = 1), a • x + b • y = z }

/-- Open segment in a vector space. Note that `open_segment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def OpenSegment (x y : E) : Set E :=
  { z : E | ∃ (a b : 𝕜)(ha : 0 < a)(hb : 0 < b)(hab : a + b = 1), a • x + b • y = z }

-- mathport name: «expr[ -[ ] ]»
localized [Convex] notation "[" x " -[" 𝕜 "] " y "]" => Segment 𝕜 x y

theorem segment_eq_image₂ (x y : E) :
    [x -[𝕜] y] = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [Segment, image, Prod.exists, mem_set_of_eq, exists_prop, and_assoc]

theorem open_segment_eq_image₂ (x y : E) :
    OpenSegment 𝕜 x y = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [OpenSegment, image, Prod.exists, mem_set_of_eq, exists_prop, and_assoc]

theorem segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩⟩

theorem open_segment_symm (x y : E) : OpenSegment 𝕜 x y = OpenSegment 𝕜 y x :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩⟩

theorem open_segment_subset_segment (x y : E) : OpenSegment 𝕜 x y ⊆ [x -[𝕜] y] := fun z ⟨a, b, ha, hb, hab, hz⟩ =>
  ⟨a, b, ha.le, hb.le, hab, hz⟩

theorem segment_subset_iff : [x -[𝕜] y] ⊆ s ↔ ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H z ⟨a, b, ha, hb, hab, hz⟩ => hz ▸ H a b ha hb hab⟩

theorem open_segment_subset_iff : OpenSegment 𝕜 x y ⊆ s ↔ ∀ a b : 𝕜, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H z ⟨a, b, ha, hb, hab, hz⟩ => hz ▸ H a b ha hb hab⟩

end HasSmul

open Convex

section MulActionWithZero

variable (𝕜) [MulActionWithZero 𝕜 E]

theorem left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
  ⟨1, 0, zero_le_one, le_reflₓ 0, add_zeroₓ 1, by
    rw [zero_smul, one_smul, add_zeroₓ]⟩

theorem right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] :=
  segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

end MulActionWithZero

section Module

variable (𝕜) [Module 𝕜 E] {s : Set E} {x y z : E}

@[simp]
theorem segment_same (x : E) : [x -[𝕜] x] = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ => by
      simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz, fun h =>
      mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

theorem insert_endpoints_open_segment (x y : E) : insert x (insert y (OpenSegment 𝕜 x y)) = [x -[𝕜] y] := by
  simp only [subset_antisymm_iff, insert_subset, left_mem_segment, right_mem_segment, open_segment_subset_segment,
    true_andₓ]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine' hb.eq_or_gt.imp _ fun hb' => ha.eq_or_gt.imp _ _
  · rintro rfl
    rw [add_zeroₓ] at hab
    rw [hab, one_smul, zero_smul, add_zeroₓ]
    
  · rintro rfl
    rw [zero_addₓ] at hab
    rw [hab, one_smul, zero_smul, zero_addₓ]
    
  · exact fun ha' => ⟨a, b, ha', hb', hab, rfl⟩
    

variable {𝕜}

theorem mem_open_segment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x -[𝕜] y]) : z ∈ OpenSegment 𝕜 x y := by
  rw [← insert_endpoints_open_segment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

theorem open_segment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) : OpenSegment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s := by
  simp only [← insert_endpoints_open_segment, insert_subset, *, true_andₓ]

end Module

end OrderedSemiring

open Convex

section OrderedRing

variable (𝕜) [OrderedRing 𝕜] [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F]

section DenselyOrdered

variable [Nontrivial 𝕜] [DenselyOrdered 𝕜]

@[simp]
theorem open_segment_same (x : E) : OpenSegment 𝕜 x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ => by
      simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz, fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine' ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, _⟩
      rw [← add_smul, add_sub_cancel'_right, one_smul, h]⟩

end DenselyOrdered

theorem segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1 :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩,
        hab ▸
          hz ▸ by
            simp only [add_sub_cancel]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

theorem open_segment_eq_image (x y : E) : OpenSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩,
        hab ▸
          hz ▸ by
            simp only [add_sub_cancel]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

theorem segment_eq_image' (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y
  ext θ
  simp only [smul_sub, sub_smul, one_smul]
  abel

theorem open_segment_eq_image' (x y : E) : OpenSegment 𝕜 x y = (fun θ : 𝕜 => x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 := by
  convert open_segment_eq_image 𝕜 x y
  ext θ
  simp only [smul_sub, sub_smul, one_smul]
  abel

theorem segment_eq_image_line_map (x y : E) : [x -[𝕜] y] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y
  ext
  exact AffineMap.line_map_apply_module _ _ _

theorem open_segment_eq_image_line_map (x y : E) : OpenSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1 := by
  convert open_segment_eq_image 𝕜 x y
  ext
  exact AffineMap.line_map_apply_module _ _ _

theorem segment_image (f : E →ₗ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
  Set.ext fun x => by
    simp_rw [segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul]

@[simp]
theorem open_segment_image (f : E →ₗ[𝕜] F) (a b : E) : f '' OpenSegment 𝕜 a b = OpenSegment 𝕜 (f a) (f b) :=
  Set.ext fun x => by
    simp_rw [open_segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul]

theorem mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[𝕜] a + c] ↔ x ∈ [b -[𝕜] c] := by
  rw [segment_eq_image', segment_eq_image']
  refine' exists_congr fun θ => and_congr Iff.rfl _
  simp only [add_sub_add_left_eq_sub, add_assocₓ, add_right_injₓ]

@[simp]
theorem mem_open_segment_translate (a : E) {x b c : E} :
    a + x ∈ OpenSegment 𝕜 (a + b) (a + c) ↔ x ∈ OpenSegment 𝕜 b c := by
  rw [open_segment_eq_image', open_segment_eq_image']
  refine' exists_congr fun θ => and_congr Iff.rfl _
  simp only [add_sub_add_left_eq_sub, add_assocₓ, add_right_injₓ]

theorem segment_translate_preimage (a b c : E) : (fun x => a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c] :=
  Set.ext fun x => mem_segment_translate 𝕜 a

theorem open_segment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' OpenSegment 𝕜 (a + b) (a + c) = OpenSegment 𝕜 b c :=
  Set.ext fun x => mem_open_segment_translate 𝕜 a

theorem segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c] :=
  segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a

theorem open_segment_translate_image (a b c : E) :
    (fun x => a + x) '' OpenSegment 𝕜 b c = OpenSegment 𝕜 (a + b) (a + c) :=
  open_segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a

end OrderedRing

theorem same_ray_of_mem_segment [OrderedCommRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {x y z : E} (h : x ∈ [y -[𝕜] z]) :
    SameRay 𝕜 (x - y) (z - x) := by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [add_sub_cancel', ← sub_sub, sub_smul, one_smul] using
    (same_ray_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)

section LinearOrderedRing

variable [LinearOrderedRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {x y : E}

theorem midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y ∈ [x -[𝕜] y] := by
  rw [segment_eq_image_line_map]
  exact ⟨⅟ 2, ⟨inv_of_nonneg.mpr zero_le_two, inv_of_le_one one_le_two⟩, rfl⟩

theorem mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x - y -[𝕜] x + y] := by
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _
  rw [midpoint_sub_add]

theorem mem_segment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x + y -[𝕜] x - y] := by
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _
  rw [midpoint_add_sub]

@[simp]
theorem left_mem_open_segment_iff [DenselyOrdered 𝕜] [NoZeroSmulDivisors 𝕜 E] : x ∈ OpenSegment 𝕜 x y ↔ x = y := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hx⟩
    refine' smul_right_injective _ hb.ne' ((add_right_injₓ (a • x)).1 _)
    rw [hx, ← add_smul, hab, one_smul]
    
  · rintro rfl
    rw [open_segment_same]
    exact mem_singleton _
    

@[simp]
theorem right_mem_open_segment_iff [DenselyOrdered 𝕜] [NoZeroSmulDivisors 𝕜 E] : y ∈ OpenSegment 𝕜 x y ↔ x = y := by
  rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end LinearOrderedRing

section LinearOrderedSemifield

variable [LinearOrderedSemifield 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {x y z : E}

theorem mem_segment_iff_div :
    x ∈ [y -[𝕜] z] ↔ ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
    
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine' ⟨a / (a + b), b / (a + b), div_nonneg ha hab.le, div_nonneg hb hab.le, _, rfl⟩
    rw [← add_div, div_self hab.ne']
    

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]
-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]
-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]
theorem mem_open_segment_iff_div :
    x ∈ OpenSegment 𝕜 y z ↔ ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab, div_one, div_one]
    
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := by
      trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]"
    refine'
      ⟨a / (a + b), b / (a + b), by
        trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]", by
        trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]", _, rfl⟩
    rw [← add_div, div_self hab.ne']
    

end LinearOrderedSemifield

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {x y z : E}

theorem mem_segment_iff_same_ray : x ∈ [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x) := by
  refine' ⟨same_ray_of_mem_segment, fun h => _⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_commₓ, sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x), neg_add_selfₓ]
  refine' ⟨b, a, hb, ha, add_commₓ a b ▸ hab, _⟩
  rw [← sub_eq_neg_add, ← neg_sub, hxy, ← sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_selfₓ]

end LinearOrderedField

/-!
#### Segments in an ordered space

Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E] {x y : E}

theorem segment_subset_Icc (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  calc
    x = a • x + b • x := (Convex.combo_self hab _).symm
    _ ≤ a • x + b • y := add_le_add_left (smul_le_smul_of_nonneg h hb) _
    
  calc
    a • x + b • y ≤ a • y + b • y := add_le_add_right (smul_le_smul_of_nonneg h ha) _
    _ = y := Convex.combo_self hab _
    

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E] {x y : E}

theorem open_segment_subset_Ioo (h : x < y) : OpenSegment 𝕜 x y ⊆ Ioo x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  calc
    x = a • x + b • x := (Convex.combo_self hab _).symm
    _ < a • x + b • y := add_lt_add_left (smul_lt_smul_of_pos h hb) _
    
  calc
    a • x + b • y < a • y + b • y := add_lt_add_right (smul_lt_smul_of_pos h ha) _
    _ = y := Convex.combo_self hab _
    

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E] {𝕜} {a b : 𝕜}

theorem segment_subset_interval (x y : E) : [x -[𝕜] y] ⊆ Interval x y := by
  cases le_totalₓ x y
  · rw [interval_of_le h]
    exact segment_subset_Icc h
    
  · rw [interval_of_ge h, segment_symm]
    exact segment_subset_Icc h
    

theorem Convex.min_le_combo (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : min x y ≤ a • x + b • y :=
  (segment_subset_interval x y ⟨_, _, ha, hb, hab, rfl⟩).1

theorem Convex.combo_le_max (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a • x + b • y ≤ max x y :=
  (segment_subset_interval x y ⟨_, _, ha, hb, hab, rfl⟩).2

end LinearOrderedAddCommMonoid

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜] {x y z : 𝕜}

theorem Icc_subset_segment : Icc x y ⊆ [x -[𝕜] y] := by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
    
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine' ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, _, _⟩
  · rw [← add_div, sub_add_sub_cancel, div_self h.ne']
    
  · rw [smul_eq_mul, smul_eq_mul, ← mul_div_right_comm, ← mul_div_right_comm, ← add_div, div_eq_iff h.ne', add_commₓ,
      sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]
    

@[simp]
theorem segment_eq_Icc (h : x ≤ y) : [x -[𝕜] y] = Icc x y :=
  (segment_subset_Icc h).antisymm Icc_subset_segment

theorem Ioo_subset_open_segment : Ioo x y ⊆ OpenSegment 𝕜 x y := fun z hz =>
  mem_open_segment_of_ne_left_right hz.1.Ne hz.2.ne' <| Icc_subset_segment <| Ioo_subset_Icc_self hz

@[simp]
theorem open_segment_eq_Ioo (h : x < y) : OpenSegment 𝕜 x y = Ioo x y :=
  (open_segment_subset_Ioo h).antisymm Ioo_subset_open_segment

theorem segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) := by
  cases le_totalₓ x y
  · rw [segment_eq_Icc h, max_eq_rightₓ h, min_eq_leftₓ h]
    
  · rw [segment_symm, segment_eq_Icc h, max_eq_leftₓ h, min_eq_rightₓ h]
    

theorem open_segment_eq_Ioo' (hxy : x ≠ y) : OpenSegment 𝕜 x y = Ioo (min x y) (max x y) := by
  cases hxy.lt_or_lt
  · rw [open_segment_eq_Ioo h, max_eq_rightₓ h.le, min_eq_leftₓ h.le]
    
  · rw [open_segment_symm, open_segment_eq_Ioo h, max_eq_leftₓ h.le, min_eq_rightₓ h.le]
    

theorem segment_eq_interval (x y : 𝕜) : [x -[𝕜] y] = Interval x y :=
  segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
theorem Convex.mem_Icc (h : x ≤ y) : z ∈ Icc x y ↔ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  rw [← segment_eq_Icc h]
  simp_rw [← exists_prop]
  rfl

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
theorem Convex.mem_Ioo (h : x < y) : z ∈ Ioo x y ↔ ∃ a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  rw [← open_segment_eq_Ioo h]
  simp_rw [← exists_prop]
  rfl

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ioc (h : x < y) : z ∈ Ioc x y ↔ ∃ a b, 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine' ⟨fun hz => _, _⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zeroₓ] at hab
      rw [hab, one_mulₓ, zero_mul, add_zeroₓ] at hz
      exact (hz.1.Ne rfl).elim
      
    · exact ⟨a, b, ha, hb', hab, rfl⟩
      
    
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_addₓ] at hab
      rwa [hab, one_mulₓ, zero_mul, zero_addₓ, right_mem_Ioc]
      
    · exact Ioo_subset_Ioc_self ((Convex.mem_Ioo h).2 ⟨a, b, ha', hb, hab, rfl⟩)
      
    

/-- A point is in an `Ico` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ico (h : x < y) : z ∈ Ico x y ↔ ∃ a b, 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine' ⟨fun hz => _, _⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_addₓ] at hab
      rw [hab, one_mulₓ, zero_mul, zero_addₓ] at hz
      exact (hz.2.Ne rfl).elim
      
    · exact ⟨a, b, ha', hb, hab, rfl⟩
      
    
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zeroₓ] at hab
      rwa [hab, one_mulₓ, zero_mul, add_zeroₓ, left_mem_Ico]
      
    · exact Ioo_subset_Ico_self ((Convex.mem_Ioo h).2 ⟨a, b, ha, hb', hab, rfl⟩)
      
    

end LinearOrderedField

