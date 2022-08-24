/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import Mathbin.Algebra.Order.Module
import Mathbin.Analysis.Convex.Star
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace

/-!
# Convex sets and functions in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.
* `std_simplex 𝕜 ι`: The standard simplex in `ι → 𝕜` (currently requires `fintype ι`). It is the
  intersection of the positive quadrant with the hyperplane `s.sum = 1`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## TODO

Generalize all this file to affine spaces.
-/


variable {𝕜 E F β : Type _}

open LinearMap Set

open BigOperators Classical Convex Pointwise

/-! ### Convexity of sets -/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E] [HasSmul 𝕜 F] (s : Set E) {x : E}

/-- Convexity of sets. -/
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s

variable {𝕜 s}

theorem Convex.star_convex (hs : Convex 𝕜 s) (hx : x ∈ s) : StarConvex 𝕜 x s :=
  hs hx

theorem convex_iff_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
  forall₂_congrₓ fun x hx => star_convex_iff_segment_subset

theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : [x -[𝕜] y] ⊆ s :=
  convex_iff_segment_subset.1 h hx hy

theorem Convex.open_segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : OpenSegment 𝕜 x y ⊆ s :=
  (open_segment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
theorem convex_iff_pointwise_add_subset : Convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h x hx y hy a b ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias convex_iff_pointwise_add_subset ↔ Convex.set_combo_subset _

theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun x => False.elim

theorem convex_univ : Convex 𝕜 (Set.Univ : Set E) := fun _ _ => star_convex_univ _

theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ∩ t) := fun x hx =>
  (hs hx.1).inter (ht hx.2)

theorem convex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) := fun x hx =>
  star_convex_sInter fun s hs => h _ hs <| hx _ hs

theorem convex_Inter {ι : Sort _} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) : Convex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ convex_sInter <| forall_range_iff.2 h

-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j)
theorem convex_Inter₂ {ι : Sort _} {κ : ι → Sort _} {s : ∀ i, κ i → Set E} (h : ∀ i j, Convex 𝕜 (s i j)) :
    Convex 𝕜 (⋂ (i) (j), s i j) :=
  convex_Inter fun i => convex_Inter <| h i

theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ×ˢ t) := fun x hx =>
  (hs hx.1).Prod (ht hx.2)

theorem convex_pi {ι : Type _} {E : ι → Type _} [∀ i, AddCommMonoidₓ (E i)] [∀ i, HasSmul 𝕜 (E i)] {s : Set ι}
    {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) := fun x hx =>
  star_convex_pi fun i hi => ht hi <| hx _ hi

theorem Directed.convex_Union {ι : Sort _} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hc : ∀ ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy a b ha hb hab
  rw [mem_Union] at hx hy⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) c)
    (hc : ∀ ⦃A : Set E⦄, A ∈ c → Convex 𝕜 A) : Convex 𝕜 (⋃₀c) := by
  rw [sUnion_eq_Union]
  exact (directed_on_iff_directed.1 hdir).convex_Union fun A => hc A.2

end HasSmul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

theorem convex_iff_open_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → OpenSegment 𝕜 x y ⊆ s :=
  forall₂_congrₓ fun x => star_convex_iff_open_segment_subset

theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  forall₂_congrₓ fun x => star_convex_iff_forall_pos

theorem convex_iff_pairwise_pos :
    Convex 𝕜 s ↔ s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine' convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, _⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
    
  · exact h hx hy hxy ha hb hab
    

theorem Convex.star_convex_iff (hs : Convex 𝕜 s) (h : s.Nonempty) : StarConvex 𝕜 x s ↔ x ∈ s :=
  ⟨fun hxs => hxs.Mem h, hs.StarConvex⟩

protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.Pairwise _)

theorem convex_singleton (c : E) : Convex 𝕜 ({c} : Set E) :=
  subsingleton_singleton.Convex

theorem convex_segment (x y : E) : Convex 𝕜 [x -[𝕜] y] := by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine'
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _⟩
  · rw [add_add_add_commₓ, ← mul_addₓ, ← mul_addₓ, habp, habq, mul_oneₓ, mul_oneₓ, hab]
    
  · simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_commₓ _ _ _ _
    

theorem convex_open_segment (a b : E) : Convex 𝕜 (OpenSegment 𝕜 a b) := by
  rw [convex_iff_open_segment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine'
    ⟨a * ap + b * aq, a * bp + b * bq, add_pos (mul_pos ha hap) (mul_pos hb haq),
      add_pos (mul_pos ha hbp) (mul_pos hb hbq), _, _⟩
  · rw [add_add_add_commₓ, ← mul_addₓ, ← mul_addₓ, habp, habq, mul_oneₓ, mul_oneₓ, hab]
    
  · simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_commₓ _ _ _ _
    

theorem Convex.linear_image (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f '' s) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy
  exact
    ⟨a • x' + b • y', hs hx' hy' ha hb hab, by
      rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem Convex.is_linear_image (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f '' s) :=
  hs.linear_image <| hf.mk' f

theorem Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy ha hb hab

theorem Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f ⁻¹' s) :=
  hs.linear_preimage <| hf.mk' f

theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.is_linear_map_add

theorem Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s) := by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs

theorem Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) '' s) :=
  hs.vadd _

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_commₓ, ← add_smul, hab, one_smul] at h

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_commₓ] using hs.translate_preimage_right z

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem convex_Iic (r : β) : Convex 𝕜 (Iic r) := fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y ≤ a • r + b • r := add_le_add (smul_le_smul_of_nonneg hx ha) (smul_le_smul_of_nonneg hy hb)
    _ = r := Convex.combo_self hab _
    

theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
  @convex_Iic 𝕜 βᵒᵈ _ _ _ _ r

theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

theorem convex_halfspace_le {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w ≤ r } :=
  (convex_Iic r).is_linear_preimage h

theorem convex_halfspace_ge {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r ≤ f w } :=
  (convex_Ici r).is_linear_preimage h

theorem convex_hyperplane {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w = r } := by
  simp_rw [le_antisymm_iffₓ]
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r)

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem convex_Iio (r : β) : Convex 𝕜 (Iio r) := by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_addₓ] at hab
    rwa [zero_smul, zero_addₓ, hab, one_smul]
    
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r :=
      add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx ha') (smul_le_smul_of_nonneg hy.le hb)
    _ = r := Convex.combo_self hab _
    

theorem convex_Ioi (r : β) : Convex 𝕜 (Ioi r) :=
  @convex_Iio 𝕜 βᵒᵈ _ _ _ _ r

theorem convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

theorem convex_Ico (r s : β) : Convex 𝕜 (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

theorem convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

theorem convex_halfspace_lt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h

theorem convex_halfspace_gt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem convex_interval (r s : β) : Convex 𝕜 (Interval r s) :=
  convex_Icc _ _

end LinearOrderedAddCommMonoid

end Module

end AddCommMonoidₓ

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [OrderedAddCommMonoid β] [Module 𝕜 E] [OrderedSmul 𝕜 E] {s : Set E} {f : E → β}

theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  fun x hx y hy a b ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' _ hx.2 hy.2)⟩

theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  fun x hx y hy a b ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' _ hx.2 hy.2)⟩

theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  @MonotoneOn.convex_le 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r

theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  @MonotoneOn.convex_lt 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r

theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  @MonotoneOn.convex_ge 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  @MonotoneOn.convex_gt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  @MonotoneOn.convex_le 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  @MonotoneOn.convex_lt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_ge convex_univ r)

theorem Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_le convex_univ r)

theorem Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_lt convex_univ r)

theorem Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_ge convex_univ r)

theorem Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_gt convex_univ r)

end LinearOrderedAddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)

theorem Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

theorem Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) : Convex 𝕜 ((fun x => z + c • x) '' s) := by
  simpa only [← image_smul, ← image_vadd, image_image] using (hs.smul c).vadd z

end AddCommMonoidₓ

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E}

theorem Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s) {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assocₓ, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

theorem Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s := by
  simpa using
    hs.add_smul_mem zero_mem
      (by
        simpa using hx)
      ht

theorem Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    x + t • (y - x) ∈ s := by
  apply h.segment_subset hx hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ht

/-- Affine subspaces are convex. -/
theorem AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E) := by
  intro x hx y hy a b ha hb hab
  rw [eq_sub_of_add_eq hab, ← AffineMap.line_map_apply_module]
  exact AffineMap.line_map_mem b hx hy

/-- The preimage of a convex set under an affine map is convex. -/
theorem Convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s) := fun x hx =>
  (hs hx).affine_preimage _

/-- The image of a convex set under an affine map is convex. -/
theorem Convex.affine_image (f : E →ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _

theorem Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.is_linear_map_neg

theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

end AddCommGroupₓ

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-- Alternative definition of set convexity, using division. -/
theorem convex_iff_div :
    Convex 𝕜 s ↔
      ∀ ⦃x⦄,
        x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  forall₂_congrₓ fun x hx => star_convex_iff_div

theorem Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s) {t : 𝕜}
    (ht : 1 ≤ t) : x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]
theorem Convex.add_smul (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) : (p + q) • s = p • s + q • s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp_rw [smul_set_empty, add_empty]
    
  obtain rfl | hp' := hp.eq_or_lt
  · rw [zero_addₓ, zero_smul_set hs, zero_addₓ]
    
  obtain rfl | hq' := hq.eq_or_lt
  · rw [add_zeroₓ, zero_smul_set hs, add_zeroₓ]
    
  ext
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨p • v, q • v, smul_mem_smul_set hv, smul_mem_smul_set hv, (add_smul _ _ _).symm⟩
    
  · rintro ⟨v₁, v₂, ⟨v₁₁, h₁₂, rfl⟩, ⟨v₂₁, h₂₂, rfl⟩, rfl⟩
    have hpq := add_pos hp' hq'
    refine'
        mem_smul_set.2
          ⟨_,
            h_conv h₁₂ h₂₂ _ _
              (by
                rw [← div_self hpq.ne', add_div] : p / (p + q) + q / (p + q) = 1),
            by
            simp only [← mul_smul, smul_add, mul_div_cancel' _ hpq.ne']⟩ <;>
      trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `positivity #[]"
    

end AddCommGroupₓ

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `convex` and `ord_connected`.
-/


section

theorem Set.OrdConnected.convex_of_chain [OrderedSemiring 𝕜] [OrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E]
    {s : Set E} (hs : s.OrdConnected) (h : IsChain (· ≤ ·) s) : Convex 𝕜 s := by
  refine' convex_iff_segment_subset.mpr fun x hx y hy => _
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
    
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)
    

theorem Set.OrdConnected.convex [OrderedSemiring 𝕜] [LinearOrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E]
    {s : Set E} (hs : s.OrdConnected) : Convex 𝕜 s :=
  hs.convex_of_chain <| is_chain_of_trichotomous s

theorem convex_iff_ord_connected [LinearOrderedField 𝕜] {s : Set 𝕜} : Convex 𝕜 s ↔ s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset]

alias convex_iff_ord_connected ↔ Convex.ord_connected _

end

/-! #### Convexity of submodules/subspaces -/


namespace Submodule

variable [OrderedSemiring 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E]

protected theorem convex (K : Submodule 𝕜 E) : Convex 𝕜 (↑K : Set E) := by
  repeat'
    intro
  refine' add_mem (smul_mem _ _ _) (smul_mem _ _ _) <;> assumption

protected theorem star_convex (K : Submodule 𝕜 E) : StarConvex 𝕜 (0 : E) K :=
  K.Convex K.zero_mem

end Submodule

/-! ### Simplex -/


section Simplex

variable (𝕜) (ι : Type _) [OrderedSemiring 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
def StdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ (∑ x, f x) = 1 }

theorem std_simplex_eq_inter : StdSimplex 𝕜 ι = (⋂ x, { f | 0 ≤ f x }) ∩ { f | (∑ x, f x) = 1 } := by
  ext f
  simp only [StdSimplex, Set.mem_inter_eq, Set.mem_Inter, Set.mem_set_of_eq]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem convex_std_simplex : Convex 𝕜 (StdSimplex 𝕜 ι) := by
  refine' fun f hf g hg a b ha hb hab => ⟨fun x => _, _⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
    
  · erw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul, smul_eq_mul, mul_oneₓ,
      mul_oneₓ]
    exact hab
    

variable {ι}

theorem ite_eq_mem_std_simplex (i : ι) : (fun j => ite (i = j) (1 : 𝕜) 0) ∈ StdSimplex 𝕜 ι :=
  ⟨fun j => by
    simp only <;> split_ifs <;> norm_num, by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]⟩

end Simplex

