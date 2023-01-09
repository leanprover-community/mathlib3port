/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module analysis.convex.strict
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Topology.Order.Basic

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.
-/


open Set

open Convex Pointwise

variable {𝕜 𝕝 E F β : Type _}

open Function Set

open Convex

section OrderedSemiring

variable [OrderedSemiring 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E] [HasSmul 𝕜 F] (s : Set E)

/-- A set is strictly convex if the open segment between any two distinct points lies is in its
interior. This basically means "convex and not flat on the boundary". -/
def StrictConvex : Prop :=
  s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ interior s
#align strict_convex StrictConvex

variable {𝕜 s} {x y : E} {a b : 𝕜}

theorem strict_convex_iff_open_segment_subset :
    StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y ⊆ interior s :=
  forall₅_congr fun x hx y hy hxy => (open_segment_subset_iff 𝕜).symm
#align strict_convex_iff_open_segment_subset strict_convex_iff_open_segment_subset

theorem StrictConvex.open_segment_subset (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s)
    (h : x ≠ y) : openSegment 𝕜 x y ⊆ interior s :=
  strict_convex_iff_open_segment_subset.1 hs hx hy h
#align strict_convex.open_segment_subset StrictConvex.open_segment_subset

theorem strict_convex_empty : StrictConvex 𝕜 (∅ : Set E) :=
  pairwise_empty _
#align strict_convex_empty strict_convex_empty

theorem strict_convex_univ : StrictConvex 𝕜 (univ : Set E) :=
  by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_univ]
  exact mem_univ _
#align strict_convex_univ strict_convex_univ

protected theorem StrictConvex.eq (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
  (hs.Eq hx hy) fun H => h <| H ha hb hab
#align strict_convex.eq StrictConvex.eq

protected theorem StrictConvex.inter {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s ∩ t) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩
#align strict_convex.inter StrictConvex.inter

theorem Directed.strict_convex_Union {ι : Sort _} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hs : ∀ ⦃i : ι⦄, StrictConvex 𝕜 (s i)) : StrictConvex 𝕜 (⋃ i, s i) :=
  by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_Union] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_Union s k) (hs (hik hx) (hjk hy) hxy ha hb hab)
#align directed.strict_convex_Union Directed.strict_convex_Union

theorem DirectedOn.strict_convex_sUnion {S : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) S)
    (hS : ∀ s ∈ S, StrictConvex 𝕜 s) : StrictConvex 𝕜 (⋃₀ S) :=
  by
  rw [sUnion_eq_Union]
  exact (directedOn_iff_directed.1 hdir).strict_convex_Union fun s => hS _ s.2
#align directed_on.strict_convex_sUnion DirectedOn.strict_convex_sUnion

end HasSmul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

protected theorem StrictConvex.convex (hs : StrictConvex 𝕜 s) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    interior_subset <| hs hx hy hxy ha hb hab
#align strict_convex.convex StrictConvex.convex

/-- An open convex set is strictly convex. -/
protected theorem Convex.strict_convex_of_open (h : IsOpen s) (hs : Convex 𝕜 s) :
    StrictConvex 𝕜 s := fun x hx y hy _ a b ha hb hab =>
  h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab
#align convex.strict_convex_of_open Convex.strict_convex_of_open

theorem IsOpen.strict_convex_iff (h : IsOpen s) : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, Convex.strict_convex_of_open h⟩
#align is_open.strict_convex_iff IsOpen.strict_convex_iff

theorem strict_convex_singleton (c : E) : StrictConvex 𝕜 ({c} : Set E) :=
  pairwise_singleton _ _
#align strict_convex_singleton strict_convex_singleton

theorem Set.Subsingleton.strict_convex (hs : s.Subsingleton) : StrictConvex 𝕜 s :=
  hs.Pairwise _
#align set.subsingleton.strict_convex Set.Subsingleton.strict_convex

theorem StrictConvex.linear_image [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F]
    [LinearMap.CompatibleSmul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕝] F) (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) :=
  by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine' hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, _⟩
  rw [map_add, f.map_smul_of_tower a, f.map_smul_of_tower b]
#align strict_convex.linear_image StrictConvex.linear_image

theorem StrictConvex.is_linear_image (hs : StrictConvex 𝕜 s) {f : E → F} (h : IsLinearMap 𝕜 f)
    (hf : IsOpenMap f) : StrictConvex 𝕜 (f '' s) :=
  hs.linear_image (h.mk' f) hf
#align strict_convex.is_linear_image StrictConvex.is_linear_image

theorem StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕜] F)
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (s.Preimage f) :=
  by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage hf _
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab
#align strict_convex.linear_preimage StrictConvex.linear_preimage

theorem StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E → F}
    (h : IsLinearMap 𝕜 f) (hf : Continuous f) (hfinj : Injective f) :
    StrictConvex 𝕜 (s.Preimage f) :=
  hs.linear_preimage (h.mk' f) hf hfinj
#align strict_convex.is_linear_preimage StrictConvex.is_linear_preimage

section LinearOrderedCancelAddCommMonoid

variable [TopologicalSpace β] [LinearOrderedCancelAddCommMonoid β] [OrderTopology β] [Module 𝕜 β]
  [OrderedSmul 𝕜 β]

protected theorem Set.OrdConnected.strict_convex {s : Set β} (hs : OrdConnected s) :
    StrictConvex 𝕜 s :=
  by
  refine' strict_convex_iff_open_segment_subset.2 fun x hx y hy hxy => _
  cases' hxy.lt_or_lt with hlt hlt <;> [skip, rw [open_segment_symm]] <;>
    exact
      (open_segment_subset_Ioo hlt).trans
        (is_open_Ioo.subset_interior_iff.2 <| Ioo_subset_Icc_self.trans <| hs.out ‹_› ‹_›)
#align set.ord_connected.strict_convex Set.OrdConnected.strict_convex

theorem strict_convex_Iic (r : β) : StrictConvex 𝕜 (Iic r) :=
  ordConnected_Iic.StrictConvex
#align strict_convex_Iic strict_convex_Iic

theorem strict_convex_Ici (r : β) : StrictConvex 𝕜 (Ici r) :=
  ordConnected_Ici.StrictConvex
#align strict_convex_Ici strict_convex_Ici

theorem strict_convex_Iio (r : β) : StrictConvex 𝕜 (Iio r) :=
  ord_connected_Iio.StrictConvex
#align strict_convex_Iio strict_convex_Iio

theorem strict_convex_Ioi (r : β) : StrictConvex 𝕜 (Ioi r) :=
  ordConnected_Ioi.StrictConvex
#align strict_convex_Ioi strict_convex_Ioi

theorem strict_convex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s) :=
  ordConnected_Icc.StrictConvex
#align strict_convex_Icc strict_convex_Icc

theorem strict_convex_Ioo (r s : β) : StrictConvex 𝕜 (Ioo r s) :=
  ordConnected_Ioo.StrictConvex
#align strict_convex_Ioo strict_convex_Ioo

theorem strict_convex_Ico (r s : β) : StrictConvex 𝕜 (Ico r s) :=
  ordConnected_Ico.StrictConvex
#align strict_convex_Ico strict_convex_Ico

theorem strict_convex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s) :=
  ordConnected_Ioc.StrictConvex
#align strict_convex_Ioc strict_convex_Ioc

theorem strict_convex_interval (r s : β) : StrictConvex 𝕜 (interval r s) :=
  strict_convex_Icc _ _
#align strict_convex_interval strict_convex_interval

theorem strict_convex_interval_oc (r s : β) : StrictConvex 𝕜 (intervalOC r s) :=
  strict_convex_Ioc _ _
#align strict_convex_interval_oc strict_convex_interval_oc

end LinearOrderedCancelAddCommMonoid

end Module

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [HasContinuousAdd E] [Module 𝕜 E] {s : Set E}

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.preimage_add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) ⁻¹' s) :=
  by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage (continuous_add_left _) _
  have h := hs hx hy ((add_right_injective _).Ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h
#align strict_convex.preimage_add_right StrictConvex.preimage_add_right

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.preimage_add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.preimage_add_right z
#align strict_convex.preimage_add_left StrictConvex.preimage_add_left

end AddCancelCommMonoid

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

section continuous_add

variable [HasContinuousAdd E] {s t : Set E}

theorem StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictConvex 𝕜 (s + t) :=
  by
  rintro _ ⟨v, w, hv, hw, rfl⟩ _ ⟨x, y, hx, hy, rfl⟩ h a b ha hb hab
  rw [smul_add, smul_add, add_add_add_comm]
  obtain rfl | hvx := eq_or_ne v x
  · refine' interior_mono (add_subset_add (singleton_subset_iff.2 hv) subset.rfl) _
    rw [Convex.combo_self hab, singleton_add]
    exact
      (is_open_map_add_left _).image_interior_subset _
        (mem_image_of_mem _ <| ht hw hy (ne_of_apply_ne _ h) ha hb hab)
  exact
    subset_interior_add_left
      (add_mem_add (hs hv hx hvx ha hb hab) <| ht.convex hw hy ha.le hb.le hab)
#align strict_convex.add StrictConvex.add

theorem StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) '' s) := by
  simpa only [singleton_add] using (strict_convex_singleton z).add hs
#align strict_convex.add_left StrictConvex.add_left

theorem StrictConvex.add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) '' s) := by simpa only [add_comm] using hs.add_left z
#align strict_convex.add_right StrictConvex.add_right

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : StrictConvex 𝕜 (x +ᵥ s) :=
  hs.add_left x
#align strict_convex.vadd StrictConvex.vadd

end continuous_add

section ContinuousSmul

variable [LinearOrderedField 𝕝] [Module 𝕝 E] [HasContinuousConstSmul 𝕝 E]
  [LinearMap.CompatibleSmul E E 𝕜 𝕝] {s : Set E} {x : E}

theorem StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : StrictConvex 𝕜 (c • s) :=
  by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).StrictConvex
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (is_open_map_smul₀ hc)
#align strict_convex.smul StrictConvex.smul

theorem StrictConvex.affinity [HasContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c : 𝕝) :
    StrictConvex 𝕜 (z +ᵥ c • s) :=
  (hs.smul c).vadd z
#align strict_convex.affinity StrictConvex.affinity

end ContinuousSmul

end AddCommGroup

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [TopologicalSpace E]

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] [NoZeroSMulDivisors 𝕜 E] [HasContinuousConstSmul 𝕜 E]
  {s : Set E}

theorem StrictConvex.preimage_smul (hs : StrictConvex 𝕜 s) (c : 𝕜) :
    StrictConvex 𝕜 ((fun z => c • z) ⁻¹' s) := by
  classical
    obtain rfl | hc := eq_or_ne c 0
    · simp_rw [zero_smul, preimage_const]
      split_ifs
      · exact strict_convex_univ
      · exact strict_convex_empty
    refine' hs.linear_preimage (LinearMap.lsmul _ _ c) _ (smul_right_injective E hc)
    unfold LinearMap.lsmul LinearMap.mk₂ LinearMap.mk₂' LinearMap.mk₂'ₛₗ
    exact continuous_const_smul _
#align strict_convex.preimage_smul StrictConvex.preimage_smul

end AddCommGroup

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E} {x y : E}

theorem StrictConvex.eq_of_open_segment_subset_frontier [Nontrivial 𝕜] [DenselyOrdered 𝕜]
    (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (h : openSegment 𝕜 x y ⊆ frontier s) :
    x = y := by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
    by_contra hxy
    exact
      (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, rfl⟩).2
        (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel'_right _ _)
#align
  strict_convex.eq_of_open_segment_subset_frontier StrictConvex.eq_of_open_segment_subset_frontier

theorem StrictConvex.add_smul_mem (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hxy : x + y ∈ s)
    (hy : y ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • y ∈ interior s :=
  by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  refine' hs hx hxy (fun h => hy <| add_left_cancel _) (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel _ _)
  exact x
  rw [← h, add_zero]
#align strict_convex.add_smul_mem StrictConvex.add_smul_mem

theorem StrictConvex.smul_mem_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s)
    (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : t • x ∈ interior s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁
#align strict_convex.smul_mem_of_zero_mem StrictConvex.smul_mem_of_zero_mem

theorem StrictConvex.add_smul_sub_mem (h : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • (y - x) ∈ interior s :=
  by
  apply h.open_segment_subset hx hy hxy
  rw [open_segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩
#align strict_convex.add_smul_sub_mem StrictConvex.add_smul_sub_mem

/-- The preimage of a strictly convex set under an affine map is strictly convex. -/
theorem StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F}
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (f ⁻¹' s) :=
  by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage hf _
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab
#align strict_convex.affine_preimage StrictConvex.affine_preimage

/-- The image of a strictly convex set under an affine map is strictly convex. -/
theorem StrictConvex.affine_image (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F} (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) :=
  by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩
#align strict_convex.affine_image StrictConvex.affine_image

variable [TopologicalAddGroup E]

theorem StrictConvex.neg (hs : StrictConvex 𝕜 s) : StrictConvex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMapNeg continuous_id.neg neg_injective
#align strict_convex.neg StrictConvex.neg

theorem StrictConvex.sub (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictConvex 𝕜 (s - t) :=
  (sub_eq_add_neg s t).symm ▸ hs.add ht.neg
#align strict_convex.sub StrictConvex.sub

end AddCommGroup

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace E]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

/-- Alternative definition of set strict convexity, using division. -/
theorem strict_convex_iff_div :
    StrictConvex 𝕜 s ↔
      s.Pairwise fun x y =>
        ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → (a / (a + b)) • x + (b / (a + b)) • y ∈ interior s :=
  ⟨fun h x hx y hy hxy a b ha hb =>
    by
    apply h hx hy hxy (div_pos ha <| add_pos ha hb) (div_pos hb <| add_pos ha hb)
    rw [← add_div]
    exact div_self (add_pos ha hb).ne', fun h x hx y hy hxy a b ha hb hab => by
    convert h hx hy hxy ha hb <;> rw [hab, div_one]⟩
#align strict_convex_iff_div strict_convex_iff_div

theorem StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s)
    (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht : 1 < t) : x ∈ t • interior s :=
  by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans ht).ne']
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (inv_pos.2 <| zero_lt_one.trans ht) (inv_lt_one ht)
#align strict_convex.mem_smul_of_zero_mem StrictConvex.mem_smul_of_zero_mem

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space

Relates `convex` and `set.ord_connected`.
-/


section

variable [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {s : Set 𝕜}

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp]
theorem strict_convex_iff_convex : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, fun hs => hs.OrdConnected.StrictConvex⟩
#align strict_convex_iff_convex strict_convex_iff_convex

theorem strict_convex_iff_ord_connected : StrictConvex 𝕜 s ↔ s.OrdConnected :=
  strict_convex_iff_convex.trans convex_iff_ord_connected
#align strict_convex_iff_ord_connected strict_convex_iff_ord_connected

alias strict_convex_iff_ord_connected ↔ StrictConvex.ord_connected _

end

