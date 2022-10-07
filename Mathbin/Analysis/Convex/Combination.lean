/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Analysis.Convex.Hull
import Mathbin.LinearAlgebra.AffineSpace.Basis

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `finset.center_mass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `finset.center_mass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/


open Set Function

open BigOperators Classical Pointwise

universe u u'

variable {R E F ι ι' : Type _} [LinearOrderedField R] [AddCommGroupₓ E] [AddCommGroupₓ F] [Module R E] [Module R F]
  {s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def Finsetₓ.centerMass (t : Finsetₓ ι) (w : ι → R) (z : ι → E) : E :=
  (∑ i in t, w i)⁻¹ • ∑ i in t, w i • z i

variable (i j : ι) (c : R) (t : Finsetₓ ι) (w : ι → R) (z : ι → E)

open Finsetₓ

theorem Finsetₓ.center_mass_empty : (∅ : Finsetₓ ι).centerMass w z = 0 := by
  simp only [center_mass, sum_empty, smul_zero]

theorem Finsetₓ.center_mass_pair (hne : i ≠ j) :
    ({i, j} : Finsetₓ ι).centerMass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := by
  simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable {w}

theorem Finsetₓ.center_mass_insert (ha : i ∉ t) (hw : (∑ j in t, w j) ≠ 0) :
    (insert i t).centerMass w z =
      (w i / (w i + ∑ j in t, w j)) • z i + ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.centerMass w z :=
  by
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul]
  congr 2
  rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]

theorem Finsetₓ.center_mass_singleton (hw : w i ≠ 0) : ({i} : Finsetₓ ι).centerMass w z = z i := by
  rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

theorem Finsetₓ.center_mass_eq_of_sum_1 (hw : (∑ i in t, w i) = 1) : t.centerMass w z = ∑ i in t, w i • z i := by
  simp only [Finsetₓ.centerMass, hw, inv_one, one_smul]

theorem Finsetₓ.center_mass_smul : (t.centerMass w fun i => c • z i) = c • t.centerMass w z := by
  simp only [Finsetₓ.centerMass, Finsetₓ.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem Finsetₓ.center_mass_segment' (s : Finsetₓ ι) (t : Finsetₓ ι') (ws : ι → R) (zs : ι → E) (wt : ι' → R)
    (zt : ι' → E) (hws : (∑ i in s, ws i) = 1) (hwt : (∑ i in t, wt i) = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass ws zs + b • t.centerMass wt zt =
      (s.map Embedding.inl ∪ t.map Embedding.inr).centerMass (Sum.elim (fun i => a * ws i) fun j => b * wt j)
        (Sum.elim zs zt) :=
  by
  rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ← Finsetₓ.sum_sum_elim,
    Finsetₓ.center_mass_eq_of_sum_1]
  · congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
    
  · rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_oneₓ, mul_oneₓ, hab]
    

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem Finsetₓ.center_mass_segment (s : Finsetₓ ι) (w₁ w₂ : ι → R) (z : ι → E) (hw₁ : (∑ i in s, w₁ i) = 1)
    (hw₂ : (∑ i in s, w₂ i) = 1) (a b : R) (hab : a + b = 1) :
    a • s.centerMass w₁ z + b • s.centerMass w₂ z = s.centerMass (fun i => a * w₁ i + b * w₂ i) z := by
  have hw : (∑ i in s, a * w₁ i + b * w₂ i) = 1 := by simp only [mul_sum.symm, sum_add_distrib, mul_oneₓ, *]
  simp only [Finsetₓ.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

theorem Finsetₓ.center_mass_ite_eq (hi : i ∈ t) : t.centerMass (fun j => if i = j then (1 : R) else 0) z = z i := by
  rw [Finsetₓ.center_mass_eq_of_sum_1]
  trans ∑ j in t, if i = j then z i else 0
  · congr with i
    split_ifs
    exacts[h ▸ one_smul _ _, zero_smul _ _]
    
  · rw [sum_ite_eq, if_pos hi]
    
  · rw [sum_ite_eq, if_pos hi]
    

variable {t w}

theorem Finsetₓ.center_mass_subset {t' : Finsetₓ ι} (ht : t ⊆ t') (h : ∀ i ∈ t', i ∉ t → w i = 0) :
    t.centerMass w z = t'.centerMass w z := by
  rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum]
  apply sum_subset ht
  intro i hit' hit
  rw [h i hit' hit, zero_smul, smul_zero]

theorem Finsetₓ.center_mass_filter_ne_zero : (t.filter fun i => w i ≠ 0).centerMass w z = t.centerMass w z :=
  (Finsetₓ.center_mass_subset z (filter_subset _ _)) fun i hit hit' => by
    simpa only [hit, mem_filter, true_andₓ, Ne.def, not_not] using hit'

variable {z}

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem Convex.center_mass_mem (hs : Convex R s) :
    (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i in t, w i) → (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ s := by
  induction' t using Finsetₓ.induction with i t hi ht
  · simp [lt_irreflₓ]
    
  intro h₀ hpos hmem
  have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
  have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
  rw [sum_insert hi] at hpos
  by_cases hsum_t:(∑ j in t, w j) = 0
  · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
    have wz : (∑ j in t, w j • z j) = 0 := sum_eq_zero fun i hi => by simp [ws i hi]
    simp only [center_mass, sum_insert hi, wz, hsum_t, add_zeroₓ]
    simp only [hsum_t, add_zeroₓ] at hpos
    rw [← mul_smul, inv_mul_cancel (ne_of_gtₓ hpos), one_smul]
    exact zi
    
  · rw [Finsetₓ.center_mass_insert _ _ _ hi hsum_t]
    refine' convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos
    · exact lt_of_le_of_neₓ (sum_nonneg hs₀) (Ne.symm hsum_t)
      
    · intro j hj
      exact hmem j (mem_insert_of_mem hj)
      
    · exact h₀ _ (mem_insert_self _ _)
      
    

theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : (∑ i in t, w i) = 1) (hz : ∀ i ∈ t, z i ∈ s) :
    (∑ i in t, w i • z i) ∈ s := by
  simpa only [h₁, center_mass, inv_one, one_smul] using hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

/-- A version of `convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R` is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a module over `R` such
that `z i ∈ s` whenever `w i ≠ 0``, then the sum `∑ᶠ i, w i • z i` belongs to `s`. See also
`partition_of_unity.finsum_smul_mem_convex`. -/
theorem Convex.finsum_mem {ι : Sort _} {w : ι → R} {z : ι → E} {s : Set E} (hs : Convex R s) (h₀ : ∀ i, 0 ≤ w i)
    (h₁ : (∑ᶠ i, w i) = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ s) : (∑ᶠ i, w i • z i) ∈ s := by
  have hfin_w : (support (w ∘ Plift.down)).Finite := by
    by_contra H
    rw [finsum, dif_neg H] at h₁
    exact zero_ne_one h₁
  have hsub : support ((fun i => w i • z i) ∘ Plift.down) ⊆ hfin_w.to_finset :=
    (support_smul_subset_left _ _).trans hfin_w.coe_to_finset.ge
  rw [finsum_eq_sum_plift_of_support_subset hsub]
  refine' hs.sum_mem (fun _ _ => h₀ _) _ fun i hi => hz _ _
  · rwa [finsum, dif_pos hfin_w] at h₁
    
  · rwa [hfin_w.mem_to_finset] at hi
    

theorem convex_iff_sum_mem :
    Convex R s ↔
      ∀ (t : Finsetₓ E) (w : E → R),
        (∀ i ∈ t, 0 ≤ w i) → (∑ i in t, w i) = 1 → (∀ x ∈ t, x ∈ s) → (∑ x in t, w x • x) ∈ s :=
  by
  refine' ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, _⟩
  intro h x hx y hy a b ha hb hab
  by_cases h_cases:x = y
  · rw [h_cases, ← add_smul, hab, one_smul]
    exact hy
    
  · convert h {x, y} (fun z => if z = y then b else a) _ _ _
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl]
      
    · simp_intro i hi
      cases hi <;> subst i <;> simp [ha, hb, if_neg h_cases]
      
    · simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab]
      
    · simp_intro i hi
      cases hi <;> subst i <;> simp [hx, hy, if_neg h_cases]
      
    

theorem Finsetₓ.center_mass_mem_convex_hull (t : Finsetₓ ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) : t.centerMass w z ∈ convexHull R s :=
  (convex_convex_hull R s).center_mass_mem hw₀ hws fun i hi => subset_convex_hull R s <| hz i hi

/-- A refinement of `finset.center_mass_mem_convex_hull` when the indexed family is a `finset` of
the space. -/
theorem Finsetₓ.center_mass_id_mem_convex_hull (t : Finsetₓ E) {w : E → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hws : 0 < ∑ i in t, w i) : t.centerMass w id ∈ convexHull R (t : Set E) :=
  t.center_mass_mem_convex_hull hw₀ hws fun i => mem_coe.2

theorem affine_combination_eq_center_mass {ι : Type _} {t : Finsetₓ ι} {p : ι → E} {w : ι → R}
    (hw₂ : (∑ i in t, w i) = 1) : affineCombination t p w = centerMass t w p := by
  rw [affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    Finsetₓ.weighted_vsub_of_point_apply, vadd_eq_add, add_zeroₓ, t.center_mass_eq_of_sum_1 _ hw₂]
  simp_rw [vsub_eq_sub, sub_zero]

theorem affine_combination_mem_convex_hull {s : Finsetₓ ι} {v : ι → E} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : s.Sum w = 1) : s.affineCombination v w ∈ convexHull R (range v) := by
  rw [affine_combination_eq_center_mass hw₁]
  apply s.center_mass_mem_convex_hull hw₀
  · simp [hw₁]
    
  · simp
    

/-- The centroid can be regarded as a center of mass. -/
@[simp]
theorem Finsetₓ.centroid_eq_center_mass (s : Finsetₓ ι) (hs : s.Nonempty) (p : ι → E) :
    s.centroid R p = s.centerMass (s.centroidWeights R) p :=
  affine_combination_eq_center_mass (s.sum_centroid_weights_eq_one_of_nonempty R hs)

theorem Finsetₓ.centroid_mem_convex_hull (s : Finsetₓ E) (hs : s.Nonempty) :
    s.centroid R id ∈ convexHull R (s : Set E) := by
  rw [s.centroid_eq_center_mass hs]
  apply s.center_mass_id_mem_convex_hull
  · simp only [inv_nonneg, implies_true_iff, Nat.cast_nonneg, Finsetₓ.centroid_weights_apply]
    
  · have hs_card : (s.card : R) ≠ 0 := by simp [finset.nonempty_iff_ne_empty.mp hs]
    simp only [hs_card, Finsetₓ.sum_const, nsmul_eq_mul, mul_inv_cancel, Ne.def, not_false_iff,
      Finsetₓ.centroid_weights_apply, zero_lt_one]
    

theorem convex_hull_range_eq_exists_affine_combination (v : ι → E) :
    convexHull R (range v) =
      { x | ∃ (s : Finsetₓ ι)(w : ι → R)(hw₀ : ∀ i ∈ s, 0 ≤ w i)(hw₁ : s.Sum w = 1), s.affineCombination v w = x } :=
  by
  refine' subset.antisymm (convex_hull_min _ _) _
  · intro x hx
    obtain ⟨i, hi⟩ := set.mem_range.mp hx
    refine' ⟨{i}, Function.const ι (1 : R), by simp, by simp, by simp [hi]⟩
    
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab
    let W : ι → R := fun i => (if i ∈ s then a * w i else 0) + if i ∈ s' then b * w' i else 0
    have hW₁ : (s ∪ s').Sum W = 1 := by
      rw [sum_add_distrib, ← sum_subset (subset_union_left s s'), ← sum_subset (subset_union_right s s'),
          sum_ite_of_true _ _ fun i hi => hi, sum_ite_of_true _ _ fun i hi => hi, ← mul_sum, ← mul_sum, hw₁, hw₁', ←
          add_mulₓ, hab, mul_oneₓ] <;>
        intro i hi hi' <;> simp [hi']
    refine' ⟨s ∪ s', W, _, hW₁, _⟩
    · rintro i -
      by_cases hi:i ∈ s <;>
        by_cases hi':i ∈ s' <;> simp [hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)]
      
    · simp_rw [affine_combination_eq_linear_combination (s ∪ s') v _ hW₁,
        affine_combination_eq_linear_combination s v w hw₁, affine_combination_eq_linear_combination s' v w' hw₁',
        add_smul, sum_add_distrib]
      rw [← sum_subset (subset_union_left s s'), ← sum_subset (subset_union_right s s')]
      · simp only [ite_smul, sum_ite_of_true _ _ fun i hi => hi, mul_smul, ← smul_sum]
        
      · intro i hi hi'
        simp [hi']
        
      · intro i hi hi'
        simp [hi']
        
      
    
  · rintro x ⟨s, w, hw₀, hw₁, rfl⟩
    exact affine_combination_mem_convex_hull hw₀ hw₁
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
theorem convex_hull_eq (s : Set E) :
    convexHull R s =
      { x : E |
        ∃ (ι : Type u')(t : Finsetₓ ι)(w : ι → R)(z : ι → E)(hw₀ : ∀ i ∈ t, 0 ≤ w i)(hw₁ : (∑ i in t, w i) = 1)(hz :
          ∀ i ∈ t, z i ∈ s), t.centerMass w z = x } :=
  by
  refine' subset.antisymm (convex_hull_min _ _) _
  · intro x hx
    use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, Finsetₓ.sum_singleton, fun _ _ => hx
    simp only [Finsetₓ.centerMass, Finsetₓ.sum_singleton, inv_one, one_smul]
    
  · rintro x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha hb hab
    rw [Finsetₓ.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine' ⟨_, _, _, _, _, _, _, rfl⟩
    · rintro i hi
      rw [Finsetₓ.mem_union, Finsetₓ.mem_map, Finsetₓ.mem_map] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;>
        simp only [Sum.elim_inl, Sum.elim_inr] <;> apply_rules [mul_nonneg, hwx₀, hwy₀]
      
    · simp [Finsetₓ.sum_sum_elim, finset.mul_sum.symm, *]
      
    · intro i hi
      rw [Finsetₓ.mem_union, Finsetₓ.mem_map, Finsetₓ.mem_map] at hi
      rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> apply_rules [hzx, hzy]
      
    
  · rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    exact t.center_mass_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hz
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem Finsetₓ.convex_hull_eq (s : Finsetₓ E) :
    convexHull R ↑s =
      { x : E | ∃ (w : E → R)(hw₀ : ∀ y ∈ s, 0 ≤ w y)(hw₁ : (∑ y in s, w y) = 1), s.centerMass w id = x } :=
  by
  refine' subset.antisymm (convex_hull_min _ _) _
  · intro x hx
    rw [Finsetₓ.mem_coe] at hx
    refine' ⟨_, _, _, Finsetₓ.center_mass_ite_eq _ _ _ hx⟩
    · intros
      split_ifs
      exacts[zero_le_one, le_reflₓ 0]
      
    · rw [Finsetₓ.sum_ite_eq, if_pos hx]
      
    
  · rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab
    rw [Finsetₓ.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
    refine' ⟨_, _, _, rfl⟩
    · rintro i hi
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
      
    · simp only [Finsetₓ.sum_add_distrib, finset.mul_sum.symm, mul_oneₓ, *]
      
    
  · rintro _ ⟨w, hw₀, hw₁, rfl⟩
    exact s.center_mass_mem_convex_hull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx
    

theorem Set.Finite.convex_hull_eq {s : Set E} (hs : s.Finite) :
    convexHull R s =
      { x : E |
        ∃ (w : E → R)(hw₀ : ∀ y ∈ s, 0 ≤ w y)(hw₁ : (∑ y in hs.toFinset, w y) = 1), hs.toFinset.centerMass w id = x } :=
  by simpa only [Set.Finite.coe_to_finset, Set.Finite.mem_to_finset, exists_propₓ] using hs.to_finset.convex_hull_eq

/-- A weak version of Carathéodory's theorem. -/
theorem convex_hull_eq_union_convex_hull_finite_subsets (s : Set E) :
    convexHull R s = ⋃ (t : Finsetₓ E) (w : ↑t ⊆ s), convexHull R ↑t := by
  refine' subset.antisymm _ _
  · rw [convex_hull_eq]
    rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
    simp only [mem_Union]
    refine' ⟨t.image z, _, _⟩
    · rw [coe_image, Set.image_subset_iff]
      exact hz
      
    · apply t.center_mass_mem_convex_hull hw₀
      · simp only [hw₁, zero_lt_one]
        
      · exact fun i hi => Finsetₓ.mem_coe.2 (Finsetₓ.mem_image_of_mem _ hi)
        
      
    
  · exact Union_subset fun i => Union_subset convex_hull_mono
    

-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
theorem mk_mem_convex_hull_prod {t : Set F} {x : E} {y : F} (hx : x ∈ convexHull R s) (hy : y ∈ convexHull R t) :
    (x, y) ∈ convexHull R (s ×ˢ t) := by
  rw [convex_hull_eq] at hx hy⊢
  obtain ⟨ι, a, w, S, hw, hw', hS, hSp⟩ := hx
  obtain ⟨κ, b, v, T, hv, hv', hT, hTp⟩ := hy
  have h_sum : (∑ i : ι × κ in a ×ˢ b, w i.fst * v i.snd) = 1 := by
    rw [Finsetₓ.sum_product, ← hw']
    congr
    ext i
    have : (∑ y : κ in b, w i * v y) = ∑ y : κ in b, v y * w i := by
      congr
      ext
      simp [mul_comm]
    rw [this, ← Finsetₓ.sum_mul, hv']
    simp
  refine' ⟨ι × κ, a ×ˢ b, fun p => w p.1 * v p.2, fun p => (S p.1, T p.2), fun p hp => _, h_sum, fun p hp => _, _⟩
  · rw [mem_product] at hp
    exact mul_nonneg (hw p.1 hp.1) (hv p.2 hp.2)
    
  · rw [mem_product] at hp
    exact ⟨hS p.1 hp.1, hT p.2 hp.2⟩
    
  ext
  · rw [← hSp, Finsetₓ.center_mass_eq_of_sum_1 _ _ hw', Finsetₓ.center_mass_eq_of_sum_1 _ _ h_sum]
    simp_rw [Prod.fst_sum, Prod.smul_mk]
    rw [Finsetₓ.sum_product]
    congr
    ext i
    have : (∑ j : κ in b, (w i * v j) • S i) = ∑ j : κ in b, v j • w i • S i := by
      congr
      ext
      rw [mul_smul, smul_comm]
    rw [this, ← Finsetₓ.sum_smul, hv', one_smul]
    
  · rw [← hTp, Finsetₓ.center_mass_eq_of_sum_1 _ _ hv', Finsetₓ.center_mass_eq_of_sum_1 _ _ h_sum]
    simp_rw [Prod.snd_sum, Prod.smul_mk]
    rw [Finsetₓ.sum_product, Finsetₓ.sum_comm]
    congr
    ext j
    simp_rw [mul_smul]
    rw [← Finsetₓ.sum_smul, hw', one_smul]
    

-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
-- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation
@[simp]
theorem convex_hull_prod (s : Set E) (t : Set F) : convexHull R (s ×ˢ t) = convexHull R s ×ˢ convexHull R t :=
  Subset.antisymm
      (convex_hull_min (prod_mono (subset_convex_hull _ _) <| subset_convex_hull _ _) <|
        (convex_convex_hull _ _).Prod <| convex_convex_hull _ _) <|
    prod_subset_iff.2 fun x hx y => mk_mem_convex_hull_prod hx

theorem convex_hull_add (s t : Set E) : convexHull R (s + t) = convexHull R s + convexHull R t := by
  simp_rw [← image2_add, ← image_prod, is_linear_map.is_linear_map_add.convex_hull_image, convex_hull_prod]

theorem convex_hull_sub (s t : Set E) : convexHull R (s - t) = convexHull R s - convexHull R t := by
  simp_rw [sub_eq_add_neg, convex_hull_add, convex_hull_neg]

/-! ### `std_simplex` -/


variable (ι) [Fintypeₓ ι] {f : ι → R}

/-- `std_simplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
theorem convex_hull_basis_eq_std_simplex :
    convexHull R (range fun i j : ι => if i = j then (1 : R) else 0) = StdSimplex R ι := by
  refine' subset.antisymm (convex_hull_min _ (convex_std_simplex R ι)) _
  · rintro _ ⟨i, rfl⟩
    exact ite_eq_mem_std_simplex R i
    
  · rintro w ⟨hw₀, hw₁⟩
    rw [pi_eq_sum_univ w, ← finset.univ.center_mass_eq_of_sum_1 _ hw₁]
    exact
      finset.univ.center_mass_mem_convex_hull (fun i hi => hw₀ i) (hw₁.symm ▸ zero_lt_one) fun i hi => mem_range_self i
    

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
theorem Set.Finite.convex_hull_eq_image {s : Set E} (hs : s.Finite) :
    convexHull R s =
      haveI := hs.fintype
      ⇑(∑ x : s, (@LinearMap.proj R s _ (fun i => R) _ _ x).smul_right x.1) '' StdSimplex R s :=
  by
  rw [← convex_hull_basis_eq_std_simplex, ← LinearMap.convex_hull_image, ← Set.range_comp, (· ∘ ·)]
  apply congr_arg
  convert subtype.range_coe.symm
  ext x
  simp [LinearMap.sum_apply, ite_smul, Finsetₓ.filter_eq]

/-- All values of a function `f ∈ std_simplex 𝕜 ι` belong to `[0, 1]`. -/
theorem mem_Icc_of_mem_std_simplex (hf : f ∈ StdSimplex R ι) (x) : f x ∈ icc (0 : R) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finsetₓ.single_le_sum (fun y hy => hf.1 y) (Finsetₓ.mem_univ x)⟩

/-- The convex hull of an affine basis is the intersection of the half-spaces defined by the
corresponding barycentric coordinates. -/
theorem convex_hull_affine_basis_eq_nonneg_barycentric {ι : Type _} (b : AffineBasis ι R E) :
    convexHull R (range b.points) = { x | ∀ i, 0 ≤ b.Coord i x } := by
  rw [convex_hull_range_eq_exists_affine_combination]
  ext x
  constructor
  · rintro ⟨s, w, hw₀, hw₁, rfl⟩ i
    by_cases hi:i ∈ s
    · rw [b.coord_apply_combination_of_mem hi hw₁]
      exact hw₀ i hi
      
    · rw [b.coord_apply_combination_of_not_mem hi hw₁]
      
    
  · intro hx
    have hx' : x ∈ affineSpan R (range b.points) := by
      rw [b.tot]
      exact AffineSubspace.mem_top R E x
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affine_span_iff_eq_affine_combination R E).mp hx'
    refine' ⟨s, w, _, hw₁, rfl⟩
    intro i hi
    specialize hx i
    rw [b.coord_apply_combination_of_mem hi hw₁] at hx
    exact hx
    

