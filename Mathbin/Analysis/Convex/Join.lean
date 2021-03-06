/-
Copyright (c) 2022 YaΓ«l Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YaΓ«l Dillies
-/
import Mathbin.Analysis.Convex.Combination

/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/


open Set

open BigOperators

variable {ΞΉ : Sort _} {π E : Type _}

section OrderedSemiring

variable (π) [OrderedSemiring π] [AddCommMonoidβ E] [Module π E] {s t sβ sβ tβ tβ u : Set E} {x y : E}

/-- The join of two sets is the union of the segments joining them. This can be interpreted as the
topological join, but within the original space. -/
def ConvexJoin (s t : Set E) : Set E :=
  β (x β s) (y β t), Segment π x y

variable {π}

theorem mem_convex_join : x β ConvexJoin π s t β β a β s, β b β t, x β Segment π a b := by
  simp [β ConvexJoin]

theorem convex_join_comm (s t : Set E) : ConvexJoin π s t = ConvexJoin π t s :=
  (Unionβ_comm _).trans <| by
    simp_rw [ConvexJoin, segment_symm]

theorem convex_join_mono (hs : sβ β sβ) (ht : tβ β tβ) : ConvexJoin π sβ tβ β ConvexJoin π sβ tβ :=
  (bUnion_mono hs) fun x hx => (bUnion_mono ht) fun y hy => Subset.rfl

theorem convex_join_mono_left (hs : sβ β sβ) : ConvexJoin π sβ t β ConvexJoin π sβ t :=
  convex_join_mono hs Subset.rfl

theorem convex_join_mono_right (ht : tβ β tβ) : ConvexJoin π s tβ β ConvexJoin π s tβ :=
  convex_join_mono Subset.rfl ht

@[simp]
theorem convex_join_empty_left (t : Set E) : ConvexJoin π β t = β := by
  simp [β ConvexJoin]

@[simp]
theorem convex_join_empty_right (s : Set E) : ConvexJoin π s β = β := by
  simp [β ConvexJoin]

@[simp]
theorem convex_join_singleton_left (t : Set E) (x : E) : ConvexJoin π {x} t = β y β t, Segment π x y := by
  simp [β ConvexJoin]

@[simp]
theorem convex_join_singleton_right (s : Set E) (y : E) : ConvexJoin π s {y} = β x β s, Segment π x y := by
  simp [β ConvexJoin]

@[simp]
theorem convex_join_singletons (x : E) : ConvexJoin π {x} {y} = Segment π x y := by
  simp [β ConvexJoin]

@[simp]
theorem convex_join_union_left (sβ sβ t : Set E) : ConvexJoin π (sβ βͺ sβ) t = ConvexJoin π sβ t βͺ ConvexJoin π sβ t :=
  by
  simp_rw [ConvexJoin, mem_union_eq, Union_or, Union_union_distrib]

@[simp]
theorem convex_join_union_right (s tβ tβ : Set E) : ConvexJoin π s (tβ βͺ tβ) = ConvexJoin π s tβ βͺ ConvexJoin π s tβ :=
  by
  simp_rw [ConvexJoin, mem_union_eq, Union_or, Union_union_distrib]

@[simp]
theorem convex_join_Union_left (s : ΞΉ β Set E) (t : Set E) : ConvexJoin π (β i, s i) t = β i, ConvexJoin π (s i) t := by
  simp_rw [ConvexJoin, mem_Union, Union_exists]
  exact Union_comm _

@[simp]
theorem convex_join_Union_right (s : Set E) (t : ΞΉ β Set E) : ConvexJoin π s (β i, t i) = β i, ConvexJoin π s (t i) :=
  by
  simp_rw [convex_join_comm s, convex_join_Union_left]

theorem segment_subset_convex_join (hx : x β s) (hy : y β t) : Segment π x y β ConvexJoin π s t :=
  (subset_Unionβ y hy).trans (subset_Unionβ x hx)

theorem subset_convex_join_left (h : t.Nonempty) : s β ConvexJoin π s t := fun x hx =>
  let β¨y, hyβ© := h
  segment_subset_convex_join hx hy <| left_mem_segment _ _ _

theorem subset_convex_join_right (h : s.Nonempty) : t β ConvexJoin π s t := fun y hy =>
  let β¨x, hxβ© := h
  segment_subset_convex_join hx hy <| right_mem_segment _ _ _

theorem convex_join_subset (hs : s β u) (ht : t β u) (hu : Convex π u) : ConvexJoin π s t β u :=
  Unionβ_subset fun x hx => Unionβ_subset fun y hy => hu.segment_subset (hs hx) (ht hy)

theorem convex_join_subset_convex_hull (s t : Set E) : ConvexJoin π s t β convexHull π (s βͺ t) :=
  convex_join_subset ((subset_union_left _ _).trans <| subset_convex_hull _ _)
      ((subset_union_right _ _).trans <| subset_convex_hull _ _) <|
    convex_convex_hull _ _

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField π] [AddCommGroupβ E] [Module π E] {s t u : Set E} {x y : E}

theorem convex_join_assoc_aux (s t u : Set E) : ConvexJoin π (ConvexJoin π s t) u β ConvexJoin π s (ConvexJoin π t u) :=
  by
  simp_rw [subset_def, mem_convex_join]
  rintro _ β¨z, β¨x, hx, y, hy, aβ, bβ, haβ, hbβ, habβ, rflβ©, z, hz, aβ, bβ, haβ, hbβ, habβ, rflβ©
  obtain rfl | hbβ := hbβ.eq_or_lt
  Β· refine' β¨x, hx, y, β¨y, hy, z, hz, left_mem_segment _ _ _β©, aβ, bβ, haβ, hbβ, habβ, _β©
    rw [add_zeroβ] at habβ
    rw [habβ, one_smul, zero_smul, add_zeroβ]
    
  have haβbβ : 0 β€ aβ * bβ := mul_nonneg haβ hbβ
  have hab : 0 < aβ * bβ + bβ := add_pos_of_nonneg_of_pos haβbβ hbβ
  refine'
    β¨x, hx, (aβ * bβ / (aβ * bβ + bβ)) β’ y + (bβ / (aβ * bβ + bβ)) β’ z, β¨y, hy, z, hz, _, _, _, _, _, rflβ©, aβ * aβ,
      aβ * bβ + bβ, mul_nonneg haβ haβ, hab.le, _, _β©
  Β· exact div_nonneg haβbβ hab.le
    
  Β· exact div_nonneg hbβ.le hab.le
    
  Β· rw [β add_div, div_self hab.ne']
    
  Β· rw [β add_assocβ, β mul_addβ, habβ, mul_oneβ, habβ]
    
  Β· simp_rw [smul_add, β mul_smul, mul_div_cancel' _ hab.ne', add_assocβ]
    

theorem convex_join_assoc (s t u : Set E) : ConvexJoin π (ConvexJoin π s t) u = ConvexJoin π s (ConvexJoin π t u) := by
  refine' (convex_join_assoc_aux _ _ _).antisymm _
  simp_rw [convex_join_comm s, convex_join_comm _ u]
  exact convex_join_assoc_aux _ _ _

theorem convex_join_left_comm (s t u : Set E) : ConvexJoin π s (ConvexJoin π t u) = ConvexJoin π t (ConvexJoin π s u) :=
  by
  simp_rw [β convex_join_assoc, convex_join_comm]

theorem convex_join_right_comm (s t u : Set E) :
    ConvexJoin π (ConvexJoin π s t) u = ConvexJoin π (ConvexJoin π s u) t := by
  simp_rw [convex_join_assoc, convex_join_comm]

theorem convex_join_convex_join_convex_join_comm (s t u v : Set E) :
    ConvexJoin π (ConvexJoin π s t) (ConvexJoin π u v) = ConvexJoin π (ConvexJoin π s u) (ConvexJoin π t v) := by
  simp_rw [β convex_join_assoc, convex_join_right_comm]

theorem convex_hull_insert (hs : s.Nonempty) : convexHull π (insert x s) = ConvexJoin π {x} (convexHull π s) := by
  classical
  refine'
    (convex_join_subset ((singleton_subset_iff.2 <| mem_insert _ _).trans <| subset_convex_hull _ _)
            (convex_hull_mono <| subset_insert _ _) <|
          convex_convex_hull _ _).antisymm'
      fun x hx => _
  rw [convex_hull_eq] at hx
  obtain β¨ΞΉ, t, w, z, hwβ, hwβ, hz, rflβ© := hx
  have :
    ((β i in t.filter fun i => z i = x, w i) β’ x + β i in t.filter fun i => z i β  x, w i β’ z i) = t.center_mass w z :=
    by
    rw [Finset.center_mass_eq_of_sum_1 _ _ hwβ, Finset.sum_smul]
    convert Finset.sum_filter_add_sum_filter_not _ _ (w β’ z) using 2
    refine' Finset.sum_congr rfl fun i hi => _
    rw [Pi.smul_apply', (Finset.mem_filter.1 hi).2]
  rw [β this]
  have hwβ' : β, β i β t.filter fun i => z i β  x, β, 0 β€ w i := fun i hi => hwβ _ <| Finset.filter_subset _ _ hi
  obtain hw | hw := (Finset.sum_nonneg hwβ').eq_or_gt
  Β· rw [β Finset.sum_filter_add_sum_filter_not _ fun i => z i = x, hw, add_zeroβ] at hwβ
    rw [hwβ, one_smul, Finset.sum_eq_zero, add_zeroβ]
    Β· exact subset_convex_join_left hs.convex_hull (mem_singleton _)
      
    simp_rw [Finset.sum_eq_zero_iff_of_nonneg hwβ'] at hw
    rintro i hi
    rw [hw _ hi, zero_smul]
    
  refine'
    mem_convex_join.2
      β¨x, mem_singleton _, (t.filter fun i => z i β  x).centerMass w z,
        Finset.center_mass_mem_convex_hull _ hwβ' hw fun i hi => _, β i in t.filter fun i => z i = x, w i,
        β i in t.filter fun i => z i β  x, w i, Finset.sum_nonneg fun i hi => hwβ _ <| Finset.filter_subset _ _ hi,
        Finset.sum_nonneg hwβ', _, _β©
  Β· rw [Finset.mem_filter] at hi
    exact mem_of_mem_insert_of_ne (hz _ hi.1) hi.2
    
  Β· rw [Finset.sum_filter_add_sum_filter_not, hwβ]
    
  Β· rw [Finset.centerMass, smul_inv_smulβ hw.ne', Finset.sum_smul]
    

theorem convex_join_segments (a b c d : E) : ConvexJoin π (Segment π a b) (Segment π c d) = convexHull π {a, b, c, d} :=
  by
  simp only [β convex_hull_insert, β insert_nonempty, β singleton_nonempty, β convex_hull_pair, convex_join_assoc, β
    convex_join_singletons]

theorem convex_join_segment_singleton (a b c : E) : ConvexJoin π (Segment π a b) {c} = convexHull π {a, b, c} := by
  rw [β pair_eq_singleton, β convex_join_segments, segment_same, pair_eq_singleton]

theorem convex_join_singleton_segment (a b c : E) : ConvexJoin π {a} (Segment π b c) = convexHull π {a, b, c} := by
  rw [β segment_same π, convex_join_segments, insert_idem]

protected theorem Convex.convex_join (hs : Convex π s) (ht : Convex π t) : Convex π (ConvexJoin π s t) := by
  rw [convex_iff_segment_subset] at ht hsβ’
  simp_rw [mem_convex_join]
  rintro x y β¨xa, hxa, xb, hxb, hxβ© β¨ya, hya, yb, hyb, hyβ©
  refine' (segment_subset_convex_join hx hy).trans _
  have triv : ({xa, xb, ya, yb} : Set E) = {xa, ya, xb, yb} := by
    simp only [β Set.insert_comm]
  rw [convex_join_segments, triv, β convex_join_segments]
  exact convex_join_mono (hs hxa hya) (ht hxb hyb)

protected theorem Convex.convex_hull_union (hs : Convex π s) (ht : Convex π t) (hsβ : s.Nonempty) (htβ : t.Nonempty) :
    convexHull π (s βͺ t) = ConvexJoin π s t :=
  (convex_hull_min (union_subset (subset_convex_join_left htβ) <| subset_convex_join_right hsβ) <|
        hs.ConvexJoin ht).antisymm <|
    convex_join_subset_convex_hull _ _

theorem convex_hull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull π (s βͺ t) = ConvexJoin π (convexHull π s) (convexHull π t) := by
  rw [β convex_hull_convex_hull_union_left, β convex_hull_convex_hull_union_right]
  exact (convex_convex_hull π s).convex_hull_union (convex_convex_hull π t) hs.convex_hull ht.convex_hull

end LinearOrderedField

