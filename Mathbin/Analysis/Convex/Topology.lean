/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.convex.topology
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Jensen
import Mathbin.Analysis.Convex.Strict
import Mathbin.Analysis.Normed.Group.Pointwise
import Mathbin.Topology.Algebra.Module.FiniteDimension
import Mathbin.Analysis.NormedSpace.Ray
import Mathbin.Topology.PathConnected
import Mathbin.Topology.Algebra.Affine

/-!
# Topological and metric properties of convex sets

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed;
* `convex_on_norm`, `convex_on_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convex_on_univ_norm`, `convex_on_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex;
-/


variable {ι : Type _} {E : Type _}

open Metric Set

open Pointwise Convex

theorem Real.convex_iff_is_preconnected {s : Set ℝ} : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ord_connected.trans is_preconnected_iff_ord_connected.symm
#align real.convex_iff_is_preconnected Real.convex_iff_is_preconnected

alias Real.convex_iff_is_preconnected ↔ _ IsPreconnected.convex

/-! ### Standard simplex -/


section stdSimplex

variable [Fintype ι]

/-- Every vector in `std_simplex 𝕜 ι` has `max`-norm at most `1`. -/
theorem std_simplex_subset_closed_ball : stdSimplex ℝ ι ⊆ Metric.closedBall 0 1 := by
  intro f hf
  rw [Metric.mem_closed_ball, dist_zero_right]
  refine' Nnreal.coe_one ▸ Nnreal.coe_le_coe.2 <| Finset.sup_le fun x hx => _
  change |f x| ≤ 1
  rw [abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_std_simplex hf x).2
#align std_simplex_subset_closed_ball std_simplex_subset_closed_ball

variable (ι)

/-- `std_simplex ℝ ι` is bounded. -/
theorem boundedStdSimplex : Metric.Bounded (stdSimplex ℝ ι) :=
  (Metric.bounded_iff_subset_ball 0).2 ⟨1, std_simplex_subset_closed_ball⟩
#align bounded_std_simplex boundedStdSimplex

/-- `std_simplex ℝ ι` is closed. -/
theorem is_closed_std_simplex : IsClosed (stdSimplex ℝ ι) :=
  (std_simplex_eq_inter ℝ ι).symm ▸
    IsClosed.inter (is_closed_Inter fun i => is_closed_le continuous_const (continuous_apply i))
      (is_closed_eq ((continuous_finset_sum _) fun x _ => continuous_apply x) continuous_const)
#align is_closed_std_simplex is_closed_std_simplex

/-- `std_simplex ℝ ι` is compact. -/
theorem is_compact_std_simplex : IsCompact (stdSimplex ℝ ι) :=
  Metric.is_compact_iff_is_closed_bounded.2 ⟨is_closed_std_simplex ι, boundedStdSimplex ι⟩
#align is_compact_std_simplex is_compact_std_simplex

end stdSimplex

/-! ### Topological vector space -/


section HasContinuousConstSmul

variable {𝕜 : Type _} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalAddGroup E] [HasContinuousConstSmul 𝕜 E]

/-- If `s` is a convex set, then `a • interior s + b • closure s ⊆ interior s` for all `0 < a`,
`0 ≤ b`, `a + b = 1`. See also `convex.combo_interior_self_subset_interior` for a weaker version. -/
theorem Convex.combo_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • closure s ⊆ interior s :=
  interior_smul₀ ha.ne' s ▸
    calc
      interior (a • s) + b • closure s ⊆ interior (a • s) + closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = interior (a • s) + b • s := by rw [is_open_interior.add_closure (b • s)]
      _ ⊆ interior (a • s + b • s) := subset_interior_add_left
      _ ⊆ interior s := interior_mono <| hs.set_combo_subset ha.le hb hab
      
#align convex.combo_interior_closure_subset_interior Convex.combo_interior_closure_subset_interior

/-- If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < a`, `0 ≤ b`,
`a + b = 1`. See also `convex.combo_interior_closure_subset_interior` for a stronger version. -/
theorem Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • s ⊆ interior s :=
  calc
    a • interior s + b • s ⊆ a • interior s + b • closure s :=
      add_subset_add Subset.rfl <| image_subset _ subset_closure
    _ ⊆ interior s := hs.combo_interior_closure_subset_interior ha hb hab
    
#align convex.combo_interior_self_subset_interior Convex.combo_interior_self_subset_interior

/-- If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for all `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `convex.combo_self_interior_subset_interior` for a weaker version. -/
theorem Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • closure s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)
#align convex.combo_closure_interior_subset_interior Convex.combo_closure_interior_subset_interior

/-- If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ a`, `0 < b`,
`a + b = 1`. See also `convex.combo_closure_interior_subset_interior` for a stronger version. -/
theorem Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)
#align convex.combo_self_interior_subset_interior Convex.combo_self_interior_subset_interior

theorem Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
#align convex.combo_interior_closure_mem_interior Convex.combo_interior_closure_mem_interior

theorem Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab
#align convex.combo_interior_self_mem_interior Convex.combo_interior_self_mem_interior

theorem Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
#align convex.combo_closure_interior_mem_interior Convex.combo_closure_interior_mem_interior

theorem Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab
#align convex.combo_self_interior_mem_interior Convex.combo_self_interior_mem_interior

theorem Convex.open_segment_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab
#align
  convex.open_segment_interior_closure_subset_interior Convex.open_segment_interior_closure_subset_interior

theorem Convex.open_segment_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.open_segment_interior_closure_subset_interior hx (subset_closure hy)
#align
  convex.open_segment_interior_self_subset_interior Convex.open_segment_interior_self_subset_interior

theorem Convex.open_segment_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab
#align
  convex.open_segment_closure_interior_subset_interior Convex.open_segment_closure_interior_subset_interior

theorem Convex.open_segment_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.open_segment_closure_interior_subset_interior (subset_closure hx) hy
#align
  convex.open_segment_self_interior_subset_interior Convex.open_segment_self_interior_subset_interior

/-- If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`.
-/
theorem Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
    x + t • (y - x) ∈ interior s := by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel'_right _ _)
#align convex.add_smul_sub_mem_interior' Convex.add_smul_sub_mem_interior'

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
theorem Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • (y - x) ∈ interior s :=
  hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht
#align convex.add_smul_sub_mem_interior Convex.add_smul_sub_mem_interior

/-- If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ closure s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s := by
  simpa only [add_sub_cancel'] using hs.add_smul_sub_mem_interior' hx hy ht
#align convex.add_smul_mem_interior' Convex.add_smul_mem_interior'

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s :=
  hs.add_smul_mem_interior' (subset_closure hx) hy ht
#align convex.add_smul_mem_interior Convex.add_smul_mem_interior

/-- In a topological vector space, the interior of a convex set is convex. -/
protected theorem Convex.interior {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (interior s) :=
  convex_iff_open_segment_subset.mpr fun x hx y hy =>
    hs.open_segment_closure_interior_subset_interior (interior_subset_closure hx) hy
#align convex.interior Convex.interior

/-- In a topological vector space, the closure of a convex set is convex. -/
protected theorem Convex.closure {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (closure s) :=
  fun x hx y hy a b ha hb hab =>
  let f : E → E → E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y ∈ closure s from map_mem_closure₂ hf hx hy fun x' hx' y' hy' => hs hx' hy' ha hb hab
#align convex.closure Convex.closure

open AffineMap

/-- A convex set `s` is strictly convex provided that for any two distinct points of
`s \ interior s`, the line passing through these points has nonempty intersection with
`interior s`. -/
protected theorem Convex.strict_convex' {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ∃ c : 𝕜, lineMap x y c ∈ interior s) :
    StrictConvex 𝕜 s := by 
  refine' strict_convex_iff_open_segment_subset.2 _
  intro x hx y hy hne
  by_cases hx' : x ∈ interior s; · exact hs.open_segment_interior_self_subset_interior hx' hy
  by_cases hy' : y ∈ interior s; · exact hs.open_segment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine' (open_segment_subset_union x y ⟨c, rfl⟩).trans (insert_subset.2 ⟨hc, union_subset _ _⟩)
  exacts[hs.open_segment_self_interior_subset_interior hx hc,
    hs.open_segment_interior_self_subset_interior hc hy]
#align convex.strict_convex' Convex.strict_convex'

/-- A convex set `s` is strictly convex provided that for any two distinct points `x`, `y` of
`s \ interior s`, the segment with endpoints `x`, `y` has nonempty intersection with
`interior s`. -/
protected theorem Convex.strict_convex {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ([x -[𝕜] y] \ frontier s).Nonempty) :
    StrictConvex 𝕜 s := by
  refine' hs.strict_convex' <| h.imp_on fun x hx y hy hne => _
  simp only [segment_eq_image_line_map, ← self_diff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine' ⟨c, hs.segment_subset hx.1 hy.1 _, hcs⟩
  exact (segment_eq_image_line_map 𝕜 x y).symm ▸ mem_image_of_mem _ hc
#align convex.strict_convex Convex.strict_convex

end HasContinuousConstSmul

section HasContinuousSmul

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [HasContinuousSmul ℝ E]

/-- Convex hull of a finite set is compact. -/
theorem Set.Finite.compact_convex_hull {s : Set E} (hs : s.Finite) : IsCompact (convexHull ℝ s) :=
  by 
  rw [hs.convex_hull_eq_image]
  apply (is_compact_std_simplex _).image
  haveI := hs.fintype
  apply LinearMap.continuous_on_pi
#align set.finite.compact_convex_hull Set.Finite.compact_convex_hull

/-- Convex hull of a finite set is closed. -/
theorem Set.Finite.is_closed_convex_hull [T2Space E] {s : Set E} (hs : s.Finite) :
    IsClosed (convexHull ℝ s) :=
  hs.compact_convex_hull.IsClosed
#align set.finite.is_closed_convex_hull Set.Finite.is_closed_convex_hull

open AffineMap

/-- If we dilate the interior of a convex set about a point in its interior by a scale `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) : closure s ⊆ homothety x t '' interior s :=
  by 
  intro y hy
  have hne : t ≠ 0 := (one_pos.trans ht).ne'
  refine'
    ⟨homothety x t⁻¹ y, hs.open_segment_interior_closure_subset_interior hx hy _,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [open_segment_eq_image_line_map, ← inv_one, ← inv_Ioi (zero_lt_one' ℝ), ← image_inv,
    image_image, homothety_eq_line_map]
  exact mem_image_of_mem _ ht
#align
  convex.closure_subset_image_homothety_interior_of_one_lt Convex.closure_subset_image_homothety_interior_of_one_lt

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ interior (homothety x t '' s) :=
  (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans <|
    (homothety_is_open_map x t (one_pos.trans ht).ne').image_interior_subset _
#align
  convex.closure_subset_interior_image_homothety_of_one_lt Convex.closure_subset_interior_image_homothety_of_one_lt

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) : s ⊆ interior (homothety x t '' s) :=
  subset_closure.trans <| hs.closure_subset_interior_image_homothety_of_one_lt hx t ht
#align
  convex.subset_interior_image_homothety_of_one_lt Convex.subset_interior_image_homothety_of_one_lt

/-- A nonempty convex set is path connected. -/
protected theorem Convex.is_path_connected {s : Set E} (hconv : Convex ℝ s) (hne : s.Nonempty) :
    IsPathConnected s := by 
  refine' is_path_connected_iff.mpr ⟨hne, _⟩
  intro x x_in y y_in
  have H := hconv.segment_subset x_in y_in
  rw [segment_eq_image_line_map] at H
  exact
    JoinedIn.of_line affine_map.line_map_continuous.continuous_on (line_map_apply_zero _ _)
      (line_map_apply_one _ _) H
#align convex.is_path_connected Convex.is_path_connected

/-- A nonempty convex set is connected. -/
protected theorem Convex.is_connected {s : Set E} (h : Convex ℝ s) (hne : s.Nonempty) :
    IsConnected s :=
  (h.IsPathConnected hne).IsConnected
#align convex.is_connected Convex.is_connected

/-- A convex set is preconnected. -/
protected theorem Convex.is_preconnected {s : Set E} (h : Convex ℝ s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ is_preconnected_empty) fun hne =>
    (h.IsConnected hne).IsPreconnected
#align convex.is_preconnected Convex.is_preconnected

/-- Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected theorem TopologicalAddGroup.path_connected : PathConnectedSpace E :=
  path_connected_space_iff_univ.mpr <| convex_univ.IsPathConnected ⟨(0 : E), trivial⟩
#align topological_add_group.path_connected TopologicalAddGroup.path_connected

end HasContinuousSmul

/-! ### Normed vector space -/


section NormedSpace

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s t : Set E}

/-- The norm on a real normed space is convex on any convex set. See also `seminorm.convex_on`
and `convex_on_univ_norm`. -/
theorem convex_on_norm (hs : Convex ℝ s) : ConvexOn ℝ s norm :=
  ⟨hs, fun x hx y hy a b ha hb hab =>
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      ⟩
#align convex_on_norm convex_on_norm

/-- The norm on a real normed space is convex on the whole space. See also `seminorm.convex_on`
and `convex_on_norm`. -/
theorem convex_on_univ_norm : ConvexOn ℝ univ (norm : E → ℝ) :=
  convex_on_norm convex_univ
#align convex_on_univ_norm convex_on_univ_norm

theorem convex_on_dist (z : E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z := by
  simpa [dist_eq_norm, preimage_preimage] using
    (convex_on_norm (hs.translate (-z))).comp_affine_map (AffineMap.id ℝ E - AffineMap.const ℝ E z)
#align convex_on_dist convex_on_dist

theorem convex_on_univ_dist (z : E) : ConvexOn ℝ univ fun z' => dist z' z :=
  convex_on_dist z convex_univ
#align convex_on_univ_dist convex_on_univ_dist

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (Metric.ball a r) := by
  simpa only [Metric.ball, sep_univ] using (convex_on_univ_dist a).convex_lt r
#align convex_ball convex_ball

theorem convex_closed_ball (a : E) (r : ℝ) : Convex ℝ (Metric.closedBall a r) := by
  simpa only [Metric.closedBall, sep_univ] using (convex_on_univ_dist a).convex_le r
#align convex_closed_ball convex_closed_ball

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)
#align convex.thickening Convex.thickening

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_Inter_thickening hδ]
    exact convex_Inter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure
#align convex.cthickening Convex.cthickening

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convex_hull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convex_on_dist y (convex_convex_hull ℝ _)).exists_ge_of_mem_convex_hull hx
#align convex_hull_exists_dist_ge convex_hull_exists_dist_ge

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
theorem convex_hull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s)
    (hy : y ∈ convexHull ℝ t) : ∃ x' ∈ s, ∃ y' ∈ t, dist x y ≤ dist x' y' := by
  rcases convex_hull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convex_hull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')
#align convex_hull_exists_dist_ge2 convex_hull_exists_dist_ge2

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp]
theorem convex_hull_ediam (s : Set E) : Emetric.diam (convexHull ℝ s) = Emetric.diam s := by
  refine'
    (Emetric.diam_le fun x hx y hy => _).antisymm (Emetric.diam_mono <| subset_convex_hull ℝ s)
  rcases convex_hull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (Ennreal.of_real_le_of_real H)
  rw [← edist_dist]
  exact Emetric.edist_le_diam_of_mem hx' hy'
#align convex_hull_ediam convex_hull_ediam

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp]
theorem convex_hull_diam (s : Set E) : Metric.diam (convexHull ℝ s) = Metric.diam s := by
  simp only [Metric.diam, convex_hull_ediam]
#align convex_hull_diam convex_hull_diam

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
theorem bounded_convex_hull {s : Set E} : Metric.Bounded (convexHull ℝ s) ↔ Metric.Bounded s := by
  simp only [Metric.bounded_iff_ediam_ne_top, convex_hull_ediam]
#align bounded_convex_hull bounded_convex_hull

instance (priority := 100) NormedSpace.path_connected : PathConnectedSpace E :=
  TopologicalAddGroup.path_connected
#align normed_space.path_connected NormedSpace.path_connected

instance (priority := 100) NormedSpace.loc_path_connected : LocPathConnectedSpace E :=
  loc_path_connected_of_bases (fun x => Metric.nhds_basis_ball) fun x r r_pos =>
    (convex_ball x r).IsPathConnected <| by simp [r_pos]
#align normed_space.loc_path_connected NormedSpace.loc_path_connected

theorem dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) :
    dist x y + dist y z = dist x z := by
  simp only [dist_eq_norm, mem_segment_iff_same_ray] at *
  simpa only [sub_add_sub_cancel', norm_sub_rev] using h.norm_add.symm
#align dist_add_dist_of_mem_segment dist_add_dist_of_mem_segment

/-- The set of vectors in the same ray as `x` is connected. -/
theorem is_connected_set_of_same_ray (x : E) : IsConnected { y | SameRay ℝ x y } := by
  by_cases hx : x = 0; · simpa [hx] using is_connected_univ
  simp_rw [← exists_nonneg_left_iff_same_ray hx]
  exact is_connected_Ici.image _ (continuous_id.smul continuous_const).ContinuousOn
#align is_connected_set_of_same_ray is_connected_set_of_same_ray

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
theorem is_connected_set_of_same_ray_and_ne_zero {x : E} (hx : x ≠ 0) :
    IsConnected { y | SameRay ℝ x y ∧ y ≠ 0 } := by
  simp_rw [← exists_pos_left_iff_same_ray_and_ne_zero hx]
  exact is_connected_Ioi.image _ (continuous_id.smul continuous_const).ContinuousOn
#align is_connected_set_of_same_ray_and_ne_zero is_connected_set_of_same_ray_and_ne_zero

end NormedSpace

