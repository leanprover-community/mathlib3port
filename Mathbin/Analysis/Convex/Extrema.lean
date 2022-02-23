/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Analysis.Convex.Function
import Mathbin.Topology.Algebra.Affine
import Mathbin.Topology.LocalExtr
import Mathbin.Topology.MetricSpace.Basic

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/


variable {E β : Type _} [AddCommGroupₓ E] [TopologicalSpace E] [Module ℝ E] [TopologicalAddGroup E]
  [HasContinuousSmul ℝ E] [LinearOrderedAddCommGroup β] [Module ℝ β] [OrderedSmul ℝ β] {s : Set E}

open Set Filter

open_locale Classical

/-- Helper lemma for the more general case: `is_min_on.of_is_local_min_on_of_convex_on`.
-/
theorem IsMinOn.of_is_local_min_on_of_convex_on_Icc {f : ℝ → β} {a b : ℝ} (a_lt_b : a < b)
    (h_local_min : IsLocalMinOn f (Icc a b) a) (h_conv : ConvexOn ℝ (Icc a b) f) : ∀, ∀ x ∈ Icc a b, ∀, f a ≤ f x := by
  by_contra' H_cont
  rcases H_cont with ⟨x, ⟨h_ax, h_xb⟩, fx_lt_fa⟩
  obtain ⟨z, hz, ge_on_nhd⟩ : ∃ z > a, ∀, ∀ y ∈ Icc a z, ∀, f y ≥ f a := by
    rcases eventually_iff_exists_mem.mp h_local_min with ⟨U, U_in_nhds_within, fy_ge_fa⟩
    rw [nhds_within_Icc_eq_nhds_within_Ici a_lt_b, mem_nhds_within_Ici_iff_exists_Icc_subset] at U_in_nhds_within
    rcases U_in_nhds_within with ⟨ε, ε_in_Ioi, Ioc_in_U⟩
    exact ⟨ε, mem_Ioi.mp ε_in_Ioi, fun y y_in_Ioc => fy_ge_fa y <| Ioc_in_U y_in_Ioc⟩
  have a_lt_x : a < x :=
    lt_of_le_of_neₓ h_ax fun H => by
      subst H <;> exact lt_irreflₓ (f a) fx_lt_fa
  have lt_on_nhd : ∀, ∀ y ∈ Ioc a x, ∀, f y < f a := by
    intro y y_in_Ioc
    rcases(Convex.mem_Ioc a_lt_x).mp y_in_Ioc with ⟨ya, yx, ya_pos, yx_pos, yax, y_combo⟩
    calc f y = f (ya * a + yx * x) := by
        rw [y_combo]_ ≤ ya • f a + yx • f x :=
        h_conv.2 (left_mem_Icc.mpr (le_of_ltₓ a_lt_b)) ⟨h_ax, h_xb⟩ ya_pos (le_of_ltₓ yx_pos)
          yax _ < ya • f a + yx • f a :=
        add_lt_add_left (smul_lt_smul_of_pos fx_lt_fa yx_pos) _ _ = f a := by
        rw [← add_smul, yax, one_smul]
  by_cases' h_xz : x ≤ z
  · exact not_lt_of_geₓ (ge_on_nhd x (show x ∈ Icc a z from ⟨h_ax, h_xz⟩)) fx_lt_fa
    
  · have h₁ : z ∈ Ioc a x := ⟨hz, le_of_not_geₓ h_xz⟩
    have h₂ : z ∈ Icc a z := ⟨le_of_ltₓ hz, le_reflₓ z⟩
    exact not_lt_of_geₓ (ge_on_nhd z h₂) (lt_on_nhd z h₁)
    

/-- A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
theorem IsMinOn.of_is_local_min_on_of_convex_on {f : E → β} {a : E} (a_in_s : a ∈ s) (h_localmin : IsLocalMinOn f s a)
    (h_conv : ConvexOn ℝ s f) : ∀, ∀ x ∈ s, ∀, f a ≤ f x := by
  by_contra' H_cont
  rcases H_cont with ⟨x, ⟨x_in_s, fx_lt_fa⟩⟩
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a x
  have hg0 : g 0 = a := AffineMap.line_map_apply_zero a x
  have hg1 : g 1 = x := AffineMap.line_map_apply_one a x
  have fg_local_min_on : IsLocalMinOn (f ∘ g) (g ⁻¹' s) 0 := by
    rw [← hg0] at h_localmin
    refine'
      IsLocalMinOn.comp_continuous_on h_localmin subset.rfl (Continuous.continuous_on AffineMap.line_map_continuous) _
    simp [mem_preimage, hg0, a_in_s]
  have fg_min_on : ∀, ∀ x ∈ (Icc 0 1 : Set ℝ), ∀, (f ∘ g) 0 ≤ (f ∘ g) x := by
    have Icc_in_s' : Icc 0 1 ⊆ g ⁻¹' s := by
      have h0 : (0 : ℝ) ∈ g ⁻¹' s := by
        simp [mem_preimage, a_in_s]
      have h1 : (1 : ℝ) ∈ g ⁻¹' s := by
        simp [mem_preimage, hg1, x_in_s]
      rw [←
        segment_eq_Icc
          (show (0 : ℝ) ≤ 1 by
            linarith)]
      exact
        (Convex.affine_preimage g h_conv.1).segment_subset
          (by
            simp [mem_preimage, hg0, a_in_s])
          (by
            simp [mem_preimage, hg1, x_in_s])
    have fg_local_min_on' : IsLocalMinOn (f ∘ g) (Icc 0 1) 0 := IsLocalMinOn.on_subset fg_local_min_on Icc_in_s'
    refine'
      IsMinOn.of_is_local_min_on_of_convex_on_Icc
        (by
          linarith)
        fg_local_min_on' _
    exact (ConvexOn.comp_affine_map g h_conv).Subset Icc_in_s' (convex_Icc 0 1)
  have gx_lt_ga : (f ∘ g) 1 < (f ∘ g) 0 := by
    simp [hg1, fx_lt_fa, hg0]
  exact not_lt_of_geₓ (fg_min_on 1 (mem_Icc.mpr ⟨zero_le_one, le_reflₓ 1⟩)) gx_lt_ga

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
theorem IsMaxOn.of_is_local_max_on_of_concave_on {f : E → β} {a : E} (a_in_s : a ∈ s) (h_localmax : IsLocalMaxOn f s a)
    (h_conc : ConcaveOn ℝ s f) : ∀, ∀ x ∈ s, ∀, f x ≤ f a :=
  @IsMinOn.of_is_local_min_on_of_convex_on _ (OrderDual β) _ _ _ _ _ _ _ _ s f a a_in_s h_localmax h_conc

/-- A local minimum of a convex function is a global minimum. -/
theorem IsMinOn.of_is_local_min_of_convex_univ {f : E → β} {a : E} (h_local_min : IsLocalMin f a)
    (h_conv : ConvexOn ℝ Univ f) : ∀ x, f a ≤ f x := fun x =>
  (IsMinOn.of_is_local_min_on_of_convex_on (mem_univ a) (IsLocalMin.on h_local_min Univ) h_conv) x (mem_univ x)

/-- A local maximum of a concave function is a global maximum. -/
theorem IsMaxOn.of_is_local_max_of_convex_univ {f : E → β} {a : E} (h_local_max : IsLocalMax f a)
    (h_conc : ConcaveOn ℝ Univ f) : ∀ x, f x ≤ f a :=
  @IsMinOn.of_is_local_min_of_convex_univ _ (OrderDual β) _ _ _ _ _ _ _ _ f a h_local_max h_conc

