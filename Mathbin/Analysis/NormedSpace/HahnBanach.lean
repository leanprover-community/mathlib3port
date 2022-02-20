/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import Mathbin.Analysis.Convex.Cone
import Mathbin.Analysis.NormedSpace.IsROrC
import Mathbin.Analysis.NormedSpace.Extend

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `ℝ` and `ℂ`.

In order to state and prove its corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `is_R_or_C 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ∥x∥` (where the norm has to be interpreted as an element
of `𝕜`).

-/


universe u v

namespace Real

variable {E : Type _} [SemiNormedGroup E] [NormedSpace ℝ E]

/-- Hahn-Banach theorem for continuous linear functions over `ℝ`. -/
theorem exists_extension_norm_eq (p : Subspace ℝ E) (f : p →L[ℝ] ℝ) :
    ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ := by
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (fun x => ∥f∥ * ∥x∥)
      (fun c hc x => by
        simp only [norm_smul c x, Real.norm_eq_abs, abs_of_pos hc, mul_left_commₓ])
      (fun x y => _) fun x => le_transₓ (le_abs_self _) (f.le_op_norm _) with
    ⟨g, g_eq, g_le⟩
  set g' := g.mk_continuous ∥f∥ fun x => abs_le.2 ⟨neg_le.1 <| g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩
  · refine' ⟨g', g_eq, _⟩
    · apply le_antisymmₓ (g.mk_continuous_norm_le (norm_nonneg f) _)
      refine' f.op_norm_le_bound (norm_nonneg _) fun x => _
      dsimp  at g_eq
      rw [← g_eq]
      apply g'.le_op_norm
      
    
  · simp only [← mul_addₓ]
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f)
    

end Real

section IsROrC

open IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜] {F : Type _} [SemiNormedGroup F] [NormedSpace 𝕜 F]

/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq (p : Subspace 𝕜 F) (f : p →L[𝕜] 𝕜) :
    ∃ g : F →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ := by
  let this' : Module ℝ F := RestrictScalars.module ℝ 𝕜 F
  let this' : IsScalarTower ℝ 𝕜 F := RestrictScalars.is_scalar_tower _ _ _
  let this' : NormedSpace ℝ F := NormedSpace.restrictScalars _ 𝕜 _
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars ℝ)
  have fr_apply : ∀ x, fr x = re (f x) := by
    intro x
    rfl
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : F →L[ℝ] ℝ`.
  rcases Real.exists_extension_norm_eq (p.restrict_scalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩
  -- Now `g` can be extended to the `F →L[𝕜] 𝕜` we need.
  refine' ⟨g.extend_to_𝕜, _⟩
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_𝕜 x = f x := by
    intro x
    rw [ContinuousLinearMap.extend_to_𝕜_apply, ← Submodule.coe_smul, hextends, hextends]
    have : (fr x : 𝕜) - I * ↑(fr (I • x)) = (re (f x) : 𝕜) - (I : 𝕜) * re (f ((I : 𝕜) • x)) := by
      rfl
    rw [this]
    apply ext
    · simp only [add_zeroₓ, Algebra.id.smul_eq_mul, I_re, of_real_im, AddMonoidHom.map_add, zero_sub, I_im', zero_mul,
        of_real_re, eq_self_iff_true, sub_zero, mul_neg, of_real_neg, mul_re, mul_zero, sub_neg_eq_add,
        ContinuousLinearMap.map_smul]
      
    · simp only [Algebra.id.smul_eq_mul, I_re, of_real_im, AddMonoidHom.map_add, zero_sub, I_im', zero_mul, of_real_re,
        mul_neg, mul_im, zero_addₓ, of_real_neg, mul_re, sub_neg_eq_add, ContinuousLinearMap.map_smul]
      
  -- And we derive the equality of the norms by bounding on both sides.
  refine' ⟨h, le_antisymmₓ _ _⟩
  · calc ∥g.extend_to_𝕜∥ ≤ ∥g∥ := g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)_ = ∥fr∥ :=
        hnormeq _ ≤ ∥re_clm∥ * ∥f∥ := ContinuousLinearMap.op_norm_comp_le _ _ _ = ∥f∥ := by
        rw [re_clm_norm, one_mulₓ]
    
  · exact f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg fun x => h x ▸ g.extend_to_𝕜.le_op_norm x
    

end IsROrC

section DualVector

variable (𝕜 : Type v) [IsROrC 𝕜]

variable {E : Type u} [NormedGroup E] [NormedSpace 𝕜 E]

open ContinuousLinearEquiv Submodule

open_locale Classical

theorem coord_norm' {x : E} (h : x ≠ 0) : ∥(∥x∥ : 𝕜) • coord 𝕜 x h∥ = 1 := by
  rw [norm_smul, IsROrC.norm_coe_norm, coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = ∥x∥ := by
  let p : Submodule 𝕜 E := 𝕜∙x
  let f := (∥x∥ : 𝕜) • coord 𝕜 x h
  obtain ⟨g, hg⟩ := exists_extension_norm_eq p f
  refine' ⟨g, _, _⟩
  · rw [hg.2, coord_norm']
    
  · calc g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜∙x) := by
        rw [coe_mk]_ = ((∥x∥ : 𝕜) • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜∙x) := by
        rw [← hg.1]_ = ∥x∥ := by
        simp
    

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [Nontrivial E] (x : E) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = ∥x∥ := by
  by_cases' hx : x = 0
  · obtain ⟨y, hy⟩ := exists_ne (0 : E)
    obtain ⟨g, hg⟩ : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g y = ∥y∥ := exists_dual_vector 𝕜 y hy
    refine' ⟨g, hg.left, _⟩
    simp [hx]
    
  · exact exists_dual_vector 𝕜 x hx
    

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, but only ensuring that
    the dual element has norm at most `1` (this can not be improved for the trivial
    vector space). -/
theorem exists_dual_vector'' (x : E) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ ≤ 1 ∧ g x = ∥x∥ := by
  by_cases' hx : x = 0
  · refine'
      ⟨0, by
        simp , _⟩
    symm
    simp [hx]
    
  · rcases exists_dual_vector 𝕜 x hx with ⟨g, g_norm, g_eq⟩
    exact ⟨g, g_norm.le, g_eq⟩
    

end DualVector

