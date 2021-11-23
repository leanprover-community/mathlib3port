import Mathbin.Analysis.Convex.Cone 
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

/--
The norm of `x` as an element of `𝕜` (a normed algebra over `ℝ`). This is needed in particular to
state equalities of the form `g x = norm' 𝕜 x` when `g` is a linear function.

For the concrete cases of `ℝ` and `ℂ`, this is just `∥x∥` and `↑∥x∥`, respectively.
-/
noncomputable def norm' (𝕜 : Type _) [NondiscreteNormedField 𝕜] [SemiNormedAlgebra ℝ 𝕜] {E : Type _} [SemiNormedGroup E]
  (x : E) : 𝕜 :=
  algebraMap ℝ 𝕜 ∥x∥

theorem norm'_def (𝕜 : Type _) [NondiscreteNormedField 𝕜] [SemiNormedAlgebra ℝ 𝕜] {E : Type _} [SemiNormedGroup E]
  (x : E) : norm' 𝕜 x = algebraMap ℝ 𝕜 ∥x∥ :=
  rfl

theorem norm_norm' (𝕜 : Type _) [NondiscreteNormedField 𝕜] [SemiNormedAlgebra ℝ 𝕜] (A : Type _) [SemiNormedGroup A]
  (x : A) : ∥norm' 𝕜 x∥ = ∥x∥ :=
  by 
    rw [norm'_def, norm_algebra_map_eq, norm_norm]

@[simp]
theorem norm'_eq_zero_iff (𝕜 : Type _) [NondiscreteNormedField 𝕜] [SemiNormedAlgebra ℝ 𝕜] (A : Type _) [NormedGroup A]
  (x : A) : norm' 𝕜 x = 0 ↔ x = 0 :=
  by 
    simp [norm', ←norm_eq_zero, norm_algebra_map_eq]

namespace Real

variable{E : Type _}[SemiNormedGroup E][SemiNormedSpace ℝ E]

/-- Hahn-Banach theorem for continuous linear functions over `ℝ`. -/
theorem exists_extension_norm_eq (p : Subspace ℝ E) (f : p →L[ℝ] ℝ) :
  ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
  by 
    rcases
      exists_extension_of_le_sublinear ⟨p, f⟩ (fun x => ∥f∥*∥x∥)
        (fun c hc x =>
          by 
            simp only [norm_smul c x, Real.norm_eq_abs, abs_of_pos hc, mul_left_commₓ])
        (fun x y => _) fun x => le_transₓ (le_abs_self _) (f.le_op_norm _) with
      ⟨g, g_eq, g_le⟩
    set g' := g.mk_continuous ∥f∥ fun x => abs_le.2 ⟨neg_le.1$ g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩
    ·
      refine' ⟨g', g_eq, _⟩
      ·
        apply le_antisymmₓ (g.mk_continuous_norm_le (norm_nonneg f) _)
        refine' f.op_norm_le_bound (norm_nonneg _) fun x => _ 
        dsimp  at g_eq 
        rw [←g_eq]
        apply g'.le_op_norm
    ·
      simp only [←mul_addₓ]
      exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f)

end Real

section IsROrC

open IsROrC

variable{𝕜 : Type _}[IsROrC 𝕜]{F : Type _}[SemiNormedGroup F][SemiNormedSpace 𝕜 F]

-- error in Analysis.NormedSpace.HahnBanach: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq
(p : subspace 𝕜 F)
(f : «expr →L[ ] »(p, 𝕜, 𝕜)) : «expr∃ , »((g : «expr →L[ ] »(F, 𝕜, 𝕜)), «expr ∧ »(∀
  x : p, «expr = »(g x, f x), «expr = »(«expr∥ ∥»(g), «expr∥ ∥»(f)))) :=
begin
  letI [] [":", expr module exprℝ() F] [":=", expr restrict_scalars.module exprℝ() 𝕜 F],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 F] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  letI [] [":", expr semi_normed_space exprℝ() F] [":=", expr semi_normed_space.restrict_scalars _ 𝕜 _],
  let [ident fr] [] [":=", expr re_clm.comp (f.restrict_scalars exprℝ())],
  have [ident fr_apply] [":", expr ∀ x, «expr = »(fr x, re (f x))] [],
  by { assume [binders (x)],
    refl },
  rcases [expr real.exists_extension_norm_eq (p.restrict_scalars exprℝ()) fr, "with", "⟨", ident g, ",", "⟨", ident hextends, ",", ident hnormeq, "⟩", "⟩"],
  refine [expr ⟨g.extend_to_𝕜, _⟩],
  have [ident h] [":", expr ∀ x : p, «expr = »(g.extend_to_𝕜 x, f x)] [],
  { assume [binders (x)],
    rw ["[", expr continuous_linear_map.extend_to_𝕜_apply, ",", "<-", expr submodule.coe_smul, ",", expr hextends, ",", expr hextends, "]"] [],
    have [] [":", expr «expr = »(«expr - »((fr x : 𝕜), «expr * »(I, «expr↑ »(fr «expr • »(I, x)))), «expr - »((re (f x) : 𝕜), «expr * »((I : 𝕜), re (f «expr • »((I : 𝕜), x)))))] [],
    by refl,
    rw [expr this] [],
    apply [expr ext],
    { simp [] [] ["only"] ["[", expr add_zero, ",", expr algebra.id.smul_eq_mul, ",", expr I_re, ",", expr of_real_im, ",", expr add_monoid_hom.map_add, ",", expr zero_sub, ",", expr I_im', ",", expr zero_mul, ",", expr of_real_re, ",", expr eq_self_iff_true, ",", expr sub_zero, ",", expr mul_neg_eq_neg_mul_symm, ",", expr of_real_neg, ",", expr mul_re, ",", expr mul_zero, ",", expr sub_neg_eq_add, ",", expr continuous_linear_map.map_smul, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr algebra.id.smul_eq_mul, ",", expr I_re, ",", expr of_real_im, ",", expr add_monoid_hom.map_add, ",", expr zero_sub, ",", expr I_im', ",", expr zero_mul, ",", expr of_real_re, ",", expr mul_neg_eq_neg_mul_symm, ",", expr mul_im, ",", expr zero_add, ",", expr of_real_neg, ",", expr mul_re, ",", expr sub_neg_eq_add, ",", expr continuous_linear_map.map_smul, "]"] [] [] } },
  refine [expr ⟨h, le_antisymm _ _⟩],
  { calc
      «expr ≤ »(«expr∥ ∥»(g.extend_to_𝕜), «expr∥ ∥»(g)) : g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
      «expr = »(..., «expr∥ ∥»(fr)) : hnormeq
      «expr ≤ »(..., «expr * »(«expr∥ ∥»(re_clm), «expr∥ ∥»(f))) : continuous_linear_map.op_norm_comp_le _ _
      «expr = »(..., «expr∥ ∥»(f)) : by rw ["[", expr re_clm_norm, ",", expr one_mul, "]"] [] },
  { exact [expr f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg (λ x, «expr ▸ »(h x, g.extend_to_𝕜.le_op_norm x))] }
end

end IsROrC

section DualVector

variable(𝕜 : Type v)[IsROrC 𝕜]

variable{E : Type u}[NormedGroup E][NormedSpace 𝕜 E]

open ContinuousLinearEquiv Submodule

open_locale Classical

theorem coord_norm' (x : E) (h : x ≠ 0) : ∥norm' 𝕜 x • coord 𝕜 x h∥ = 1 :=
  by 
    rw [norm_smul, norm_norm', coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
  by 
    let p : Submodule 𝕜 E := 𝕜∙x 
    let f := norm' 𝕜 x • coord 𝕜 x h 
    obtain ⟨g, hg⟩ := exists_extension_norm_eq p f 
    refine' ⟨g, _, _⟩
    ·
      rw [hg.2, coord_norm']
    ·
      calc g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜∙x) :=
        by 
          rw [coe_mk]_ = (norm' 𝕜 x • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜∙x) :=
        by 
          rw [←hg.1]_ = norm' 𝕜 x :=
        by 
          simp 

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [Nontrivial E] (x : E) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = norm' 𝕜 x :=
  by 
    byCases' hx : x = 0
    ·
      obtain ⟨y, hy⟩ := exists_ne (0 : E)
      obtain ⟨g, hg⟩ : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g y = norm' 𝕜 y := exists_dual_vector 𝕜 y hy 
      refine' ⟨g, hg.left, _⟩
      rw [norm'_def, hx, norm_zero, RingHom.map_zero, ContinuousLinearMap.map_zero]
    ·
      exact exists_dual_vector 𝕜 x hx

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, but only ensuring that
    the dual element has norm at most `1` (this can not be improved for the trivial
    vector space). -/
theorem exists_dual_vector'' (x : E) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ ≤ 1 ∧ g x = norm' 𝕜 x :=
  by 
    byCases' hx : x = 0
    ·
      refine'
        ⟨0,
          by 
            simp ,
          _⟩
      symm 
      simp [hx]
    ·
      rcases exists_dual_vector 𝕜 x hx with ⟨g, g_norm, g_eq⟩
      exact ⟨g, g_norm.le, g_eq⟩

end DualVector

