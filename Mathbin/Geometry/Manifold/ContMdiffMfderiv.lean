/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module geometry.manifold.cont_mdiff_mfderiv
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.ContMdiff
import Mathbin.Geometry.Manifold.Mfderiv

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `mdifferentiable`, `cont_mdiff`, `mfderiv`, `tangent_map`
and related notions.

## Main statements

* `cont_mdiff_on.cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff.cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/


open Set Function Filter ChartedSpace SmoothManifoldWithCorners

open Topology Manifold

/-! ### Definition of smooth functions between manifolds -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [Is : SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [I's : SmoothManifoldWithCorners I' M']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type _} [TopologicalSpace N] [ChartedSpace G N]
  [Js : SmoothManifoldWithCorners J N]
  -- declare a smooth manifold `N'` over the pair `(F', G')`.
  {F' : Type _}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type _} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type _} [TopologicalSpace N'] [ChartedSpace G' N']
  [J's : SmoothManifoldWithCorners J' N']
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M → M'}
  {s s₁ t : Set M} {x : M} {m n : ℕ∞}

/-! ### Deducing differentiability from smoothness -/


theorem ContMdiffWithinAt.mdifferentiableWithinAt (hf : ContMdiffWithinAt I I' n f s x)
    (hn : 1 ≤ n) : MdifferentiableWithinAt I I' f s x :=
  by
  suffices h : MdifferentiableWithinAt I I' f (s ∩ f ⁻¹' (extChartAt I' (f x)).source) x
  · rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhds_within
    exact extChartAt_source_mem_nhds I' (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono (inter_subset_left _ _), (hf.2.DifferentiableWithinAt hn).mono (by mfld_set_tac)⟩
#align cont_mdiff_within_at.mdifferentiable_within_at ContMdiffWithinAt.mdifferentiableWithinAt

theorem ContMdiffAt.mdifferentiableAt (hf : ContMdiffAt I I' n f x) (hn : 1 ≤ n) :
    MdifferentiableAt I I' f x :=
  mdifferentiableWithinAt_univ.1 <| ContMdiffWithinAt.mdifferentiableWithinAt hf hn
#align cont_mdiff_at.mdifferentiable_at ContMdiffAt.mdifferentiableAt

theorem ContMdiffOn.mdifferentiableOn (hf : ContMdiffOn I I' n f s) (hn : 1 ≤ n) :
    MdifferentiableOn I I' f s := fun x hx => (hf x hx).MdifferentiableWithinAt hn
#align cont_mdiff_on.mdifferentiable_on ContMdiffOn.mdifferentiableOn

theorem ContMdiff.mdifferentiable (hf : ContMdiff I I' n f) (hn : 1 ≤ n) : Mdifferentiable I I' f :=
  fun x => (hf x).MdifferentiableAt hn
#align cont_mdiff.mdifferentiable ContMdiff.mdifferentiable

theorem SmoothWithinAt.mdifferentiableWithinAt (hf : SmoothWithinAt I I' f s x) :
    MdifferentiableWithinAt I I' f s x :=
  hf.MdifferentiableWithinAt le_top
#align smooth_within_at.mdifferentiable_within_at SmoothWithinAt.mdifferentiableWithinAt

theorem SmoothAt.mdifferentiableAt (hf : SmoothAt I I' f x) : MdifferentiableAt I I' f x :=
  hf.MdifferentiableAt le_top
#align smooth_at.mdifferentiable_at SmoothAt.mdifferentiableAt

theorem SmoothOn.mdifferentiableOn (hf : SmoothOn I I' f s) : MdifferentiableOn I I' f s :=
  hf.MdifferentiableOn le_top
#align smooth_on.mdifferentiable_on SmoothOn.mdifferentiableOn

theorem Smooth.mdifferentiable (hf : Smooth I I' f) : Mdifferentiable I I' f :=
  ContMdiff.mdifferentiable hf le_top
#align smooth.mdifferentiable Smooth.mdifferentiable

theorem Smooth.mdifferentiableAt (hf : Smooth I I' f) : MdifferentiableAt I I' f x :=
  hf.Mdifferentiable x
#align smooth.mdifferentiable_at Smooth.mdifferentiableAt

theorem Smooth.mdifferentiableWithinAt (hf : Smooth I I' f) : MdifferentiableWithinAt I I' f s x :=
  hf.MdifferentiableAt.MdifferentiableWithinAt
#align smooth.mdifferentiable_within_at Smooth.mdifferentiableWithinAt

/-! ### The tangent map of a smooth function is smooth -/


section tangentMap

/-- If a function is `C^n` with `1 ≤ n` on a domain with unique derivatives, then its bundled
derivative is continuous. In this auxiliary lemma, we prove this fact when the source and target
space are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.continuous_on_tangent_map_within`-/
theorem ContMdiffOn.continuousOn_tangentMapWithin_aux {f : H → H'} {s : Set H}
    (hf : ContMdiffOn I I' n f s) (hn : 1 ≤ n) (hs : UniqueMdiffOn I s) :
    ContinuousOn (tangentMapWithin I I' f s) (TangentBundle.proj I H ⁻¹' s) :=
  by
  suffices h :
    ContinuousOn
      (fun p : H × E =>
        (f p.fst,
          (fderivWithin 𝕜 (writtenInExtChartAt I I' p.fst f) (I.symm ⁻¹' s ∩ range I)
                ((extChartAt I p.fst) p.fst) :
              E →L[𝕜] E')
            p.snd))
      (Prod.fst ⁻¹' s)
  · have A := (tangentBundleModelSpaceHomeomorph H I).Continuous
    rw [continuous_iff_continuousOn_univ] at A
    have B :=
      ((tangentBundleModelSpaceHomeomorph H' I').symm.Continuous.comp_continuous_on h).comp' A
    have :
      univ ∩ ⇑(tangentBundleModelSpaceHomeomorph H I) ⁻¹' (Prod.fst ⁻¹' s) =
        TangentBundle.proj I H ⁻¹' s :=
      by
      ext ⟨x, v⟩
      simp only [mfld_simps]
    rw [this] at B
    apply B.congr
    rintro ⟨x, v⟩ hx
    dsimp [tangentMapWithin]
    ext
    · rfl
    simp only [mfld_simps]
    apply congr_fun
    apply congr_arg
    rw [MdifferentiableWithinAt.mfderivWithin (hf.mdifferentiable_on hn x hx)]
    rfl
  suffices h :
    ContinuousOn
      (fun p : H × E =>
        (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I p.fst) : E →L[𝕜] E') p.snd)
      (Prod.fst ⁻¹' s)
  · dsimp [writtenInExtChartAt, extChartAt]
    apply
      ContinuousOn.prod
        (ContinuousOn.comp hf.continuous_on continuous_fst.continuous_on (subset.refl _))
    apply h.congr
    intro p hp
    rfl
  suffices h : ContinuousOn (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)) (I '' s)
  · have C := ContinuousOn.comp h I.continuous_to_fun.continuous_on (subset.refl _)
    have A : Continuous fun q : (E →L[𝕜] E') × E => q.1 q.2 :=
      is_bounded_bilinear_map_apply.continuous
    have B :
      ContinuousOn
        (fun p : H × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I p.1), p.2))
        (Prod.fst ⁻¹' s) :=
      by
      apply ContinuousOn.prod _ continuous_snd.continuous_on
      refine' (ContinuousOn.comp C continuous_fst.continuous_on _ : _)
      exact preimage_mono (subset_preimage_image _ _)
    exact A.comp_continuous_on B
  rw [contMdiffOn_iff] at hf
  let x : H := I.symm (0 : E)
  let y : H' := I'.symm (0 : E')
  have A := hf.2 x y
  simp only [I.image_eq, inter_comm, mfld_simps] at A⊢
  apply A.continuous_on_fderiv_within _ hn
  convert hs.unique_diff_on_target_inter x using 1
  simp only [inter_comm, mfld_simps]
#align cont_mdiff_on.continuous_on_tangent_map_within_aux ContMdiffOn.continuousOn_tangentMapWithin_aux

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative is
`C^m` when `m+1 ≤ n`. In this auxiliary lemma, we prove this fact when the source and target space
are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.cont_mdiff_on_tangent_map_within` -/
theorem ContMdiffOn.contMdiffOn_tangentMapWithin_aux {f : H → H'} {s : Set H}
    (hf : ContMdiffOn I I' n f s) (hmn : m + 1 ≤ n) (hs : UniqueMdiffOn I s) :
    ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) (TangentBundle.proj I H ⁻¹' s) :=
  by
  have m_le_n : m ≤ n := by
    apply le_trans _ hmn
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _
    simpa only [add_zero] using this
  have one_le_n : 1 ≤ n := by
    apply le_trans _ hmn
    change 0 + 1 ≤ m + 1
    exact add_le_add_right (zero_le _) _
  have U' : UniqueDiffOn 𝕜 (range I ∩ I.symm ⁻¹' s) :=
    by
    intro y hy
    simpa only [UniqueMdiffOn, UniqueMdiffWithinAt, hy.1, inter_comm, mfld_simps] using
      hs (I.symm y) hy.2
  rw [contMdiffOn_iff]
  refine' ⟨hf.continuous_on_tangent_map_within_aux one_le_n hs, fun p q => _⟩
  have A :
    range I ×ˢ univ ∩
        ((Equiv.sigmaEquivProd H E).symm ∘ fun p : E × E => (I.symm p.fst, p.snd)) ⁻¹'
          (TangentBundle.proj I H ⁻¹' s) =
      (range I ∩ I.symm ⁻¹' s) ×ˢ univ :=
    by
    ext ⟨x, v⟩
    simp only [mfld_simps]
  suffices h :
    ContDiffOn 𝕜 m
      (((fun p : H' × E' => (I' p.fst, p.snd)) ∘ Equiv.sigmaEquivProd H' E') ∘
        tangentMapWithin I I' f s ∘
          (Equiv.sigmaEquivProd H E).symm ∘ fun p : E × E => (I.symm p.fst, p.snd))
      ((range ⇑I ∩ ⇑I.symm ⁻¹' s) ×ˢ univ)
  · simpa [A] using h
  change
    ContDiffOn 𝕜 m
      (fun p : E × E =>
        ((I' (f (I.symm p.fst)), (mfderivWithin I I' f s (I.symm p.fst) : E → E') p.snd) : E' × E'))
      ((range I ∩ I.symm ⁻¹' s) ×ˢ univ)
  -- check that all bits in this formula are `C^n`
  have hf' := contMdiffOn_iff.1 hf
  have A : ContDiffOn 𝕜 m (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) := by
    simpa only [mfld_simps] using (hf'.2 (I.symm 0) (I'.symm 0)).of_le m_le_n
  have B : ContDiffOn 𝕜 m ((I' ∘ f ∘ I.symm) ∘ Prod.fst) ((range I ∩ I.symm ⁻¹' s) ×ˢ univ) :=
    A.comp cont_diff_fst.cont_diff_on (prod_subset_preimage_fst _ _)
  suffices C :
    ContDiffOn 𝕜 m
      (fun p : E × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) p.1 : _) p.2)
      ((range I ∩ I.symm ⁻¹' s) ×ˢ univ)
  · apply ContDiffOn.prod B _
    apply C.congr fun p hp => _
    simp only [mfld_simps] at hp
    simp only [mfderivWithin, hf.mdifferentiable_on one_le_n _ hp.2, hp.1, if_pos, mfld_simps]
  have D :
    ContDiffOn 𝕜 m (fun x => fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) x)
      (range I ∩ I.symm ⁻¹' s) :=
    by
    have : ContDiffOn 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) := by
      simpa only [mfld_simps] using hf'.2 (I.symm 0) (I'.symm 0)
    simpa only [inter_comm] using this.fderiv_within U' hmn
  have := D.comp cont_diff_fst.cont_diff_on (prod_subset_preimage_fst _ _)
  have := ContDiffOn.prod this cont_diff_snd.cont_diff_on
  exact is_bounded_bilinear_map_apply.cont_diff.comp_cont_diff_on this
#align cont_mdiff_on.cont_mdiff_on_tangent_map_within_aux ContMdiffOn.contMdiffOn_tangentMapWithin_aux

include Is I's

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem ContMdiffOn.contMdiffOn_tangentMapWithin (hf : ContMdiffOn I I' n f s) (hmn : m + 1 ≤ n)
    (hs : UniqueMdiffOn I s) :
    ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) (TangentBundle.proj I M ⁻¹' s) :=
  by
  /- The strategy of the proof is to avoid unfolding the definitions, and reduce by functoriality
    to the case of functions on the model spaces, where we have already proved the result.
    Let `l` and `r` be the charts to the left and to the right, so that we have
    ```
       l^{-1}      f       r
    H --------> M ---> M' ---> H'
    ```
    Then the tangent map `T(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
    ```
        Tl        T(r ∘ f ∘ l^{-1})         Tr^{-1}
    TM -----> TH -------------------> TH' ---------> TM'
    ```
    where `Tr^{-1}` and `Tl` are the tangent maps of `r^{-1}` and `l`. Writing `Tl` and `Tr^{-1}` as
    composition of charts (called `Dl` and `il` for `l` and `Dr` and `ir` in the proof below), it
    follows that they are smooth. The composition of all these maps is `Tf`, and is therefore smooth
    as a composition of smooth maps.
    -/
  have m_le_n : m ≤ n := by
    apply le_trans _ hmn
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _
    simpa only [add_zero]
  have one_le_n : 1 ≤ n := by
    apply le_trans _ hmn
    change 0 + 1 ≤ m + 1
    exact add_le_add_right (zero_le _) _
  -- First step: local reduction on the space, to a set `s'` which is contained in chart domains.
  refine' contMdiffOn_of_locally_contMdiffOn fun p hp => _
  have hf' := contMdiffOn_iff.1 hf
  simp [TangentBundle.proj] at hp
  let l := chart_at H p.1
  set Dl := chart_at (ModelProd H E) p with hDl
  let r := chart_at H' (f p.1)
  let Dr := chart_at (ModelProd H' E') (tangentMapWithin I I' f s p)
  let il := chart_at (ModelProd H E) (tangentMap I I l p)
  let ir := chart_at (ModelProd H' E') (tangentMap I I' (r ∘ f) p)
  let s' := f ⁻¹' r.source ∩ s ∩ l.source
  let s'_lift := TangentBundle.proj I M ⁻¹' s'
  let s'l := l.target ∩ l.symm ⁻¹' s'
  let s'l_lift := TangentBundle.proj I H ⁻¹' s'l
  rcases continuousOn_iff'.1 hf'.1 r.source r.open_source with ⟨o, o_open, ho⟩
  suffices h : ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) s'_lift
  · refine' ⟨TangentBundle.proj I M ⁻¹' (o ∩ l.source), _, _, _⟩
    show IsOpen (TangentBundle.proj I M ⁻¹' (o ∩ l.source))
    exact (IsOpen.inter o_open l.open_source).Preimage (tangentBundle_proj_continuous _ _)
    show p ∈ TangentBundle.proj I M ⁻¹' (o ∩ l.source)
    · simp [TangentBundle.proj]
      have : p.1 ∈ f ⁻¹' r.source ∩ s := by simp [hp]
      rw [ho] at this
      exact this.1
    · have : TangentBundle.proj I M ⁻¹' s ∩ TangentBundle.proj I M ⁻¹' (o ∩ l.source) = s'_lift :=
        by
        dsimp only [s'_lift, s']
        rw [ho]
        mfld_set_tac
      rw [this]
      exact h
  /- Second step: check that all functions are smooth, and use the chain rule to write the bundled
    derivative as a composition of a function between model spaces and of charts.
    Convention: statements about the differentiability of `a ∘ b ∘ c` are named `diff_abc`. Statements
    about differentiability in the bundle have a `_lift` suffix. -/
  have U' : UniqueMdiffOn I s' :=
    by
    apply UniqueMdiffOn.inter _ l.open_source
    rw [ho, inter_comm]
    exact hs.inter o_open
  have U'l : UniqueMdiffOn I s'l := U'.unique_mdiff_on_preimage (mdifferentiable_chart _ _)
  have diff_f : ContMdiffOn I I' n f s' := hf.mono (by mfld_set_tac)
  have diff_r : ContMdiffOn I' I' n r r.source := contMdiffOn_chart
  have diff_rf : ContMdiffOn I I' n (r ∘ f) s' :=
    by
    apply ContMdiffOn.comp diff_r diff_f fun x hx => _
    simp only [s', mfld_simps] at hx
    simp only [hx, mfld_simps]
  have diff_l : ContMdiffOn I I n l.symm s'l :=
    haveI A : ContMdiffOn I I n l.symm l.target := contMdiffOn_chart_symm
    A.mono (by mfld_set_tac)
  have diff_rfl : ContMdiffOn I I' n (r ∘ f ∘ l.symm) s'l :=
    by
    apply ContMdiffOn.comp diff_rf diff_l
    mfld_set_tac
  have diff_rfl_lift :
    ContMdiffOn I.tangent I'.tangent m (tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    diff_rfl.cont_mdiff_on_tangent_map_within_aux hmn U'l
  have diff_irrfl_lift :
    ContMdiffOn I.tangent I'.tangent m (ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    haveI A : ContMdiffOn I'.tangent I'.tangent m ir ir.source := contMdiffOn_chart
    ContMdiffOn.comp A diff_rfl_lift fun p hp => by simp only [ir, mfld_simps]
  have diff_Drirrfl_lift :
    ContMdiffOn I.tangent I'.tangent m (Dr.symm ∘ ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l)
      s'l_lift :=
    by
    have A : ContMdiffOn I'.tangent I'.tangent m Dr.symm Dr.target := contMdiffOn_chart_symm
    apply ContMdiffOn.comp A diff_irrfl_lift fun p hp => _
    simp only [s'l_lift, TangentBundle.proj, mfld_simps] at hp
    simp only [ir, @LocalEquiv.refl_coe (ModelProd H' E'), hp, mfld_simps]
  -- conclusion of this step: the composition of all the maps above is smooth
  have diff_DrirrflilDl :
    ContMdiffOn I.tangent I'.tangent m
      (Dr.symm ∘ (ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) ∘ il.symm ∘ Dl) s'_lift :=
    by
    have A : ContMdiffOn I.tangent I.tangent m Dl Dl.source := contMdiffOn_chart
    have A' : ContMdiffOn I.tangent I.tangent m Dl s'_lift :=
      by
      apply A.mono fun p hp => _
      simp only [s'_lift, TangentBundle.proj, mfld_simps] at hp
      simp only [Dl, hp, mfld_simps]
    have B : ContMdiffOn I.tangent I.tangent m il.symm il.target := contMdiffOn_chart_symm
    have C : ContMdiffOn I.tangent I.tangent m (il.symm ∘ Dl) s'_lift :=
      ContMdiffOn.comp B A' fun p hp => by simp only [il, mfld_simps]
    apply ContMdiffOn.comp diff_Drirrfl_lift C fun p hp => _
    simp only [s'_lift, TangentBundle.proj, mfld_simps] at hp
    simp only [il, s'l_lift, hp, TangentBundle.proj, mfld_simps]
  /- Third step: check that the composition of all the maps indeed coincides with the derivative we
    are looking for -/
  have eq_comp :
    ∀ q ∈ s'_lift,
      tangentMapWithin I I' f s q =
        (Dr.symm ∘ ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l ∘ il.symm ∘ Dl) q :=
    by
    intro q hq
    simp only [s'_lift, TangentBundle.proj, mfld_simps] at hq
    have U'q : UniqueMdiffWithinAt I s' q.1 := by
      apply U'
      simp only [hq, s', mfld_simps]
    have U'lq : UniqueMdiffWithinAt I s'l (Dl q).1 :=
      by
      apply U'l
      simp only [hq, s'l, mfld_simps]
    have A :
      tangentMapWithin I I' ((r ∘ f) ∘ l.symm) s'l (il.symm (Dl q)) =
        tangentMapWithin I I' (r ∘ f) s' (tangentMapWithin I I l.symm s'l (il.symm (Dl q))) :=
      by
      refine' tangentMapWithin_comp_at (il.symm (Dl q)) _ _ (fun p hp => _) U'lq
      · apply diff_rf.mdifferentiable_on one_le_n
        simp only [hq, mfld_simps]
      · apply diff_l.mdifferentiable_on one_le_n
        simp only [s'l, hq, mfld_simps]
      · simp only [mfld_simps] at hp
        simp only [hp, mfld_simps]
    have B : tangentMapWithin I I l.symm s'l (il.symm (Dl q)) = q :=
      by
      have :
        tangentMapWithin I I l.symm s'l (il.symm (Dl q)) = tangentMap I I l.symm (il.symm (Dl q)) :=
        by
        refine' tangentMapWithin_eq_tangentMap U'lq _
        refine' mdifferentiableAt_atlas_symm _ (chart_mem_atlas _ _) _
        simp only [hq, mfld_simps]
      rw [this, tangentMap_chart_symm, hDl]
      · simp only [hq, mfld_simps]
        have : q ∈ (chart_at (ModelProd H E) p).source := by simp only [hq, mfld_simps]
        exact (chart_at (ModelProd H E) p).left_inv this
      · simp only [hq, mfld_simps]
    have C :
      tangentMapWithin I I' (r ∘ f) s' q =
        tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q) :=
      by
      refine' tangentMapWithin_comp_at q _ _ (fun r hr => _) U'q
      · apply diff_r.mdifferentiable_on one_le_n
        simp only [hq, mfld_simps]
      · apply diff_f.mdifferentiable_on one_le_n
        simp only [hq, mfld_simps]
      · simp only [s', mfld_simps] at hr
        simp only [hr, mfld_simps]
    have D :
      Dr.symm (ir (tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q))) =
        tangentMapWithin I I' f s' q :=
      by
      have A :
        tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q) =
          tangentMap I' I' r (tangentMapWithin I I' f s' q) :=
        by
        apply tangentMapWithin_eq_tangentMap
        · apply IsOpen.uniqueMdiffWithinAt _ r.open_source
          simp [hq]
        · refine' mdifferentiableAt_atlas _ (chart_mem_atlas _ _) _
          simp only [hq, mfld_simps]
      have : f p.1 = (tangentMapWithin I I' f s p).1 := rfl
      rw [A]
      dsimp [r, Dr]
      rw [this, tangentMap_chart]
      · simp only [hq, mfld_simps]
        have :
          tangentMapWithin I I' f s' q ∈
            (chart_at (ModelProd H' E') (tangentMapWithin I I' f s p)).source :=
          by simp only [hq, mfld_simps]
        exact (chart_at (ModelProd H' E') (tangentMapWithin I I' f s p)).left_inv this
      · simp only [hq, mfld_simps]
    have E : tangentMapWithin I I' f s' q = tangentMapWithin I I' f s q :=
      by
      refine' tangentMapWithin_subset (by mfld_set_tac) U'q _
      apply hf.mdifferentiable_on one_le_n
      simp only [hq, mfld_simps]
    simp only [(· ∘ ·), A, B, C, D, E.symm]
  exact diff_DrirrflilDl.congr eq_comp
#align cont_mdiff_on.cont_mdiff_on_tangent_map_within ContMdiffOn.contMdiffOn_tangentMapWithin

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem ContMdiffOn.continuousOn_tangentMapWithin (hf : ContMdiffOn I I' n f s) (hmn : 1 ≤ n)
    (hs : UniqueMdiffOn I s) :
    ContinuousOn (tangentMapWithin I I' f s) (TangentBundle.proj I M ⁻¹' s) :=
  haveI :
    ContMdiffOn I.tangent I'.tangent 0 (tangentMapWithin I I' f s) (TangentBundle.proj I M ⁻¹' s) :=
    hf.cont_mdiff_on_tangent_map_within hmn hs
  this.continuous_on
#align cont_mdiff_on.continuous_on_tangent_map_within ContMdiffOn.continuousOn_tangentMapWithin

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem ContMdiff.contMdiff_tangentMap (hf : ContMdiff I I' n f) (hmn : m + 1 ≤ n) :
    ContMdiff I.tangent I'.tangent m (tangentMap I I' f) :=
  by
  rw [← contMdiffOn_univ] at hf⊢
  convert hf.cont_mdiff_on_tangent_map_within hmn uniqueMdiffOn_univ
  rw [tangentMapWithin_univ]
#align cont_mdiff.cont_mdiff_tangent_map ContMdiff.contMdiff_tangentMap

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem ContMdiff.continuous_tangentMap (hf : ContMdiff I I' n f) (hmn : 1 ≤ n) :
    Continuous (tangentMap I I' f) :=
  by
  rw [← contMdiffOn_univ] at hf
  rw [continuous_iff_continuousOn_univ]
  convert hf.continuous_on_tangent_map_within hmn uniqueMdiffOn_univ
  rw [tangentMapWithin_univ]
#align cont_mdiff.continuous_tangent_map ContMdiff.continuous_tangentMap

end tangentMap

/-! ### Smoothness of the projection in a basic smooth bundle -/


namespace BasicSmoothVectorBundleCore

variable (Z : BasicSmoothVectorBundleCore I M E')

/-- A version of `cont_mdiff_at_iff_target` when the codomain is the total space of
  a `basic_smooth_vector_bundle_core`. The continuity condition in the RHS is weaker. -/
theorem contMdiffAt_iff_target {f : N → Z.toVectorBundleCore.TotalSpace} {x : N} {n : ℕ∞} :
    ContMdiffAt J (I.Prod 𝓘(𝕜, E')) n f x ↔
      ContinuousAt (Bundle.TotalSpace.proj ∘ f) x ∧
        ContMdiffAt J 𝓘(𝕜, E × E') n (extChartAt (I.Prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
  by
  let Z' := Z.to_vector_bundle_core
  rw [contMdiffAt_iff_target, and_congr_left_iff]
  refine' fun hf => ⟨fun h => Z'.continuous_proj.continuous_at.comp h, fun h => _⟩
  exact
    (Z'.local_triv ⟨chart_at _ (f x).1, chart_mem_atlas _ _⟩).continuous_at_of_comp_left h
      (mem_chart_source _ _) (h.prod hf.continuous_at.snd)
#align basic_smooth_vector_bundle_core.cont_mdiff_at_iff_target BasicSmoothVectorBundleCore.contMdiffAt_iff_target

theorem smooth_iff_target {f : N → Z.toVectorBundleCore.TotalSpace} :
    Smooth J (I.Prod 𝓘(𝕜, E')) f ↔
      Continuous (Bundle.TotalSpace.proj ∘ f) ∧
        ∀ x, SmoothAt J 𝓘(𝕜, E × E') (extChartAt (I.Prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
  by
  simp_rw [Smooth, SmoothAt, ContMdiff, Z.cont_mdiff_at_iff_target, forall_and,
    continuous_iff_continuousAt]
#align basic_smooth_vector_bundle_core.smooth_iff_target BasicSmoothVectorBundleCore.smooth_iff_target

theorem contMdiff_proj : ContMdiff (I.Prod 𝓘(𝕜, E')) I n Z.toVectorBundleCore.proj :=
  by
  intro x
  rw [ContMdiffAt, contMdiffWithinAt_iff']
  refine' ⟨Z.to_vector_bundle_core.continuous_proj.continuous_within_at, _⟩
  simp only [(· ∘ ·), chart_at, chart, mfld_simps]
  apply cont_diff_within_at_fst.congr
  · rintro ⟨a, b⟩ hab
    simp only [mfld_simps] at hab
    simp only [hab, mfld_simps]
  · simp only [mfld_simps]
#align basic_smooth_vector_bundle_core.cont_mdiff_proj BasicSmoothVectorBundleCore.contMdiff_proj

theorem smooth_proj : Smooth (I.Prod 𝓘(𝕜, E')) I Z.toVectorBundleCore.proj :=
  contMdiff_proj Z
#align basic_smooth_vector_bundle_core.smooth_proj BasicSmoothVectorBundleCore.smooth_proj

theorem contMdiffOn_proj {s : Set Z.toVectorBundleCore.TotalSpace} :
    ContMdiffOn (I.Prod 𝓘(𝕜, E')) I n Z.toVectorBundleCore.proj s :=
  Z.cont_mdiff_proj.ContMdiffOn
#align basic_smooth_vector_bundle_core.cont_mdiff_on_proj BasicSmoothVectorBundleCore.contMdiffOn_proj

theorem smoothOn_proj {s : Set Z.toVectorBundleCore.TotalSpace} :
    SmoothOn (I.Prod 𝓘(𝕜, E')) I Z.toVectorBundleCore.proj s :=
  contMdiffOn_proj Z
#align basic_smooth_vector_bundle_core.smooth_on_proj BasicSmoothVectorBundleCore.smoothOn_proj

theorem contMdiffAt_proj {p : Z.toVectorBundleCore.TotalSpace} :
    ContMdiffAt (I.Prod 𝓘(𝕜, E')) I n Z.toVectorBundleCore.proj p :=
  Z.cont_mdiff_proj.ContMdiffAt
#align basic_smooth_vector_bundle_core.cont_mdiff_at_proj BasicSmoothVectorBundleCore.contMdiffAt_proj

theorem smoothAt_proj {p : Z.toVectorBundleCore.TotalSpace} :
    SmoothAt (I.Prod 𝓘(𝕜, E')) I Z.toVectorBundleCore.proj p :=
  Z.cont_mdiff_at_proj
#align basic_smooth_vector_bundle_core.smooth_at_proj BasicSmoothVectorBundleCore.smoothAt_proj

theorem contMdiffWithinAt_proj {s : Set Z.toVectorBundleCore.TotalSpace}
    {p : Z.toVectorBundleCore.TotalSpace} :
    ContMdiffWithinAt (I.Prod 𝓘(𝕜, E')) I n Z.toVectorBundleCore.proj s p :=
  Z.cont_mdiff_at_proj.ContMdiffWithinAt
#align basic_smooth_vector_bundle_core.cont_mdiff_within_at_proj BasicSmoothVectorBundleCore.contMdiffWithinAt_proj

theorem smoothWithinAt_proj {s : Set Z.toVectorBundleCore.TotalSpace}
    {p : Z.toVectorBundleCore.TotalSpace} :
    SmoothWithinAt (I.Prod 𝓘(𝕜, E')) I Z.toVectorBundleCore.proj s p :=
  Z.cont_mdiff_within_at_proj
#align basic_smooth_vector_bundle_core.smooth_within_at_proj BasicSmoothVectorBundleCore.smoothWithinAt_proj

/-- If an element of `E'` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is smooth. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem smooth_const_section (v : E')
    (h : ∀ i j : atlas H M, ∀ x ∈ i.1.source ∩ j.1.source, Z.coordChange i j (i.1 x) v = v) :
    Smooth I (I.Prod 𝓘(𝕜, E')) (show M → Z.toVectorBundleCore.TotalSpace from fun x => ⟨x, v⟩) :=
  by
  intro x
  rw [ContMdiffAt, contMdiffWithinAt_iff']
  constructor
  · apply Continuous.continuousWithinAt
    apply FiberBundleCore.continuous_const_section
    intro i j y hy
    exact h _ _ _ hy
  · have : ContDiff 𝕜 ⊤ fun y : E => (y, v) := cont_diff_id.prod contDiff_const
    apply this.cont_diff_within_at.congr
    · intro y hy
      simp only [mfld_simps] at hy
      simp only [chart, hy, chart_at, Prod.mk.inj_iff, to_vector_bundle_core, mfld_simps]
      apply h
      simp only [hy, Subtype.val_eq_coe, mfld_simps]
    · simp only [chart, chart_at, Prod.mk.inj_iff, to_vector_bundle_core, mfld_simps]
      apply h
      simp only [Subtype.val_eq_coe, mfld_simps]
#align basic_smooth_vector_bundle_core.smooth_const_section BasicSmoothVectorBundleCore.smooth_const_section

end BasicSmoothVectorBundleCore

/-! ### Smoothness of the tangent bundle projection -/


namespace TangentBundle

include Is

theorem contMdiff_proj : ContMdiff I.tangent I n (proj I M) :=
  BasicSmoothVectorBundleCore.contMdiff_proj _
#align tangent_bundle.cont_mdiff_proj TangentBundle.contMdiff_proj

theorem smooth_proj : Smooth I.tangent I (proj I M) :=
  BasicSmoothVectorBundleCore.smooth_proj _
#align tangent_bundle.smooth_proj TangentBundle.smooth_proj

theorem contMdiffOn_proj {s : Set (TangentBundle I M)} : ContMdiffOn I.tangent I n (proj I M) s :=
  BasicSmoothVectorBundleCore.contMdiffOn_proj _
#align tangent_bundle.cont_mdiff_on_proj TangentBundle.contMdiffOn_proj

theorem smoothOn_proj {s : Set (TangentBundle I M)} : SmoothOn I.tangent I (proj I M) s :=
  BasicSmoothVectorBundleCore.smoothOn_proj _
#align tangent_bundle.smooth_on_proj TangentBundle.smoothOn_proj

theorem contMdiffAt_proj {p : TangentBundle I M} : ContMdiffAt I.tangent I n (proj I M) p :=
  BasicSmoothVectorBundleCore.contMdiffAt_proj _
#align tangent_bundle.cont_mdiff_at_proj TangentBundle.contMdiffAt_proj

theorem smoothAt_proj {p : TangentBundle I M} : SmoothAt I.tangent I (proj I M) p :=
  BasicSmoothVectorBundleCore.smoothAt_proj _
#align tangent_bundle.smooth_at_proj TangentBundle.smoothAt_proj

theorem contMdiffWithinAt_proj {s : Set (TangentBundle I M)} {p : TangentBundle I M} :
    ContMdiffWithinAt I.tangent I n (proj I M) s p :=
  BasicSmoothVectorBundleCore.contMdiffWithinAt_proj _
#align tangent_bundle.cont_mdiff_within_at_proj TangentBundle.contMdiffWithinAt_proj

theorem smoothWithinAt_proj {s : Set (TangentBundle I M)} {p : TangentBundle I M} :
    SmoothWithinAt I.tangent I (proj I M) s p :=
  BasicSmoothVectorBundleCore.smoothWithinAt_proj _
#align tangent_bundle.smooth_within_at_proj TangentBundle.smoothWithinAt_proj

variable (I M)

/-- The zero section of the tangent bundle -/
def zeroSection : M → TangentBundle I M := fun x => ⟨x, 0⟩
#align tangent_bundle.zero_section TangentBundle.zeroSection

variable {I M}

theorem smooth_zeroSection : Smooth I I.tangent (zeroSection I M) :=
  by
  apply BasicSmoothVectorBundleCore.smooth_const_section (tangentBundleCore I M) 0
  intro i j x hx
  simp only [tangentBundleCore, ContinuousLinearMap.map_zero, ContinuousLinearMap.coe_coe,
    mfld_simps]
#align tangent_bundle.smooth_zero_section TangentBundle.smooth_zeroSection

open Bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
theorem tangentMap_tangentBundle_pure (p : TangentBundle I M) :
    tangentMap I I.tangent (TangentBundle.zeroSection I M) p = ⟨⟨p.1, 0⟩, ⟨p.2, 0⟩⟩ :=
  by
  rcases p with ⟨x, v⟩
  have N : I.symm ⁻¹' (chart_at H x).target ∈ 𝓝 (I ((chart_at H x) x)) :=
    by
    apply IsOpen.mem_nhds
    apply (LocalHomeomorph.open_target _).Preimage I.continuous_inv_fun
    simp only [mfld_simps]
  have A : MdifferentiableAt I I.tangent (fun x => @total_space_mk M (TangentSpace I) x 0) x :=
    tangent_bundle.smooth_zero_section.mdifferentiable_at
  have B :
    fderivWithin 𝕜 (fun x_1 : E => (x_1, (0 : E))) (Set.range ⇑I) (I ((chart_at H x) x)) v =
      (v, 0) :=
    by
    rw [fderivWithin_eq_fderiv, DifferentiableAt.fderiv_prod]
    · simp
    · exact differentiableAt_id'
    · exact differentiableAt_const _
    · exact ModelWithCorners.unique_diff_at_image I
    · exact differentiable_at_id'.prod (differentiableAt_const _)
  simp only [TangentBundle.zeroSection, tangentMap, mfderiv, A, if_pos, chart_at,
    BasicSmoothVectorBundleCore.chart, BasicSmoothVectorBundleCore.toVectorBundleCore,
    tangentBundleCore, Function.comp, ContinuousLinearMap.map_zero, mfld_simps]
  rw [← fderivWithin_inter N (I.unique_diff (I ((chart_at H x) x)) (Set.mem_range_self _))] at B
  rw [← fderivWithin_inter N (I.unique_diff (I ((chart_at H x) x)) (Set.mem_range_self _)), ← B]
  congr 2
  apply fderivWithin_congr _ fun y hy => _
  · simp only [Prod.mk.inj_iff, mfld_simps]
  · apply UniqueDiffWithinAt.inter (I.unique_diff _ _) N
    simp only [mfld_simps]
  · simp only [mfld_simps] at hy
    simp only [hy, Prod.mk.inj_iff, mfld_simps]
#align tangent_bundle.tangent_map_tangent_bundle_pure TangentBundle.tangentMap_tangentBundle_pure

end TangentBundle

