/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module geometry.manifold.bump_function
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.SpecificFunctions
import Mathbin.Geometry.Manifold.ContMdiff

/-!
# Smooth bump functions on a smooth manifold

In this file we define `smooth_bump_function I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < r < R` with small enough `R`. We
define a coercion to function for this type, and for `f : smooth_bump_function I c`, the function
`⇑f` written in the extended chart at `c` has the following properties:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `ext_chart_at I f` and are given as lemmas in the
`smooth_bump_function` namespace.

## Tags

manifold, smooth bump function
-/


universe uE uF uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M]

open Function Filter FiniteDimensional Set

open TopologicalSpace Manifold Classical Filter BigOperators

noncomputable section

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/


/-- Given a smooth manifold modelled on a finite dimensional space `E`,
`f : smooth_bump_function I M` is a smooth function on `M` such that in the extended chart `e` at
`f.c`:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `f.c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properties. The function is
available as `⇑f` or `f x`. Formal statements of the properties listed above involve some
(pre)images under `ext_chart_at I f.c` and are given as lemmas in the `smooth_bump_function`
namespace. -/
structure SmoothBumpFunction (c : M) extends ContDiffBump (extChartAt I c c) where
  closed_ball_subset : Euclidean.closedBall (extChartAt I c c) R ∩ range I ⊆ (extChartAt I c).target
#align smooth_bump_function SmoothBumpFunction

variable {M}

namespace SmoothBumpFunction

open Euclidean renaming dist → eudist

variable {c : M} (f : SmoothBumpFunction I c) {x : M} {I}

/-- The function defined by `f : smooth_bump_function c`. Use automatic coercion to function
instead. -/
def toFun : M → ℝ :=
  indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c)
#align smooth_bump_function.to_fun SmoothBumpFunction.toFun

instance : CoeFun (SmoothBumpFunction I c) fun _ => M → ℝ :=
  ⟨toFun⟩

theorem coe_def : ⇑f = indicator (chartAt H c).source (f.toContDiffBump ∘ extChartAt I c) :=
  rfl
#align smooth_bump_function.coe_def SmoothBumpFunction.coe_def

theorem R_pos : 0 < f.r :=
  f.toContDiffBump.R_pos
#align smooth_bump_function.R_pos SmoothBumpFunction.R_pos

theorem ball_subset : ball (extChartAt I c c) f.r ∩ range I ⊆ (extChartAt I c).target :=
  Subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) f.closed_ball_subset
#align smooth_bump_function.ball_subset SmoothBumpFunction.ball_subset

theorem eq_on_source : EqOn f (f.toContDiffBump ∘ extChartAt I c) (chartAt H c).source :=
  eq_on_indicator
#align smooth_bump_function.eq_on_source SmoothBumpFunction.eq_on_source

theorem eventually_eq_of_mem_source (hx : x ∈ (chartAt H c).source) :
    f =ᶠ[𝓝 x] f.toContDiffBump ∘ extChartAt I c :=
  f.EqOnSource.eventually_eq_of_mem <| IsOpen.mem_nhds (chartAt H c).open_source hx
#align
  smooth_bump_function.eventually_eq_of_mem_source SmoothBumpFunction.eventually_eq_of_mem_source

theorem one_of_dist_le (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) ≤ f.R) : f x = 1 := by
  simp only [f.eq_on_source hs, (· ∘ ·), f.to_cont_diff_bump.one_of_mem_closed_ball hd]
#align smooth_bump_function.one_of_dist_le SmoothBumpFunction.one_of_dist_le

theorem support_eq_inter_preimage :
    support f = (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) f.r := by
  rw [coe_def, support_indicator, (· ∘ ·), support_comp_eq_preimage, ← ext_chart_at_source I, ←
    (extChartAt I c).symm_image_target_inter_eq', ← (extChartAt I c).symm_image_target_inter_eq',
    f.to_cont_diff_bump.support_eq]
#align smooth_bump_function.support_eq_inter_preimage SmoothBumpFunction.support_eq_inter_preimage

theorem is_open_support : IsOpen (support f) :=
  by
  rw [support_eq_inter_preimage]
  exact is_open_ext_chart_at_preimage I c is_open_ball
#align smooth_bump_function.is_open_support SmoothBumpFunction.is_open_support

theorem support_eq_symm_image :
    support f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.r ∩ range I) :=
  by
  rw [f.support_eq_inter_preimage, ← ext_chart_at_source I, ←
    (extChartAt I c).symm_image_target_inter_eq', inter_comm]
  congr 1 with y
  exact
    and_congr_right_iff.2 fun hy =>
      ⟨fun h => ext_chart_at_target_subset_range _ _ h, fun h => f.ball_subset ⟨hy, h⟩⟩
#align smooth_bump_function.support_eq_symm_image SmoothBumpFunction.support_eq_symm_image

theorem support_subset_source : support f ⊆ (chartAt H c).source :=
  by
  rw [f.support_eq_inter_preimage, ← ext_chart_at_source I]
  exact inter_subset_left _ _
#align smooth_bump_function.support_subset_source SmoothBumpFunction.support_subset_source

theorem image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s ⊆ support f) :
    extChartAt I c '' s =
      closedBall (extChartAt I c c) f.r ∩ range I ∩ (extChartAt I c).symm ⁻¹' s :=
  by
  rw [support_eq_inter_preimage, subset_inter_iff, ← ext_chart_at_source I, ← image_subset_iff] at
    hs
  cases' hs with hse hsf
  apply subset.antisymm
  · refine' subset_inter (subset_inter (subset.trans hsf ball_subset_closed_ball) _) _
    · rintro _ ⟨x, -, rfl⟩
      exact mem_range_self _
    · rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
      exact inter_subset_right _ _
  · refine' subset.trans (inter_subset_inter_left _ f.closed_ball_subset) _
    rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
#align
  smooth_bump_function.image_eq_inter_preimage_of_subset_support SmoothBumpFunction.image_eq_inter_preimage_of_subset_support

theorem mem_Icc : f x ∈ Icc (0 : ℝ) 1 :=
  by
  have : f x = 0 ∨ f x = _ := indicator_eq_zero_or_self _ _ _
  cases this <;> rw [this]
  exacts[left_mem_Icc.2 zero_le_one, ⟨f.to_cont_diff_bump.nonneg, f.to_cont_diff_bump.le_one⟩]
#align smooth_bump_function.mem_Icc SmoothBumpFunction.mem_Icc

theorem nonneg : 0 ≤ f x :=
  f.mem_Icc.1
#align smooth_bump_function.nonneg SmoothBumpFunction.nonneg

theorem le_one : f x ≤ 1 :=
  f.mem_Icc.2
#align smooth_bump_function.le_one SmoothBumpFunction.le_one

theorem eventually_eq_one_of_dist_lt (hs : x ∈ (chartAt H c).source)
    (hd : dist (extChartAt I c x) (extChartAt I c c) < f.R) : f =ᶠ[𝓝 x] 1 :=
  by
  filter_upwards [IsOpen.mem_nhds (is_open_ext_chart_at_preimage I c is_open_ball) ⟨hs, hd⟩]
  rintro z ⟨hzs, hzd : _ < _⟩
  exact f.one_of_dist_le hzs hzd.le
#align
  smooth_bump_function.eventually_eq_one_of_dist_lt SmoothBumpFunction.eventually_eq_one_of_dist_lt

theorem eventually_eq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventually_eq_one_of_dist_lt (mem_chart_source _ _) <|
    by
    rw [Euclidean.dist, dist_self]
    exact f.r_pos
#align smooth_bump_function.eventually_eq_one SmoothBumpFunction.eventually_eq_one

@[simp]
theorem eq_one : f c = 1 :=
  f.eventually_eq_one.eq_of_nhds
#align smooth_bump_function.eq_one SmoothBumpFunction.eq_one

theorem support_mem_nhds : support f ∈ 𝓝 c :=
  f.eventually_eq_one.mono fun x hx => by
    rw [hx]
    exact one_ne_zero
#align smooth_bump_function.support_mem_nhds SmoothBumpFunction.support_mem_nhds

theorem tsupport_mem_nhds : tsupport f ∈ 𝓝 c :=
  mem_of_superset f.support_mem_nhds subset_closure
#align smooth_bump_function.tsupport_mem_nhds SmoothBumpFunction.tsupport_mem_nhds

theorem c_mem_support : c ∈ support f :=
  mem_of_mem_nhds f.support_mem_nhds
#align smooth_bump_function.c_mem_support SmoothBumpFunction.c_mem_support

theorem nonempty_support : (support f).Nonempty :=
  ⟨c, f.c_mem_support⟩
#align smooth_bump_function.nonempty_support SmoothBumpFunction.nonempty_support

theorem compact_symm_image_closed_ball :
    IsCompact ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.r ∩ range I)) :=
  (Euclidean.is_compact_closed_ball.inter_right I.closed_range).image_of_continuous_on <|
    (continuous_on_ext_chart_at_symm _ _).mono f.closed_ball_subset
#align
  smooth_bump_function.compact_symm_image_closed_ball SmoothBumpFunction.compact_symm_image_closed_ball

/-- Given a smooth bump function `f : smooth_bump_function I c`, the closed ball of radius `f.R` is
known to include the support of `f`. These closed balls (in the model normed space `E`) intersected
with `set.range I` form a basis of `𝓝[range I] (ext_chart_at I c c)`. -/
theorem nhds_within_range_basis :
    (𝓝[range I] extChartAt I c c).HasBasis (fun f : SmoothBumpFunction I c => True) fun f =>
      closedBall (extChartAt I c c) f.r ∩ range I :=
  by
  refine'
    ((nhds_within_has_basis Euclidean.nhds_basis_closed_ball _).restrict_subset
          (ext_chart_at_target_mem_nhds_within _ _)).to_has_basis'
      _ _
  · rintro R ⟨hR0, hsub⟩
    exact ⟨⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩⟩, hsub⟩, trivial, subset.rfl⟩
  ·
    exact fun f _ =>
      inter_mem (mem_nhds_within_of_mem_nhds <| closed_ball_mem_nhds f.R_pos) self_mem_nhds_within
#align smooth_bump_function.nhds_within_range_basis SmoothBumpFunction.nhds_within_range_basis

theorem is_closed_image_of_is_closed {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    IsClosed (extChartAt I c '' s) :=
  by
  rw [f.image_eq_inter_preimage_of_subset_support hs]
  refine'
    ContinuousOn.preimage_closed_of_closed
      ((continuous_on_ext_chart_at_symm _ _).mono f.closed_ball_subset) _ hsc
  exact IsClosed.inter is_closed_closed_ball I.closed_range
#align
  smooth_bump_function.is_closed_image_of_is_closed SmoothBumpFunction.is_closed_image_of_is_closed

/-- If `f` is a smooth bump function and `s` closed subset of the support of `f` (i.e., of the open
ball of radius `f.R`), then there exists `0 < r < f.R` such that `s` is a subset of the open ball of
radius `r`. Formally, `s ⊆ e.source ∩ e ⁻¹' (ball (e c) r)`, where `e = ext_chart_at I c`. -/
theorem exists_r_pos_lt_subset_ball {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) :
    ∃ (r : _)(hr : r ∈ Ioo 0 f.r),
      s ⊆ (chartAt H c).source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) r :=
  by
  set e := extChartAt I c
  have : IsClosed (e '' s) := f.is_closed_image_of_is_closed hsc hs
  rw [support_eq_inter_preimage, subset_inter_iff, ← image_subset_iff] at hs
  rcases Euclidean.exists_pos_lt_subset_ball f.R_pos this hs.2 with ⟨r, hrR, hr⟩
  exact ⟨r, hrR, subset_inter hs.1 (image_subset_iff.1 hr)⟩
#align
  smooth_bump_function.exists_r_pos_lt_subset_ball SmoothBumpFunction.exists_r_pos_lt_subset_ball

/-- Replace `r` with another value in the interval `(0, f.R)`. -/
def updateR (r : ℝ) (hr : r ∈ Ioo 0 f.r) : SmoothBumpFunction I c :=
  ⟨⟨⟨r, f.r, hr.1, hr.2⟩⟩, f.closed_ball_subset⟩
#align smooth_bump_function.update_r SmoothBumpFunction.updateR

@[simp]
theorem update_r_R {r : ℝ} (hr : r ∈ Ioo 0 f.r) : (f.updateR r hr).r = f.r :=
  rfl
#align smooth_bump_function.update_r_R SmoothBumpFunction.update_r_R

@[simp]
theorem update_r_r {r : ℝ} (hr : r ∈ Ioo 0 f.r) : (f.updateR r hr).R = r :=
  rfl
#align smooth_bump_function.update_r_r SmoothBumpFunction.update_r_r

@[simp]
theorem support_update_r {r : ℝ} (hr : r ∈ Ioo 0 f.r) : support (f.updateR r hr) = support f := by
  simp only [support_eq_inter_preimage, update_r_R]
#align smooth_bump_function.support_update_r SmoothBumpFunction.support_update_r

instance : Inhabited (SmoothBumpFunction I c) :=
  Classical.inhabited_of_nonempty nhds_within_range_basis.Nonempty

variable [T2Space M]

theorem is_closed_symm_image_closed_ball :
    IsClosed ((extChartAt I c).symm '' (closedBall (extChartAt I c c) f.r ∩ range I)) :=
  f.compact_symm_image_closed_ball.IsClosed
#align
  smooth_bump_function.is_closed_symm_image_closed_ball SmoothBumpFunction.is_closed_symm_image_closed_ball

theorem tsupport_subset_symm_image_closed_ball :
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.r ∩ range I) :=
  by
  rw [tsupport, support_eq_symm_image]
  exact
    closure_minimal (image_subset _ <| inter_subset_inter_left _ ball_subset_closed_ball)
      f.is_closed_symm_image_closed_ball
#align
  smooth_bump_function.tsupport_subset_symm_image_closed_ball SmoothBumpFunction.tsupport_subset_symm_image_closed_ball

theorem tsupport_subset_ext_chart_at_source : tsupport f ⊆ (extChartAt I c).source :=
  calc
    tsupport f ⊆ (extChartAt I c).symm '' (closedBall (extChartAt I c c) f.r ∩ range I) :=
      f.tsupport_subset_symm_image_closed_ball
    _ ⊆ (extChartAt I c).symm '' (extChartAt I c).target := image_subset _ f.closed_ball_subset
    _ = (extChartAt I c).source := (extChartAt I c).symm_image_target_eq_source
    
#align
  smooth_bump_function.tsupport_subset_ext_chart_at_source SmoothBumpFunction.tsupport_subset_ext_chart_at_source

theorem tsupport_subset_chart_at_source : tsupport f ⊆ (chartAt H c).source := by
  simpa only [ext_chart_at_source] using f.tsupport_subset_ext_chart_at_source
#align
  smooth_bump_function.tsupport_subset_chart_at_source SmoothBumpFunction.tsupport_subset_chart_at_source

protected theorem has_compact_support : HasCompactSupport f :=
  is_compact_of_is_closed_subset f.compact_symm_image_closed_ball is_closed_closure
    f.tsupport_subset_symm_image_closed_ball
#align smooth_bump_function.has_compact_support SmoothBumpFunction.has_compact_support

variable (I c)

/-- The closures of supports of smooth bump functions centered at `c` form a basis of `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighborhood of `c`
includes `tsupport f` for some `f : smooth_bump_function I c`. -/
theorem nhds_basis_tsupport :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => True) fun f => tsupport f :=
  by
  have :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => True) fun f =>
      (extChartAt I c).symm '' (closed_ball (extChartAt I c c) f.r ∩ range I) :=
    by
    rw [← map_ext_chart_at_symm_nhds_within_range I c]
    exact nhds_within_range_basis.map _
  refine'
    this.to_has_basis' (fun f hf => ⟨f, trivial, f.tsupport_subset_symm_image_closed_ball⟩)
      fun f _ => f.tsupport_mem_nhds
#align smooth_bump_function.nhds_basis_tsupport SmoothBumpFunction.nhds_basis_tsupport

variable {c}

/-- Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : smooth_bump_function I c` such that
`tsupport f ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some `f :
smooth_bump_function I c` such that `tsupport f ⊆ s`. -/
theorem nhds_basis_support {s : Set M} (hs : s ∈ 𝓝 c) :
    (𝓝 c).HasBasis (fun f : SmoothBumpFunction I c => tsupport f ⊆ s) fun f => support f :=
  ((nhds_basis_tsupport I c).restrict_subset hs).to_has_basis'
    (fun f hf => ⟨f, hf.2, subset_closure⟩) fun f hf => f.support_mem_nhds
#align smooth_bump_function.nhds_basis_support SmoothBumpFunction.nhds_basis_support

variable [SmoothManifoldWithCorners I M] {I}

/-- A smooth bump function is infinitely smooth. -/
protected theorem smooth : Smooth I 𝓘(ℝ) f :=
  by
  refine' cont_mdiff_of_support fun x hx => _
  have : x ∈ (chart_at H c).source := f.tsupport_subset_chart_at_source hx
  refine'
    ContMdiffAt.congr_of_eventually_eq _
      (f.eq_on_source.eventually_eq_of_mem <| IsOpen.mem_nhds (chart_at _ _).open_source this)
  exact f.to_cont_diff_bump.cont_diff_at.cont_mdiff_at.comp _ (cont_mdiff_at_ext_chart_at' this)
#align smooth_bump_function.smooth SmoothBumpFunction.smooth

protected theorem smooth_at {x} : SmoothAt I 𝓘(ℝ) f x :=
  f.Smooth.SmoothAt
#align smooth_bump_function.smooth_at SmoothBumpFunction.smooth_at

protected theorem continuous : Continuous f :=
  f.Smooth.Continuous
#align smooth_bump_function.continuous SmoothBumpFunction.continuous

/-- If `f : smooth_bump_function I c` is a smooth bump function and `g : M → G` is a function smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold. -/
theorem smooth_smul {G} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : M → G}
    (hg : SmoothOn I 𝓘(ℝ, G) g (chartAt H c).source) : Smooth I 𝓘(ℝ, G) fun x => f x • g x :=
  by
  apply cont_mdiff_of_support fun x hx => _
  have : x ∈ (chart_at H c).source
  calc
    x ∈ tsupport fun x => f x • g x := hx
    _ ⊆ tsupport f := tsupport_smul_subset_left _ _
    _ ⊆ (chart_at _ c).source := f.tsupport_subset_chart_at_source
    
  exact
    f.smooth_at.smul ((hg _ this).ContMdiffAt <| IsOpen.mem_nhds (chart_at _ _).open_source this)
#align smooth_bump_function.smooth_smul SmoothBumpFunction.smooth_smul

end SmoothBumpFunction

