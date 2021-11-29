import Mathbin.Analysis.Calculus.SpecificFunctions 
import Mathbin.Geometry.Manifold.TimesContMdiff

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

variable{E :
    Type
      uE}[NormedGroup
      E][NormedSpace ℝ
      E][FiniteDimensional ℝ
      E]{H :
    Type
      uH}[TopologicalSpace
      H](I : ModelWithCorners ℝ E H){M : Type uM}[TopologicalSpace M][ChartedSpace H M][SmoothManifoldWithCorners I M]

open Function Filter FiniteDimensional Set

open_locale TopologicalSpace Manifold Classical Filter BigOperators

noncomputable theory

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
structure SmoothBumpFunction(c : M) extends TimesContDiffBump (extChartAt I c c) where 
  closed_ball_subset : Euclidean.ClosedBall (extChartAt I c c) R ∩ range I ⊆ (extChartAt I c).Target

variable{M}

namespace SmoothBumpFunction

open Euclidean renaming dist→eudist

variable{c : M}(f : SmoothBumpFunction I c){x : M}{I}

/-- The function defined by `f : smooth_bump_function c`. Use automatic coercion to function
instead. -/
def to_fun : M → ℝ :=
  indicator (chart_at H c).Source (f.to_times_cont_diff_bump ∘ extChartAt I c)

instance  : CoeFun (SmoothBumpFunction I c) fun _ => M → ℝ :=
  ⟨to_fun⟩

theorem coe_def : «expr⇑ » f = indicator (chart_at H c).Source (f.to_times_cont_diff_bump ∘ extChartAt I c) :=
  rfl

theorem R_pos : 0 < f.R :=
  f.to_times_cont_diff_bump.R_pos

theorem ball_subset : ball (extChartAt I c c) f.R ∩ range I ⊆ (extChartAt I c).Target :=
  subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) f.closed_ball_subset

theorem eq_on_source : eq_on f (f.to_times_cont_diff_bump ∘ extChartAt I c) (chart_at H c).Source :=
  eq_on_indicator

theorem eventually_eq_of_mem_source (hx : x ∈ (chart_at H c).Source) :
  f =ᶠ[𝓝 x] (f.to_times_cont_diff_bump ∘ extChartAt I c) :=
  f.eq_on_source.eventually_eq_of_mem$ IsOpen.mem_nhds (chart_at H c).open_source hx

theorem one_of_dist_le (hs : x ∈ (chart_at H c).Source) (hd : eudist (extChartAt I c x) (extChartAt I c c) ≤ f.r) :
  f x = 1 :=
  by 
    simp only [f.eq_on_source hs, · ∘ ·, f.to_times_cont_diff_bump.one_of_mem_closed_ball hd]

theorem support_eq_inter_preimage :
  support f = (chart_at H c).Source ∩ extChartAt I c ⁻¹' ball (extChartAt I c c) f.R :=
  by 
    rw [coe_def, support_indicator, · ∘ ·, support_comp_eq_preimage, ←ext_chart_at_source I,
      ←(extChartAt I c).symm_image_target_inter_eq', ←(extChartAt I c).symm_image_target_inter_eq',
      f.to_times_cont_diff_bump.support_eq]

theorem open_support : IsOpen (support f) :=
  by 
    rw [support_eq_inter_preimage]
    exact ext_chart_preimage_open_of_open I c is_open_ball

theorem support_eq_symm_image : support f = (extChartAt I c).symm '' (ball (extChartAt I c c) f.R ∩ range I) :=
  by 
    rw [f.support_eq_inter_preimage, ←ext_chart_at_source I, ←(extChartAt I c).symm_image_target_inter_eq', inter_comm]
    congr 1 with y 
    exact
      And.congr_right_iff.2 fun hy => ⟨fun h => ext_chart_at_target_subset_range _ _ h, fun h => f.ball_subset ⟨hy, h⟩⟩

theorem support_subset_source : support f ⊆ (chart_at H c).Source :=
  by 
    rw [f.support_eq_inter_preimage, ←ext_chart_at_source I]
    exact inter_subset_left _ _

theorem image_eq_inter_preimage_of_subset_support {s : Set M} (hs : s ⊆ support f) :
  extChartAt I c '' s = closed_ball (extChartAt I c c) f.R ∩ range I ∩ (extChartAt I c).symm ⁻¹' s :=
  by 
    rw [support_eq_inter_preimage, subset_inter_iff, ←ext_chart_at_source I, ←image_subset_iff] at hs 
    cases' hs with hse hsf 
    apply subset.antisymm
    ·
      refine' subset_inter (subset_inter (subset.trans hsf ball_subset_closed_ball) _) _
      ·
        rintro _ ⟨x, -, rfl⟩
        exact mem_range_self _
      ·
        rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]
        exact inter_subset_right _ _
    ·
      refine' subset.trans (inter_subset_inter_left _ f.closed_ball_subset) _ 
      rw [(extChartAt I c).image_eq_target_inter_inv_preimage hse]

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_Icc : «expr ∈ »(f x, Icc (0 : exprℝ()) 1) :=
begin
  have [] [":", expr «expr ∨ »(«expr = »(f x, 0), «expr = »(f x, _))] [],
  from [expr indicator_eq_zero_or_self _ _ _],
  cases [expr this] []; rw [expr this] [],
  exacts ["[", expr left_mem_Icc.2 zero_le_one, ",", expr ⟨f.to_times_cont_diff_bump.nonneg, f.to_times_cont_diff_bump.le_one⟩, "]"]
end

theorem nonneg : 0 ≤ f x :=
  f.mem_Icc.1

theorem le_one : f x ≤ 1 :=
  f.mem_Icc.2

theorem eventually_eq_one_of_dist_lt (hs : x ∈ (chart_at H c).Source)
  (hd : eudist (extChartAt I c x) (extChartAt I c c) < f.r) : f =ᶠ[𝓝 x] 1 :=
  by 
    filterUpwards [IsOpen.mem_nhds (ext_chart_preimage_open_of_open I c is_open_ball) ⟨hs, hd⟩]
    rintro z ⟨hzs, hzd : _ < _⟩
    exact f.one_of_dist_le hzs hzd.le

theorem eventually_eq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventually_eq_one_of_dist_lt (mem_chart_source _ _)$
    by 
      rw [Euclidean.dist, dist_self]
      exact f.r_pos

@[simp]
theorem eq_one : f c = 1 :=
  f.eventually_eq_one.eq_of_nhds

theorem support_mem_nhds : support f ∈ 𝓝 c :=
  f.eventually_eq_one.mono$
    fun x hx =>
      by 
        rw [hx]
        exact one_ne_zero

theorem closure_support_mem_nhds : Closure (support f) ∈ 𝓝 c :=
  mem_of_superset f.support_mem_nhds subset_closure

theorem c_mem_support : c ∈ support f :=
  mem_of_mem_nhds f.support_mem_nhds

theorem nonempty_support : (support f).Nonempty :=
  ⟨c, f.c_mem_support⟩

theorem compact_symm_image_closed_ball :
  IsCompact ((extChartAt I c).symm '' (closed_ball (extChartAt I c c) f.R ∩ range I)) :=
  (is_compact_closed_ball.inter_right I.closed_range).image_of_continuous_on$
    (ext_chart_at_continuous_on_symm _ _).mono f.closed_ball_subset

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a smooth bump function `f : smooth_bump_function I c`, the closed ball of radius `f.R` is
known to include the support of `f`. These closed balls (in the model normed space `E`) intersected
with `set.range I` form a basis of `𝓝[range I] (ext_chart_at I c c)`. -/
theorem nhds_within_range_basis : «expr𝓝[ ] »(range I, ext_chart_at I c c).has_basis (λ
 f : smooth_bump_function I c, true) (λ f, «expr ∩ »(closed_ball (ext_chart_at I c c) f.R, range I)) :=
begin
  refine [expr ((nhds_within_has_basis euclidean.nhds_basis_closed_ball _).restrict_subset (ext_chart_at_target_mem_nhds_within _ _)).to_has_basis' _ _],
  { rintro [ident R, "⟨", ident hR0, ",", ident hsub, "⟩"],
    exact [expr ⟨⟨⟨⟨«expr / »(R, 2), R, half_pos hR0, half_lt_self hR0⟩⟩, hsub⟩, trivial, subset.rfl⟩] },
  { exact [expr λ
     f _, inter_mem «expr $ »(mem_nhds_within_of_mem_nhds, closed_ball_mem_nhds f.R_pos) self_mem_nhds_within] }
end

theorem closed_image_of_closed {s : Set M} (hsc : IsClosed s) (hs : s ⊆ support f) : IsClosed (extChartAt I c '' s) :=
  by 
    rw [f.image_eq_inter_preimage_of_subset_support hs]
    refine' ContinuousOn.preimage_closed_of_closed ((ext_chart_continuous_on_symm _ _).mono f.closed_ball_subset) _ hsc 
    exact IsClosed.inter is_closed_closed_ball I.closed_range

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a smooth bump function and `s` closed subset of the support of `f` (i.e., of the open
ball of radius `f.R`), then there exists `0 < r < f.R` such that `s` is a subset of the open ball of
radius `r`. Formally, `s ⊆ e.source ∩ e ⁻¹' (ball (e c) r)`, where `e = ext_chart_at I c`. -/
theorem exists_r_pos_lt_subset_ball
{s : set M}
(hsc : is_closed s)
(hs : «expr ⊆ »(s, support f)) : «expr∃ , »((r)
 (hr : «expr ∈ »(r, Ioo 0 f.R)), «expr ⊆ »(s, «expr ∩ »((chart_at H c).source, «expr ⁻¹' »(ext_chart_at I c, ball (ext_chart_at I c c) r)))) :=
begin
  set [] [ident e] [] [":="] [expr ext_chart_at I c] [],
  have [] [":", expr is_closed «expr '' »(e, s)] [":=", expr f.closed_image_of_closed hsc hs],
  rw ["[", expr support_eq_inter_preimage, ",", expr subset_inter_iff, ",", "<-", expr image_subset_iff, "]"] ["at", ident hs],
  rcases [expr euclidean.exists_pos_lt_subset_ball f.R_pos this hs.2, "with", "⟨", ident r, ",", ident hrR, ",", ident hr, "⟩"],
  exact [expr ⟨r, hrR, subset_inter hs.1 (image_subset_iff.1 hr)⟩]
end

/-- Replace `r` with another value in the interval `(0, f.R)`. -/
def update_r (r : ℝ) (hr : r ∈ Ioo 0 f.R) : SmoothBumpFunction I c :=
  ⟨⟨⟨r, f.R, hr.1, hr.2⟩⟩, f.closed_ball_subset⟩

@[simp]
theorem update_r_R {r : ℝ} (hr : r ∈ Ioo 0 f.R) : (f.update_r r hr).r = f.R :=
  rfl

@[simp]
theorem update_r_r {r : ℝ} (hr : r ∈ Ioo 0 f.R) : (f.update_r r hr).R = r :=
  rfl

@[simp]
theorem support_update_r {r : ℝ} (hr : r ∈ Ioo 0 f.R) : support (f.update_r r hr) = support f :=
  by 
    simp only [support_eq_inter_preimage, update_r_R]

instance  : Inhabited (SmoothBumpFunction I c) :=
  Classical.inhabitedOfNonempty nhds_within_range_basis.Nonempty

variable[T2Space M]

theorem closed_symm_image_closed_ball :
  IsClosed ((extChartAt I c).symm '' (closed_ball (extChartAt I c c) f.R ∩ range I)) :=
  f.compact_symm_image_closed_ball.is_closed

theorem closure_support_subset_symm_image_closed_ball :
  Closure (support f) ⊆ (extChartAt I c).symm '' (closed_ball (extChartAt I c c) f.R ∩ range I) :=
  by 
    rw [support_eq_symm_image]
    exact
      closure_minimal (image_subset _$ inter_subset_inter_left _ ball_subset_closed_ball)
        f.closed_symm_image_closed_ball

theorem closure_support_subset_ext_chart_at_source : Closure (support f) ⊆ (extChartAt I c).Source :=
  calc Closure (support f) ⊆ (extChartAt I c).symm '' (closed_ball (extChartAt I c c) f.R ∩ range I) :=
    f.closure_support_subset_symm_image_closed_ball 
    _ ⊆ (extChartAt I c).symm '' (extChartAt I c).Target := image_subset _ f.closed_ball_subset 
    _ = (extChartAt I c).Source := (extChartAt I c).symm_image_target_eq_source
    

theorem closure_support_subset_chart_at_source : Closure (support f) ⊆ (chart_at H c).Source :=
  by 
    simpa only [ext_chart_at_source] using f.closure_support_subset_ext_chart_at_source

theorem compact_closure_support : IsCompact (Closure$ support f) :=
  compact_of_is_closed_subset f.compact_symm_image_closed_ball is_closed_closure
    f.closure_support_subset_symm_image_closed_ball

variable(I c)

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The closures of supports of smooth bump functions centered at `c` form a basis of `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighborhood of `c`
includes `closure (support f)` for some `f : smooth_bump_function I c`. -/
theorem nhds_basis_closure_support : (expr𝓝() c).has_basis (λ
 f : smooth_bump_function I c, true) (λ f, «expr $ »(closure, support f)) :=
begin
  have [] [":", expr (expr𝓝() c).has_basis (λ
    f : smooth_bump_function I c, true) (λ
    f, «expr '' »((ext_chart_at I c).symm, «expr ∩ »(closed_ball (ext_chart_at I c c) f.R, range I)))] [],
  { rw ["[", "<-", expr ext_chart_at_symm_map_nhds_within_range I c, "]"] [],
    exact [expr nhds_within_range_basis.map _] },
  refine [expr this.to_has_basis' (λ
    f hf, ⟨f, trivial, f.closure_support_subset_symm_image_closed_ball⟩) (λ f _, f.closure_support_mem_nhds)]
end

variable{c}

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : smooth_bump_function I c` such that
`closure (support f) ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some `f :
smooth_bump_function I c` such that `closure (support f) ⊆ s`. -/
theorem nhds_basis_support
{s : set M}
(hs : «expr ∈ »(s, expr𝓝() c)) : (expr𝓝() c).has_basis (λ
 f : smooth_bump_function I c, «expr ⊆ »(closure (support f), s)) (λ f, support f) :=
((nhds_basis_closure_support I c).restrict_subset hs).to_has_basis' (λ
 f hf, ⟨f, hf.2, subset_closure⟩) (λ f hf, f.support_mem_nhds)

variable[SmoothManifoldWithCorners I M]{I}

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A smooth bump function is infinitely smooth. -/ protected theorem smooth : smooth I «expr𝓘( )»(exprℝ()) f :=
begin
  refine [expr times_cont_mdiff_of_support (λ x hx, _)],
  have [] [":", expr «expr ∈ »(x, (chart_at H c).source)] [":=", expr f.closure_support_subset_chart_at_source hx],
  refine [expr times_cont_mdiff_at.congr_of_eventually_eq _ «expr $ »(f.eq_on_source.eventually_eq_of_mem, is_open.mem_nhds (chart_at _ _).open_source this)],
  exact [expr f.to_times_cont_diff_bump.times_cont_diff_at.times_cont_mdiff_at.comp _ (times_cont_mdiff_at_ext_chart_at' this)]
end

protected theorem SmoothAt {x} : SmoothAt I 𝓘(ℝ) f x :=
  f.smooth.smooth_at

protected theorem Continuous : Continuous f :=
  f.smooth.continuous

-- error in Geometry.Manifold.BumpFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : smooth_bump_function I c` is a smooth bump function and `g : M → G` is a function smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold. -/
theorem smooth_smul
{G}
[normed_group G]
[normed_space exprℝ() G]
{g : M → G}
(hg : smooth_on I «expr𝓘( , )»(exprℝ(), G) g (chart_at H c).source) : smooth I «expr𝓘( , )»(exprℝ(), G) (λ
 x, «expr • »(f x, g x)) :=
begin
  apply [expr times_cont_mdiff_of_support (λ x hx, _)],
  have [] [":", expr «expr ∈ »(x, (chart_at H c).source)] [],
  calc
    «expr ∈ »(x, closure (support (λ x, «expr • »(f x, g x)))) : hx
    «expr ⊆ »(..., closure (support f)) : closure_mono (support_smul_subset_left _ _)
    «expr ⊆ »(..., (chart_at _ c).source) : f.closure_support_subset_chart_at_source,
  exact [expr f.smooth_at.smul «expr $ »((hg _ this).times_cont_mdiff_at, is_open.mem_nhds (chart_at _ _).open_source this)]
end

end SmoothBumpFunction

