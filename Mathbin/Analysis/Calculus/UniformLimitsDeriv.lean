/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import Mathbin.Analysis.Calculus.MeanValue
import Mathbin.Analysis.NormedSpace.IsROrC
import Mathbin.Order.Filter.Curry

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_locally_uniformly_at`.

## Main statements

* `uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv`: If
    1. `f : ℕ → E → G` is a sequence of functions which have derivatives
       `f' : ℕ → E → (E →L[𝕜] G)` on a neighborhood of `x`,
    2. the functions `f` converge at `x`, and
    3. the derivatives `f'` converge uniformly on a neighborhood of `x`,
  then the `f` converge _uniformly_ on a neighborhood of `x`
* `has_fderiv_at_of_tendsto_uniformly_on_filter` : Suppose (1), (2), and (3) above are true. Let
  `g` (resp. `g'`) be the limiting function of the `f` (resp. `g'`). Then `f'` is the derivative of
  `g` on a neighborhood of `x`
* `has_fderiv_at_of_tendsto_uniformly_on`: An often-easier-to-use version of the above theorem when
  *all* the derivatives exist and functions converge on a common open set and the derivatives
  converge uniformly there.

Each of the above statements also has variations that support `deriv` instead of `fderiv`.

## Implementation notes

Our technique for proving the main result is the famous "`ε / 3` proof." In words, you can find it
explained, for instance, at [this StackExchange post](https://math.stackexchange.com/questions/214218/uniform-convergence-of-derivatives-tao-14-2-7).
The subtlety is that we want to prove that the difference quotients of the `g` converge to the `g'`.
That is, we want to prove something like:

```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

To do so, we will need to introduce a pair of quantifers

```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

So how do we write this in terms of filters? Well, the initial definition of the derivative is

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

There are two ways we might introduce `n`. We could do:

```lean
∀ᶠ (n : ℕ) in at_top, tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∃ N, ∀ n ≥ N, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`,
which _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is _not_ equivalent to it. On the other hand, we might
try

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (at_top ×ᶠ 𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifer order `∀ ε > 0, ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ y ∈ B_δ(x)`, which
again _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is not equivalent to it.

So to get the quantifier order we want, we need to introduce a new filter construction, which we
call a "curried filter"

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (at_top.curry (𝓝 x)) (𝓝 0)
```

Then the above implications are `filter.tendsto.curry` and
`filter.tendsto.mono_left filter.curry_le_prod`. We will use both of these deductions as part of
our proof.

We note that if you loosen the assumptions of the main theorem then the proof becomes quite a bit
easier. In particular, if you assume there is a common neighborhood `s` where all of the three
assumptions of `has_fderiv_at_of_tendsto_uniformly_on_filter` hold and that the `f'` are
continuous, then you can avoid the mean value theorem and much of the work around curried filters.

## Tags

uniform convergence, limits of derivatives
-/


open Filter

open uniformity Filter TopologicalSpace

section LimitsOfDerivatives

variable {ι : Type _} {l : Filter ι} [NeBot l] {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {𝕜 : Type _}
  [IsROrC 𝕜] [NormedSpace 𝕜 E] {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G} {g : E → G}
  {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}

/-- If a sequence of functions real or complex functions are eventually differentiable on a
neighborhood of `x`, they converge pointwise _at_ `x`, and their derivatives
converge uniformly in a neighborhood of `x`, then the functions form a uniform Cauchy sequence
in a neighborhood of `x`. -/
theorem uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ᶠ 𝓝 x, HasFderivAt (f n.1) (f' n.1 n.2) n.2) (hfg : Tendsto (fun n => f n x) l (𝓝 (g x))) :
    UniformCauchySeqOnFilter f l (𝓝 x) := by
  rw [SeminormedAddGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero] at hf'⊢
  suffices
    TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0 (l ×ᶠ l) (𝓝 x) ∧
      TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 x - f n.2 x) 0 (l ×ᶠ l) (𝓝 x)
    by
    have := this.1.add this.2
    rw [add_zero] at this
    exact this.congr (by simp)
  constructor
  · -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw [Metric.tendsto_uniformly_on_filter_iff] at hf'⊢
    intro ε hε
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).And this)
    obtain ⟨R, hR, hR'⟩ := metric.nhds_basis_ball.eventually_iff.mp d
    let r := min 1 R
    have hr : 0 < r := by simp [hR]
    have hr' : ∀ ⦃y : E⦄, y ∈ Metric.Ball x r → c y := fun y hy =>
      hR' (lt_of_lt_of_le (metric.mem_ball.mp hy) (min_le_right _ _))
    have hxy : ∀ y : E, y ∈ Metric.Ball x r → ∥y - x∥ < 1 := by
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hxyε : ∀ y : E, y ∈ Metric.Ball x r → ε * ∥y - x∥ < ε := by
      intro y hy
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy)
    -- With a small ball in hand, apply the mean value theorem
    refine'
      eventually_prod_iff.mpr
        ⟨_, b, fun e : E => Metric.Ball x r e, eventually_mem_set.mpr (metric.nhds_basis_ball.mem_of_mem hr),
          fun n hn y hy => _⟩
    simp only [Pi.zero_apply, dist_zero_left] at e⊢
    refine' lt_of_le_of_lt _ (hxyε y hy)
    exact
      Convex.norm_image_sub_le_of_norm_has_fderiv_within_le
        (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).HasFderivWithinAt) (fun y hy => (e hn (hr' hy)).1.le)
        (convex_ball x r) (Metric.mem_ball_self hr) hy
    
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine' metric.tendsto_uniformly_on_filter_iff.mpr fun ε hε => _
    obtain ⟨t, ht, ht'⟩ := (metric.cauchy_iff.mp hfg.cauchy_map).2 ε hε
    exact
      eventually_prod_iff.mpr
        ⟨fun n : ι × ι => f n.1 x ∈ t ∧ f n.2 x ∈ t,
          eventually_prod_iff.mpr ⟨_, ht, _, ht, fun n hn n' hn' => ⟨hn, hn'⟩⟩, fun y => True, by simp, fun n hn y hy =>
          by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2⟩
    

/-- A variant of the second fundamental theorem of calculus (FTC-2): If a sequence of functions
between real or complex normed spaces are differentiable on a ball centered at `x`, they
converge pointwise _at_ `x`, and their derivatives converge uniformly on the ball, then the
functions form a uniform Cauchy sequence on the ball.

NOTE: The fact that we work on a ball is typically all that is necessary to work with power series
and Dirichlet series (our primary use case). However, this can be generalized by replacing the ball
with any connected, bounded, open set and replacing uniform convergence with local uniform
convergence.
-/
theorem uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_fderiv {r : ℝ} (hr : 0 < r)
    (hf' : UniformCauchySeqOn f' l (Metric.Ball x r))
    (hf : ∀ n : ι, ∀ y : E, y ∈ Metric.Ball x r → HasFderivAt (f n) (f' n y) y)
    (hfg : Tendsto (fun n => f n x) l (𝓝 (g x))) : UniformCauchySeqOn f l (Metric.Ball x r) := by
  rw [SeminormedAddGroup.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero] at hf'⊢
  suffices
    TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0 (l ×ᶠ l)
        (Metric.Ball x r) ∧
      TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 x - f n.2 x) 0 (l ×ᶠ l) (Metric.Ball x r)
    by
    have := this.1.add this.2
    rw [add_zero] at this
    refine' this.congr _
    apply eventually_of_forall
    intro n z hz
    simp
  constructor
  · -- This inequality follows from the mean value theorem
    rw [Metric.tendsto_uniformly_on_iff] at hf'⊢
    intro ε hε
    obtain ⟨q, hqpos, hq⟩ : ∃ q : ℝ, 0 < q ∧ q * r < ε := by
      simp_rw [mul_comm]
      exact exists_pos_mul_lt hε.lt r
    apply (hf' q hqpos.gt).mono
    intro n hn y hy
    simp_rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg] at hn⊢
    have mvt :=
      Convex.norm_image_sub_le_of_norm_has_fderiv_within_le
        (fun z hz => ((hf n.1 z hz).sub (hf n.2 z hz)).HasFderivWithinAt) (fun z hz => (hn z hz).le) (convex_ball x r)
        (Metric.mem_ball_self hr) hy
    refine' lt_of_le_of_lt mvt _
    have : q * ∥y - x∥ < q * r :=
      mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using metric.mem_ball.mp hy) (norm_nonneg _) hqpos
    exact this.trans hq
    
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine' metric.tendsto_uniformly_on_iff.mpr fun ε hε => _
    obtain ⟨t, ht, ht'⟩ := (metric.cauchy_iff.mp hfg.cauchy_map).2 ε hε
    rw [eventually_prod_iff]
    refine' ⟨fun n => f n x ∈ t, ht, fun n => f n x ∈ t, ht, _⟩
    intro n hn n' hn' z hz
    rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, ← dist_eq_norm]
    exact ht' _ hn _ hn'
    

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
theorem difference_quotients_converge_uniformly (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ᶠ 𝓝 x, HasFderivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y : E in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) :
    TendstoUniformlyOnFilter (fun n : ι => fun y : E => (∥y - x∥⁻¹ : 𝕜) • (f n y - f n x))
      (fun y : E => (∥y - x∥⁻¹ : 𝕜) • (g y - g x)) l (𝓝 x) :=
  by
  refine'
    UniformCauchySeqOnFilter.tendsto_uniformly_on_filter_of_tendsto _
      ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy => (hy.1.sub hy.2).const_smul _)
  rw [SeminormedAddGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero]
  rw [Metric.tendsto_uniformly_on_filter_iff]
  have hfg' := hf'.uniform_cauchy_seq_on_filter
  rw [SeminormedAddGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero] at hfg'
  rw [Metric.tendsto_uniformly_on_filter_iff] at hfg'
  intro ε hε
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε
  specialize hfg' (q : ℝ) (by simp [hqpos])
  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this)
  obtain ⟨r, hr, hr'⟩ := metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine'
    ⟨_, b, fun e : E => Metric.Ball x r e, eventually_mem_set.mpr (metric.nhds_basis_ball.mem_of_mem hr),
      fun n hn y hy => _⟩
  simp only [Pi.zero_apply, dist_zero_left]
  rw [← smul_sub, norm_smul, norm_inv, IsROrC.norm_coe_norm]
  refine' lt_of_le_of_lt _ hqε
  by_cases hyz':x = y
  · simp [hyz', hqpos.le]
    
  have hyz : 0 < ∥y - x∥ := by
    rw [norm_pos_iff]
    intro hy'
    exact hyz' (eq_of_sub_eq_zero hy').symm
  rw [inv_mul_le_iff hyz, mul_comm, sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left] at e
  refine'
    Convex.norm_image_sub_le_of_norm_has_fderiv_within_le
      (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).HasFderivWithinAt) (fun y hy => (e hn (hr' hy)).1.le)
      (convex_ball x r) (Metric.mem_ball_self hr) hy

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`!
  * `hf`: For all `(y, n)` with `y` sufficiently close to `x` and `n` sufficiently large, `f' n` is
    the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x` -/
theorem hasFderivAtOfTendstoUniformlyOnFilter (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ᶠ 𝓝 x, HasFderivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasFderivAt g (g' x) x := by
  -- The proof strategy follows several steps:
  --   1. The quantifiers in the definition of the derivative are
  --      `∀ ε > 0, ∃δ > 0, ∀y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  --      `∀ ε > 0, ∃N, ∀n ≥ N, ∃δ > 0, ∀y ∈ B_δ(x)` which will allow us to introduce the `f(') n`
  --   2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  --      the quantifiers using the uniform convergence assumption
  rw [has_fderiv_at_iff_tendsto]
  -- Introduce extra quantifier via curried filters
  suffices tendsto (fun y : ι × E => ∥y.2 - x∥⁻¹ * ∥g y.2 - g x - (g' x) (y.2 - x)∥) (l.curry (𝓝 x)) (𝓝 0) by
    rw [Metric.tendsto_nhds] at this⊢
    intro ε hε
    specialize this ε hε
    rw [eventually_curry_iff] at this
    simp only at this
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const])
  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
-- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
--   * The difference functions of the `f n` converge *uniformly* to the difference functions
--     of the `g n`
--   * The `f' n` are the derivatives of the `f n`
--   * The `f' n` converge to `g'` at `x`
conv =>
  congr
  ext
  rw [← norm_norm, ← norm_inv, ← @IsROrC.norm_of_real 𝕜 _ _, IsROrC.of_real_inv, ← norm_smul]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have :
    (fun a : ι × E => (∥a.2 - x∥⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
      ((fun a : ι × E => (∥a.2 - x∥⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) + fun a : ι × E =>
          (∥a.2 - x∥⁻¹ : 𝕜) • (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x))) +
        fun a : ι × E => (∥a.2 - x∥⁻¹ : 𝕜) • (f' a.1 x - g' x) (a.2 - x) :=
    by
    ext
    simp only [Pi.add_apply]
    rw [← smul_add, ← smul_add]
    congr
    simp only [map_sub, sub_add_sub_cancel, ContinuousLinearMap.coe_sub', Pi.sub_apply]
  simp_rw [this]
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0)
  simp only [add_zero]
  rw [this]
  refine' tendsto.add (tendsto.add _ _) _
  simp only
  · have := difference_quotients_converge_uniformly hf' hf hfg
    rw [Metric.tendsto_uniformly_on_filter_iff] at this
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((this ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn⊢
    rw [← smul_sub] at hn
    rwa [sub_zero]
    
  · -- (Almost) the definition of the derivatives
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine' hf.curry.mono fun n hn => _
    have := hn.self_of_nhds
    rw [has_fderiv_at_iff_tendsto, Metric.tendsto_nhds] at this
    refine' (this ε hε).mono fun y hy => _
    rw [dist_eq_norm] at hy⊢
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy⊢
    rw [norm_smul, norm_inv, IsROrC.norm_coe_norm]
    exact hy
    
  · -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine' tendsto.mono_left _ curry_le_prod
    have h1 : tendsto (fun n : ι × E => g' n.2 - f' n.1 n.2) (l ×ᶠ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendsto_uniformly_on_filter_iff] at hf'
      exact metric.tendsto_nhds.mpr fun ε hε => by simpa using hf' ε hε
    have h2 : tendsto (fun n : ι => g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1⊢
      exact fun ε hε => (h1 ε hε).curry.mono fun n hn => hn.self_of_nhds
    have := tendsto_fst.comp (h2.prod_map tendsto_id)
    refine' squeeze_zero_norm _ (tendsto_zero_iff_norm_tendsto_zero.mp this)
    intro n
    simp_rw [norm_smul, norm_inv, IsROrC.norm_coe_norm]
    by_cases hx:x = n.2
    · simp [hx]
      
    have hnx : 0 < ∥n.2 - x∥ := by
      rw [norm_pos_iff]
      intro hx'
      exact hx (eq_of_sub_eq_zero hx').symm
    rw [inv_mul_le_iff hnx, mul_comm]
    simp only [Function.comp_app, prod_map]
    rw [norm_sub_rev]
    exact (f' n.1 x - g' x).le_op_norm (n.2 - x)
    

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit on an open set containing `x`. -/
theorem hasFderivAtOfTendstoUniformlyOn {s : Set E} (hs : IsOpen s) (hf' : TendstoUniformlyOn f' g' l s)
    (hf : ∀ n : ι, ∀ x : E, x ∈ s → HasFderivAt (f n) (f' n x) x)
    (hfg : ∀ x : E, x ∈ s → Tendsto (fun n => f n x) l (𝓝 (g x))) : ∀ x : E, x ∈ s → HasFderivAt g (g' x) x := by
  intro x hx
  have hf : ∀ᶠ n : ι × E in l ×ᶠ 𝓝 x, HasFderivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_prod_iff.mpr
      ⟨fun y => True, by simp, fun y => y ∈ s, eventually_mem_set.mpr (mem_nhds_iff.mpr ⟨s, rfl.subset, hs, hx⟩),
        fun n hn y hy => hf n y hy⟩
  have hfg : ∀ᶠ y in 𝓝 x, tendsto (fun n => f n y) l (𝓝 (g y)) :=
    eventually_iff.mpr (mem_nhds_iff.mpr ⟨s, set.subset_def.mpr hfg, hs, hx⟩)
  have hfg' :=
    hf'.tendsto_uniformly_on_filter.mono_right
      (calc
        𝓝 x = 𝓝[s] x := (hs.nhds_within_eq hx).symm
        _ ≤ 𝓟 s := by simp only [nhdsWithin, inf_le_right]
        )
  exact hasFderivAtOfTendstoUniformlyOnFilter hfg' hf hfg

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit. -/
theorem hasFderivAtOfTendstoUniformly (hf' : TendstoUniformly f' g' l)
    (hf : ∀ n : ι, ∀ x : E, HasFderivAt (f n) (f' n x) x) (hfg : ∀ x : E, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    ∀ x : E, HasFderivAt g (g' x) x := by
  intro x
  have hf : ∀ n : ι, ∀ x : E, x ∈ Set.Univ → HasFderivAt (f n) (f' n x) x := by simp [hf]
  have hfg : ∀ x : E, x ∈ Set.Univ → tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.Univ := by rwa [tendsto_uniformly_on_univ]
  refine' hasFderivAtOfTendstoUniformlyOn is_open_univ hf' hf hfg x (Set.mem_univ x)

end LimitsOfDerivatives

section deriv

/-! ### `deriv` versions of above theorems

In this section, we provide `deriv` equivalents of the `fderiv` lemmas in the previous section.
The protected function `promote_deriv` provides the translation between derivatives and Fréchet
derivatives
-/


variable {ι : Type _} {l : Filter ι} {𝕜 : Type _} [IsROrC 𝕜] {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : ι → 𝕜 → G} {g : 𝕜 → G} {f' : ι → 𝕜 → G} {g' : 𝕜 → G} {x : 𝕜}

/-- If our derivatives converge uniformly, then the Fréchet derivatives converge uniformly -/
theorem UniformCauchySeqOnFilter.one_smul_right {l' : Filter 𝕜} (hf' : UniformCauchySeqOnFilter f' l l') :
    UniformCauchySeqOnFilter (fun n => fun z => (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)) l l' := by
  -- The tricky part of this proof is that operator norms are written in terms of `≤` whereas
  -- metrics are written in terms of `<`. So we need to shrink `ε` utilizing the archimedean
  -- property of `ℝ`
  rw [SeminormedAddGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero,
    Metric.tendsto_uniformly_on_filter_iff] at hf'⊢
  intro ε hε
  obtain ⟨q, hq, hq'⟩ := exists_between hε.lt
  apply (hf' q hq).mono
  intro n hn
  refine' lt_of_le_of_lt _ hq'
  simp only [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg] at hn⊢
  refine' ContinuousLinearMap.op_norm_le_bound _ hq.le _
  intro z
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.smul_right_apply,
    ContinuousLinearMap.one_apply]
  rw [← smul_sub, norm_smul, mul_comm]
  exact mul_le_mul hn.le rfl.le (norm_nonneg _) hq.le

variable [NeBot l]

theorem uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_deriv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : ∀ᶠ n : ι × 𝕜 in l ×ᶠ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2) (hfg : Tendsto (fun n => f n x) l (𝓝 (g x))) :
    UniformCauchySeqOnFilter f l (𝓝 x) := by
  simp_rw [has_deriv_at_iff_has_fderiv_at] at hf
  exact uniform_cauchy_seq_on_filter_of_tendsto_uniformly_on_filter_fderiv hf'.one_smul_right hf hfg

theorem uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_deriv {r : ℝ} (hr : 0 < r)
    (hf' : UniformCauchySeqOn f' l (Metric.Ball x r))
    (hf : ∀ n : ι, ∀ y : 𝕜, y ∈ Metric.Ball x r → HasDerivAt (f n) (f' n y) y)
    (hfg : Tendsto (fun n => f n x) l (𝓝 (g x))) : UniformCauchySeqOn f l (Metric.Ball x r) := by
  simp_rw [has_deriv_at_iff_has_fderiv_at] at hf
  rw [uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter] at hf'
  have hf' : UniformCauchySeqOn (fun n => fun z => (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)) l (Metric.Ball x r) := by
    rw [uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter]
    exact hf'.one_smul_right
  exact uniform_cauchy_seq_on_ball_of_tendsto_uniformly_on_ball_fderiv hr hf' hf hfg

theorem hasDerivAtOfTendstoUniformlyOnFilter (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × 𝕜 in l ×ᶠ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasDerivAt g (g' x) x := by
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `has_fderiv_at_of_tendsto_uniformly_on_filter`
  let F' n z := (1 : 𝕜 →L[𝕜] 𝕜).smul_right (f' n z)
  let G' z := (1 : 𝕜 →L[𝕜] 𝕜).smul_right (g' z)
  simp_rw [has_deriv_at_iff_has_fderiv_at] at hf⊢
  -- Now we need to rewrite hf' in terms of continuous_linear_maps. The tricky part is that
  -- operator norms are written in terms of `≤` whereas metrics are written in terms of `<`. So we
  -- need to shrink `ε` utilizing the archimedean property of `ℝ`
  have hf' : TendstoUniformlyOnFilter F' G' l (𝓝 x) := by
    rw [Metric.tendsto_uniformly_on_filter_iff] at hf'⊢
    intro ε hε
    obtain ⟨q, hq, hq'⟩ := exists_between hε.lt
    apply (hf' q hq).mono
    intro n hn
    refine' lt_of_le_of_lt _ hq'
    simp only [F', G', dist_eq_norm] at hn⊢
    refine' ContinuousLinearMap.op_norm_le_bound _ hq.le _
    intro z
    simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.smul_right_apply,
      ContinuousLinearMap.one_apply]
    rw [← smul_sub, norm_smul, mul_comm]
    exact mul_le_mul hn.le rfl.le (norm_nonneg _) hq.le
  exact hasFderivAtOfTendstoUniformlyOnFilter hf' hf hfg

theorem hasDerivAtOfTendstoUniformlyOn {s : Set 𝕜} (hs : IsOpen s) (hf' : TendstoUniformlyOn f' g' l s)
    (hf : ∀ n : ι, ∀ x : 𝕜, x ∈ s → HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : 𝕜, x ∈ s → Tendsto (fun n => f n x) l (𝓝 (g x))) : ∀ x : 𝕜, x ∈ s → HasDerivAt g (g' x) x := by
  intro x hx
  have hsx : s ∈ 𝓝 x := mem_nhds_iff.mpr ⟨s, rfl.subset, hs, hx⟩
  rw [tendsto_uniformly_on_iff_tendsto_uniformly_on_filter] at hf'
  have hf' := hf'.mono_right (le_principal_iff.mpr hsx)
  have hfg : ∀ᶠ y in 𝓝 x, tendsto (fun n => f n y) l (𝓝 (g y)) := eventually_iff_exists_mem.mpr ⟨s, hsx, hfg⟩
  have hf : ∀ᶠ n : ι × 𝕜 in l ×ᶠ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2 := by
    rw [eventually_prod_iff]
    refine' ⟨fun y => True, by simp, fun y => y ∈ s, _, fun n hn y hy => hf n y hy⟩
    exact eventually_mem_set.mpr hsx
  exact hasDerivAtOfTendstoUniformlyOnFilter hf' hf hfg

theorem hasDerivAtOfTendstoUniformly (hf' : TendstoUniformly f' g' l)
    (hf : ∀ n : ι, ∀ x : 𝕜, HasDerivAt (f n) (f' n x) x) (hfg : ∀ x : 𝕜, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    ∀ x : 𝕜, HasDerivAt g (g' x) x := by
  intro x
  have hf : ∀ n : ι, ∀ x : 𝕜, x ∈ Set.Univ → HasDerivAt (f n) (f' n x) x := by simp [hf]
  have hfg : ∀ x : 𝕜, x ∈ Set.Univ → tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.Univ := by rwa [tendsto_uniformly_on_univ]
  exact hasDerivAtOfTendstoUniformlyOn is_open_univ hf' hf hfg x (Set.mem_univ x)

end deriv

