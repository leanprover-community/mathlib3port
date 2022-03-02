/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.FormalMultilinearSeries
import Mathbin.Data.Equiv.Fin

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ℝ≥0∞` such that `∥p n∥ * r^n` grows subexponentially, defined as
  a liminf.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_is_O`: if `∥p n∥ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.is_o_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`, `p.is_o_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `∥p n∥ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_is_O`: if `r ≠ 0` and `∥p n∥ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partial_sum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

Additionally, let `f` be a function from `E` to `F`.

* `has_fpower_series_on_ball f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `has_fpower_series_at f p x`: on some ball of center `x` with positive radius, holds
  `has_fpower_series_on_ball f p x r`.
* `analytic_at 𝕜 f x`: there exists a power series `p` such that holds
  `has_fpower_series_at f p x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `has_fpower_series_on_ball.continuous_on` and `has_fpower_series_at.continuous_at` and
  `analytic_at.continuous_at`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `formal_multilinear_series.has_fpower_series_on_ball`.
* If a function admits a power series in a ball, then it is analytic at any point `y` of this ball,
  and the power series there can be expressed in terms of the initial power series `p` as
  `p.change_origin y`. See `has_fpower_series_on_ball.change_origin`. It follows in particular that
  the set of points at which a given function is analytic is open, see `is_open_analytic_at`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/


noncomputable section

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

open_locale TopologicalSpace Classical BigOperators Nnreal Filter Ennreal

open Set Filter Asymptotics

/-! ### The radius of a formal multilinear series -/


namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 }

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ ∥pₙ∥ ∥y∥ⁿ`
converges for all `∥y∥ < r`. This implies that `Σ pₙ yⁿ` converges for all `∥y∥ < r`, but these
definitions are *not* equivalent in general. -/
def radius (p : FormalMultilinearSeries 𝕜 E F) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0 ) (C : ℝ) (hr : ∀ n, ∥p n∥ * r ^ n ≤ C), (r : ℝ≥0∞)

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0 } (h : ∀ n : ℕ, ∥p n∥ * r ^ n ≤ C) : (r : ℝ≥0∞) ≤ p.radius :=
  le_supr_of_le r <| le_supr_of_le C <| le_supr (fun _ => (r : ℝ≥0∞)) h

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nnreal (C : ℝ≥0 ) {r : ℝ≥0 } (h : ∀ n : ℕ, ∥p n∥₊ * r ^ n ≤ C) : (r : ℝ≥0∞) ≤ p.radius :=
  (p.le_radius_of_bound C) fun n => by
    exact_mod_cast h n

/-- If `∥pₙ∥ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_is_O (h : IsO (fun n => ∥p n∥ * r ^ n) (fun n => (1 : ℝ)) atTop) : ↑r ≤ p.radius :=
  (Exists.elim (is_O_one_nat_at_top_iff.1 h)) fun C hC => (p.le_radius_of_bound C) fun n => (le_abs_self _).trans (hC n)

theorem le_radius_of_eventually_le C (h : ∀ᶠ n in at_top, ∥p n∥ * r ^ n ≤ C) : ↑r ≤ p.radius :=
  p.le_radius_of_is_O <|
    IsO.of_bound C <|
      h.mono fun n hn => by
        simpa

theorem le_radius_of_summable_nnnorm (h : Summable fun n => ∥p n∥₊ * r ^ n) : ↑r ≤ p.radius :=
  (p.le_radius_of_bound_nnreal (∑' n, ∥p n∥₊ * r ^ n)) fun n => le_tsum' h _

theorem le_radius_of_summable (h : Summable fun n => ∥p n∥ * r ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm <| by
    simp only [← coe_nnnorm] at h
    exact_mod_cast h

theorem radius_eq_top_of_forall_nnreal_is_O (h : ∀ r : ℝ≥0 , IsO (fun n => ∥p n∥ * r ^ n) (fun n => (1 : ℝ)) atTop) :
    p.radius = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_is_O (h r)

theorem radius_eq_top_of_eventually_eq_zero (h : ∀ᶠ n in at_top, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_is_O fun r =>
    (is_O_zero _ _).congr'
      (h.mono fun n hn => by
        simp [hn])
      EventuallyEq.rfl

theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m + n) = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero <| mem_at_top_sets.2 ⟨n, fun k hk => tsub_add_cancel_of_le hk ▸ hn _⟩

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `∥p n∥ rⁿ = o(aⁿ)`. -/
theorem is_o_of_lt_radius (h : ↑r < p.radius) : ∃ a ∈ Ioo (0 : ℝ) 1, IsOₓ (fun n => ∥p n∥ * r ^ n) (pow a) atTop := by
  rw [(tfae_exists_lt_is_o_pow (fun n => ∥p n∥ * r ^ n) 1).out 1 4]
  simp only [radius, lt_supr_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [Ennreal.coe_lt_coe, ← Nnreal.coe_lt_coe] at rt
  have : 0 < (t : ℝ) := r.coe_nonneg.trans_lt rt
  rw [← div_lt_one this] at rt
  refine' ⟨_, rt, C, Or.inr zero_lt_one, fun n => _⟩
  calc abs (∥p n∥ * r ^ n) = ∥p n∥ * t ^ n * (r / t) ^ n := by
      field_simp [mul_right_commₓ, abs_mul, this.ne']_ ≤ C * (r / t) ^ n :=
      mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (div_nonneg r.2 t.2) _)

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ = o(1)`. -/
theorem is_o_one_of_lt_radius (h : ↑r < p.radius) : IsOₓ (fun n => ∥p n∥ * r ^ n) (fun _ => 1 : ℕ → ℝ) atTop :=
  let ⟨a, ha, hp⟩ := p.is_o_of_lt_radius h
  hp.trans <| (is_o_pow_pow_of_lt_left ha.1.le ha.2).congr (fun n => rfl) one_pow

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`,  `∥p n∥ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ∥p n∥ * r ^ n ≤ C * a ^ n := by
  rcases((tfae_exists_lt_is_o_pow (fun n => ∥p n∥ * r ^ n) 1).out 1 5).mp (p.is_o_of_lt_radius h) with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

/-- If `r ≠ 0` and `∥pₙ∥ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_is_O (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hp : IsO (fun n => ∥p n∥ * r ^ n) (pow a) atTop) : ↑r < p.radius := by
  rcases((tfae_exists_lt_is_o_pow (fun n => ∥p n∥ * r ^ n) 1).out 2 5).mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero, ← Nnreal.coe_pos] at h₀
  lift a to ℝ≥0 using ha.1.le
  have : (r : ℝ) < r / a := by
    simpa only [div_one] using (div_lt_div_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast  at this
  rw [← Ennreal.coe_lt_coe] at this
  refine' this.trans_le ((p.le_radius_of_bound C) fun n => _)
  rw [Nnreal.coe_div, div_pow, ← mul_div_assoc, div_le_iff (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : (r : ℝ≥0∞) < p.radius) :
    ∃ C > 0, ∀ n, ∥p n∥ * r ^ n ≤ C :=
  let ⟨a, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans <| mul_le_of_le_one_right hC.lt.le (pow_le_one _ ha.1.le ha.2.le)⟩

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h0 : 0 < r)
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ∥p n∥ ≤ C / r ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff (pow_pos h0 _)) (hp n)⟩

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : (r : ℝ≥0∞) < p.radius) :
    ∃ C > 0, ∀ n, ∥p n∥₊ * r ^ n ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, by
    exact_mod_cast hp⟩

theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
    (h : Tendsto (fun n => ∥p n∥ * r ^ n) atTop (𝓝 l)) : ↑r ≤ p.radius :=
  p.le_radius_of_is_O (is_O_one_of_tendsto _ h)

theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summable fun n => ∥p n∥ * r ^ n) :
    ↑r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_at_top_zero

theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E} (h : p.radius < ∥x∥₊) :
    ¬Summable fun n => ∥p n∥ * ∥x∥ ^ n := fun hs => not_le_of_lt h (p.le_radius_of_summable_norm hs)

theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : ↑r < p.radius) :
    Summable fun n : ℕ => ∥p n∥ * r ^ n := by
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact
    summable_of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)) hp
      ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _)

theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E} (hx : x ∈ Emetric.Ball (0 : E) p.radius) :
    Summable fun n : ℕ => ∥p n fun _ => x∥ := by
  rw [mem_emetric_ball_zero_iff] at hx
  refine'
    summable_of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ((p n).le_op_norm _).trans_eq _)
      (p.summable_norm_mul_pow hx)
  simp

theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0 } (h : ↑r < p.radius) :
    Summable fun n : ℕ => ∥p n∥₊ * r ^ n := by
  rw [← Nnreal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h

protected theorem summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Emetric.Ball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  summable_of_summable_norm (p.summable_norm_apply hx)

theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : ∀ r : ℝ≥0 , Summable fun n => ∥p n∥ * r ^ n) : p.radius = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ ∀ r : ℝ≥0 , Summable fun n => ∥p n∥ * r ^ n := by
  constructor
  · intro h r
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ :=
      p.norm_mul_pow_le_mul_pow_of_lt_radius (show (r : ℝ≥0∞) < p.radius from h.symm ▸ Ennreal.coe_lt_top)
    refine'
      summable_of_norm_bounded (fun n => (C : ℝ) * a ^ n) ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _)
        fun n => _
    specialize hp n
    rwa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n))]
    
  · exact p.radius_eq_top_of_summable_norm
    

/-- If the radius of `p` is positive, then `∥pₙ∥` grows at most geometrically. -/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    ∃ (C r : _)(hC : 0 < C)(hr : 0 < r), ∀ n, ∥p n∥ ≤ C * r ^ n := by
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : ℝ) := by
    simp [Ennreal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine'
    ⟨C, r⁻¹, Cpos, by
      simp [rpos], fun n => _⟩
  convert hCp n
  exact inv_pow₀ _ _

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) : min p.radius q.radius ≤ (p + q).radius := by
  refine' Ennreal.le_of_forall_nnreal_lt fun r hr => _
  rw [lt_min_iff] at hr
  have := ((p.is_o_one_of_lt_radius hr.1).add (q.is_o_one_of_lt_radius hr.2)).IsO
  refine' (p + q).le_radius_of_is_O (((is_O_of_le _) fun n => _).trans this)
  rw [← add_mulₓ, norm_mul, norm_mul, norm_norm]
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_abs_self _)) (norm_nonneg _)

@[simp]
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp [radius]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `∥x∥ < p.radius`. -/
protected def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : ℕ, p n fun i => x

protected theorem has_sum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Emetric.Ball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.Sum x) :=
  (p.Summable hx).HasSum

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑ k in Finset.range n, p k fun i : Finₓ k => x

/-- The partial sums of a formal multilinear series are continuous. -/
theorem partial_sum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : Continuous (p.partialSum n) := by
  continuity

end FormalMultilinearSeries

/-! ### Expanding a function as a power series -/


section

variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : ℝ≥0∞}

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series on the ball of radius `r > 0` around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `∥y∥ < r`.
-/
structure HasFpowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) : Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  HasSum : ∀ {y}, y ∈ Emetric.Ball (0 : E) r → HasSum (fun n : ℕ => p n fun i : Finₓ n => y) (f (x + y))

/-- Given a function `f : E → F` and a formal multilinear series `p`, we say that `f` has `p` as
a power series around `x` if `f (x + y) = ∑' pₙ yⁿ` for all `y` in a neighborhood of `0`. -/
def HasFpowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFpowerSeriesOnBall f p x r

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
def AnalyticAt (f : E → F) (x : E) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFpowerSeriesAt f p x

variable {𝕜}

theorem HasFpowerSeriesOnBall.has_fpower_series_at (hf : HasFpowerSeriesOnBall f p x r) : HasFpowerSeriesAt f p x :=
  ⟨r, hf⟩

theorem HasFpowerSeriesAt.analytic_at (hf : HasFpowerSeriesAt f p x) : AnalyticAt 𝕜 f x :=
  ⟨p, hf⟩

theorem HasFpowerSeriesOnBall.analytic_at (hf : HasFpowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.HasFpowerSeriesAt.AnalyticAt

theorem HasFpowerSeriesOnBall.has_sum_sub (hf : HasFpowerSeriesOnBall f p x r) {y : E} (hy : y ∈ Emetric.Ball x r) :
    HasSum (fun n : ℕ => p n fun i => y - x) (f y) := by
  have : y - x ∈ Emetric.Ball (0 : E) r := by
    simpa [edist_eq_coe_nnnorm_sub] using hy
  simpa only [add_sub_cancel'_right] using hf.has_sum this

theorem HasFpowerSeriesOnBall.radius_pos (hf : HasFpowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_leₓ hf.r_pos hf.r_le

theorem HasFpowerSeriesAt.radius_pos (hf : HasFpowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨r, hr⟩ := hf
  hr.radius_pos

theorem HasFpowerSeriesOnBall.mono (hf : HasFpowerSeriesOnBall f p x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
    HasFpowerSeriesOnBall f p x r' :=
  ⟨le_transₓ hr hf.1, r'_pos, fun y hy => hf.HasSum (Emetric.ball_subset_ball hr hy)⟩

protected theorem HasFpowerSeriesAt.eventually (hf : HasFpowerSeriesAt f p x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFpowerSeriesOnBall f p x r :=
  let ⟨r, hr⟩ := hf
  (mem_of_superset (Ioo_mem_nhds_within_Ioi (left_mem_Ico.2 hr.r_pos))) fun r' hr' => hr.mono hr'.1 hr'.2.le

theorem HasFpowerSeriesOnBall.add (hf : HasFpowerSeriesOnBall f pf x r) (hg : HasFpowerSeriesOnBall g pg x r) :
    HasFpowerSeriesOnBall (f + g) (pf + pg) x r :=
  { r_le := le_transₓ (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg), r_pos := hf.r_pos,
    HasSum := fun y hy => (hf.HasSum hy).add (hg.HasSum hy) }

theorem HasFpowerSeriesAt.add (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
    HasFpowerSeriesAt (f + g) (pf + pg) x := by
  rcases(hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f + g) x :=
  let ⟨pf, hpf⟩ := hf
  let ⟨qf, hqf⟩ := hg
  (hpf.add hqf).AnalyticAt

theorem HasFpowerSeriesOnBall.neg (hf : HasFpowerSeriesOnBall f pf x r) : HasFpowerSeriesOnBall (-f) (-pf) x r :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le,
    r_pos := hf.r_pos, HasSum := fun y hy => (hf.HasSum hy).neg }

theorem HasFpowerSeriesAt.neg (hf : HasFpowerSeriesAt f pf x) : HasFpowerSeriesAt (-f) (-pf) x :=
  let ⟨rf, hrf⟩ := hf
  hrf.neg.HasFpowerSeriesAt

theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨pf, hpf⟩ := hf
  hpf.neg.AnalyticAt

theorem HasFpowerSeriesOnBall.sub (hf : HasFpowerSeriesOnBall f pf x r) (hg : HasFpowerSeriesOnBall g pg x r) :
    HasFpowerSeriesOnBall (f - g) (pf - pg) x r := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFpowerSeriesAt.sub (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
    HasFpowerSeriesAt (f - g) (pf - pg) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f - g) x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (i «expr ≠ » 0)
theorem HasFpowerSeriesOnBall.coeff_zero (hf : HasFpowerSeriesOnBall f pf x r) (v : Finₓ 0 → E) : pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elimₓ _ _
  have zero_mem : (0 : E) ∈ Emetric.Ball (0 : E) r := by
    simp [hf.r_pos]
  have : ∀ i _ : i ≠ 0, (pf i fun j => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Finₓ i) rfl
  have A := (hf.has_sum zero_mem).unique (has_sum_single _ this)
  simpa [v_eq] using A.symm

theorem HasFpowerSeriesAt.coeff_zero (hf : HasFpowerSeriesAt f pf x) (v : Finₓ 0 → E) : pf 0 v = f x :=
  let ⟨rf, hrf⟩ := hf
  hrf.coeff_zero v

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `∥y∥` and `n`. See also
`has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/
theorem HasFpowerSeriesOnBall.uniform_geometric_approx' {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x + y) - p.partialSum n y∥ ≤ C * (a * (∥y∥ / r')) ^ n :=
  by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ∥p n∥ * r' ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine' ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n => _⟩
  have yr' : ∥y∥ < r' := by
    rw [ball_zero_eq] at hy
    exact hy
  have hr'0 : 0 < (r' : ℝ) := (norm_nonneg _).trans_lt yr'
  have : y ∈ Emetric.Ball (0 : E) r := by
    refine' mem_emetric_ball_zero_iff.2 (lt_transₓ _ h)
    exact_mod_cast yr'
  rw [norm_sub_rev, ← mul_div_right_comm]
  have ya : a * (∥y∥ / ↑r') ≤ a := mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)
  suffices ∥p.partial_sum n y - f (x + y)∥ ≤ C * (a * (∥y∥ / r')) ^ n / (1 - a * (∥y∥ / r')) by
    refine' this.trans _
    apply_rules [div_le_div_of_le_left, sub_pos.2, div_nonneg, mul_nonneg, pow_nonneg, hC.lt.le, ha.1.le, norm_nonneg,
        Nnreal.coe_nonneg, ha.2, (sub_le_sub_iff_left _).2] <;>
      infer_instance
  apply norm_sub_le_of_geometric_bound_of_has_sum (ya.trans_lt ha.2) _ (hf.has_sum this)
  intro n
  calc ∥(p n) fun i : Finₓ n => y∥ ≤ ∥p n∥ * ∏ i : Finₓ n, ∥y∥ :=
      ContinuousMultilinearMap.le_op_norm _ _ _ = ∥p n∥ * r' ^ n * (∥y∥ / r') ^ n := by
      field_simp [hr'0.ne', mul_right_commₓ]_ ≤ C * a ^ n * (∥y∥ / r') ^ n :=
      mul_le_mul_of_nonneg_right (hp n)
        (pow_nonneg (div_nonneg (norm_nonneg _) r'.coe_nonneg) _)_ ≤ C * (a * (∥y∥ / r')) ^ n :=
      by
      rw [mul_powₓ, mul_assoc]

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFpowerSeriesOnBall.uniform_geometric_approx {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x + y) - p.partialSum n y∥ ≤ C * a ^ n :=
  by
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x + y) - p.partial_sum n y∥ ≤ C * (a * (∥y∥ / r')) ^ n
  exact hf.uniform_geometric_approx' h
  refine' ⟨a, ha, C, hC, fun y hy n => (hp y hy n).trans _⟩
  have yr' : ∥y∥ < r' := by
    rwa [ball_zero_eq] at hy
  refine' mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ _ _) hC.lt.le
  exacts[mul_nonneg ha.1.le (div_nonneg (norm_nonneg y) r'.coe_nonneg),
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)]

/-- Taylor formula for an analytic function, `is_O` version. -/
theorem HasFpowerSeriesAt.is_O_sub_partial_sum_pow (hf : HasFpowerSeriesAt f p x) (n : ℕ) :
    IsO (fun y : E => f (x + y) - p.partialSum n y) (fun y => ∥y∥ ^ n) (𝓝 0) := by
  rcases hf with ⟨r, hf⟩
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x + y) - p.partial_sum n y∥ ≤ C * (a * (∥y∥ / r')) ^ n
  exact hf.uniform_geometric_approx' h
  refine' is_O_iff.2 ⟨C * (a / r') ^ n, _⟩
  replace r'0 : 0 < (r' : ℝ)
  · exact_mod_cast r'0
    
  filter_upwards [Metric.ball_mem_nhds (0 : E) r'0] with y hy
  simpa [mul_powₓ, mul_div_assoc, mul_assoc, div_mul_eq_mul_div] using hp y hy n

-- hack to speed up simp when dealing with complicated types
attribute [-instance] Unique.subsingleton Pi.subsingleton

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. This lemma formulates this property using `is_O` and
`filter.principal` on `E × E`. -/
theorem HasFpowerSeriesOnBall.is_O_image_sub_image_sub_deriv_principal (hf : HasFpowerSeriesOnBall f p x r)
    (hr : r' < r) :
    IsO (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) (fun y => ∥y - (x, x)∥ * ∥y.1 - y.2∥)
      (𝓟 <| Emetric.Ball (x, x) r') :=
  by
  lift r' to ℝ≥0 using ne_top_of_lt hr
  rcases(zero_le r').eq_or_lt with (rfl | hr'0)
  · simp only [is_O_bot, Emetric.ball_zero, principal_empty, Ennreal.coe_zero]
    
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n : ℕ, ∥p n∥ * ↑r' ^ n ≤ C * a ^ n
  exact p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  simp only [← le_div_iff (pow_pos (Nnreal.coe_pos.2 hr'0) _)] at hp
  set L : E × E → ℝ := fun y => C * (a / r') ^ 2 * (∥y - (x, x)∥ * ∥y.1 - y.2∥) * (a / (1 - a) ^ 2 + 2 / (1 - a))
  have hL : ∀, ∀ y ∈ Emetric.Ball (x, x) r', ∀, ∥f y.1 - f y.2 - p 1 fun _ => y.1 - y.2∥ ≤ L y := by
    intro y hy'
    have hy : y ∈ Emetric.Ball x r ×ˢ Emetric.Ball x r := by
      rw [Emetric.ball_prod_same]
      exact Emetric.ball_subset_ball hr.le hy'
    set A : ℕ → F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n + 2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert (has_sum_nat_add_iff' 2).2 ((hf.has_sum_sub hy.1).sub (hf.has_sum_sub hy.2)) using 1
      rw [Finset.sum_range_succ, Finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self, zero_addₓ, ←
        Subsingleton.pi_single_eq (0 : Finₓ 1) (y.1 - x), Pi.single, ← Subsingleton.pi_single_eq (0 : Finₓ 1) (y.2 - x),
        Pi.single, ← (p 1).map_sub, ← Pi.single, Subsingleton.pi_single_eq, sub_sub_sub_cancel_right]
    rw [Emetric.mem_ball, edist_eq_coe_nnnorm_sub, Ennreal.coe_lt_coe] at hy'
    set B : ℕ → ℝ := fun n => C * (a / r') ^ 2 * (∥y - (x, x)∥ * ∥y.1 - y.2∥) * ((n + 2) * a ^ n)
    have hAB : ∀ n, ∥A (n + 2)∥ ≤ B n := fun n =>
      calc
        ∥A (n + 2)∥ ≤ ∥p (n + 2)∥ * ↑(n + 2) * ∥y - (x, x)∥ ^ (n + 1) * ∥y.1 - y.2∥ := by
          simpa only [Fintype.card_fin, pi_norm_const (_ : E), Prod.norm_def, Pi.sub_def, Prod.fst_sub, Prod.snd_sub,
            sub_sub_sub_cancel_right] using (p <| n + 2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = ∥p (n + 2)∥ * ∥y - (x, x)∥ ^ n * (↑(n + 2) * ∥y - (x, x)∥ * ∥y.1 - y.2∥) := by
          rw [pow_succₓ ∥y - (x, x)∥]
          ac_rfl
        _ ≤ C * a ^ (n + 2) / r' ^ (n + 2) * r' ^ n * (↑(n + 2) * ∥y - (x, x)∥ * ∥y.1 - y.2∥) := by
          apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul, hp, pow_le_pow_of_le_left, hy'.le, norm_nonneg,
            pow_nonneg, div_nonneg, mul_nonneg, Nat.cast_nonneg, hC.le, r'.coe_nonneg, ha.1.le]
        _ = B n := by
          field_simp [B, pow_succₓ, hr'0.ne']
          simp only [mul_assoc, mul_comm, mul_left_commₓ]
        
    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mulₓ]
      have : ∥a∥ < 1 := by
        simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      convert (has_sum_coe_mul_geometric_of_norm_lt_1 this).add ((has_sum_geometric_of_norm_lt_1 this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices is_O L (fun y => ∥y - (x, x)∥ * ∥y.1 - y.2∥) (𝓟 (Emetric.Ball (x, x) r')) by
    refine' (is_O.of_bound 1 (eventually_principal.2 fun y hy => _)).trans this
    rw [one_mulₓ]
    exact (hL y hy).trans (le_abs_self _)
  simp_rw [L, mul_right_commₓ _ (_ * _)]
  exact (is_O_refl _ _).const_mul_left _

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (y z «expr ∈ » emetric.ball x r')
/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. -/
theorem HasFpowerSeriesOnBall.image_sub_sub_deriv_le (hf : HasFpowerSeriesOnBall f p x r) (hr : r' < r) :
    ∃ C,
      ∀ y z _ : y ∈ Emetric.Ball x r' _ : z ∈ Emetric.Ball x r',
        ∥f y - f z - p 1 fun _ => y - z∥ ≤ C * max ∥y - x∥ ∥z - x∥ * ∥y - z∥ :=
  by
  simpa only [is_O_principal, mul_assoc, norm_mul, norm_norm, Prod.forall, Emetric.mem_ball, Prod.edist_eq, max_lt_iff,
    and_imp, @forall_swap (_ < _) E] using hf.is_O_image_sub_image_sub_deriv_principal hr

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (λ _, y - z) = O(∥(y, z) - (x, x)∥ * ∥y - z∥)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem HasFpowerSeriesAt.is_O_image_sub_norm_mul_norm_sub (hf : HasFpowerSeriesAt f p x) :
    IsO (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) (fun y => ∥y - (x, x)∥ * ∥y.1 - y.2∥) (𝓝 (x, x)) := by
  rcases hf with ⟨r, hf⟩
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine' (hf.is_O_image_sub_image_sub_deriv_principal h).mono _
  exact le_principal_iff.2 (Emetric.ball_mem_nhds _ r'0)

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
theorem HasFpowerSeriesOnBall.tendsto_uniformly_on {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop (Metric.Ball (0 : E) r') := by
  obtain ⟨a, ha, C, hC, hp⟩ :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀, ∀ y ∈ Metric.Ball (0 : E) r', ∀, ∀ n, ∥f (x + y) - p.partial_sum n y∥ ≤ C * a ^ n
  exact hf.uniform_geometric_approx h
  refine' Metric.tendsto_uniformly_on_iff.2 fun ε εpos => _
  have L : tendsto (fun n => (C : ℝ) * a ^ n) at_top (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 ha.1.le ha.2)
  rw [mul_zero] at L
  refine' (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => _
  rw [dist_eq_norm]
  exact (hp y hy n).trans_lt hn

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
theorem HasFpowerSeriesOnBall.tendsto_locally_uniformly_on (hf : HasFpowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop (Emetric.Ball (0 : E) r) := by
  intro u hu x hx
  rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hx with ⟨r', xr', hr'⟩
  have : Emetric.Ball (0 : E) r' ∈ 𝓝 x := IsOpen.mem_nhds Emetric.is_open_ball xr'
  refine' ⟨Emetric.Ball (0 : E) r', mem_nhds_within_of_mem_nhds this, _⟩
  simpa [Metric.emetric_ball_nnreal] using hf.tendsto_uniformly_on hr' u hu

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendsto_uniformly_on' {r' : ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) : TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop (Metric.Ball (x : E) r') :=
  by
  convert (hf.tendsto_uniformly_on h).comp fun y => y - x
  · simp [(· ∘ ·)]
    
  · ext z
    simp [dist_eq_norm]
    

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendsto_locally_uniformly_on' (hf : HasFpowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop (Emetric.Ball (x : E) r) := by
  have A : ContinuousOn (fun y : E => y - x) (Emetric.Ball (x : E) r) :=
    (continuous_id.sub continuous_const).ContinuousOn
  convert hf.tendsto_locally_uniformly_on.comp (fun y : E => y - x) _ A
  · ext z
    simp
    
  · intro z
    simp [edist_eq_coe_nnnorm, edist_eq_coe_nnnorm_sub]
    

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
protected theorem HasFpowerSeriesOnBall.continuous_on (hf : HasFpowerSeriesOnBall f p x r) :
    ContinuousOn f (Emetric.Ball x r) :=
  hf.tendsto_locally_uniformly_on'.ContinuousOn <|
    eventually_of_forall fun n => ((p.partial_sum_continuous n).comp (continuous_id.sub continuous_const)).ContinuousOn

protected theorem HasFpowerSeriesAt.continuous_at (hf : HasFpowerSeriesAt f p x) : ContinuousAt f x :=
  let ⟨r, hr⟩ := hf
  hr.ContinuousOn.ContinuousAt (Emetric.ball_mem_nhds x hr.r_pos)

protected theorem AnalyticAt.continuous_at (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨p, hp⟩ := hf
  hp.ContinuousAt

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected theorem FormalMultilinearSeries.has_fpower_series_on_ball [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) : HasFpowerSeriesOnBall p.Sum p 0 p.radius :=
  { r_le := le_rfl, r_pos := h,
    HasSum := fun y hy => by
      rw [zero_addₓ]
      exact p.has_sum hy }

theorem HasFpowerSeriesOnBall.sum [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ Emetric.Ball (0 : E) r) : f (x + y) = p.Sum y :=
  (h.HasSum hy).unique (p.HasSum (lt_of_lt_of_leₓ hy h.r_le))

/-- The sum of a converging power series is continuous in its disk of convergence. -/
protected theorem FormalMultilinearSeries.continuous_on [CompleteSpace F] :
    ContinuousOn p.Sum (Emetric.Ball 0 p.radius) := by
  cases' (zero_le p.radius).eq_or_lt with h h
  · simp [← h, continuous_on_empty]
    
  · exact (p.has_fpower_series_on_ball h).ContinuousOn
    

end

/-!
### Uniqueness of power series
If a function `f : E → F` has two representations as power series at a point `x : E`, corresponding
to formal multilinear series `p₁` and `p₂`, then these representations agree term-by-term. That is,
for any `n : ℕ` and `y : E`,  `p₁ n (λ i, y) = p₂ n (λ i, y)`. In the one-dimensional case, when
`f : 𝕜 → E`, the continuous multilinear maps `p₁ n` and `p₂ n` are given by
`formal_multilinear_series.mk_pi_field`, and hence are determined completely by the value of
`p₁ n (λ i, 1)`, so `p₁ = p₂`. Consequently, the radius of convergence for one series can be
transferred to the other.
-/


section Uniqueness

open ContinuousMultilinearMap

theorem Asymptotics.IsO.continuous_multilinear_map_apply_eq_zero {n : ℕ} {p : E[×n]→L[𝕜] F}
    (h : IsO (fun y => p fun i => y) (fun y => ∥y∥ ^ (n + 1)) (𝓝 0)) (y : E) : (p fun i => y) = 0 := by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (is_O_with_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (metric.is_open_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  cases n
  · exact
      norm_eq_zero.mp
        (by
          simpa only [fin0_apply_norm, norm_eq_zero, norm_zero, zero_pow', Ne.def, Nat.one_ne_zero, not_false_iff,
            mul_zero, norm_le_zero_iff] using ht 0 (δε (Metric.mem_ball_self δ_pos)))
    
  · refine'
      Or.elim (em (y = 0))
        (fun hy => by
          simpa only [hy] using p.map_zero)
        fun hy => _
    replace hy := norm_pos_iff.mpr hy
    refine' norm_eq_zero.mp (le_antisymmₓ (le_of_forall_pos_le_add fun ε ε_pos => _) (norm_nonneg _))
    have h₀ := mul_pos c_pos (pow_pos hy (n.succ + 1))
    obtain ⟨k, k_pos, k_norm⟩ :=
      NormedField.exists_norm_lt 𝕜 (lt_minₓ (mul_pos δ_pos (inv_pos.mpr hy)) (mul_pos ε_pos (inv_pos.mpr h₀)))
    have h₁ : ∥k • y∥ < δ := by
      rw [norm_smul]
      exact inv_mul_cancel_right₀ hy.ne.symm δ ▸ mul_lt_mul_of_pos_right (lt_of_lt_of_leₓ k_norm (min_le_leftₓ _ _)) hy
    have h₂ :=
      calc
        ∥p fun i => k • y∥ ≤ c * ∥k • y∥ ^ (n.succ + 1) := by
          simpa only [norm_pow, norm_norm] using ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
        _ = ∥k∥ ^ n.succ * (∥k∥ * (c * ∥y∥ ^ (n.succ + 1))) := by
          simp only [norm_smul, mul_powₓ]
          rw [pow_succₓ]
          ring
        
    have h₃ : ∥k∥ * (c * ∥y∥ ^ (n.succ + 1)) < ε :=
      inv_mul_cancel_right₀ h₀.ne.symm ε ▸ mul_lt_mul_of_pos_right (lt_of_lt_of_leₓ k_norm (min_le_rightₓ _ _)) h₀
    calc ∥p fun i => y∥ = ∥k⁻¹ ^ n.succ∥ * ∥p fun i => k • y∥ := by
        simpa only [inv_smul_smul₀ (norm_pos_iff.mp k_pos), norm_smul, Finset.prod_const, Finset.card_fin] using
          congr_argₓ norm
            (p.map_smul_univ (fun i : Finₓ n.succ => k⁻¹) fun i : Finₓ n.succ =>
              k • y)_ ≤ ∥k⁻¹ ^ n.succ∥ * (∥k∥ ^ n.succ * (∥k∥ * (c * ∥y∥ ^ (n.succ + 1)))) :=
        mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)_ = ∥(k⁻¹ * k) ^ n.succ∥ * (∥k∥ * (c * ∥y∥ ^ (n.succ + 1))) := by
        rw [← mul_assoc]
        simp [norm_mul, mul_powₓ]_ ≤ 0 + ε := by
        rw [inv_mul_cancel (norm_pos_iff.mp k_pos)]
        simpa using h₃.le
    

/-- If a formal multilinear series `p` represents the zero function at `x : E`, then the
terms `p n (λ i, y)` appearing the in sum are zero for any `n : ℕ`, `y : E`. -/
theorem HasFpowerSeriesAt.apply_eq_zero {p : FormalMultilinearSeries 𝕜 E F} {x : E} (h : HasFpowerSeriesAt 0 p x)
    (n : ℕ) : ∀ y : E, (p n fun i => y) = 0 := by
  refine' Nat.strongRecOn n fun k hk => _
  have psum_eq : p.partial_sum (k + 1) = fun y => p k fun i => y := by
    funext z
    refine' Finset.sum_eq_single _ (fun b hb hnb => _) fun hn => _
    · have := finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb), Pi.zero_apply, zero_apply]
      
    · exact False.elim (hn (finset.mem_range.mpr (lt_add_one k)))
      
  replace h := h.is_O_sub_partial_sum_pow k.succ
  simp only [psum_eq, zero_sub, Pi.zero_apply, Asymptotics.is_O_neg_left] at h
  exact h.continuous_multilinear_map_apply_eq_zero

/-- A one-dimensional formal multilinear series representing the zero function is zero. -/
theorem HasFpowerSeriesAt.eq_zero {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : 𝕜} (h : HasFpowerSeriesAt 0 p x) : p = 0 :=
  by
  ext n x
  rw [← mk_pi_field_apply_one_eq_self (p n)]
  simp [h.apply_eq_zero n 1]

/-- One-dimensional formal multilinear series representing the same function are equal. -/
theorem HasFpowerSeriesAt.eq_formal_multilinear_series {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {x : 𝕜}
    (h₁ : HasFpowerSeriesAt f p₁ x) (h₂ : HasFpowerSeriesAt f p₂ x) : p₁ = p₂ :=
  sub_eq_zero.mp
    (HasFpowerSeriesAt.eq_zero
      (by
        simpa only [sub_self] using h₁.sub h₂))

/-- If a function `f : 𝕜 → E` has two power series representations at `x`, then the given radii in
which convergence is guaranteed may be interchanged. This can be useful when the formal multilinear
series in one representation has a particularly nice form, but the other has a larger radius. -/
theorem HasFpowerSeriesOnBall.exchange_radius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {r₁ r₂ : ℝ≥0∞} {x : 𝕜}
    (h₁ : HasFpowerSeriesOnBall f p₁ x r₁) (h₂ : HasFpowerSeriesOnBall f p₂ x r₂) : HasFpowerSeriesOnBall f p₁ x r₂ :=
  h₂.HasFpowerSeriesAt.eq_formal_multilinear_series h₁.HasFpowerSeriesAt ▸ h₂

/-- If a function `f : 𝕜 → E` has power series representation `p` on a ball of some radius and for
each positive radius it has some power series representation, then `p` converges to `f` on the whole
`𝕜`. -/
theorem HasFpowerSeriesOnBall.r_eq_top_of_exists {f : 𝕜 → E} {r : ℝ≥0∞} {x : 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    (h : HasFpowerSeriesOnBall f p x r)
    (h' : ∀ r' : ℝ≥0 hr : 0 < r', ∃ p' : FormalMultilinearSeries 𝕜 𝕜 E, HasFpowerSeriesOnBall f p' x r') :
    HasFpowerSeriesOnBall f p x ∞ :=
  { r_le :=
      Ennreal.le_of_forall_pos_nnreal_lt fun r hr hr' =>
        let ⟨p', hp'⟩ := h' r hr
        (h.exchange_radius hp').r_le,
    r_pos := Ennreal.coe_lt_top,
    HasSum := fun y hy =>
      let ⟨r', hr'⟩ := exists_gt ∥y∥₊
      let ⟨p', hp'⟩ := h' r' hr'.ne_bot.bot_lt
      (h.exchange_radius hp').HasSum <| mem_emetric_ball_zero_iff.mpr (Ennreal.coe_lt_coe.2 hr') }

end Uniqueness

/-!
### Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `fin n` of cardinal `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this paragraph, we implement this. The new power series is called `p.change_origin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open.
-/


namespace FormalMultilinearSeries

section

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0 }

/-- A term of `formal_multilinear_series.change_origin_series`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Each term of `p.change_origin x`
is itself an analytic function of `x` given by the series `p.change_origin_series`. Each term in
`change_origin_series` is the sum of `change_origin_series_term`'s over all `s` of cardinality `l`.
-/
def changeOriginSeriesTerm (k l : ℕ) (s : Finset (Finₓ (k + l))) (hs : s.card = l) : E[×l]→L[𝕜] E[×k]→L[𝕜] F :=
  ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by
      erw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
    (p <| k + l)

theorem change_origin_series_term_apply (k l : ℕ) (s : Finset (Finₓ (k + l))) (hs : s.card = l) (x y : E) :
    (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y) = p (k + l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curry_fin_finset_apply_const _ _ _ _ _

@[simp]
theorem norm_change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k + l))) (hs : s.card = l) :
    ∥p.changeOriginSeriesTerm k l s hs∥ = ∥p (k + l)∥ := by
  simp only [change_origin_series_term, LinearIsometryEquiv.norm_map]

@[simp]
theorem nnnorm_change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k + l))) (hs : s.card = l) :
    ∥p.changeOriginSeriesTerm k l s hs∥₊ = ∥p (k + l)∥₊ := by
  simp only [change_origin_series_term, LinearIsometryEquiv.nnnorm_map]

theorem nnnorm_change_origin_series_term_apply_le (k l : ℕ) (s : Finset (Finₓ (k + l))) (hs : s.card = l) (x y : E) :
    ∥p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y∥₊ ≤ ∥p (k + l)∥₊ * ∥x∥₊ ^ l * ∥y∥₊ ^ k := by
  rw [← p.nnnorm_change_origin_series_term k l s hs, ← Finₓ.prod_const, ← Finₓ.prod_const]
  apply ContinuousMultilinearMap.le_of_op_nnnorm_le
  apply ContinuousMultilinearMap.le_op_nnnorm

/-- The power series for `f.change_origin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. -/
def changeOriginSeries (k : ℕ) : FormalMultilinearSeries 𝕜 E (E[×k]→L[𝕜] F) := fun l =>
  ∑ s : { s : Finset (Finₓ (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2

theorem nnnorm_change_origin_series_le_tsum (k l : ℕ) :
    ∥p.changeOriginSeries k l∥₊ ≤ ∑' x : { s : Finset (Finₓ (k + l)) // s.card = l }, ∥p (k + l)∥₊ :=
  (nnnorm_sum_le _ _).trans_eq <| by
    simp only [tsum_fintype, nnnorm_change_origin_series_term]

theorem nnnorm_change_origin_series_apply_le_tsum (k l : ℕ) (x : E) :
    ∥p.changeOriginSeries k l fun _ => x∥₊ ≤
      ∑' s : { s : Finset (Finₓ (k + l)) // s.card = l }, ∥p (k + l)∥₊ * ∥x∥₊ ^ l :=
  by
  rw [Nnreal.tsum_mul_right, ← Finₓ.prod_const]
  exact (p.change_origin_series k l).le_of_op_nnnorm_le _ (p.nnnorm_change_origin_series_le_tsum _ _)

/-- Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.
-/
def changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F := fun k => (p.changeOriginSeries k).Sum x

/-- An auxiliary equivalence useful in the proofs about
`formal_multilinear_series.change_origin_series`: the set of triples `(k, l, s)`, where `s` is a
`finset (fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`finset (fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - finset.card s, finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps]
def changeOriginIndexEquiv : (Σk l : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l }) ≃ Σn : ℕ, Finset (Finₓ n) where
  toFun := fun s => ⟨s.1 + s.2.1, s.2.2⟩
  invFun := fun s =>
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map (Finₓ.cast <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEquiv.toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Finₓ <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subtype.coe_mk]
    -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
    -- formulate the generalized goal
    suffices
      ∀ k' l',
        k' = k →
          l' = l →
            ∀ hkl : k + l = k' + l' hs',
              (⟨k', l', ⟨Finset.map (Finₓ.cast hkl).toEquiv.toEmbedding s, hs'⟩⟩ :
                  Σk l : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l }) =
                ⟨k, l, ⟨s, hs⟩⟩
      by
      apply this <;> simp only [hs, add_tsub_cancel_right]
    rintro _ _ rfl rfl hkl hs'
    simp only [Equivₓ.refl_to_embedding, Finₓ.cast_refl, Finset.map_refl, eq_self_iff_true, OrderIso.refl_to_equiv,
      and_selfₓ, heq_iff_eq]
  right_inv := by
    rintro ⟨n, s⟩
    simp [tsub_add_cancel_of_le (card_finset_fin_le s), Finₓ.cast_to_equiv]

theorem change_origin_series_summable_aux₁ {r r' : ℝ≥0 } (hr : (r + r' : ℝ≥0∞) < p.radius) :
    Summable fun s : Σk l : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l } =>
      ∥p (s.1 + s.2.1)∥₊ * r ^ s.2.1 * r' ^ s.1 :=
  by
  rw [← change_origin_index_equiv.symm.summable_iff]
  dsimp only [(· ∘ ·), change_origin_index_equiv_symm_apply_fst, change_origin_index_equiv_symm_apply_snd_fst]
  have :
    ∀ n : ℕ,
      HasSum (fun s : Finset (Finₓ n) => ∥p (n - s.card + s.card)∥₊ * r ^ s.card * r' ^ (n - s.card))
        (∥p n∥₊ * (r + r') ^ n) :=
    by
    intro n
    -- TODO: why `simp only [tsub_add_cancel_of_le (card_finset_fin_le _)]` fails?
    convert_to HasSum (fun s : Finset (Finₓ n) => ∥p n∥₊ * (r ^ s.card * r' ^ (n - s.card))) _
    · ext1 s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc]
      
    rw [← Finₓ.sum_pow_mul_eq_add_pow]
    exact (has_sum_fintype _).mul_left _
  refine' Nnreal.summable_sigma.2 ⟨fun n => (this n).Summable, _⟩
  simp only [(this _).tsum_eq]
  exact p.summable_nnnorm_mul_pow hr

theorem change_origin_series_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
    Summable fun s : Σl : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l } => ∥p (k + s.1)∥₊ * r ^ s.1 := by
  rcases Ennreal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((Nnreal.summable_sigma.1 (p.change_origin_series_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹

theorem change_origin_series_summable_aux₃ {r : ℝ≥0 } (hr : ↑r < p.radius) (k : ℕ) :
    Summable fun l : ℕ => ∥p.changeOriginSeries k l∥₊ * r ^ l := by
  refine' Nnreal.summable_of_le (fun n => _) (Nnreal.summable_sigma.1 <| p.change_origin_series_summable_aux₂ hr k).2
  simp only [Nnreal.tsum_mul_right]
  exact mul_le_mul' (p.nnnorm_change_origin_series_le_tsum _ _) le_rfl

theorem le_change_origin_series_radius (k : ℕ) : p.radius ≤ (p.changeOriginSeries k).radius :=
  Ennreal.le_of_forall_nnreal_lt fun r hr => le_radius_of_summable_nnnorm _ (p.change_origin_series_summable_aux₃ hr k)

theorem nnnorm_change_origin_le (k : ℕ) (h : (∥x∥₊ : ℝ≥0∞) < p.radius) :
    ∥p.changeOrigin x k∥₊ ≤ ∑' s : Σl : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l }, ∥p (k + s.1)∥₊ * ∥x∥₊ ^ s.1 :=
  by
  refine' tsum_of_nnnorm_bounded _ fun l => p.nnnorm_change_origin_series_apply_le_tsum k l x
  have := p.change_origin_series_summable_aux₂ h k
  refine' HasSum.sigma this.has_sum fun l => _
  exact ((Nnreal.summable_sigma.1 this).1 l).HasSum

/-- The radius of convergence of `p.change_origin x` is at least `p.radius - ∥x∥`. In other words,
`p.change_origin x` is well defined on the largest ball contained in the original ball of
convergence.-/
theorem change_origin_radius : p.radius - ∥x∥₊ ≤ (p.changeOrigin x).radius := by
  refine' Ennreal.le_of_forall_pos_nnreal_lt fun r h0 hr => _
  rw [lt_tsub_iff_right, add_commₓ] at hr
  have hr' : (∥x∥₊ : ℝ≥0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have :
    ∀ k : ℕ,
      ∥p.change_origin x k∥₊ * r ^ k ≤
        (∑' s : Σl : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l }, ∥p (k + s.1)∥₊ * ∥x∥₊ ^ s.1) * r ^ k :=
    fun k => mul_le_mul_right' (p.nnnorm_change_origin_le k hr') (r ^ k)
  refine' Nnreal.summable_of_le this _
  simpa only [← Nnreal.tsum_mul_right] using (Nnreal.summable_sigma.1 (p.change_origin_series_summable_aux₁ hr)).2

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R : ℝ≥0 }

theorem has_fpower_series_on_ball_change_origin (k : ℕ) (hr : 0 < p.radius) :
    HasFpowerSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius :=
  have := p.le_change_origin_series_radius k
  ((p.changeOriginSeries k).HasFpowerSeriesOnBall (hr.trans_le this)).mono hr this

/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
theorem change_origin_eval (h : (∥x∥₊ + ∥y∥₊ : ℝ≥0∞) < p.radius) : (p.changeOrigin x).Sum y = p.Sum (x + y) := by
  have radius_pos : 0 < p.radius := lt_of_le_of_ltₓ (zero_le _) h
  have x_mem_ball : x ∈ Emetric.Ball (0 : E) p.radius := mem_emetric_ball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y ∈ Emetric.Ball (0 : E) (p.change_origin x).radius := by
    refine' mem_emetric_ball_zero_iff.2 (lt_of_lt_of_leₓ _ p.change_origin_radius)
    rwa [lt_tsub_iff_right, add_commₓ]
  have x_add_y_mem_ball : x + y ∈ Emetric.Ball (0 : E) p.radius := by
    refine' mem_emetric_ball_zero_iff.2 (lt_of_le_of_ltₓ _ h)
    exact_mod_cast nnnorm_add_le x y
  set f : (Σk l : ℕ, { s : Finset (Finₓ (k + l)) // s.card = l }) → F := fun s =>
    p.change_origin_series_term s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have hsf : Summable f := by
    refine' summable_of_nnnorm_bounded _ (p.change_origin_series_summable_aux₁ h) _
    rintro ⟨k, l, s, hs⟩
    dsimp only [Subtype.coe_mk]
    exact p.nnnorm_change_origin_series_term_apply_le _ _ _ _ _ _
  have hf : HasSum f ((p.change_origin x).Sum y) := by
    refine' HasSum.sigma_of_has_sum ((p.change_origin x).Summable y_mem_ball).HasSum (fun k => _) hsf
    · dsimp only [f]
      refine' ContinuousMultilinearMap.has_sum_eval _ _
      have := (p.has_fpower_series_on_ball_change_origin k radius_pos).HasSum x_mem_ball
      rw [zero_addₓ] at this
      refine' HasSum.sigma_of_has_sum this (fun l => _) _
      · simp only [change_origin_series, ContinuousMultilinearMap.sum_apply]
        apply has_sum_fintype
        
      · refine'
          summable_of_nnnorm_bounded _ (p.change_origin_series_summable_aux₂ (mem_emetric_ball_zero_iff.1 x_mem_ball) k)
            fun s => _
        refine' (ContinuousMultilinearMap.le_op_nnnorm _ _).trans_eq _
        simp
        
      
  refine' hf.unique (change_origin_index_equiv.symm.has_sum_iff.1 _)
  refine'
    HasSum.sigma_of_has_sum (p.has_sum x_add_y_mem_ball) (fun n => _)
      (change_origin_index_equiv.symm.summable_iff.2 hsf)
  erw [(p n).map_add_univ (fun _ => x) fun _ => y]
  convert has_sum_fintype _
  ext1 s
  dsimp only [f, change_origin_series_term, (· ∘ ·), change_origin_index_equiv_symm_apply_fst,
    change_origin_index_equiv_symm_apply_snd_fst, change_origin_index_equiv_symm_apply_snd_snd_coe]
  rw [ContinuousMultilinearMap.curry_fin_finset_apply_const]
  have :
    ∀ m hm : n = m,
      p n (s.piecewise (fun _ => x) fun _ => y) =
        p m ((s.map (Finₓ.cast hm).toEquiv.toEmbedding).piecewise (fun _ => x) fun _ => y) :=
    by
    rintro m rfl
    simp
  apply this

end FormalMultilinearSeries

section

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x y : E} {r : ℝ≥0∞}

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem HasFpowerSeriesOnBall.change_origin (hf : HasFpowerSeriesOnBall f p x r) (h : (∥y∥₊ : ℝ≥0∞) < r) :
    HasFpowerSeriesOnBall f (p.changeOrigin y) (x + y) (r - ∥y∥₊) :=
  { r_le := by
      apply le_transₓ _ p.change_origin_radius
      exact tsub_le_tsub hf.r_le le_rfl,
    r_pos := by
      simp [h],
    HasSum := fun z hz => by
      convert (p.change_origin y).HasSum _
      · rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_commₓ] at hz
        rw [p.change_origin_eval (hz.trans_le hf.r_le), add_assocₓ, hf.sum]
        refine' mem_emetric_ball_zero_iff.2 (lt_of_le_of_ltₓ _ hz)
        exact_mod_cast nnnorm_add_le y z
        
      · refine' Emetric.ball_subset_ball (le_transₓ _ p.change_origin_radius) hz
        exact tsub_le_tsub hf.r_le le_rfl
         }

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
theorem HasFpowerSeriesOnBall.analytic_at_of_mem (hf : HasFpowerSeriesOnBall f p x r) (h : y ∈ Emetric.Ball x r) :
    AnalyticAt 𝕜 f y := by
  have : (∥y - x∥₊ : ℝ≥0∞) < r := by
    simpa [edist_eq_coe_nnnorm_sub] using h
  have := hf.change_origin this
  rw [add_sub_cancel'_right] at this
  exact this.analytic_at

variable (𝕜 f)

/-- For any function `f` from a normed vector space to a Banach space, the set of points `x` such
that `f` is analytic at `x` is open. -/
theorem is_open_analytic_at : IsOpen { x | AnalyticAt 𝕜 f x } := by
  rw [is_open_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (Emetric.ball_mem_nhds _ hr.r_pos) fun y hy => hr.analytic_at_of_mem hy

end

