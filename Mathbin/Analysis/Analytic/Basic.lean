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


noncomputable theory

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedGroup G] [NormedSpace 𝕜 G]

open_locale TopologicalSpace Classical BigOperators Nnreal Filter Ennreal

open Set Filter Asymptotics

/-! ### The radius of a formal multilinear series -/


namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r :  ℝ≥0 }

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ ∥pₙ∥ ∥y∥ⁿ`
converges for all `∥y∥ < r`. This implies that `Σ pₙ yⁿ` converges for all `∥y∥ < r`, but these
definitions are *not* equivalent in general. -/
def radius (p : FormalMultilinearSeries 𝕜 E F) : ℝ≥0∞ :=
  ⨆(r :  ℝ≥0 )(C : ℝ)(hr : ∀ n, (∥p n∥*r ^ n) ≤ C), (r : ℝ≥0∞)

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound (C : ℝ) {r :  ℝ≥0 } (h : ∀ n : ℕ, (∥p n∥*r ^ n) ≤ C) : (r : ℝ≥0∞) ≤ p.radius :=
  le_supr_of_le r$ le_supr_of_le C$ le_supr (fun _ => (r : ℝ≥0∞)) h

/-- If `∥pₙ∥ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_bound_nnreal (C :  ℝ≥0 ) {r :  ℝ≥0 } (h : ∀ n : ℕ, (∥p n∥₊*r ^ n) ≤ C) : (r : ℝ≥0∞) ≤ p.radius :=
  p.le_radius_of_bound C$
    fun n =>
      by 
        exactModCast h n

/-- If `∥pₙ∥ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
theorem le_radius_of_is_O (h : is_O (fun n => ∥p n∥*r ^ n) (fun n => (1 : ℝ)) at_top) : «expr↑ » r ≤ p.radius :=
  Exists.elim (is_O_one_nat_at_top_iff.1 h)$ fun C hC => p.le_radius_of_bound C$ fun n => (le_abs_self _).trans (hC n)

theorem le_radius_of_eventually_le C (h : ∀ᶠn in at_top, (∥p n∥*r ^ n) ≤ C) : «expr↑ » r ≤ p.radius :=
  p.le_radius_of_is_O$
    is_O.of_bound C$
      h.mono$
        fun n hn =>
          by 
            simpa

theorem le_radius_of_summable_nnnorm (h : Summable fun n => ∥p n∥₊*r ^ n) : «expr↑ » r ≤ p.radius :=
  p.le_radius_of_bound_nnreal (∑'n, ∥p n∥₊*r ^ n)$ fun n => le_tsum' h _

theorem le_radius_of_summable (h : Summable fun n => ∥p n∥*r ^ n) : «expr↑ » r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm$
    by 
      simp only [←coe_nnnorm] at h 
      exactModCast h

theorem radius_eq_top_of_forall_nnreal_is_O (h : ∀ r :  ℝ≥0 , is_O (fun n => ∥p n∥*r ^ n) (fun n => (1 : ℝ)) at_top) :
  p.radius = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le$ fun r => p.le_radius_of_is_O (h r)

theorem radius_eq_top_of_eventually_eq_zero (h : ∀ᶠn in at_top, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_is_O$
    fun r =>
      (is_O_zero _ _).congr'
        (h.mono$
          fun n hn =>
            by 
              simp [hn])
        eventually_eq.rfl

theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m+n) = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero$ mem_at_top_sets.2 ⟨n, fun k hk => tsub_add_cancel_of_le hk ▸ hn _⟩

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `∥p n∥ rⁿ = o(aⁿ)`. -/
theorem is_o_of_lt_radius
(h : «expr < »(«expr↑ »(r), p.radius)) : «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1), is_o (λ
  n, «expr * »(«expr∥ ∥»(p n), «expr ^ »(r, n))) (pow a) at_top) :=
begin
  rw [expr (tfae_exists_lt_is_o_pow (λ n, «expr * »(«expr∥ ∥»(p n), «expr ^ »(r, n))) 1).out 1 4] [],
  simp [] [] ["only"] ["[", expr radius, ",", expr lt_supr_iff, "]"] [] ["at", ident h],
  rcases [expr h, "with", "⟨", ident t, ",", ident C, ",", ident hC, ",", ident rt, "⟩"],
  rw ["[", expr ennreal.coe_lt_coe, ",", "<-", expr nnreal.coe_lt_coe, "]"] ["at", ident rt],
  have [] [":", expr «expr < »(0, (t : exprℝ()))] [],
  from [expr r.coe_nonneg.trans_lt rt],
  rw ["[", "<-", expr div_lt_one this, "]"] ["at", ident rt],
  refine [expr ⟨_, rt, C, or.inr zero_lt_one, λ n, _⟩],
  calc
    «expr = »(«expr| |»(«expr * »(«expr∥ ∥»(p n), «expr ^ »(r, n))), «expr * »(«expr * »(«expr∥ ∥»(p n), «expr ^ »(t, n)), «expr ^ »(«expr / »(r, t), n))) : by field_simp [] ["[", expr mul_right_comm, ",", expr abs_mul, ",", expr this.ne', "]"] [] []
    «expr ≤ »(..., «expr * »(C, «expr ^ »(«expr / »(r, t), n))) : mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (div_nonneg r.2 t.2) _)
end

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ = o(1)`. -/
theorem is_o_one_of_lt_radius (h : «expr↑ » r < p.radius) : is_o (fun n => ∥p n∥*r ^ n) (fun _ => 1 : ℕ → ℝ) at_top :=
  let ⟨a, ha, hp⟩ := p.is_o_of_lt_radius h 
  hp.trans$ (is_o_pow_pow_of_lt_left ha.1.le ha.2).congr (fun n => rfl) one_pow

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`,  `∥p n∥ * r ^ n ≤ C * a ^ n`. -/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : «expr↑ » r < p.radius) :
  ∃ (a : _)(_ : a ∈ Ioo (0 : ℝ) 1)(C : _)(_ : C > 0), ∀ n, (∥p n∥*r ^ n) ≤ C*a ^ n :=
  by 
    rcases((tfae_exists_lt_is_o_pow (fun n => ∥p n∥*r ^ n) 1).out 1 5).mp (p.is_o_of_lt_radius h) with ⟨a, ha, C, hC, H⟩
    exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `r ≠ 0` and `∥pₙ∥ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
theorem lt_radius_of_is_O
(h₀ : «expr ≠ »(r, 0))
{a : exprℝ()}
(ha : «expr ∈ »(a, Ioo («expr- »(1) : exprℝ()) 1))
(hp : is_O (λ n, «expr * »(«expr∥ ∥»(p n), «expr ^ »(r, n))) (pow a) at_top) : «expr < »(«expr↑ »(r), p.radius) :=
begin
  rcases [expr ((tfae_exists_lt_is_o_pow (λ
      n, «expr * »(«expr∥ ∥»(p n), «expr ^ »(r, n))) 1).out 2 5).mp ⟨a, ha, hp⟩, "with", "⟨", ident a, ",", ident ha, ",", ident C, ",", ident hC, ",", ident hp, "⟩"],
  rw ["[", "<-", expr pos_iff_ne_zero, ",", "<-", expr nnreal.coe_pos, "]"] ["at", ident h₀],
  lift [expr a] ["to", expr «exprℝ≥0»()] ["using", expr ha.1.le] [],
  have [] [":", expr «expr < »((r : exprℝ()), «expr / »(r, a))] [":=", expr by simpa [] [] ["only"] ["[", expr div_one, "]"] [] ["using", expr (div_lt_div_left h₀ zero_lt_one ha.1).2 ha.2]],
  norm_cast ["at", ident this],
  rw ["[", "<-", expr ennreal.coe_lt_coe, "]"] ["at", ident this],
  refine [expr this.trans_le «expr $ »(p.le_radius_of_bound C, λ n, _)],
  rw ["[", expr nnreal.coe_div, ",", expr div_pow, ",", "<-", expr mul_div_assoc, ",", expr div_le_iff (pow_pos ha.1 n), "]"] [],
  exact [expr (le_abs_self _).trans (hp n)]
end

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r :  ℝ≥0 } (h : (r : ℝ≥0∞) < p.radius) :
  ∃ (C : _)(_ : C > 0), ∀ n, (∥p n∥*r ^ n) ≤ C :=
  let ⟨a, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans$ mul_le_of_le_one_right hC.lt.le (pow_le_one _ ha.1.le ha.2.le)⟩

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r :  ℝ≥0 } (h0 : 0 < r)
  (h : (r : ℝ≥0∞) < p.radius) : ∃ (C : _)(_ : C > 0), ∀ n, ∥p n∥ ≤ C / r ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff (pow_pos h0 _)) (hp n)⟩

/-- For `r` strictly smaller than the radius of `p`, then `∥pₙ∥ rⁿ` is bounded. -/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r :  ℝ≥0 } (h : (r : ℝ≥0∞) < p.radius) :
  ∃ (C : _)(_ : C > 0), ∀ n, (∥p n∥₊*r ^ n) ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC,
    by 
      exactModCast hp⟩

theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
  (h : tendsto (fun n => ∥p n∥*r ^ n) at_top (𝓝 l)) : «expr↑ » r ≤ p.radius :=
  p.le_radius_of_is_O (is_O_one_of_tendsto _ h)

theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summable fun n => ∥p n∥*r ^ n) :
  «expr↑ » r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_at_top_zero

theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E} (h : p.radius < ∥x∥₊) :
  ¬Summable fun n => ∥p n∥*∥x∥ ^ n :=
  fun hs => not_le_of_lt h (p.le_radius_of_summable_norm hs)

theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r :  ℝ≥0 } (h : «expr↑ » r < p.radius) :
  Summable fun n : ℕ => ∥p n∥*r ^ n :=
  by 
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h 
    exact
      summable_of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)) hp
        ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _)

theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E} (hx : x ∈ Emetric.Ball (0 : E) p.radius) :
  Summable fun n : ℕ => ∥p n fun _ => x∥ :=
  by 
    rw [mem_emetric_ball_zero_iff] at hx 
    refine'
      summable_of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ((p n).le_op_norm _).trans_eq _)
        (p.summable_norm_mul_pow hx)
    simp 

theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r :  ℝ≥0 } (h : «expr↑ » r < p.radius) :
  Summable fun n : ℕ => ∥p n∥₊*r ^ n :=
  by 
    rw [←Nnreal.summable_coe]
    pushCast 
    exact p.summable_norm_mul_pow h

protected theorem Summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  (hx : x ∈ Emetric.Ball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  summable_of_summable_norm (p.summable_norm_apply hx)

theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
  (hs : ∀ r :  ℝ≥0 , Summable fun n => ∥p n∥*r ^ n) : p.radius = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)

theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
  p.radius = ∞ ↔ ∀ r :  ℝ≥0 , Summable fun n => ∥p n∥*r ^ n :=
  by 
    split 
    ·
      intro h r 
      obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, hC : 0 < C, hp⟩ :=
        p.norm_mul_pow_le_mul_pow_of_lt_radius (show (r : ℝ≥0∞) < p.radius from h.symm ▸ Ennreal.coe_lt_top)
      refine'
        summable_of_norm_bounded (fun n => (C : ℝ)*a ^ n) ((summable_geometric_of_lt_1 ha.1.le ha.2).mul_left _)
          fun n => _ 
      specialize hp n 
      rwa [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n))]
    ·
      exact p.radius_eq_top_of_summable_norm

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the radius of `p` is positive, then `∥pₙ∥` grows at most geometrically. -/
theorem le_mul_pow_of_radius_pos
(p : formal_multilinear_series 𝕜 E F)
(h : «expr < »(0, p.radius)) : «expr∃ , »((C r)
 (hC : «expr < »(0, C))
 (hr : «expr < »(0, r)), ∀ n, «expr ≤ »(«expr∥ ∥»(p n), «expr * »(C, «expr ^ »(r, n)))) :=
begin
  rcases [expr ennreal.lt_iff_exists_nnreal_btwn.1 h, "with", "⟨", ident r, ",", ident r0, ",", ident rlt, "⟩"],
  have [ident rpos] [":", expr «expr < »(0, (r : exprℝ()))] [],
  by simp [] [] [] ["[", expr ennreal.coe_pos.1 r0, "]"] [] [],
  rcases [expr norm_le_div_pow_of_pos_of_lt_radius p rpos rlt, "with", "⟨", ident C, ",", ident Cpos, ",", ident hCp, "⟩"],
  refine [expr ⟨C, «expr ⁻¹»(r), Cpos, by simp [] [] [] ["[", expr rpos, "]"] [] [], λ n, _⟩],
  convert [] [expr hCp n] [],
  exact [expr inv_pow₀ _ _]
end

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
theorem min_radius_le_radius_add
(p q : formal_multilinear_series 𝕜 E F) : «expr ≤ »(min p.radius q.radius, «expr + »(p, q).radius) :=
begin
  refine [expr ennreal.le_of_forall_nnreal_lt (λ r hr, _)],
  rw [expr lt_min_iff] ["at", ident hr],
  have [] [] [":=", expr ((p.is_o_one_of_lt_radius hr.1).add (q.is_o_one_of_lt_radius hr.2)).is_O],
  refine [expr «expr + »(p, q).le_radius_of_is_O («expr $ »(is_O_of_le _, λ n, _).trans this)],
  rw ["[", "<-", expr add_mul, ",", expr normed_field.norm_mul, ",", expr normed_field.norm_mul, ",", expr norm_norm, "]"] [],
  exact [expr mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (le_abs_self _)) (norm_nonneg _)]
end

@[simp]
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius :=
  by 
    simp [radius]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `∥x∥ < p.radius`. -/
protected def Sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑'n : ℕ, p n fun i => x

protected theorem HasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
  (hx : x ∈ Emetric.Ball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  (p.summable hx).HasSum

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partial_sum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
def partial_sum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑k in Finset.range n, p k fun i : Finₓ k => x

/-- The partial sums of a formal multilinear series are continuous. -/
theorem partial_sum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : Continuous (p.partial_sum n) :=
  by 
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
  HasSum : ∀ {y}, y ∈ Emetric.Ball (0 : E) r → HasSum (fun n : ℕ => p n fun i : Finₓ n => y) (f (x+y))

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
  hf.has_fpower_series_at.analytic_at

theorem HasFpowerSeriesOnBall.has_sum_sub (hf : HasFpowerSeriesOnBall f p x r) {y : E} (hy : y ∈ Emetric.Ball x r) :
  HasSum (fun n : ℕ => p n fun i => y - x) (f y) :=
  have  : y - x ∈ Emetric.Ball (0 : E) r :=
    by 
      simpa [edist_eq_coe_nnnorm_sub] using hy 
  by 
    simpa only [add_sub_cancel'_right] using hf.has_sum this

theorem HasFpowerSeriesOnBall.radius_pos (hf : HasFpowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_leₓ hf.r_pos hf.r_le

theorem HasFpowerSeriesAt.radius_pos (hf : HasFpowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨r, hr⟩ := hf 
  hr.radius_pos

theorem HasFpowerSeriesOnBall.mono (hf : HasFpowerSeriesOnBall f p x r) (r'_pos : 0 < r') (hr : r' ≤ r) :
  HasFpowerSeriesOnBall f p x r' :=
  ⟨le_transₓ hr hf.1, r'_pos, fun y hy => hf.has_sum (Emetric.ball_subset_ball hr hy)⟩

protected theorem HasFpowerSeriesAt.eventually (hf : HasFpowerSeriesAt f p x) :
  ∀ᶠr : ℝ≥0∞ in 𝓝[Ioi 0] 0, HasFpowerSeriesOnBall f p x r :=
  let ⟨r, hr⟩ := hf 
  mem_of_superset (Ioo_mem_nhds_within_Ioi (left_mem_Ico.2 hr.r_pos))$ fun r' hr' => hr.mono hr'.1 hr'.2.le

theorem HasFpowerSeriesOnBall.add (hf : HasFpowerSeriesOnBall f pf x r) (hg : HasFpowerSeriesOnBall g pg x r) :
  HasFpowerSeriesOnBall (f+g) (pf+pg) x r :=
  { r_le := le_transₓ (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg), r_pos := hf.r_pos,
    HasSum := fun y hy => (hf.has_sum hy).add (hg.has_sum hy) }

theorem HasFpowerSeriesAt.add (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
  HasFpowerSeriesAt (f+g) (pf+pg) x :=
  by 
    rcases(hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
    exact ⟨r, hr.1.add hr.2⟩

theorem AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f+g) x :=
  let ⟨pf, hpf⟩ := hf 
  let ⟨qf, hqf⟩ := hg
  (hpf.add hqf).AnalyticAt

theorem HasFpowerSeriesOnBall.neg (hf : HasFpowerSeriesOnBall f pf x r) : HasFpowerSeriesOnBall (-f) (-pf) x r :=
  { r_le :=
      by 
        rw [pf.radius_neg]
        exact hf.r_le,
    r_pos := hf.r_pos, HasSum := fun y hy => (hf.has_sum hy).neg }

theorem HasFpowerSeriesAt.neg (hf : HasFpowerSeriesAt f pf x) : HasFpowerSeriesAt (-f) (-pf) x :=
  let ⟨rf, hrf⟩ := hf 
  hrf.neg.has_fpower_series_at

theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨pf, hpf⟩ := hf 
  hpf.neg.analytic_at

theorem HasFpowerSeriesOnBall.sub (hf : HasFpowerSeriesOnBall f pf x r) (hg : HasFpowerSeriesOnBall g pg x r) :
  HasFpowerSeriesOnBall (f - g) (pf - pg) x r :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFpowerSeriesAt.sub (hf : HasFpowerSeriesAt f pf x) (hg : HasFpowerSeriesAt g pg x) :
  HasFpowerSeriesAt (f - g) (pf - pg) x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (f - g) x :=
  by 
    simpa only [sub_eq_add_neg] using hf.add hg.neg

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_fpower_series_on_ball.coeff_zero
(hf : has_fpower_series_on_ball f pf x r)
(v : fin 0 → E) : «expr = »(pf 0 v, f x) :=
begin
  have [ident v_eq] [":", expr «expr = »(v, λ i, 0)] [":=", expr subsingleton.elim _ _],
  have [ident zero_mem] [":", expr «expr ∈ »((0 : E), emetric.ball (0 : E) r)] [],
  by simp [] [] [] ["[", expr hf.r_pos, "]"] [] [],
  have [] [":", expr ∀ i «expr ≠ » 0, «expr = »(pf i (λ j, 0), 0)] [],
  { assume [binders (i hi)],
    have [] [":", expr «expr < »(0, i)] [":=", expr pos_iff_ne_zero.2 hi],
    exact [expr continuous_multilinear_map.map_coord_zero _ (⟨0, this⟩ : fin i) rfl] },
  have [ident A] [] [":=", expr (hf.has_sum zero_mem).unique (has_sum_single _ this)],
  simpa [] [] [] ["[", expr v_eq, "]"] [] ["using", expr A.symm]
end

theorem HasFpowerSeriesAt.coeff_zero (hf : HasFpowerSeriesAt f pf x) (v : Finₓ 0 → E) : pf 0 v = f x :=
  let ⟨rf, hrf⟩ := hf 
  hrf.coeff_zero v

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `∥y∥` and `n`. See also
`has_fpower_series_on_ball.uniform_geometric_approx` for a weaker version. -/
theorem has_fpower_series_on_ball.uniform_geometric_approx'
{r' : «exprℝ≥0»()}
(hf : has_fpower_series_on_ball f p x r)
(h : «expr < »((r' : «exprℝ≥0∞»()), r)) : «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1)
 (C «expr > » 0), ∀
 y «expr ∈ » metric.ball (0 : E) r', ∀
 n, «expr ≤ »(«expr∥ ∥»(«expr - »(f «expr + »(x, y), p.partial_sum n y)), «expr * »(C, «expr ^ »(«expr * »(a, «expr / »(«expr∥ ∥»(y), r')), n)))) :=
begin
  obtain ["⟨", ident a, ",", ident ha, ",", ident C, ",", ident hC, ",", ident hp, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1)
    (C «expr > » 0), ∀
    n, «expr ≤ »(«expr * »(«expr∥ ∥»(p n), «expr ^ »(r', n)), «expr * »(C, «expr ^ »(a, n)))), ":=", expr p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)],
  refine [expr ⟨a, ha, «expr / »(C, «expr - »(1, a)), div_pos hC (sub_pos.2 ha.2), λ y hy n, _⟩],
  have [ident yr'] [":", expr «expr < »(«expr∥ ∥»(y), r')] [],
  by { rw [expr ball_zero_eq] ["at", ident hy],
    exact [expr hy] },
  have [ident hr'0] [":", expr «expr < »(0, (r' : exprℝ()))] [],
  from [expr (norm_nonneg _).trans_lt yr'],
  have [] [":", expr «expr ∈ »(y, emetric.ball (0 : E) r)] [],
  { refine [expr mem_emetric_ball_zero_iff.2 (lt_trans _ h)],
    exact_mod_cast [expr yr'] },
  rw ["[", expr norm_sub_rev, ",", "<-", expr mul_div_right_comm, "]"] [],
  have [ident ya] [":", expr «expr ≤ »(«expr * »(a, «expr / »(«expr∥ ∥»(y), «expr↑ »(r'))), a)] [],
  from [expr mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg)],
  suffices [] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(p.partial_sum n y, f «expr + »(x, y))), «expr / »(«expr * »(C, «expr ^ »(«expr * »(a, «expr / »(«expr∥ ∥»(y), r')), n)), «expr - »(1, «expr * »(a, «expr / »(«expr∥ ∥»(y), r')))))],
  { refine [expr this.trans _],
    apply_rules ["[", expr div_le_div_of_le_left, ",", expr sub_pos.2, ",", expr div_nonneg, ",", expr mul_nonneg, ",", expr pow_nonneg, ",", expr hC.lt.le, ",", expr ha.1.le, ",", expr norm_nonneg, ",", expr nnreal.coe_nonneg, ",", expr ha.2, ",", expr (sub_le_sub_iff_left _).2, "]"]; apply_instance },
  apply [expr norm_sub_le_of_geometric_bound_of_has_sum (ya.trans_lt ha.2) _ (hf.has_sum this)],
  assume [binders (n)],
  calc
    «expr ≤ »(«expr∥ ∥»(p n (λ
       i : fin n, y)), «expr * »(«expr∥ ∥»(p n), «expr∏ , »((i : fin n), «expr∥ ∥»(y)))) : continuous_multilinear_map.le_op_norm _ _
    «expr = »(..., «expr * »(«expr * »(«expr∥ ∥»(p n), «expr ^ »(r', n)), «expr ^ »(«expr / »(«expr∥ ∥»(y), r'), n))) : by field_simp [] ["[", expr hr'0.ne', ",", expr mul_right_comm, "]"] [] []
    «expr ≤ »(..., «expr * »(«expr * »(C, «expr ^ »(a, n)), «expr ^ »(«expr / »(«expr∥ ∥»(y), r'), n))) : mul_le_mul_of_nonneg_right (hp n) (pow_nonneg (div_nonneg (norm_nonneg _) r'.coe_nonneg) _)
    «expr ≤ »(..., «expr * »(C, «expr ^ »(«expr * »(a, «expr / »(«expr∥ ∥»(y), r')), n))) : by rw ["[", expr mul_pow, ",", expr mul_assoc, "]"] []
end

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem has_fpower_series_on_ball.uniform_geometric_approx
{r' : «exprℝ≥0»()}
(hf : has_fpower_series_on_ball f p x r)
(h : «expr < »((r' : «exprℝ≥0∞»()), r)) : «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1)
 (C «expr > » 0), ∀
 y «expr ∈ » metric.ball (0 : E) r', ∀
 n, «expr ≤ »(«expr∥ ∥»(«expr - »(f «expr + »(x, y), p.partial_sum n y)), «expr * »(C, «expr ^ »(a, n)))) :=
begin
  obtain ["⟨", ident a, ",", ident ha, ",", ident C, ",", ident hC, ",", ident hp, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1)
    (C «expr > » 0), ∀
    y «expr ∈ » metric.ball (0 : E) r', ∀
    n, «expr ≤ »(«expr∥ ∥»(«expr - »(f «expr + »(x, y), p.partial_sum n y)), «expr * »(C, «expr ^ »(«expr * »(a, «expr / »(«expr∥ ∥»(y), r')), n))))],
  from [expr hf.uniform_geometric_approx' h],
  refine [expr ⟨a, ha, C, hC, λ y hy n, (hp y hy n).trans _⟩],
  have [ident yr'] [":", expr «expr < »(«expr∥ ∥»(y), r')] [],
  by rwa [expr ball_zero_eq] ["at", ident hy],
  refine [expr mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left _ _ _) hC.lt.le],
  exacts ["[", expr mul_nonneg ha.1.le (div_nonneg (norm_nonneg y) r'.coe_nonneg), ",", expr mul_le_of_le_one_right ha.1.le (div_le_one_of_le yr'.le r'.coe_nonneg), "]"]
end

/-- Taylor formula for an analytic function, `is_O` version. -/
theorem HasFpowerSeriesAt.is_O_sub_partial_sum_pow (hf : HasFpowerSeriesAt f p x) (n : ℕ) :
  is_O (fun y : E => f (x+y) - p.partial_sum n y) (fun y => ∥y∥ ^ n) (𝓝 0) :=
  by 
    rcases hf with ⟨r, hf⟩
    rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
    obtain ⟨a, ha, C, hC, hp⟩ :
      ∃ (a : _)(_ : a ∈ Ioo (0 : ℝ) 1)(C : _)(_ : C > 0),
        ∀ y _ : y ∈ Metric.Ball (0 : E) r', ∀ n, ∥f (x+y) - p.partial_sum n y∥ ≤ C*(a*∥y∥ / r') ^ n 
    exact hf.uniform_geometric_approx' h 
    refine' is_O_iff.2 ⟨C*(a / r') ^ n, _⟩
    replace r'0 : 0 < (r' : ℝ)
    ·
      exactModCast r'0 
    filterUpwards [Metric.ball_mem_nhds (0 : E) r'0]
    intro y hy 
    simpa [mul_powₓ, mul_div_assoc, mul_assocₓ, div_mul_eq_mul_div] using hp y hy n

attribute [-instance] Unique.subsingleton Pi.subsingleton

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. This lemma formulates this property using `is_O` and
`filter.principal` on `E × E`. -/
theorem has_fpower_series_on_ball.is_O_image_sub_image_sub_deriv_principal
(hf : has_fpower_series_on_ball f p x r)
(hr : «expr < »(r', r)) : is_O (λ
 y : «expr × »(E, E), «expr - »(«expr - »(f y.1, f y.2), p 1 (λ
   _, «expr - »(y.1, y.2)))) (λ
 y, «expr * »(«expr∥ ∥»(«expr - »(y, (x, x))), «expr∥ ∥»(«expr - »(y.1, y.2)))) «expr $ »(expr𝓟(), emetric.ball (x, x) r') :=
begin
  lift [expr r'] ["to", expr «exprℝ≥0»()] ["using", expr ne_top_of_lt hr] [],
  rcases [expr (zero_le r').eq_or_lt, "with", ident rfl, "|", ident hr'0],
  { simp [] [] ["only"] ["[", expr is_O_bot, ",", expr emetric.ball_zero, ",", expr principal_empty, ",", expr ennreal.coe_zero, "]"] [] [] },
  obtain ["⟨", ident a, ",", ident ha, ",", ident C, ",", ident hC, ":", expr «expr < »(0, C), ",", ident hp, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1)
    (C «expr > » 0), ∀
    n : exprℕ(), «expr ≤ »(«expr * »(«expr∥ ∥»(p n), «expr ^ »(«expr↑ »(r'), n)), «expr * »(C, «expr ^ »(a, n))))],
  from [expr p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)],
  simp [] [] ["only"] ["[", "<-", expr le_div_iff (pow_pos (nnreal.coe_pos.2 hr'0) _), "]"] [] ["at", ident hp],
  set [] [ident L] [":", expr «expr × »(E, E) → exprℝ()] [":="] [expr λ
   y, «expr * »(«expr * »(«expr * »(C, «expr ^ »(«expr / »(a, r'), 2)), «expr * »(«expr∥ ∥»(«expr - »(y, (x, x))), «expr∥ ∥»(«expr - »(y.1, y.2)))), «expr + »(«expr / »(a, «expr ^ »(«expr - »(1, a), 2)), «expr / »(2, «expr - »(1, a))))] [],
  have [ident hL] [":", expr ∀
   y «expr ∈ » emetric.ball (x, x) r', «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f y.1, f y.2), p 1 (λ
       _, «expr - »(y.1, y.2)))), L y)] [],
  { intros [ident y, ident hy'],
    have [ident hy] [":", expr «expr ∈ »(y, (emetric.ball x r).prod (emetric.ball x r))] [],
    { rw ["[", expr emetric.ball_prod_same, "]"] [],
      exact [expr emetric.ball_subset_ball hr.le hy'] },
    set [] [ident A] [":", expr exprℕ() → F] [":="] [expr λ
     n, «expr - »(p n (λ _, «expr - »(y.1, x)), p n (λ _, «expr - »(y.2, x)))] [],
    have [ident hA] [":", expr has_sum (λ
      n, A «expr + »(n, 2)) «expr - »(«expr - »(f y.1, f y.2), p 1 (λ _, «expr - »(y.1, y.2)))] [],
    { convert [] [expr (has_sum_nat_add_iff' 2).2 ((hf.has_sum_sub hy.1).sub (hf.has_sum_sub hy.2))] ["using", 1],
      rw ["[", expr finset.sum_range_succ, ",", expr finset.sum_range_one, ",", expr hf.coeff_zero, ",", expr hf.coeff_zero, ",", expr sub_self, ",", expr zero_add, ",", "<-", expr subsingleton.pi_single_eq (0 : fin 1) «expr - »(y.1, x), ",", expr pi.single, ",", "<-", expr subsingleton.pi_single_eq (0 : fin 1) «expr - »(y.2, x), ",", expr pi.single, ",", "<-", expr (p 1).map_sub, ",", "<-", expr pi.single, ",", expr subsingleton.pi_single_eq, ",", expr sub_sub_sub_cancel_right, "]"] [] },
    rw ["[", expr emetric.mem_ball, ",", expr edist_eq_coe_nnnorm_sub, ",", expr ennreal.coe_lt_coe, "]"] ["at", ident hy'],
    set [] [ident B] [":", expr exprℕ() → exprℝ()] [":="] [expr λ
     n, «expr * »(«expr * »(«expr * »(C, «expr ^ »(«expr / »(a, r'), 2)), «expr * »(«expr∥ ∥»(«expr - »(y, (x, x))), «expr∥ ∥»(«expr - »(y.1, y.2)))), «expr * »(«expr + »(n, 2), «expr ^ »(a, n)))] [],
    have [ident hAB] [":", expr ∀
     n, «expr ≤ »(«expr∥ ∥»(A «expr + »(n, 2)), B n)] [":=", expr λ n, calc
       «expr ≤ »(«expr∥ ∥»(A «expr + »(n, 2)), «expr * »(«expr * »(«expr * »(«expr∥ ∥»(p «expr + »(n, 2)), «expr↑ »(«expr + »(n, 2))), «expr ^ »(«expr∥ ∥»(«expr - »(y, (x, x))), «expr + »(n, 1))), «expr∥ ∥»(«expr - »(y.1, y.2)))) : by simpa [] [] ["only"] ["[", expr fintype.card_fin, ",", expr pi_norm_const, ",", expr prod.norm_def, ",", expr pi.sub_def, ",", expr prod.fst_sub, ",", expr prod.snd_sub, ",", expr sub_sub_sub_cancel_right, "]"] [] ["using", expr «expr $ »(p, «expr + »(n, 2)).norm_image_sub_le (λ
         _, «expr - »(y.1, x)) (λ _, «expr - »(y.2, x))]
       «expr = »(..., «expr * »(«expr * »(«expr∥ ∥»(p «expr + »(n, 2)), «expr ^ »(«expr∥ ∥»(«expr - »(y, (x, x))), n)), «expr * »(«expr * »(«expr↑ »(«expr + »(n, 2)), «expr∥ ∥»(«expr - »(y, (x, x)))), «expr∥ ∥»(«expr - »(y.1, y.2))))) : by { rw ["[", expr pow_succ «expr∥ ∥»(«expr - »(y, (x, x))), "]"] [],
         ac_refl }
       «expr ≤ »(..., «expr * »(«expr * »(«expr / »(«expr * »(C, «expr ^ »(a, «expr + »(n, 2))), «expr ^ »(r', «expr + »(n, 2))), «expr ^ »(r', n)), «expr * »(«expr * »(«expr↑ »(«expr + »(n, 2)), «expr∥ ∥»(«expr - »(y, (x, x)))), «expr∥ ∥»(«expr - »(y.1, y.2))))) : by apply_rules ["[", expr mul_le_mul_of_nonneg_right, ",", expr mul_le_mul, ",", expr hp, ",", expr pow_le_pow_of_le_left, ",", expr hy'.le, ",", expr norm_nonneg, ",", expr pow_nonneg, ",", expr div_nonneg, ",", expr mul_nonneg, ",", expr nat.cast_nonneg, ",", expr hC.le, ",", expr r'.coe_nonneg, ",", expr ha.1.le, "]"]
       «expr = »(..., B n) : by { field_simp [] ["[", expr B, ",", expr pow_succ, ",", expr hr'0.ne', "]"] [] [],
         simp [] [] ["only"] ["[", expr mul_assoc, ",", expr mul_comm, ",", expr mul_left_comm, "]"] [] [] }],
    have [ident hBL] [":", expr has_sum B (L y)] [],
    { apply [expr has_sum.mul_left],
      simp [] [] ["only"] ["[", expr add_mul, "]"] [] [],
      have [] [":", expr «expr < »(«expr∥ ∥»(a), 1)] [],
      by simp [] [] ["only"] ["[", expr real.norm_eq_abs, ",", expr abs_of_pos ha.1, ",", expr ha.2, "]"] [] [],
      convert [] [expr (has_sum_coe_mul_geometric_of_norm_lt_1 this).add ((has_sum_geometric_of_norm_lt_1 this).mul_left 2)] [] },
    exact [expr hA.norm_le_of_bounded hBL hAB] },
  suffices [] [":", expr is_O L (λ
    y, «expr * »(«expr∥ ∥»(«expr - »(y, (x, x))), «expr∥ ∥»(«expr - »(y.1, y.2)))) (expr𝓟() (emetric.ball (x, x) r'))],
  { refine [expr (is_O.of_bound 1 «expr $ »(eventually_principal.2, λ y hy, _)).trans this],
    rw [expr one_mul] [],
    exact [expr (hL y hy).trans (le_abs_self _)] },
  simp_rw ["[", expr L, ",", expr mul_right_comm _ «expr * »(_, _), "]"] [],
  exact [expr (is_O_refl _ _).const_mul_left _]
end

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (λ _, y - z)` is bounded above by
`C * (max ∥y - x∥ ∥z - x∥) * ∥y - z∥`. -/
theorem HasFpowerSeriesOnBall.image_sub_sub_deriv_le (hf : HasFpowerSeriesOnBall f p x r) (hr : r' < r) :
  ∃ C,
    ∀ y z _ : y ∈ Emetric.Ball x r' _ : z ∈ Emetric.Ball x r',
      ∥f y - f z - p 1 fun _ => y - z∥ ≤ (C*max ∥y - x∥ ∥z - x∥)*∥y - z∥ :=
  by 
    simpa only [is_O_principal, mul_assocₓ, NormedField.norm_mul, norm_norm, Prod.forall, Emetric.mem_ball,
      Prod.edist_eq, max_lt_iff, and_imp] using hf.is_O_image_sub_image_sub_deriv_principal hr

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (λ _, y - z) = O(∥(y, z) - (x, x)∥ * ∥y - z∥)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem HasFpowerSeriesAt.is_O_image_sub_norm_mul_norm_sub (hf : HasFpowerSeriesAt f p x) :
  is_O (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) (fun y => ∥y - (x, x)∥*∥y.1 - y.2∥) (𝓝 (x, x)) :=
  by 
    rcases hf with ⟨r, hf⟩
    rcases Ennreal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
    refine' (hf.is_O_image_sub_image_sub_deriv_principal h).mono _ 
    exact le_principal_iff.2 (Emetric.ball_mem_nhds _ r'0)

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partial_sum n y` there. -/
theorem has_fpower_series_on_ball.tendsto_uniformly_on
{r' : «exprℝ≥0»()}
(hf : has_fpower_series_on_ball f p x r)
(h : «expr < »((r' : «exprℝ≥0∞»()), r)) : tendsto_uniformly_on (λ
 n y, p.partial_sum n y) (λ y, f «expr + »(x, y)) at_top (metric.ball (0 : E) r') :=
begin
  obtain ["⟨", ident a, ",", ident ha, ",", ident C, ",", ident hC, ",", ident hp, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo (0 : exprℝ()) 1)
    (C «expr > » 0), ∀
    y «expr ∈ » metric.ball (0 : E) r', ∀
    n, «expr ≤ »(«expr∥ ∥»(«expr - »(f «expr + »(x, y), p.partial_sum n y)), «expr * »(C, «expr ^ »(a, n))))],
  from [expr hf.uniform_geometric_approx h],
  refine [expr metric.tendsto_uniformly_on_iff.2 (λ ε εpos, _)],
  have [ident L] [":", expr tendsto (λ
    n, «expr * »((C : exprℝ()), «expr ^ »(a, n))) at_top (expr𝓝() «expr * »((C : exprℝ()), 0))] [":=", expr tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 ha.1.le ha.2)],
  rw [expr mul_zero] ["at", ident L],
  refine [expr (L.eventually (gt_mem_nhds εpos)).mono (λ n hn y hy, _)],
  rw [expr dist_eq_norm] [],
  exact [expr (hp y hy n).trans_lt hn]
end

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partial_sum n y` there. -/
theorem has_fpower_series_on_ball.tendsto_locally_uniformly_on
(hf : has_fpower_series_on_ball f p x r) : tendsto_locally_uniformly_on (λ
 n y, p.partial_sum n y) (λ y, f «expr + »(x, y)) at_top (emetric.ball (0 : E) r) :=
begin
  assume [binders (u hu x hx)],
  rcases [expr ennreal.lt_iff_exists_nnreal_btwn.1 hx, "with", "⟨", ident r', ",", ident xr', ",", ident hr', "⟩"],
  have [] [":", expr «expr ∈ »(emetric.ball (0 : E) r', expr𝓝() x)] [":=", expr is_open.mem_nhds emetric.is_open_ball xr'],
  refine [expr ⟨emetric.ball (0 : E) r', mem_nhds_within_of_mem_nhds this, _⟩],
  simpa [] [] [] ["[", expr metric.emetric_ball_nnreal, "]"] [] ["using", expr hf.tendsto_uniformly_on hr' u hu]
end

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partial_sum n (y - x)` there. -/
theorem HasFpowerSeriesOnBall.tendsto_uniformly_on' {r' :  ℝ≥0 } (hf : HasFpowerSeriesOnBall f p x r)
  (h : (r' : ℝ≥0∞) < r) : TendstoUniformlyOn (fun n y => p.partial_sum n (y - x)) f at_top (Metric.Ball (x : E) r') :=
  by 
    convert (hf.tendsto_uniformly_on h).comp fun y => y - x
    ·
      simp [· ∘ ·]
    ·
      ext z 
      simp [dist_eq_norm]

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the  partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partial_sum n (y - x)` there. -/
theorem has_fpower_series_on_ball.tendsto_locally_uniformly_on'
(hf : has_fpower_series_on_ball f p x r) : tendsto_locally_uniformly_on (λ
 n y, p.partial_sum n «expr - »(y, x)) f at_top (emetric.ball (x : E) r) :=
begin
  have [ident A] [":", expr continuous_on (λ
    y : E, «expr - »(y, x)) (emetric.ball (x : E) r)] [":=", expr (continuous_id.sub continuous_const).continuous_on],
  convert [] [expr hf.tendsto_locally_uniformly_on.comp (λ y : E, «expr - »(y, x)) _ A] [],
  { ext [] [ident z] [],
    simp [] [] [] [] [] [] },
  { assume [binders (z)],
    simp [] [] [] ["[", expr edist_eq_coe_nnnorm, ",", expr edist_eq_coe_nnnorm_sub, "]"] [] [] }
end

/-- If a function admits a power series expansion on a disk, then it is continuous there. -/
protected theorem HasFpowerSeriesOnBall.continuous_on (hf : HasFpowerSeriesOnBall f p x r) :
  ContinuousOn f (Emetric.Ball x r) :=
  hf.tendsto_locally_uniformly_on'.continuous_on$
    eventually_of_forall$ fun n => ((p.partial_sum_continuous n).comp (continuous_id.sub continuous_const)).ContinuousOn

protected theorem HasFpowerSeriesAt.continuous_at (hf : HasFpowerSeriesAt f p x) : ContinuousAt f x :=
  let ⟨r, hr⟩ := hf 
  hr.continuous_on.continuous_at (Emetric.ball_mem_nhds x hr.r_pos)

protected theorem AnalyticAt.continuous_at (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨p, hp⟩ := hf 
  hp.continuous_at

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected theorem FormalMultilinearSeries.has_fpower_series_on_ball [CompleteSpace F]
  (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) : HasFpowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_reflₓ _, r_pos := h,
    HasSum :=
      fun y hy =>
        by 
          rw [zero_addₓ]
          exact p.has_sum hy }

theorem HasFpowerSeriesOnBall.sum [CompleteSpace F] (h : HasFpowerSeriesOnBall f p x r) {y : E}
  (hy : y ∈ Emetric.Ball (0 : E) r) : f (x+y) = p.sum y :=
  (h.has_sum hy).unique (p.has_sum (lt_of_lt_of_leₓ hy h.r_le))

/-- The sum of a converging power series is continuous in its disk of convergence. -/
protected theorem FormalMultilinearSeries.continuous_on [CompleteSpace F] :
  ContinuousOn p.sum (Emetric.Ball 0 p.radius) :=
  by 
    cases' (zero_le p.radius).eq_or_lt with h h
    ·
      simp [←h, continuous_on_empty]
    ·
      exact (p.has_fpower_series_on_ball h).ContinuousOn

end 

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

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R :  ℝ≥0 }

/-- A term of `formal_multilinear_series.change_origin_series`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. Each term of `p.change_origin x`
is itself an analytic function of `x` given by the series `p.change_origin_series`. Each term in
`change_origin_series` is the sum of `change_origin_series_term`'s over all `s` of cardinality `l`.
-/
def change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) : E[×l]→L[𝕜] E[×k]→L[𝕜] F :=
  ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by 
      erw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
    (p$ k+l)

theorem change_origin_series_term_apply (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) (x y : E) :
  (p.change_origin_series_term k l s hs (fun _ => x) fun _ => y) = p (k+l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curry_fin_finset_apply_const _ _ _ _ _

@[simp]
theorem norm_change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) :
  ∥p.change_origin_series_term k l s hs∥ = ∥p (k+l)∥ :=
  by 
    simp only [change_origin_series_term, LinearIsometryEquiv.norm_map]

@[simp]
theorem nnnorm_change_origin_series_term (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) :
  ∥p.change_origin_series_term k l s hs∥₊ = ∥p (k+l)∥₊ :=
  by 
    simp only [change_origin_series_term, LinearIsometryEquiv.nnnorm_map]

theorem nnnorm_change_origin_series_term_apply_le (k l : ℕ) (s : Finset (Finₓ (k+l))) (hs : s.card = l) (x y : E) :
  ∥p.change_origin_series_term k l s hs (fun _ => x) fun _ => y∥₊ ≤ (∥p (k+l)∥₊*∥x∥₊ ^ l)*∥y∥₊ ^ k :=
  by 
    rw [←p.nnnorm_change_origin_series_term k l s hs, ←Finₓ.prod_const, ←Finₓ.prod_const]
    apply ContinuousMultilinearMap.le_of_op_nnnorm_le 
    apply ContinuousMultilinearMap.le_op_nnnorm

/-- The power series for `f.change_origin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.change_origin x` is a formal multilinear series such that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense. -/
def change_origin_series (k : ℕ) : FormalMultilinearSeries 𝕜 E (E[×k]→L[𝕜] F) :=
  fun l => ∑s : { s : Finset (Finₓ (k+l)) // Finset.card s = l }, p.change_origin_series_term k l s s.2

theorem nnnorm_change_origin_series_le_tsum (k l : ℕ) :
  ∥p.change_origin_series k l∥₊ ≤ ∑'x : { s : Finset (Finₓ (k+l)) // s.card = l }, ∥p (k+l)∥₊ :=
  (nnnorm_sum_le _ _).trans_eq$
    by 
      simp only [tsum_fintype, nnnorm_change_origin_series_term]

theorem nnnorm_change_origin_series_apply_le_tsum (k l : ℕ) (x : E) :
  ∥p.change_origin_series k l fun _ => x∥₊ ≤ ∑'s : { s : Finset (Finₓ (k+l)) // s.card = l }, ∥p (k+l)∥₊*∥x∥₊ ^ l :=
  by 
    rw [Nnreal.tsum_mul_right, ←Finₓ.prod_const]
    exact (p.change_origin_series k l).le_of_op_nnnorm_le _ (p.nnnorm_change_origin_series_le_tsum _ _)

/--
Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.change_origin x).sum y` when this makes sense.
-/
def change_origin (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun k => (p.change_origin_series k).Sum x

/-- An auxiliary equivalence useful in the proofs about
`formal_multilinear_series.change_origin_series`: the set of triples `(k, l, s)`, where `s` is a
`finset (fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`finset (fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - finset.card s, finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps]
def change_origin_index_equiv : (Σk l : ℕ, { s : Finset (Finₓ (k+l)) // s.card = l }) ≃ Σn : ℕ, Finset (Finₓ n) :=
  { toFun := fun s => ⟨s.1+s.2.1, s.2.2⟩,
    invFun :=
      fun s =>
        ⟨s.1 - s.2.card, s.2.card,
          ⟨s.2.map (Finₓ.cast$ (tsub_add_cancel_of_le$ card_finset_fin_le s.2).symm).toEquiv.toEmbedding,
            Finset.card_map _⟩⟩,
    left_inv :=
      by 
        rintro ⟨k, l, ⟨s : Finset (Finₓ$ k+l), hs : s.card = l⟩⟩
        dsimp only [Subtype.coe_mk]
        suffices  :
          ∀ k' l',
            k' = k →
              l' = l →
                ∀ hkl : (k+l) = k'+l' hs',
                  (⟨k', l', ⟨Finset.map (Finₓ.cast hkl).toEquiv.toEmbedding s, hs'⟩⟩ :
                    Σk l : ℕ, { s : Finset (Finₓ (k+l)) // s.card = l }) =
                    ⟨k, l, ⟨s, hs⟩⟩
        ·
          apply this <;> simp only [hs, add_tsub_cancel_right]
        rintro _ _ rfl rfl hkl hs' 
        simp only [Equiv.refl_to_embedding, Finₓ.cast_refl, Finset.map_refl, eq_self_iff_true, OrderIso.refl_to_equiv,
          and_selfₓ, heq_iff_eq],
    right_inv :=
      by 
        rintro ⟨n, s⟩
        simp [tsub_add_cancel_of_le (card_finset_fin_le s), Finₓ.cast_to_equiv] }

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem change_origin_series_summable_aux₁
{r r' : «exprℝ≥0»()}
(hr : «expr < »((«expr + »(r, r') : «exprℝ≥0∞»()), p.radius)) : summable (λ
 s : «exprΣ , »((k
   l : exprℕ()), {s : finset (fin «expr + »(k, l)) // «expr = »(s.card, l)}), «expr * »(«expr * »(«expr∥ ∥₊»(p «expr + »(s.1, s.2.1)), «expr ^ »(r, s.2.1)), «expr ^ »(r', s.1))) :=
begin
  rw ["<-", expr change_origin_index_equiv.symm.summable_iff] [],
  dsimp ["only"] ["[", expr («expr ∘ »), ",", expr change_origin_index_equiv_symm_apply_fst, ",", expr change_origin_index_equiv_symm_apply_snd_fst, "]"] [] [],
  have [] [":", expr ∀
   n : exprℕ(), has_sum (λ
    s : finset (fin n), «expr * »(«expr * »(«expr∥ ∥₊»(p «expr + »(«expr - »(n, s.card), s.card)), «expr ^ »(r, s.card)), «expr ^ »(r', «expr - »(n, s.card)))) «expr * »(«expr∥ ∥₊»(p n), «expr ^ »(«expr + »(r, r'), n))] [],
  { intro [ident n],
    convert_to [expr has_sum (λ
      s : finset (fin n), «expr * »(«expr∥ ∥₊»(p n), «expr * »(«expr ^ »(r, s.card), «expr ^ »(r', «expr - »(n, s.card))))) _] [],
    { ext1 [] [ident s],
      rw ["[", expr tsub_add_cancel_of_le (card_finset_fin_le _), ",", expr mul_assoc, "]"] [] },
    rw ["<-", expr fin.sum_pow_mul_eq_add_pow] [],
    exact [expr (has_sum_fintype _).mul_left _] },
  refine [expr nnreal.summable_sigma.2 ⟨λ n, (this n).summable, _⟩],
  simp [] [] ["only"] ["[", expr (this _).tsum_eq, "]"] [] [],
  exact [expr p.summable_nnnorm_mul_pow hr]
end

theorem change_origin_series_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
  Summable fun s : Σl : ℕ, { s : Finset (Finₓ (k+l)) // s.card = l } => ∥p (k+s.1)∥₊*r ^ s.1 :=
  by 
    rcases Ennreal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
    simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
      ((Nnreal.summable_sigma.1 (p.change_origin_series_summable_aux₁ hr')).1 k).mul_right ((r' ^ k)⁻¹)

theorem change_origin_series_summable_aux₃ {r :  ℝ≥0 } (hr : «expr↑ » r < p.radius) (k : ℕ) :
  Summable fun l : ℕ => ∥p.change_origin_series k l∥₊*r ^ l :=
  by 
    refine' Nnreal.summable_of_le (fun n => _) (Nnreal.summable_sigma.1$ p.change_origin_series_summable_aux₂ hr k).2
    simp only [Nnreal.tsum_mul_right]
    exact mul_le_mul' (p.nnnorm_change_origin_series_le_tsum _ _) le_rfl

theorem le_change_origin_series_radius (k : ℕ) : p.radius ≤ (p.change_origin_series k).radius :=
  Ennreal.le_of_forall_nnreal_lt$ fun r hr => le_radius_of_summable_nnnorm _ (p.change_origin_series_summable_aux₃ hr k)

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nnnorm_change_origin_le
(k : exprℕ())
(h : «expr < »((«expr∥ ∥₊»(x) : «exprℝ≥0∞»()), p.radius)) : «expr ≤ »(«expr∥ ∥₊»(p.change_origin x k), «expr∑' , »((s : «exprΣ , »((l : exprℕ()), {s : finset (fin «expr + »(k, l)) // «expr = »(s.card, l)})), «expr * »(«expr∥ ∥₊»(p «expr + »(k, s.1)), «expr ^ »(«expr∥ ∥₊»(x), s.1)))) :=
begin
  refine [expr tsum_of_nnnorm_bounded _ (λ l, p.nnnorm_change_origin_series_apply_le_tsum k l x)],
  have [] [] [":=", expr p.change_origin_series_summable_aux₂ h k],
  refine [expr has_sum.sigma this.has_sum (λ l, _)],
  exact [expr ((nnreal.summable_sigma.1 this).1 l).has_sum]
end

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The radius of convergence of `p.change_origin x` is at least `p.radius - ∥x∥`. In other words,
`p.change_origin x` is well defined on the largest ball contained in the original ball of
convergence.-/
theorem change_origin_radius : «expr ≤ »(«expr - »(p.radius, «expr∥ ∥₊»(x)), (p.change_origin x).radius) :=
begin
  refine [expr ennreal.le_of_forall_pos_nnreal_lt (λ r h0 hr, _)],
  rw ["[", expr lt_tsub_iff_right, ",", expr add_comm, "]"] ["at", ident hr],
  have [ident hr'] [":", expr «expr < »((«expr∥ ∥₊»(x) : «exprℝ≥0∞»()), p.radius)] [],
  from [expr (le_add_right le_rfl).trans_lt hr],
  apply [expr le_radius_of_summable_nnnorm],
  have [] [":", expr ∀
   k : exprℕ(), «expr ≤ »(«expr * »(«expr∥ ∥₊»(p.change_origin x k), «expr ^ »(r, k)), «expr * »(«expr∑' , »((s : «exprΣ , »((l : exprℕ()), {s : finset (fin «expr + »(k, l)) // «expr = »(s.card, l)})), «expr * »(«expr∥ ∥₊»(p «expr + »(k, s.1)), «expr ^ »(«expr∥ ∥₊»(x), s.1))), «expr ^ »(r, k)))] [],
  from [expr λ k, mul_le_mul_right' (p.nnnorm_change_origin_le k hr') «expr ^ »(r, k)],
  refine [expr nnreal.summable_of_le this _],
  simpa [] [] ["only"] ["[", "<-", expr nnreal.tsum_mul_right, "]"] [] ["using", expr (nnreal.summable_sigma.1 (p.change_origin_series_summable_aux₁ hr)).2]
end

end 

variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r R :  ℝ≥0 }

theorem has_fpower_series_on_ball_change_origin (k : ℕ) (hr : 0 < p.radius) :
  HasFpowerSeriesOnBall (fun x => p.change_origin x k) (p.change_origin_series k) 0 p.radius :=
  have  := p.le_change_origin_series_radius k
  ((p.change_origin_series k).HasFpowerSeriesOnBall (hr.trans_le this)).mono hr this

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Summing the series `p.change_origin x` at a point `y` gives back `p (x + y)`-/
theorem change_origin_eval
(h : «expr < »((«expr + »(«expr∥ ∥₊»(x), «expr∥ ∥₊»(y)) : «exprℝ≥0∞»()), p.radius)) : «expr = »((p.change_origin x).sum y, p.sum «expr + »(x, y)) :=
begin
  have [ident radius_pos] [":", expr «expr < »(0, p.radius)] [":=", expr lt_of_le_of_lt (zero_le _) h],
  have [ident x_mem_ball] [":", expr «expr ∈ »(x, emetric.ball (0 : E) p.radius)] [],
  from [expr mem_emetric_ball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)],
  have [ident y_mem_ball] [":", expr «expr ∈ »(y, emetric.ball (0 : E) (p.change_origin x).radius)] [],
  { refine [expr mem_emetric_ball_zero_iff.2 (lt_of_lt_of_le _ p.change_origin_radius)],
    rwa ["[", expr lt_tsub_iff_right, ",", expr add_comm, "]"] [] },
  have [ident x_add_y_mem_ball] [":", expr «expr ∈ »(«expr + »(x, y), emetric.ball (0 : E) p.radius)] [],
  { refine [expr mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt _ h)],
    exact_mod_cast [expr nnnorm_add_le x y] },
  set [] [ident f] [":", expr «exprΣ , »((k
     l : exprℕ()), {s : finset (fin «expr + »(k, l)) // «expr = »(s.card, l)}) → F] [":="] [expr λ
   s, p.change_origin_series_term s.1 s.2.1 s.2.2 s.2.2.2 (λ _, x) (λ _, y)] [],
  have [ident hsf] [":", expr summable f] [],
  { refine [expr summable_of_nnnorm_bounded _ (p.change_origin_series_summable_aux₁ h) _],
    rintro ["⟨", ident k, ",", ident l, ",", ident s, ",", ident hs, "⟩"],
    dsimp ["only"] ["[", expr subtype.coe_mk, "]"] [] [],
    exact [expr p.nnnorm_change_origin_series_term_apply_le _ _ _ _ _ _] },
  have [ident hf] [":", expr has_sum f ((p.change_origin x).sum y)] [],
  { refine [expr has_sum.sigma_of_has_sum ((p.change_origin x).summable y_mem_ball).has_sum (λ k, _) hsf],
    { dsimp ["only"] ["[", expr f, "]"] [] [],
      refine [expr continuous_multilinear_map.has_sum_eval _ _],
      have [] [] [":=", expr (p.has_fpower_series_on_ball_change_origin k radius_pos).has_sum x_mem_ball],
      rw [expr zero_add] ["at", ident this],
      refine [expr has_sum.sigma_of_has_sum this (λ l, _) _],
      { simp [] [] ["only"] ["[", expr change_origin_series, ",", expr continuous_multilinear_map.sum_apply, "]"] [] [],
        apply [expr has_sum_fintype] },
      { refine [expr summable_of_nnnorm_bounded _ (p.change_origin_series_summable_aux₂ (mem_emetric_ball_zero_iff.1 x_mem_ball) k) (λ
          s, _)],
        refine [expr (continuous_multilinear_map.le_op_nnnorm _ _).trans_eq _],
        simp [] [] [] [] [] [] } } },
  refine [expr hf.unique (change_origin_index_equiv.symm.has_sum_iff.1 _)],
  refine [expr has_sum.sigma_of_has_sum (p.has_sum x_add_y_mem_ball) (λ
    n, _) (change_origin_index_equiv.symm.summable_iff.2 hsf)],
  erw ["[", expr (p n).map_add_univ (λ _, x) (λ _, y), "]"] [],
  convert [] [expr has_sum_fintype _] [],
  ext1 [] [ident s],
  dsimp ["only"] ["[", expr f, ",", expr change_origin_series_term, ",", expr («expr ∘ »), ",", expr change_origin_index_equiv_symm_apply_fst, ",", expr change_origin_index_equiv_symm_apply_snd_fst, ",", expr change_origin_index_equiv_symm_apply_snd_snd_coe, "]"] [] [],
  rw [expr continuous_multilinear_map.curry_fin_finset_apply_const] [],
  have [] [":", expr ∀
   (m)
   (hm : «expr = »(n, m)), «expr = »(p n (s.piecewise (λ
      _, x) (λ _, y)), p m ((s.map (fin.cast hm).to_equiv.to_embedding).piecewise (λ _, x) (λ _, y)))] [],
  { rintro [ident m, ident rfl],
    simp [] [] [] [] [] [],
    congr },
  apply [expr this]
end

end FormalMultilinearSeries

section 

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x y : E} {r : ℝ≥0∞}

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.change_origin`.
-/
theorem HasFpowerSeriesOnBall.change_origin (hf : HasFpowerSeriesOnBall f p x r) (h : (∥y∥₊ : ℝ≥0∞) < r) :
  HasFpowerSeriesOnBall f (p.change_origin y) (x+y) (r - ∥y∥₊) :=
  { r_le :=
      by 
        apply le_transₓ _ p.change_origin_radius 
        exact tsub_le_tsub hf.r_le (le_reflₓ _),
    r_pos :=
      by 
        simp [h],
    HasSum :=
      fun z hz =>
        by 
          convert (p.change_origin y).HasSum _
          ·
            rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_commₓ] at hz 
            rw [p.change_origin_eval (hz.trans_le hf.r_le), add_assocₓ, hf.sum]
            refine' mem_emetric_ball_zero_iff.2 (lt_of_le_of_ltₓ _ hz)
            exactModCast nnnorm_add_le y z
          ·
            refine' Emetric.ball_subset_ball (le_transₓ _ p.change_origin_radius) hz 
            exact tsub_le_tsub hf.r_le le_rfl }

-- error in Analysis.Analytic.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
theorem has_fpower_series_on_ball.analytic_at_of_mem
(hf : has_fpower_series_on_ball f p x r)
(h : «expr ∈ »(y, emetric.ball x r)) : analytic_at 𝕜 f y :=
begin
  have [] [":", expr «expr < »((«expr∥ ∥₊»(«expr - »(y, x)) : «exprℝ≥0∞»()), r)] [],
  by simpa [] [] [] ["[", expr edist_eq_coe_nnnorm_sub, "]"] [] ["using", expr h],
  have [] [] [":=", expr hf.change_origin this],
  rw ["[", expr add_sub_cancel'_right, "]"] ["at", ident this],
  exact [expr this.analytic_at]
end

variable (𝕜 f)

/-- For any function `f` from a normed vector space to a Banach space, the set of points `x` such
that `f` is analytic at `x` is open. -/
theorem is_open_analytic_at : IsOpen { x | AnalyticAt 𝕜 f x } :=
  by 
    rw [is_open_iff_mem_nhds]
    rintro x ⟨p, r, hr⟩
    exact mem_of_superset (Emetric.ball_mem_nhds _ hr.r_pos) fun y hy => hr.analytic_at_of_mem hy

end 

