/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathbin.Analysis.Calculus.Deriv
import Mathbin.MeasureTheory.Constructions.BorelSpace
import Mathbin.MeasureTheory.Function.StronglyMeasurable
import Mathbin.Tactic.RingExp

/-!
# Derivative is measurable

In this file we prove that the derivative of any function with complete codomain is a measurable
function. Namely, we prove:

* `measurable_set_of_differentiable_at`: the set `{x | differentiable_at 𝕜 f x}` is measurable;
* `measurable_fderiv`: the function `fderiv 𝕜 f` is measurable;
* `measurable_fderiv_apply_const`: for a fixed vector `y`, the function `λ x, fderiv 𝕜 f x y`
  is measurable;
* `measurable_deriv`: the function `deriv f` is measurable (for `f : 𝕜 → F`).

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map `L`, up to `ε r`. It is an open set.
Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`: we require that at two possibly different
scales `r` and `s`, the function is well approximated by the linear map `L`. It is also open.

We claim that the differentiability set of `f` is exactly
`D = ⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, we require that there is a size `δ` such that, for any two scales
below this size, the function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to `D` (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_set_subset_D`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`∥L - L'∥` is bounded by `ε` (see `norm_sub_le_of_mem_A`). Assume now `x ∈ D`. If one has two maps
`L` and `L'` such that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is
close to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a
linear map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to `D`). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.

To show that the derivative itself is measurable, add in the definition of `B` and `D` a set
`K` of continuous linear maps to which `L` should belong. Then, when `K` is complete, the set `D K`
is exactly the set of points where `f` is differentiable with a derivative in `K`.

## Tags

derivative, measurable function, Borel σ-algebra
-/


noncomputable section

open Set Metric Asymptotics Filter ContinuousLinearMap

open TopologicalSpace (SecondCountableTopology)

open MeasureTheory

open TopologicalSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type _} [NondiscreteNormedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E] [NormedGroup F] [NormedSpace 𝕜 F]

theorem measurable_apply₂ [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    [SecondCountableTopology (E →L[𝕜] F)] [MeasurableSpace F] [BorelSpace F] :
    Measurable fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  is_bounded_bilinear_map_apply.Continuous.Measurable

end ContinuousLinearMap

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedGroup F] [NormedSpace 𝕜 F]

variable {f : E → F} (K : Set (E →L[𝕜] F))

namespace FderivMeasurableAux

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (y z «expr ∈ » ball x r')
/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set.-/
def A (f : E → F) (L : E →L[𝕜] F) (r ε : ℝ) : Set E :=
  { x | ∃ r' ∈ Ioc (r / 2) r, ∀ y z _ : y ∈ Ball x r' _ : z ∈ Ball x r', ∥f z - f y - L (z - y)∥ ≤ ε * r }

/-- The set `B f K r s ε` is the set of points `x` around which there exists a continuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates well the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`. -/
def B (f : E → F) (K : Set (E →L[𝕜] F)) (r s ε : ℝ) : Set E :=
  ⋃ L ∈ K, A f L r ε ∩ A f L s ε

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
def D (f : E → F) (K : Set (E →L[𝕜] F)) : Set E :=
  ⋂ e : ℕ, ⋃ n : ℕ, ⋂ (p ≥ n) (q ≥ n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)

theorem is_open_A (L : E →L[𝕜] F) (r ε : ℝ) : IsOpen (A f L r ε) := by
  rw [Metric.is_open_iff]
  rintro x ⟨r', r'_mem, hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : ∃ s : ℝ, r / 2 < s ∧ s < r' := exists_between r'_mem.1
  have : s ∈ Ioc (r / 2) r := ⟨s_gt, le_of_ltₓ (s_lt.trans_le r'_mem.2)⟩
  refine'
    ⟨r' - s, by
      linarith, fun x' hx' => ⟨s, this, _⟩⟩
  have B : ball x' s ⊆ ball x r' := ball_subset (le_of_ltₓ hx')
  intro y hy z hz
  exact hr' y (B hy) z (B hz)

theorem is_open_B {K : Set (E →L[𝕜] F)} {r s ε : ℝ} : IsOpen (B f K r s ε) := by
  simp [B, is_open_Union, IsOpen.inter, is_open_A]

theorem A_mono (L : E →L[𝕜] F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) : A f L r ε ⊆ A f L r δ := by
  rintro x ⟨r', r'r, hr'⟩
  refine' ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h _)⟩
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x]

theorem le_of_mem_A {r ε : ℝ} {L : E →L[𝕜] F} {x : E} (hx : x ∈ A f L r ε) {y z : E} (hy : y ∈ ClosedBall x (r / 2))
    (hz : z ∈ ClosedBall x (r / 2)) : ∥f z - f y - L (z - y)∥ ≤ ε * r := by
  rcases hx with ⟨r', r'mem, hr'⟩
  exact hr' _ ((mem_closed_ball.1 hy).trans_lt r'mem.1) _ ((mem_closed_ball.1 hz).trans_lt r'mem.1)

theorem mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : E} (hx : DifferentiableAt 𝕜 f x) :
    ∃ R > 0, ∀, ∀ r ∈ Ioo (0 : ℝ) R, ∀, x ∈ A f (fderiv 𝕜 f x) r ε := by
  have := hx.has_fderiv_at
  simp only [HasFderivAt, HasFderivAtFilter, is_o_iff] at this
  rcases eventually_nhds_iff_ball.1 (this (half_pos hε)) with ⟨R, R_pos, hR⟩
  refine' ⟨R, R_pos, fun r hr => _⟩
  have : r ∈ Ioc (r / 2) r := ⟨half_lt_self hr.1, le_rfl⟩
  refine' ⟨r, this, fun y hy z hz => _⟩
  calc
    ∥f z - f y - (fderiv 𝕜 f x) (z - y)∥ =
        ∥f z - f x - (fderiv 𝕜 f x) (z - x) - (f y - f x - (fderiv 𝕜 f x) (y - x))∥ :=
      by
      congr 1
      simp only [ContinuousLinearMap.map_sub]
      abel _ ≤ ∥f z - f x - (fderiv 𝕜 f x) (z - x)∥ + ∥f y - f x - (fderiv 𝕜 f x) (y - x)∥ :=
      norm_sub_le _ _ _ ≤ ε / 2 * ∥z - x∥ + ε / 2 * ∥y - x∥ :=
      add_le_add (hR _ (lt_transₓ (mem_ball.1 hz) hr.2))
        (hR _ (lt_transₓ (mem_ball.1 hy) hr.2))_ ≤ ε / 2 * r + ε / 2 * r :=
      add_le_add (mul_le_mul_of_nonneg_left (le_of_ltₓ (mem_ball_iff_norm.1 hz)) (le_of_ltₓ (half_pos hε)))
        (mul_le_mul_of_nonneg_left (le_of_ltₓ (mem_ball_iff_norm.1 hy)) (le_of_ltₓ (half_pos hε)))_ = ε * r :=
      by
      ring

theorem norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ∥c∥) {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) {x : E} {L₁ L₂ : E →L[𝕜] F}
    (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : ∥L₁ - L₂∥ ≤ 4 * ∥c∥ * ε := by
  have : 0 ≤ 4 * ∥c∥ * ε :=
    mul_nonneg
      (mul_nonneg
        (by
          norm_num : (0 : ℝ) ≤ 4)
        (norm_nonneg _))
      hε.le
  refine' op_norm_le_of_shell (half_pos hr) this hc _
  intro y ley ylt
  rw [div_div_eq_div_mul,
    div_le_iff'
      (mul_pos
        (by
          norm_num : (0 : ℝ) < 2)
        (zero_lt_one.trans hc))] at
    ley
  calc ∥(L₁ - L₂) y∥ = ∥f (x + y) - f x - L₂ (x + y - x) - (f (x + y) - f x - L₁ (x + y - x))∥ := by
      simp _ ≤ ∥f (x + y) - f x - L₂ (x + y - x)∥ + ∥f (x + y) - f x - L₁ (x + y - x)∥ :=
      norm_sub_le _ _ _ ≤ ε * r + ε * r := by
      apply add_le_add
      · apply le_of_mem_A h₂
        · simp only [le_of_ltₓ (half_pos hr), mem_closed_ball, dist_self]
          
        · simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, ylt.le]
          
        
      · apply le_of_mem_A h₁
        · simp only [le_of_ltₓ (half_pos hr), mem_closed_ball, dist_self]
          
        · simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, ylt.le]
          
        _ = 2 * ε * r :=
      by
      ring _ ≤ 2 * ε * (2 * ∥c∥ * ∥y∥) :=
      mul_le_mul_of_nonneg_left ley
        (mul_nonneg
          (by
            norm_num)
          hε.le)_ = 4 * ∥c∥ * ε * ∥y∥ :=
      by
      ring

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
theorem differentiable_set_subset_D : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } ⊆ D f K := by
  intro x hx
  rw [D, mem_Inter]
  intro e
  have : (0 : ℝ) < (1 / 2) ^ e :=
    pow_pos
      (by
        norm_num)
      _
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos
      (by
        norm_num : (1 : ℝ) / 2 < 1)
  simp only [mem_Union, mem_Inter, B, mem_inter_eq]
  refine' ⟨n, fun p hp q hq => ⟨fderiv 𝕜 f x, hx.2, ⟨_, _⟩⟩⟩ <;>
    · refine'
        hR _
          ⟨pow_pos
              (by
                norm_num)
              _,
            lt_of_le_of_ltₓ _ hn⟩
      exact
        pow_le_pow_of_le_one
          (by
            norm_num)
          (by
            norm_num)
          (by
            assumption)
      

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:53:9: parse error
/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
theorem D_subset_differentiable_set {K : Set (E →L[𝕜] F)} (hK : IsComplete K) :
    D f K ⊆ { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } := by
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1 / 2) ^ n :=
    pow_pos
      (by
        norm_num)
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have cpos : 0 < ∥c∥ := lt_transₓ zero_lt_one hc
  intro x hx
  have :
    ∀ e : ℕ,
      ∃ n : ℕ,
        ∀ p q, n ≤ p → n ≤ q → ∃ L ∈ K, x ∈ A f L ((1 / 2) ^ p) ((1 / 2) ^ e) ∩ A f L ((1 / 2) ^ q) ((1 / 2) ^ e) :=
    by
    intro e
    have := mem_Inter.1 hx e
    rcases mem_Union.1 this with ⟨n, hn⟩
    refine' ⟨n, fun p q hp hq => _⟩
    simp only [mem_Inter, ge_iff_le] at hn
    rcases mem_Union.1 (hn p hp q hq) with ⟨L, hL⟩
    exact ⟨L, mem_Union.1 hL⟩
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
    such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
    `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
      that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
      scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
      `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
      `2 ^ (- p')`. -/
  have M :
    ∀ e p q e' p' q',
      n e ≤ p → n e ≤ q → n e' ≤ p' → n e' ≤ q' → e ≤ e' → ∥L e p q - L e' p' q'∥ ≤ 12 * ∥c∥ * (1 / 2) ^ e :=
    by
    intro e p q e' p' q' hp hq hp' hq' he'
    let r := max (n e) (n e')
    have I : ((1 : ℝ) / 2) ^ e' ≤ (1 / 2) ^ e :=
      pow_le_pow_of_le_one
        (by
          norm_num)
        (by
          norm_num)
        he'
    have J1 : ∥L e p q - L e p r∥ ≤ 4 * ∥c∥ * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e p q) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p q hp hq).2.1
      have I2 : x ∈ A f (L e p r) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p r hp (le_max_leftₓ _ _)).2.1
      exact norm_sub_le_of_mem_A hc P P I1 I2
    have J2 : ∥L e p r - L e' p' r∥ ≤ 4 * ∥c∥ * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e p r) ((1 / 2) ^ r) ((1 / 2) ^ e) := (hn e p r hp (le_max_leftₓ _ _)).2.2
      have I2 : x ∈ A f (L e' p' r) ((1 / 2) ^ r) ((1 / 2) ^ e') := (hn e' p' r hp' (le_max_rightₓ _ _)).2.2
      exact norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ I I2)
    have J3 : ∥L e' p' r - L e' p' q'∥ ≤ 4 * ∥c∥ * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e' p' r) ((1 / 2) ^ p') ((1 / 2) ^ e') := (hn e' p' r hp' (le_max_rightₓ _ _)).2.1
      have I2 : x ∈ A f (L e' p' q') ((1 / 2) ^ p') ((1 / 2) ^ e') := (hn e' p' q' hp' hq').2.1
      exact norm_sub_le_of_mem_A hc P P (A_mono _ _ I I1) (A_mono _ _ I I2)
    calc ∥L e p q - L e' p' q'∥ = ∥L e p q - L e p r + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')∥ := by
        congr 1
        abel _ ≤ ∥L e p q - L e p r∥ + ∥L e p r - L e' p' r∥ + ∥L e' p' r - L e' p' q'∥ :=
        le_transₓ (norm_add_le _ _)
          (add_le_add_right (norm_add_le _ _)
            _)_ ≤ 4 * ∥c∥ * (1 / 2) ^ e + 4 * ∥c∥ * (1 / 2) ^ e + 4 * ∥c∥ * (1 / 2) ^ e :=
        by
        apply_rules [add_le_add]_ = 12 * ∥c∥ * (1 / 2) ^ e := by
        ring
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
    is a Cauchy sequence. -/
  let L0 : ℕ → E →L[𝕜] F := fun e => L e (n e) (n e)
  have : CauchySeq L0 := by
    rw [Metric.cauchy_seq_iff']
    intro ε εpos
    obtain ⟨e, he⟩ : ∃ e : ℕ, (1 / 2) ^ e < ε / (12 * ∥c∥) :=
      exists_pow_lt_of_lt_one
        (div_pos εpos
          (mul_pos
            (by
              norm_num)
            cpos))
        (by
          norm_num)
    refine' ⟨e, fun e' he' => _⟩
    rw [dist_comm, dist_eq_norm]
    calc ∥L0 e - L0 e'∥ ≤ 12 * ∥c∥ * (1 / 2) ^ e :=
        M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he' _ < 12 * ∥c∥ * (ε / (12 * ∥c∥)) :=
        mul_lt_mul' le_rfl he (le_of_ltₓ P)
          (mul_pos
            (by
              norm_num)
            cpos)_ = ε :=
        by
        field_simp [(by
            norm_num : (12 : ℝ) ≠ 0),
          ne_of_gtₓ cpos]
        ring
  -- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.
  obtain ⟨f', f'K, hf'⟩ : ∃ f' ∈ K, tendsto L0 at_top (𝓝 f') :=
    cauchy_seq_tendsto_of_is_complete hK (fun e => (hn e (n e) (n e) le_rfl le_rfl).1) this
  have Lf' : ∀ e p, n e ≤ p → ∥L e (n e) p - f'∥ ≤ 12 * ∥c∥ * (1 / 2) ^ e := by
    intro e p hp
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm
    rw [eventually_at_top]
    exact ⟨e, fun e' he' => M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩
  -- Let us show that `f` has derivative `f'` at `x`.
  have : HasFderivAt f f' x := by
    simp only [has_fderiv_at_iff_is_o_nhds_zero, is_o_iff]
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
        some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
        this makes it possible to cover all scales, and thus to obtain a good linear approximation in
        the whole ball of radius `(1/2)^(n e)`. -/
    intro ε εpos
    have pos : 0 < 4 + 12 * ∥c∥ :=
      add_pos_of_pos_of_nonneg
        (by
          norm_num)
        (mul_nonneg
          (by
            norm_num)
          (norm_nonneg _))
    obtain ⟨e, he⟩ : ∃ e : ℕ, (1 / 2) ^ e < ε / (4 + 12 * ∥c∥) :=
      exists_pow_lt_of_lt_one (div_pos εpos Pos)
        (by
          norm_num)
    rw [eventually_nhds_iff_ball]
    refine' ⟨(1 / 2) ^ (n e + 1), P, fun y hy => _⟩
    -- We need to show that `f (x + y) - f x - f' y` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `∥y∥ ∼ 2 ^ (-k)`.
    by_cases' y_pos : y = 0
    · simp [y_pos]
      
    have yzero : 0 < ∥y∥ := norm_pos_iff.mpr y_pos
    have y_lt : ∥y∥ < (1 / 2) ^ (n e + 1) := by
      simpa using mem_ball_iff_norm.1 hy
    have yone : ∥y∥ ≤ 1 :=
      le_transₓ y_lt.le
        (pow_le_one _
          (by
            norm_num)
          (by
            norm_num))
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ k : ℕ, (1 / 2) ^ (k + 1) < ∥y∥ ∧ ∥y∥ ≤ (1 / 2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone
        (by
          norm_num : (0 : ℝ) < 1 / 2)
        (by
          norm_num : (1 : ℝ) / 2 < 1)
    -- the scale is large enough (as `y` is small enough)
    have k_gt : n e < k := by
      have : ((1 : ℝ) / 2) ^ (k + 1) < (1 / 2) ^ (n e + 1) := lt_transₓ hk y_lt
      rw
        [pow_lt_pow_iff_of_lt_one
          (by
            norm_num : (0 : ℝ) < 1 / 2)
          (by
            norm_num)] at
        this
      linarith
    set m := k - 1 with hl
    have m_ge : n e ≤ m := Nat.le_pred_of_ltₓ k_gt
    have km : k = m + 1 := (Nat.succ_pred_eq_of_posₓ (lt_of_le_of_ltₓ (zero_le _) k_gt)).symm
    rw [km] at hk h'k
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J1 : ∥f (x + y) - f x - L e (n e) m (x + y - x)∥ ≤ (1 / 2) ^ e * (1 / 2) ^ m := by
      apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2
      · simp only [mem_closed_ball, dist_self]
        exact div_nonneg (le_of_ltₓ P) zero_le_two
        
      · simpa only [dist_eq_norm, add_sub_cancel', mem_closed_ball, pow_succ'ₓ, mul_one_div] using h'k
        
    have J2 : ∥f (x + y) - f x - L e (n e) m y∥ ≤ 4 * (1 / 2) ^ e * ∥y∥ :=
      calc
        ∥f (x + y) - f x - L e (n e) m y∥ ≤ (1 / 2) ^ e * (1 / 2) ^ m := by
          simpa only [add_sub_cancel'] using J1
        _ = 4 * (1 / 2) ^ e * (1 / 2) ^ (m + 2) := by
          field_simp
          ring_exp
        _ ≤ 4 * (1 / 2) ^ e * ∥y∥ :=
          mul_le_mul_of_nonneg_left (le_of_ltₓ hk)
            (mul_nonneg
              (by
                norm_num)
              (le_of_ltₓ P))
        
    -- use the previous estimates to see that `f (x + y) - f x - f' y` is small.
    calc ∥f (x + y) - f x - f' y∥ = ∥f (x + y) - f x - L e (n e) m y + (L e (n e) m - f') y∥ :=
        congr_argₓ _
          (by
            simp )_ ≤ 4 * (1 / 2) ^ e * ∥y∥ + 12 * ∥c∥ * (1 / 2) ^ e * ∥y∥ :=
        norm_add_le_of_le J2
          ((le_op_norm _ _).trans
            (mul_le_mul_of_nonneg_right (Lf' _ _ m_ge) (norm_nonneg _)))_ = (4 + 12 * ∥c∥) * ∥y∥ * (1 / 2) ^ e :=
        by
        ring _ ≤ (4 + 12 * ∥c∥) * ∥y∥ * (ε / (4 + 12 * ∥c∥)) :=
        mul_le_mul_of_nonneg_left he.le
          (mul_nonneg
            (add_nonneg
              (by
                norm_num)
              (mul_nonneg
                (by
                  norm_num)
                (norm_nonneg _)))
            (norm_nonneg _))_ = ε * ∥y∥ :=
        by
        field_simp [ne_of_gtₓ Pos]
        ring
  rw [← this.fderiv] at f'K
  exact ⟨this.differentiable_at, f'K⟩

theorem differentiable_set_eq_D (hK : IsComplete K) : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } = D f K :=
  Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end FderivMeasurableAux

open FderivMeasurableAux

variable [MeasurableSpace E] [OpensMeasurableSpace E]

variable (𝕜 f)

/-- The set of differentiability points of a function, with derivative in a given complete set,
is Borel-measurable. -/
theorem measurable_set_of_differentiable_at_of_is_complete {K : Set (E →L[𝕜] F)} (hK : IsComplete K) :
    MeasurableSet { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } := by
  simp [differentiable_set_eq_D K hK, D, is_open_B.measurable_set, MeasurableSet.Inter_Prop, MeasurableSet.Inter,
    MeasurableSet.Union]

variable [CompleteSpace F]

/-- The set of differentiability points of a function taking values in a complete space is
Borel-measurable. -/
theorem measurable_set_of_differentiable_at : MeasurableSet { x | DifferentiableAt 𝕜 f x } := by
  have : IsComplete (univ : Set (E →L[𝕜] F)) := complete_univ
  convert measurable_set_of_differentiable_at_of_is_complete 𝕜 f this
  simp

@[measurability]
theorem measurable_fderiv : Measurable (fderiv 𝕜 f) := by
  refine' measurable_of_is_closed fun s hs => _
  have :
    fderiv 𝕜 f ⁻¹' s =
      { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s } ∪
        { x | (0 : E →L[𝕜] F) ∈ s } ∩ { x | ¬DifferentiableAt 𝕜 f x } :=
    Set.ext fun x => mem_preimage.trans fderiv_mem_iff
  rw [this]
  exact
    (measurable_set_of_differentiable_at_of_is_complete _ _ hs.is_complete).union
      ((MeasurableSet.const _).inter (measurable_set_of_differentiable_at _ _).Compl)

@[measurability]
theorem measurable_fderiv_apply_const [MeasurableSpace F] [BorelSpace F] (y : E) : Measurable fun x => fderiv 𝕜 f x y :=
  (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv 𝕜 f)

variable {𝕜}

@[measurability]
theorem measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] (f : 𝕜 → F) :
    Measurable (deriv f) := by
  simpa only [fderiv_deriv] using measurable_fderiv_apply_const 𝕜 f 1

-- ././Mathport/Syntax/Translate/Basic.lean:536:16: unsupported tactic `borelize
theorem strongly_measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [SecondCountableTopology F] (f : 𝕜 → F) :
    StronglyMeasurable (deriv f) := by
  "././Mathport/Syntax/Translate/Basic.lean:536:16: unsupported tactic `borelize"
  exact (measurable_deriv f).StronglyMeasurable

theorem ae_measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] (f : 𝕜 → F)
    (μ : Measureₓ 𝕜) : AeMeasurable (deriv f) μ :=
  (measurable_deriv f).AeMeasurable

theorem ae_strongly_measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [SecondCountableTopology F]
    (f : 𝕜 → F) (μ : Measureₓ 𝕜) : AeStronglyMeasurable (deriv f) μ :=
  (strongly_measurable_deriv f).AeStronglyMeasurable

