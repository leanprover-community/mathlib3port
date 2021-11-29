import Mathbin.Analysis.Calculus.Deriv 
import Mathbin.MeasureTheory.Constructions.BorelSpace 
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


noncomputable theory

open Set Metric Asymptotics Filter ContinuousLinearMap

open topological_space(SecondCountableTopology)

open_locale TopologicalSpace

namespace ContinuousLinearMap

variable{𝕜 E F : Type _}[NondiscreteNormedField 𝕜][NormedGroup E][NormedSpace 𝕜 E][NormedGroup F][NormedSpace 𝕜 F]

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem measurable_apply₂
[measurable_space E]
[opens_measurable_space E]
[second_countable_topology E]
[second_countable_topology «expr →L[ ] »(E, 𝕜, F)]
[measurable_space F]
[borel_space F] : measurable (λ p : «expr × »(«expr →L[ ] »(E, 𝕜, F), E), p.1 p.2) :=
is_bounded_bilinear_map_apply.continuous.measurable

end ContinuousLinearMap

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

variable{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

variable{f : E → F}(K : Set (E →L[𝕜] F))

namespace FderivMeasurableAux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set.-/
def A (f : E → F) (L : E →L[𝕜] F) (r ε : ℝ) : Set E :=
  { x |
    ∃ (r' : _)(_ : r' ∈ Ioc (r / 2) r), ∀ y z (_ : y ∈ ball x r') (_ : z ∈ ball x r'), ∥f z - f y - L (z - y)∥ ≤ ε*r }

/-- The set `B f K r s ε` is the set of points `x` around which there exists a continuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates well the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`. -/
def B (f : E → F) (K : Set (E →L[𝕜] F)) (r s ε : ℝ) : Set E :=
  ⋃(L : _)(_ : L ∈ K), A f L r ε ∩ A f L s ε

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
def D (f : E → F) (K : Set (E →L[𝕜] F)) : Set E :=
  ⋂e : ℕ, ⋃n : ℕ, ⋂(p : _)(_ : p ≥ n)(q : _)(_ : q ≥ n), B f K (1 / 2^p) (1 / 2^q) (1 / 2^e)

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_A (L : «expr →L[ ] »(E, 𝕜, F)) (r ε : exprℝ()) : is_open (A f L r ε) :=
begin
  rw [expr metric.is_open_iff] [],
  rintros [ident x, "⟨", ident r', ",", ident r'_mem, ",", ident hr', "⟩"],
  obtain ["⟨", ident s, ",", ident s_gt, ",", ident s_lt, "⟩", ":", expr «expr∃ , »((s : exprℝ()), «expr ∧ »(«expr < »(«expr / »(r, 2), s), «expr < »(s, r'))), ":=", expr exists_between r'_mem.1],
  have [] [":", expr «expr ∈ »(s, Ioc «expr / »(r, 2) r)] [":=", expr ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩],
  refine [expr ⟨«expr - »(r', s), by linarith [] [] [], λ x' hx', ⟨s, this, _⟩⟩],
  have [ident B] [":", expr «expr ⊆ »(ball x' s, ball x r')] [":=", expr ball_subset (le_of_lt hx')],
  assume [binders (y z hy hz)],
  exact [expr hr' y z (B hy) (B hz)]
end

theorem is_open_B {K : Set (E →L[𝕜] F)} {r s ε : ℝ} : IsOpen (B f K r s ε) :=
  by 
    simp [B, is_open_Union, IsOpen.inter, is_open_A]

theorem A_mono (L : E →L[𝕜] F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) : A f L r ε ⊆ A f L r δ :=
  by 
    rintro x ⟨r', r'r, hr'⟩
    refine' ⟨r', r'r, fun y z hy hz => _⟩
    apply le_transₓ (hr' y z hy hz)
    apply mul_le_mul_of_nonneg_right h 
    linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x]

theorem le_of_mem_A {r ε : ℝ} {L : E →L[𝕜] F} {x : E} (hx : x ∈ A f L r ε) {y z : E} (hy : y ∈ closed_ball x (r / 2))
  (hz : z ∈ closed_ball x (r / 2)) : ∥f z - f y - L (z - y)∥ ≤ ε*r :=
  by 
    rcases hx with ⟨r', r'mem, hr'⟩
    exact hr' _ _ (lt_of_le_of_ltₓ (mem_closed_ball.1 hy) r'mem.1) (lt_of_le_of_ltₓ (mem_closed_ball.1 hz) r'mem.1)

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_A_of_differentiable
{ε : exprℝ()}
(hε : «expr < »(0, ε))
{x : E}
(hx : differentiable_at 𝕜 f x) : «expr∃ , »((R «expr > » 0), ∀
 r «expr ∈ » Ioo (0 : exprℝ()) R, «expr ∈ »(x, A f (fderiv 𝕜 f x) r ε)) :=
begin
  have [] [] [":=", expr hx.has_fderiv_at],
  simp [] [] ["only"] ["[", expr has_fderiv_at, ",", expr has_fderiv_at_filter, ",", expr is_o_iff, "]"] [] ["at", ident this],
  rcases [expr eventually_nhds_iff_ball.1 (this (half_pos hε)), "with", "⟨", ident R, ",", ident R_pos, ",", ident hR, "⟩"],
  refine [expr ⟨R, R_pos, λ r hr, _⟩],
  have [] [":", expr «expr ∈ »(r, Ioc «expr / »(r, 2) r)] [":=", expr ⟨half_lt_self hr.1, le_refl _⟩],
  refine [expr ⟨r, this, λ y z hy hz, _⟩],
  calc
    «expr = »(«expr∥ ∥»(«expr - »(«expr - »(f z, f y), fderiv 𝕜 f x «expr - »(z, y))), «expr∥ ∥»(«expr - »(«expr - »(«expr - »(f z, f x), fderiv 𝕜 f x «expr - »(z, x)), «expr - »(«expr - »(f y, f x), fderiv 𝕜 f x «expr - »(y, x))))) : by { congr' [1] [],
      simp [] [] ["only"] ["[", expr continuous_linear_map.map_sub, "]"] [] [],
      abel [] [] [] }
    «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(«expr - »(f z, f x), fderiv 𝕜 f x «expr - »(z, x))), «expr∥ ∥»(«expr - »(«expr - »(f y, f x), fderiv 𝕜 f x «expr - »(y, x))))) : norm_sub_le _ _
    «expr ≤ »(..., «expr + »(«expr * »(«expr / »(ε, 2), «expr∥ ∥»(«expr - »(z, x))), «expr * »(«expr / »(ε, 2), «expr∥ ∥»(«expr - »(y, x))))) : add_le_add (hR _ (lt_trans (mem_ball.1 hz) hr.2)) (hR _ (lt_trans (mem_ball.1 hy) hr.2))
    «expr ≤ »(..., «expr + »(«expr * »(«expr / »(ε, 2), r), «expr * »(«expr / »(ε, 2), r))) : add_le_add (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hz)) (le_of_lt (half_pos hε))) (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hy)) (le_of_lt (half_pos hε)))
    «expr = »(..., «expr * »(ε, r)) : by ring []
end

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_sub_le_of_mem_A
{c : 𝕜}
(hc : «expr < »(1, «expr∥ ∥»(c)))
{r ε : exprℝ()}
(hε : «expr < »(0, ε))
(hr : «expr < »(0, r))
{x : E}
{L₁ L₂ : «expr →L[ ] »(E, 𝕜, F)}
(h₁ : «expr ∈ »(x, A f L₁ r ε))
(h₂ : «expr ∈ »(x, A f L₂ r ε)) : «expr ≤ »(«expr∥ ∥»(«expr - »(L₁, L₂)), «expr * »(«expr * »(4, «expr∥ ∥»(c)), ε)) :=
begin
  have [] [":", expr «expr ≤ »(0, «expr * »(«expr * »(4, «expr∥ ∥»(c)), ε))] [":=", expr mul_nonneg (mul_nonneg (by norm_num [] [] : «expr ≤ »((0 : exprℝ()), 4)) (norm_nonneg _)) hε.le],
  apply [expr op_norm_le_of_shell (half_pos hr) this hc],
  assume [binders (y ley ylt)],
  rw ["[", expr div_div_eq_div_mul, ",", expr div_le_iff' (mul_pos (by norm_num [] [] : «expr < »((0 : exprℝ()), 2)) (zero_lt_one.trans hc)), "]"] ["at", ident ley],
  calc
    «expr = »(«expr∥ ∥»(«expr - »(L₁, L₂) y), «expr∥ ∥»(«expr - »(«expr - »(«expr - »(f «expr + »(x, y), f x), L₂ «expr - »(«expr + »(x, y), x)), «expr - »(«expr - »(f «expr + »(x, y), f x), L₁ «expr - »(«expr + »(x, y), x))))) : by simp [] [] [] [] [] []
    «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(«expr - »(f «expr + »(x, y), f x), L₂ «expr - »(«expr + »(x, y), x))), «expr∥ ∥»(«expr - »(«expr - »(f «expr + »(x, y), f x), L₁ «expr - »(«expr + »(x, y), x))))) : norm_sub_le _ _
    «expr ≤ »(..., «expr + »(«expr * »(ε, r), «expr * »(ε, r))) : begin
      apply [expr add_le_add],
      { apply [expr le_of_mem_A h₂],
        { simp [] [] ["only"] ["[", expr le_of_lt (half_pos hr), ",", expr mem_closed_ball, ",", expr dist_self, "]"] [] [] },
        { simp [] [] ["only"] ["[", expr dist_eq_norm, ",", expr add_sub_cancel', ",", expr mem_closed_ball, ",", expr ylt.le, "]"] [] [] } },
      { apply [expr le_of_mem_A h₁],
        { simp [] [] ["only"] ["[", expr le_of_lt (half_pos hr), ",", expr mem_closed_ball, ",", expr dist_self, "]"] [] [] },
        { simp [] [] ["only"] ["[", expr dist_eq_norm, ",", expr add_sub_cancel', ",", expr mem_closed_ball, ",", expr ylt.le, "]"] [] [] } }
    end
    «expr = »(..., «expr * »(«expr * »(2, ε), r)) : by ring []
    «expr ≤ »(..., «expr * »(«expr * »(2, ε), «expr * »(«expr * »(2, «expr∥ ∥»(c)), «expr∥ ∥»(y)))) : mul_le_mul_of_nonneg_left ley (mul_nonneg (by norm_num [] []) hε.le)
    «expr = »(..., «expr * »(«expr * »(«expr * »(4, «expr∥ ∥»(c)), ε), «expr∥ ∥»(y))) : by ring []
end

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
theorem differentiable_set_subset_D : «expr ⊆ »({x | «expr ∧ »(differentiable_at 𝕜 f x, «expr ∈ »(fderiv 𝕜 f x, K))}, D f K) :=
begin
  assume [binders (x hx)],
  rw ["[", expr D, ",", expr mem_Inter, "]"] [],
  assume [binders (e)],
  have [] [":", expr «expr < »((0 : exprℝ()), «expr ^ »(«expr / »(1, 2), e))] [":=", expr pow_pos (by norm_num [] []) _],
  rcases [expr mem_A_of_differentiable this hx.1, "with", "⟨", ident R, ",", ident R_pos, ",", ident hR, "⟩"],
  obtain ["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n : exprℕ()), «expr < »(«expr ^ »(«expr / »(1, 2), n), R)), ":=", expr exists_pow_lt_of_lt_one R_pos (by norm_num [] [] : «expr < »(«expr / »((1 : exprℝ()), 2), 1))],
  simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_Inter, ",", expr B, ",", expr mem_inter_eq, "]"] [] [],
  refine [expr ⟨n, λ
    p
    hp
    q
    hq, ⟨fderiv 𝕜 f x, hx.2, ⟨_, _⟩⟩⟩]; { refine [expr hR _ ⟨pow_pos (by norm_num [] []) _, lt_of_le_of_lt _ hn⟩],
    exact [expr pow_le_pow_of_le_one (by norm_num [] []) (by norm_num [] []) (by assumption)] }
end

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
theorem D_subset_differentiable_set
{K : set «expr →L[ ] »(E, 𝕜, F)}
(hK : is_complete K) : «expr ⊆ »(D f K, {x | «expr ∧ »(differentiable_at 𝕜 f x, «expr ∈ »(fderiv 𝕜 f x, K))}) :=
begin
  have [ident P] [":", expr ∀
   {n : exprℕ()}, «expr < »((0 : exprℝ()), «expr ^ »(«expr / »(1, 2), n))] [":=", expr pow_pos (by norm_num [] [])],
  rcases [expr normed_field.exists_one_lt_norm 𝕜, "with", "⟨", ident c, ",", ident hc, "⟩"],
  have [ident cpos] [":", expr «expr < »(0, «expr∥ ∥»(c))] [":=", expr lt_trans zero_lt_one hc],
  assume [binders (x hx)],
  have [] [":", expr ∀
   e : exprℕ(), «expr∃ , »((n : exprℕ()), ∀
    p
    q, «expr ≤ »(n, p) → «expr ≤ »(n, q) → «expr∃ , »((L «expr ∈ » K), «expr ∈ »(x, «expr ∩ »(A f L «expr ^ »(«expr / »(1, 2), p) «expr ^ »(«expr / »(1, 2), e), A f L «expr ^ »(«expr / »(1, 2), q) «expr ^ »(«expr / »(1, 2), e)))))] [],
  { assume [binders (e)],
    have [] [] [":=", expr mem_Inter.1 hx e],
    rcases [expr mem_Union.1 this, "with", "⟨", ident n, ",", ident hn, "⟩"],
    refine [expr ⟨n, λ p q hp hq, _⟩],
    simp [] [] ["only"] ["[", expr mem_Inter, ",", expr ge_iff_le, "]"] [] ["at", ident hn],
    rcases [expr mem_Union.1 (hn p hp q hq), "with", "⟨", ident L, ",", ident hL, "⟩"],
    exact [expr ⟨L, mem_Union.1 hL⟩] },
  choose ["!"] [ident n] [ident L, ident hn] ["using", expr this],
  have [ident M] [":", expr ∀
   e
   p
   q
   e'
   p'
   q', «expr ≤ »(n e, p) → «expr ≤ »(n e, q) → «expr ≤ »(n e', p') → «expr ≤ »(n e', q') → «expr ≤ »(e, e') → «expr ≤ »(«expr∥ ∥»(«expr - »(L e p q, L e' p' q')), «expr * »(«expr * »(12, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)))] [],
  { assume [binders (e p q e' p' q' hp hq hp' hq' he')],
    let [ident r] [] [":=", expr max (n e) (n e')],
    have [ident I] [":", expr «expr ≤ »(«expr ^ »(«expr / »((1 : exprℝ()), 2), e'), «expr ^ »(«expr / »(1, 2), e))] [":=", expr pow_le_pow_of_le_one (by norm_num [] []) (by norm_num [] []) he'],
    have [ident J1] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(L e p q, L e p r)), «expr * »(«expr * »(4, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)))] [],
    { have [ident I1] [":", expr «expr ∈ »(x, A f (L e p q) «expr ^ »(«expr / »(1, 2), p) «expr ^ »(«expr / »(1, 2), e))] [":=", expr (hn e p q hp hq).2.1],
      have [ident I2] [":", expr «expr ∈ »(x, A f (L e p r) «expr ^ »(«expr / »(1, 2), p) «expr ^ »(«expr / »(1, 2), e))] [":=", expr (hn e p r hp (le_max_left _ _)).2.1],
      exact [expr norm_sub_le_of_mem_A hc P P I1 I2] },
    have [ident J2] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(L e p r, L e' p' r)), «expr * »(«expr * »(4, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)))] [],
    { have [ident I1] [":", expr «expr ∈ »(x, A f (L e p r) «expr ^ »(«expr / »(1, 2), r) «expr ^ »(«expr / »(1, 2), e))] [":=", expr (hn e p r hp (le_max_left _ _)).2.2],
      have [ident I2] [":", expr «expr ∈ »(x, A f (L e' p' r) «expr ^ »(«expr / »(1, 2), r) «expr ^ »(«expr / »(1, 2), e'))] [":=", expr (hn e' p' r hp' (le_max_right _ _)).2.2],
      exact [expr norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ I I2)] },
    have [ident J3] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(L e' p' r, L e' p' q')), «expr * »(«expr * »(4, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)))] [],
    { have [ident I1] [":", expr «expr ∈ »(x, A f (L e' p' r) «expr ^ »(«expr / »(1, 2), p') «expr ^ »(«expr / »(1, 2), e'))] [":=", expr (hn e' p' r hp' (le_max_right _ _)).2.1],
      have [ident I2] [":", expr «expr ∈ »(x, A f (L e' p' q') «expr ^ »(«expr / »(1, 2), p') «expr ^ »(«expr / »(1, 2), e'))] [":=", expr (hn e' p' q' hp' hq').2.1],
      exact [expr norm_sub_le_of_mem_A hc P P (A_mono _ _ I I1) (A_mono _ _ I I2)] },
    calc
      «expr = »(«expr∥ ∥»(«expr - »(L e p q, L e' p' q')), «expr∥ ∥»(«expr + »(«expr + »(«expr - »(L e p q, L e p r), «expr - »(L e p r, L e' p' r)), «expr - »(L e' p' r, L e' p' q')))) : by { congr' [1] [],
        abel [] [] [] }
      «expr ≤ »(..., «expr + »(«expr + »(«expr∥ ∥»(«expr - »(L e p q, L e p r)), «expr∥ ∥»(«expr - »(L e p r, L e' p' r))), «expr∥ ∥»(«expr - »(L e' p' r, L e' p' q')))) : le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
      «expr ≤ »(..., «expr + »(«expr + »(«expr * »(«expr * »(4, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)), «expr * »(«expr * »(4, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e))), «expr * »(«expr * »(4, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)))) : by apply_rules ["[", expr add_le_add, "]"]
      «expr = »(..., «expr * »(«expr * »(12, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e))) : by ring [] },
  let [ident L0] [":", expr exprℕ() → «expr →L[ ] »(E, 𝕜, F)] [":=", expr λ e, L e (n e) (n e)],
  have [] [":", expr cauchy_seq L0] [],
  { rw [expr metric.cauchy_seq_iff'] [],
    assume [binders (ε εpos)],
    obtain ["⟨", ident e, ",", ident he, "⟩", ":", expr «expr∃ , »((e : exprℕ()), «expr < »(«expr ^ »(«expr / »(1, 2), e), «expr / »(ε, «expr * »(12, «expr∥ ∥»(c))))), ":=", expr exists_pow_lt_of_lt_one (div_pos εpos (mul_pos (by norm_num [] []) cpos)) (by norm_num [] [])],
    refine [expr ⟨e, λ e' he', _⟩],
    rw ["[", expr dist_comm, ",", expr dist_eq_norm, "]"] [],
    calc
      «expr ≤ »(«expr∥ ∥»(«expr - »(L0 e, L0 e')), «expr * »(«expr * »(12, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e))) : M _ _ _ _ _ _ (le_refl _) (le_refl _) (le_refl _) (le_refl _) he'
      «expr < »(..., «expr * »(«expr * »(12, «expr∥ ∥»(c)), «expr / »(ε, «expr * »(12, «expr∥ ∥»(c))))) : mul_lt_mul' (le_refl _) he (le_of_lt P) (mul_pos (by norm_num [] []) cpos)
      «expr = »(..., ε) : by { field_simp [] ["[", expr (by norm_num [] [] : «expr ≠ »((12 : exprℝ()), 0)), ",", expr ne_of_gt cpos, "]"] [] [],
        ring [] } },
  obtain ["⟨", ident f', ",", ident f'K, ",", ident hf', "⟩", ":", expr «expr∃ , »((f' «expr ∈ » K), tendsto L0 at_top (expr𝓝() f')), ":=", expr cauchy_seq_tendsto_of_is_complete hK (λ
    e, (hn e (n e) (n e) (le_refl _) (le_refl _)).1) this],
  have [ident Lf'] [":", expr ∀
   e
   p, «expr ≤ »(n e, p) → «expr ≤ »(«expr∥ ∥»(«expr - »(L e (n e) p, f')), «expr * »(«expr * »(12, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)))] [],
  { assume [binders (e p hp)],
    apply [expr le_of_tendsto (tendsto_const_nhds.sub hf').norm],
    rw [expr eventually_at_top] [],
    exact [expr ⟨e, λ e' he', M _ _ _ _ _ _ (le_refl _) hp (le_refl _) (le_refl _) he'⟩] },
  have [] [":", expr has_fderiv_at f f' x] [],
  { simp [] [] ["only"] ["[", expr has_fderiv_at_iff_is_o_nhds_zero, ",", expr is_o_iff, "]"] [] [],
    assume [binders (ε εpos)],
    have [ident pos] [":", expr «expr < »(0, «expr + »(4, «expr * »(12, «expr∥ ∥»(c))))] [":=", expr add_pos_of_pos_of_nonneg (by norm_num [] []) (mul_nonneg (by norm_num [] []) (norm_nonneg _))],
    obtain ["⟨", ident e, ",", ident he, "⟩", ":", expr «expr∃ , »((e : exprℕ()), «expr < »(«expr ^ »(«expr / »(1, 2), e), «expr / »(ε, «expr + »(4, «expr * »(12, «expr∥ ∥»(c)))))), ":=", expr exists_pow_lt_of_lt_one (div_pos εpos pos) (by norm_num [] [])],
    rw [expr eventually_nhds_iff_ball] [],
    refine [expr ⟨«expr ^ »(«expr / »(1, 2), «expr + »(n e, 1)), P, λ y hy, _⟩],
    by_cases [expr y_pos, ":", expr «expr = »(y, 0)],
    { simp [] [] [] ["[", expr y_pos, "]"] [] [] },
    have [ident yzero] [":", expr «expr < »(0, «expr∥ ∥»(y))] [":=", expr norm_pos_iff.mpr y_pos],
    have [ident y_lt] [":", expr «expr < »(«expr∥ ∥»(y), «expr ^ »(«expr / »(1, 2), «expr + »(n e, 1)))] [],
    by simpa [] [] [] [] [] ["using", expr mem_ball_iff_norm.1 hy],
    have [ident yone] [":", expr «expr ≤ »(«expr∥ ∥»(y), 1)] [":=", expr le_trans y_lt.le (pow_le_one _ (by norm_num [] []) (by norm_num [] []))],
    obtain ["⟨", ident k, ",", ident hk, ",", ident h'k, "⟩", ":", expr «expr∃ , »((k : exprℕ()), «expr ∧ »(«expr < »(«expr ^ »(«expr / »(1, 2), «expr + »(k, 1)), «expr∥ ∥»(y)), «expr ≤ »(«expr∥ ∥»(y), «expr ^ »(«expr / »(1, 2), k)))), ":=", expr exists_nat_pow_near_of_lt_one yzero yone (by norm_num [] [] : «expr < »((0 : exprℝ()), «expr / »(1, 2))) (by norm_num [] [] : «expr < »(«expr / »((1 : exprℝ()), 2), 1))],
    have [ident k_gt] [":", expr «expr < »(n e, k)] [],
    { have [] [":", expr «expr < »(«expr ^ »(«expr / »((1 : exprℝ()), 2), «expr + »(k, 1)), «expr ^ »(«expr / »(1, 2), «expr + »(n e, 1)))] [":=", expr lt_trans hk y_lt],
      rw [expr pow_lt_pow_iff_of_lt_one (by norm_num [] [] : «expr < »((0 : exprℝ()), «expr / »(1, 2))) (by norm_num [] [])] ["at", ident this],
      linarith [] [] [] },
    set [] [ident m] [] [":="] [expr «expr - »(k, 1)] ["with", ident hl],
    have [ident m_ge] [":", expr «expr ≤ »(n e, m)] [":=", expr nat.le_pred_of_lt k_gt],
    have [ident km] [":", expr «expr = »(k, «expr + »(m, 1))] [":=", expr (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) k_gt)).symm],
    rw [expr km] ["at", ident hk, ident h'k],
    have [ident J1] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f «expr + »(x, y), f x), L e (n e) m «expr - »(«expr + »(x, y), x))), «expr * »(«expr ^ »(«expr / »(1, 2), e), «expr ^ »(«expr / »(1, 2), m)))] [],
    { apply [expr le_of_mem_A (hn e (n e) m (le_refl _) m_ge).2.2],
      { simp [] [] ["only"] ["[", expr mem_closed_ball, ",", expr dist_self, "]"] [] [],
        exact [expr div_nonneg (le_of_lt P) zero_le_two] },
      { simpa [] [] ["only"] ["[", expr dist_eq_norm, ",", expr add_sub_cancel', ",", expr mem_closed_ball, ",", expr pow_succ', ",", expr mul_one_div, "]"] [] ["using", expr h'k] } },
    have [ident J2] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f «expr + »(x, y), f x), L e (n e) m y)), «expr * »(«expr * »(4, «expr ^ »(«expr / »(1, 2), e)), «expr∥ ∥»(y)))] [":=", expr calc
       «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f «expr + »(x, y), f x), L e (n e) m y)), «expr * »(«expr ^ »(«expr / »(1, 2), e), «expr ^ »(«expr / »(1, 2), m))) : by simpa [] [] ["only"] ["[", expr add_sub_cancel', "]"] [] ["using", expr J1]
       «expr = »(..., «expr * »(«expr * »(4, «expr ^ »(«expr / »(1, 2), e)), «expr ^ »(«expr / »(1, 2), «expr + »(m, 2)))) : by { field_simp [] [] [] [],
         ring_exp [] [] }
       «expr ≤ »(..., «expr * »(«expr * »(4, «expr ^ »(«expr / »(1, 2), e)), «expr∥ ∥»(y))) : mul_le_mul_of_nonneg_left (le_of_lt hk) (mul_nonneg (by norm_num [] []) (le_of_lt P))],
    calc
      «expr = »(«expr∥ ∥»(«expr - »(«expr - »(f «expr + »(x, y), f x), f' y)), «expr∥ ∥»(«expr + »(«expr - »(«expr - »(f «expr + »(x, y), f x), L e (n e) m y), «expr - »(L e (n e) m, f') y))) : congr_arg _ (by simp [] [] [] [] [] [])
      «expr ≤ »(..., «expr + »(«expr * »(«expr * »(4, «expr ^ »(«expr / »(1, 2), e)), «expr∥ ∥»(y)), «expr * »(«expr * »(«expr * »(12, «expr∥ ∥»(c)), «expr ^ »(«expr / »(1, 2), e)), «expr∥ ∥»(y)))) : norm_add_le_of_le J2 ((le_op_norm _ _).trans (mul_le_mul_of_nonneg_right (Lf' _ _ m_ge) (norm_nonneg _)))
      «expr = »(..., «expr * »(«expr * »(«expr + »(4, «expr * »(12, «expr∥ ∥»(c))), «expr∥ ∥»(y)), «expr ^ »(«expr / »(1, 2), e))) : by ring []
      «expr ≤ »(..., «expr * »(«expr * »(«expr + »(4, «expr * »(12, «expr∥ ∥»(c))), «expr∥ ∥»(y)), «expr / »(ε, «expr + »(4, «expr * »(12, «expr∥ ∥»(c)))))) : mul_le_mul_of_nonneg_left he.le (mul_nonneg (add_nonneg (by norm_num [] []) (mul_nonneg (by norm_num [] []) (norm_nonneg _))) (norm_nonneg _))
      «expr = »(..., «expr * »(ε, «expr∥ ∥»(y))) : by { field_simp [] ["[", expr ne_of_gt pos, "]"] [] [],
        ring [] } },
  rw ["<-", expr this.fderiv] ["at", ident f'K],
  exact [expr ⟨this.differentiable_at, f'K⟩]
end

theorem differentiable_set_eq_D (hK : IsComplete K) : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } = D f K :=
  subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end FderivMeasurableAux

open FderivMeasurableAux

variable[MeasurableSpace E][OpensMeasurableSpace E]

variable(𝕜 f)

/-- The set of differentiability points of a function, with derivative in a given complete set,
is Borel-measurable. -/
theorem measurable_set_of_differentiable_at_of_is_complete {K : Set (E →L[𝕜] F)} (hK : IsComplete K) :
  MeasurableSet { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } :=
  by 
    simp [differentiable_set_eq_D K hK, D, is_open_B.measurable_set, MeasurableSet.Inter_Prop, MeasurableSet.Inter,
      MeasurableSet.Union]

variable[CompleteSpace F]

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The set of differentiability points of a function taking values in a complete space is
Borel-measurable. -/ theorem measurable_set_of_differentiable_at : measurable_set {x | differentiable_at 𝕜 f x} :=
begin
  have [] [":", expr is_complete (univ : set «expr →L[ ] »(E, 𝕜, F))] [":=", expr complete_univ],
  convert [] [expr measurable_set_of_differentiable_at_of_is_complete 𝕜 f this] [],
  simp [] [] [] [] [] []
end

-- error in Analysis.Calculus.FderivMeasurable: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measurable_fderiv : measurable (fderiv 𝕜 f) :=
begin
  refine [expr measurable_of_is_closed (λ s hs, _)],
  have [] [":", expr «expr = »(«expr ⁻¹' »(fderiv 𝕜 f, s), «expr ∪ »({x | «expr ∧ »(differentiable_at 𝕜 f x, «expr ∈ »(fderiv 𝕜 f x, s))}, «expr ∩ »({x | «expr ∈ »((0 : «expr →L[ ] »(E, 𝕜, F)), s)}, {x | «expr¬ »(differentiable_at 𝕜 f x)})))] [":=", expr set.ext (λ
    x, mem_preimage.trans fderiv_mem_iff)],
  rw [expr this] [],
  exact [expr (measurable_set_of_differentiable_at_of_is_complete _ _ hs.is_complete).union ((measurable_set.const _).inter (measurable_set_of_differentiable_at _ _).compl)]
end

theorem measurable_fderiv_apply_const [MeasurableSpace F] [BorelSpace F] (y : E) : Measurable fun x => fderiv 𝕜 f x y :=
  (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv 𝕜 f)

variable{𝕜}

theorem measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] (f : 𝕜 → F) :
  Measurable (deriv f) :=
  by 
    simpa only [fderiv_deriv] using measurable_fderiv_apply_const 𝕜 f 1

