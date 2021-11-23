import Mathbin.Analysis.Calculus.LocalExtr 
import Mathbin.Analysis.Convex.Slope 
import Mathbin.Analysis.Convex.Topology 
import Mathbin.Data.Complex.IsROrC

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `is_R_or_C`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `∥f x∥ ≤ B x` from upper estimates on `f'` or `∥f'∥`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `∥f x∥ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `∥f x - f a∥ ≤ C * ∥x - a∥`; several versions deal with
  right derivative and derivative within `[a, b]` (`has_deriv_within_at` or `deriv_within`).

* `convex.is_const_of_fderiv_within_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `exists_ratio_has_deriv_at_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_has_deriv_at_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `convex.image_sub_lt_mul_sub_of_deriv_lt`, `convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `convex.image_sub_le_mul_sub_of_deriv_le`, `convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `convex.monotone_on_of_deriv_nonneg`, `convex.antitone_on_of_deriv_nonpos`,
  `convex.strict_mono_of_deriv_pos`, `convex.strict_anti_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/antitone/strictly monotone/strictly monotonically
  decreasing.

* `convex_on_of_deriv_monotone_on`, `convex_on_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

* `strict_fderiv_of_cont_diff` : a C^1 function over the reals is strictly differentiable.  (This
  is a corollary of the mean value inequality.)
-/


variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]{F : Type _}[NormedGroup F][NormedSpace ℝ F]

open Metric Set Asymptotics ContinuousLinearMap Filter

open_locale Classical TopologicalSpace Nnreal

/-! ### One-dimensional fencing inequalities -/


-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary'
{f f' : exprℝ() → exprℝ()}
{a b : exprℝ()}
(hf : continuous_on f (Icc a b))
(hf' : ∀
 x «expr ∈ » Ico a b, ∀
 r, «expr < »(f' x, r) → «expr∃ᶠ in , »((z), «expr𝓝[ ] »(Ioi x, x), «expr < »(«expr * »(«expr ⁻¹»(«expr - »(z, x)), «expr - »(f z, f x)), r)))
{B B' : exprℝ() → exprℝ()}
(ha : «expr ≤ »(f a, B a))
(hB : continuous_on B (Icc a b))
(hB' : ∀ x «expr ∈ » Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
(bound : ∀
 x «expr ∈ » Ico a b, «expr = »(f x, B x) → «expr < »(f' x, B' x)) : ∀
{{x}}, «expr ∈ »(x, Icc a b) → «expr ≤ »(f x, B x) :=
begin
  change [expr «expr ⊆ »(Icc a b, {x | «expr ≤ »(f x, B x)})] [] [],
  set [] [ident s] [] [":="] [expr «expr ∩ »({x | «expr ≤ »(f x, B x)}, Icc a b)] [],
  have [ident A] [":", expr continuous_on (λ x, (f x, B x)) (Icc a b)] [],
  from [expr hf.prod hB],
  have [] [":", expr is_closed s] [],
  { simp [] [] ["only"] ["[", expr s, ",", expr inter_comm, "]"] [] [],
    exact [expr A.preimage_closed_of_closed is_closed_Icc order_closed_topology.is_closed_le'] },
  apply [expr this.Icc_subset_of_forall_exists_gt ha],
  rintros [ident x, "⟨", ident hxB, ":", expr «expr ≤ »(f x, B x), ",", ident xab, "⟩", ident y, ident hy],
  cases [expr hxB.lt_or_eq] ["with", ident hxB, ident hxB],
  { refine [expr nonempty_of_mem (inter_mem _ (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩))],
    have [] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Icc a b, x), «expr < »(f x, B x))] [],
    from [expr A x (Ico_subset_Icc_self xab) (is_open.mem_nhds (is_open_lt continuous_fst continuous_snd) hxB)],
    have [] [":", expr «expr∀ᶠ in , »((x), «expr𝓝[ ] »(Ioi x, x), «expr < »(f x, B x))] [],
    from [expr nhds_within_le_of_mem (Icc_mem_nhds_within_Ioi xab) this],
    exact [expr this.mono (λ y, le_of_lt)] },
  { rcases [expr exists_between (bound x xab hxB), "with", "⟨", ident r, ",", ident hfr, ",", ident hrB, "⟩"],
    specialize [expr hf' x xab r hfr],
    have [ident HB] [":", expr «expr∀ᶠ in , »((z), «expr𝓝[ ] »(Ioi x, x), «expr < »(r, «expr * »(«expr ⁻¹»(«expr - »(z, x)), «expr - »(B z, B x))))] [],
    from [expr «expr $ »(has_deriv_within_at_iff_tendsto_slope', lt_irrefl x).1 (hB' x xab).Ioi_of_Ici (Ioi_mem_nhds hrB)],
    obtain ["⟨", ident z, ",", "⟨", ident hfz, ",", ident hzB, "⟩", ",", ident hz, "⟩", ":", expr «expr∃ , »((z), «expr ∧ »(«expr ∧ »(«expr < »(«expr * »(«expr ⁻¹»(«expr - »(z, x)), «expr - »(f z, f x)), r), «expr < »(r, «expr * »(«expr ⁻¹»(«expr - »(z, x)), «expr - »(B z, B x)))), «expr ∈ »(z, Ioc x y)))],
    from [expr ((hf'.and_eventually HB).and_eventually (Ioc_mem_nhds_within_Ioi ⟨le_rfl, hy⟩)).exists],
    refine [expr ⟨z, _, hz⟩],
    have [] [] [":=", expr (hfz.trans hzB).le],
    rwa ["[", expr mul_le_mul_left «expr $ »(inv_pos.2, sub_pos.2 hz.1), ",", expr hxB, ",", expr sub_le_sub_iff_right, "]"] ["at", ident this] }
end

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠz in 𝓝[Ioi x] x, ((z - x)⁻¹*f z - f x) < r) {B B' : ℝ → ℝ}
  (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀ x _ : x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_le_deriv_boundary
{f : exprℝ() → exprℝ()}
{a b : exprℝ()}
(hf : continuous_on f (Icc a b))
{B B' : exprℝ() → exprℝ()}
(ha : «expr ≤ »(f a, B a))
(hB : continuous_on B (Icc a b))
(hB' : ∀ x «expr ∈ » Ico a b, has_deriv_within_at B (B' x) (Ici x) x)
(bound : ∀
 x «expr ∈ » Ico a b, ∀
 r, «expr < »(B' x, r) → «expr∃ᶠ in , »((z), «expr𝓝[ ] »(Ioi x, x), «expr < »(«expr * »(«expr ⁻¹»(«expr - »(z, x)), «expr - »(f z, f x)), r))) : ∀
{{x}}, «expr ∈ »(x, Icc a b) → «expr ≤ »(f x, B x) :=
begin
  have [ident Hr] [":", expr ∀
   x «expr ∈ » Icc a b, ∀ r «expr > » 0, «expr ≤ »(f x, «expr + »(B x, «expr * »(r, «expr - »(x, a))))] [],
  { intros [ident x, ident hx, ident r, ident hr],
    apply [expr image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound],
    { rwa ["[", expr sub_self, ",", expr mul_zero, ",", expr add_zero, "]"] [] },
    { exact [expr hB.add (continuous_on_const.mul (continuous_id.continuous_on.sub continuous_on_const))] },
    { assume [binders (x hx)],
      exact [expr (hB' x hx).add (((has_deriv_within_at_id x (Ici x)).sub_const a).const_mul r)] },
    { assume [binders (x hx _)],
      rw ["[", expr mul_one, "]"] [],
      exact [expr (lt_add_iff_pos_right _).2 hr] },
    exact [expr hx] },
  assume [binders (x hx)],
  have [] [":", expr continuous_within_at (λ r, «expr + »(B x, «expr * »(r, «expr - »(x, a)))) (Ioi 0) 0] [],
  from [expr continuous_within_at_const.add (continuous_within_at_id.mul continuous_within_at_const)],
  convert [] [expr continuous_within_at_const.closure_le _ this (Hr x hx)] []; simp [] [] [] [] [] []
end

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : f a ≤ B a)
  (hB : ContinuousOn B (Icc a b)) (hB' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x _ : x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf (fun x hx r hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB'
    bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : f a ≤ B a)
  (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀ x _ : x ∈ Ico a b, f x = B x → f' x < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : f a ≤ B a)
  (hB : ContinuousOn B (Icc a b)) (hB' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x _ : x ∈ Ico a b, f' x ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB'$
    fun x hx r hr => (hf' x hx).liminf_right_slope_le (lt_of_le_of_ltₓ (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/


section 

variable{f : ℝ → E}{a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(∥f z∥ - ∥f x∥) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. -/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type _} [NormedGroup E] {f : ℝ → E} {f' : ℝ → ℝ}
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠz in 𝓝[Ioi x] x, ((z - x)⁻¹*∥f z∥ - ∥f x∥) < r) {B B' : ℝ → ℝ}
  (ha : ∥f a∥ ≤ B a) (hB : ContinuousOn B (Icc a b)) (hB' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x _ : x ∈ Ico a b, ∥f x∥ = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuous_on hf) hf' ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
  (hB : ContinuousOn B (Icc a b)) (hB' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x _ : x ∈ Ico a b, ∥f x∥ = B x → ∥f' x∥ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `∥f x∥ = B x`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
  (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀ x _ : x ∈ Ico a b, ∥f x∥ = B x → ∥f' x∥ < B' x) :
  ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
  (hB : ContinuousOn B (Icc a b)) (hB' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
  (bound : ∀ x _ : x ∈ Ico a b, ∥f' x∥ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuous_on hf) ha hB hB'$
    fun x hx r hr => (hf' x hx).liminf_right_slope_norm_le (lt_of_le_of_ltₓ (bound x hx) hr)

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `∥f a∥ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `∥f' x∥ ≤ B x` everywhere on `[a, b)`.

Then `∥f x∥ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) {B B' : ℝ → ℝ} (ha : ∥f a∥ ≤ B a)
  (hB : ∀ x, HasDerivAt B (B' x) x) (bound : ∀ x _ : x ∈ Ico a b, ∥f' x∥ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ∥f x∥ ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha (fun x hx => (hB x).ContinuousAt.ContinuousWithinAt)
    (fun x hx => (hB x).HasDerivWithinAt) bound

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `∥f x - f a∥ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment
{f' : exprℝ() → E}
{C : exprℝ()}
(hf : continuous_on f (Icc a b))
(hf' : ∀ x «expr ∈ » Ico a b, has_deriv_within_at f (f' x) (Ici x) x)
(bound : ∀
 x «expr ∈ » Ico a b, «expr ≤ »(«expr∥ ∥»(f' x), C)) : ∀
x «expr ∈ » Icc a b, «expr ≤ »(«expr∥ ∥»(«expr - »(f x, f a)), «expr * »(C, «expr - »(x, a))) :=
begin
  let [ident g] [] [":=", expr λ x, «expr - »(f x, f a)],
  have [ident hg] [":", expr continuous_on g (Icc a b)] [],
  from [expr hf.sub continuous_on_const],
  have [ident hg'] [":", expr ∀ x «expr ∈ » Ico a b, has_deriv_within_at g (f' x) (Ici x) x] [],
  { assume [binders (x hx)],
    simpa [] [] [] [] [] ["using", expr (hf' x hx).sub (has_deriv_within_at_const _ _ _)] },
  let [ident B] [] [":=", expr λ x, «expr * »(C, «expr - »(x, a))],
  have [ident hB] [":", expr ∀ x, has_deriv_at B C x] [],
  { assume [binders (x)],
    simpa [] [] [] [] [] ["using", expr (has_deriv_at_const x C).mul ((has_deriv_at_id x).sub (has_deriv_at_const x a))] },
  convert [] [expr image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound] [],
  simp [] [] ["only"] ["[", expr g, ",", expr B, "]"] [] [],
  rw ["[", expr sub_self, ",", expr norm_zero, ",", expr sub_self, ",", expr mul_zero, "]"] []
end

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
  (hf : ∀ x _ : x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) (bound : ∀ x _ : x ∈ Ico a b, ∥f' x∥ ≤ C) :
  ∀ x _ : x ∈ Icc a b, ∥f x - f a∥ ≤ C*x - a :=
  by 
    refine'
      norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).ContinuousWithinAt) (fun x hx => _) bound 
    exact (hf x$ Ico_subset_Icc_self hx).nhdsWithin (Icc_mem_nhds_within_Ici hx)

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `∥f x - f a∥ ≤ C * (x - a)`, `deriv_within`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
  (bound : ∀ x _ : x ∈ Ico a b, ∥derivWithin f (Icc a b) x∥ ≤ C) : ∀ x _ : x ∈ Icc a b, ∥f x - f a∥ ≤ C*x - a :=
  by 
    refine' norm_image_sub_le_of_norm_deriv_le_segment' _ bound 
    exact fun x hx => (hf x hx).HasDerivWithinAt

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `has_deriv_within_at`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
  (hf : ∀ x _ : x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
  (bound : ∀ x _ : x ∈ Ico (0 : ℝ) 1, ∥f' x∥ ≤ C) : ∥f 1 - f 0∥ ≤ C :=
  by 
    simpa only [sub_zero, mul_oneₓ] using
      norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `∥f 1 - f 0∥ ≤ C`, `deriv_within` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ} (hf : DifferentiableOn ℝ f (Icc (0 : ℝ) 1))
  (bound : ∀ x _ : x ∈ Ico (0 : ℝ) 1, ∥derivWithin f (Icc (0 : ℝ) 1) x∥ ≤ C) : ∥f 1 - f 0∥ ≤ C :=
  by 
    simpa only [sub_zero, mul_oneₓ] using
      norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
  (hderiv : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f 0 (Ici x) x) : ∀ x _ : x ∈ Icc a b, f x = f a :=
  by 
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
      fun x hx =>
        norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv
          (fun y hy =>
            by 
              rw [norm_le_zero_iff])
          x hx

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem constant_of_deriv_within_zero
(hdiff : differentiable_on exprℝ() f (Icc a b))
(hderiv : ∀
 x «expr ∈ » Ico a b, «expr = »(deriv_within f (Icc a b) x, 0)) : ∀ x «expr ∈ » Icc a b, «expr = »(f x, f a) :=
begin
  have [ident H] [":", expr ∀
   x «expr ∈ » Ico a b, «expr ≤ »(«expr∥ ∥»(deriv_within f (Icc a b) x), 0)] [":=", expr by simpa [] [] ["only"] ["[", expr norm_le_zero_iff, "]"] [] ["using", expr λ
    x hx, hderiv x hx]],
  simpa [] [] ["only"] ["[", expr zero_mul, ",", expr norm_le_zero_iff, ",", expr sub_eq_zero, "]"] [] ["using", expr λ
   x hx, norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx]
end

variable{f' g : ℝ → E}

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
theorem eq_of_has_deriv_right_eq (derivf : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
  (derivg : ∀ x _ : x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
  (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : ∀ y _ : y ∈ Icc a b, f y = g y :=
  by 
    simp only [←@sub_eq_zero _ _ (f _)] at hi⊢
    exact
      hi ▸
        constant_of_has_deriv_right_zero (fcont.sub gcont)
          fun y hy =>
            by 
              simpa only [sub_self] using (derivf y hy).sub (derivg y hy)

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
theorem eq_of_deriv_within_eq
(fdiff : differentiable_on exprℝ() f (Icc a b))
(gdiff : differentiable_on exprℝ() g (Icc a b))
(hderiv : eq_on (deriv_within f (Icc a b)) (deriv_within g (Icc a b)) (Ico a b))
(hi : «expr = »(f a, g a)) : ∀ y «expr ∈ » Icc a b, «expr = »(f y, g y) :=
begin
  have [ident A] [":", expr ∀
   y «expr ∈ » Ico a b, has_deriv_within_at f (deriv_within f (Icc a b) y) (Ici y) y] [":=", expr λ
   y hy, (fdiff y (mem_Icc_of_Ico hy)).has_deriv_within_at.nhds_within (Icc_mem_nhds_within_Ici hy)],
  have [ident B] [":", expr ∀
   y «expr ∈ » Ico a b, has_deriv_within_at g (deriv_within g (Icc a b) y) (Ici y) y] [":=", expr λ
   y hy, (gdiff y (mem_Icc_of_Ico hy)).has_deriv_within_at.nhds_within (Icc_mem_nhds_within_Ici hy)],
  exact [expr eq_of_has_deriv_right_eq A (λ
    y hy, «expr ▸ »((hderiv hy).symm, B y hy)) fdiff.continuous_on gdiff.continuous_on hi]
end

end 

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[is_R_or_C 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 G]` to achieve this result. For the domain `E` we
also assume `[normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E]` to have a notion of a `convex` set. In both
interesting cases `𝕜 = ℝ` and `𝕜 = ℂ` the assumption `[is_scalar_tower ℝ 𝕜 E]` is satisfied
automatically. -/


section 

variable{𝕜 G : Type _}[IsROrC 𝕜][NormedSpace 𝕜 E][IsScalarTower ℝ 𝕜 E][NormedGroup G][NormedSpace 𝕜 G]

namespace Convex

variable{f : E → G}{C : ℝ}{s : Set E}{x y : E}{f' : E → E →L[𝕜] G}{φ : E →L[𝕜] G}

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `has_fderiv_within`. -/
theorem norm_image_sub_le_of_norm_has_fderiv_within_le
(hf : ∀ x «expr ∈ » s, has_fderiv_within_at f (f' x) s x)
(bound : ∀ x «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(f' x), C))
(hs : convex exprℝ() s)
(xs : «expr ∈ »(x, s))
(ys : «expr ∈ »(y, s)) : «expr ≤ »(«expr∥ ∥»(«expr - »(f y, f x)), «expr * »(C, «expr∥ ∥»(«expr - »(y, x)))) :=
begin
  letI [] [":", expr normed_space exprℝ() G] [":=", expr restrict_scalars.normed_space exprℝ() 𝕜 G],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 G] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  have [ident C0] [":", expr «expr ≤ »(0, C)] [":=", expr le_trans (norm_nonneg _) (bound x xs)],
  set [] [ident g] [":", expr exprℝ() → E] [":="] [expr λ t, «expr + »(x, «expr • »(t, «expr - »(y, x)))] [],
  have [ident Dg] [":", expr ∀ t, has_deriv_at g «expr - »(y, x) t] [],
  { assume [binders (t)],
    simpa [] [] ["only"] ["[", expr one_smul, "]"] [] ["using", expr ((has_deriv_at_id t).smul_const «expr - »(y, x)).const_add x] },
  have [ident segm] [":", expr «expr ⊆ »(Icc 0 1, «expr ⁻¹' »(g, s))] [],
  { rw ["[", "<-", expr image_subset_iff, ",", "<-", expr segment_eq_image', "]"] [],
    apply [expr hs.segment_subset xs ys] },
  have [] [":", expr «expr = »(f x, f (g 0))] [],
  by { simp [] [] ["only"] ["[", expr g, "]"] [] [],
    rw ["[", expr zero_smul, ",", expr add_zero, "]"] [] },
  rw [expr this] [],
  have [] [":", expr «expr = »(f y, f (g 1))] [],
  by { simp [] [] ["only"] ["[", expr g, "]"] [] [],
    rw ["[", expr one_smul, ",", expr add_sub_cancel'_right, "]"] [] },
  rw [expr this] [],
  have [ident D2] [":", expr ∀
   t «expr ∈ » Icc (0 : exprℝ()) 1, has_deriv_within_at «expr ∘ »(f, g) (f' (g t) «expr - »(y, x)) (Icc 0 1) t] [],
  { intros [ident t, ident ht],
    have [] [":", expr has_fderiv_within_at f ((f' (g t)).restrict_scalars exprℝ()) s (g t)] [],
    from [expr hf (g t) (segm ht)],
    exact [expr this.comp_has_deriv_within_at _ (Dg t).has_deriv_within_at segm] },
  apply [expr norm_image_sub_le_of_norm_deriv_le_segment_01' D2],
  refine [expr λ t ht, le_of_op_norm_le _ _ _],
  exact [expr bound (g t) «expr $ »(segm, Ico_subset_Icc_self ht)]
end

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `has_fderiv_within` and
`lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_has_fderiv_within_le {C :  ℝ≥0 }
  (hf : ∀ x _ : x ∈ s, HasFderivWithinAt f (f' x) s x) (bound : ∀ x _ : x ∈ s, ∥f' x∥₊ ≤ C) (hs : Convex ℝ s) :
  LipschitzOnWith C f s :=
  by 
    rw [lipschitz_on_with_iff_norm_sub_le]
    intro x x_in y y_in 
    exact hs.norm_image_sub_le_of_norm_has_fderiv_within_le hf bound y_in x_in

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `∥f' x∥₊`, `f` is
`K`-Lipschitz on some neighborhood of `x` within `s`. See also
`convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at` for a version that claims
existence of `K` instead of an explicit estimate. -/
theorem exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt (hs : Convex ℝ s) {f : E → G}
  (hder : ∀ᶠy in 𝓝[s] x, HasFderivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) (K :  ℝ≥0 )
  (hK : ∥f' x∥₊ < K) : ∃ (t : _)(_ : t ∈ 𝓝[s] x), LipschitzOnWith K f t :=
  by 
    obtain ⟨ε, ε0, hε⟩ : ∃ (ε : _)(_ : ε > 0), ball x ε ∩ s ⊆ { y | HasFderivWithinAt f (f' y) s y ∧ ∥f' y∥₊ < K }
    exact mem_nhds_within_iff.1 (hder.and$ hcont.nnnorm.eventually (gt_mem_nhds hK))
    rw [inter_comm] at hε 
    refine' ⟨s ∩ ball x ε, inter_mem_nhds_within _ (ball_mem_nhds _ ε0), _⟩
    exact
      (hs.inter (convex_ball _ _)).lipschitz_on_with_of_nnnorm_has_fderiv_within_le
        (fun y hy => (hε hy).1.mono (inter_subset_left _ _)) fun y hy => (hε hy).2.le

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `∥f' x∥₊`, `f` is Lipschitz
on some neighborhood of `x` within `s`. See also
`convex.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt` for a version
with an explicit estimate on the Lipschitz constant. -/
theorem exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at (hs : Convex ℝ s) {f : E → G}
  (hder : ∀ᶠy in 𝓝[s] x, HasFderivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
  ∃ (K : _)(t : _)(_ : t ∈ 𝓝[s] x), LipschitzOnWith K f t :=
  (no_top _).imp$ hs.exists_nhds_within_lipschitz_on_with_of_has_fderiv_within_at_of_nnnorm_lt hder hcont

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderiv_within`. -/
theorem norm_image_sub_le_of_norm_fderiv_within_le (hf : DifferentiableOn 𝕜 f s)
  (bound : ∀ x _ : x ∈ s, ∥fderivWithin 𝕜 f s x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
  ∥f y - f x∥ ≤ C*∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv_within` and
`lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_fderiv_within_le {C :  ℝ≥0 } (hf : DifferentiableOn 𝕜 f s)
  (bound : ∀ x _ : x ∈ s, ∥fderivWithin 𝕜 f s x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt) bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀ x _ : x ∈ s, DifferentiableAt 𝕜 f x)
  (bound : ∀ x _ : x ∈ s, ∥fderiv 𝕜 f x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C*∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivAt.HasFderivWithinAt) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_fderiv_le {C :  ℝ≥0 } (hf : ∀ x _ : x ∈ s, DifferentiableAt 𝕜 f x)
  (bound : ∀ x _ : x ∈ s, ∥fderiv 𝕜 f x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivAt.HasFderivWithinAt) bound

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`has_fderiv_within`. -/
theorem norm_image_sub_le_of_norm_has_fderiv_within_le'
(hf : ∀ x «expr ∈ » s, has_fderiv_within_at f (f' x) s x)
(bound : ∀ x «expr ∈ » s, «expr ≤ »(«expr∥ ∥»(«expr - »(f' x, φ)), C))
(hs : convex exprℝ() s)
(xs : «expr ∈ »(x, s))
(ys : «expr ∈ »(y, s)) : «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(f y, f x), φ «expr - »(y, x))), «expr * »(C, «expr∥ ∥»(«expr - »(y, x)))) :=
begin
  let [ident g] [] [":=", expr λ y, «expr - »(f y, φ y)],
  have [ident hg] [":", expr ∀
   x «expr ∈ » s, has_fderiv_within_at g «expr - »(f' x, φ) s x] [":=", expr λ
   x xs, (hf x xs).sub φ.has_fderiv_within_at],
  calc
    «expr = »(«expr∥ ∥»(«expr - »(«expr - »(f y, f x), φ «expr - »(y, x))), «expr∥ ∥»(«expr - »(«expr - »(f y, f x), «expr - »(φ y, φ x)))) : by simp [] [] [] [] [] []
    «expr = »(..., «expr∥ ∥»(«expr - »(«expr - »(f y, φ y), «expr - »(f x, φ x)))) : by abel [] [] []
    «expr = »(..., «expr∥ ∥»(«expr - »(g y, g x))) : by simp [] [] [] [] [] []
    «expr ≤ »(..., «expr * »(C, «expr∥ ∥»(«expr - »(y, x)))) : convex.norm_image_sub_le_of_norm_has_fderiv_within_le hg bound hs xs ys
end

/-- Variant of the mean value inequality on a convex set. Version with `fderiv_within`. -/
theorem norm_image_sub_le_of_norm_fderiv_within_le' (hf : DifferentiableOn 𝕜 f s)
  (bound : ∀ x _ : x ∈ s, ∥fderivWithin 𝕜 f s x - φ∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
  ∥f y - f x - φ (y - x)∥ ≤ C*∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le' (fun x hx => (hf x hx).HasFderivWithinAt) bound xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀ x _ : x ∈ s, DifferentiableAt 𝕜 f x)
  (bound : ∀ x _ : x ∈ s, ∥fderiv 𝕜 f x - φ∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
  ∥f y - f x - φ (y - x)∥ ≤ C*∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_fderiv_within_le' (fun x hx => (hf x hx).HasFderivAt.HasFderivWithinAt) bound xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem is_const_of_fderiv_within_eq_zero (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
  (hf' : ∀ x _ : x ∈ s, fderivWithin 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  have bound : ∀ x _ : x ∈ s, ∥fderivWithin 𝕜 f s x∥ ≤ 0 :=
    fun x hx =>
      by 
        simp only [hf' x hx, norm_zero]
  by 
    simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
      hs.norm_image_sub_le_of_norm_fderiv_within_le hf bound hx hy

theorem _root_.is_const_of_fderiv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0) (x y : E) :
  f x = f y :=
  convex_univ.is_const_of_fderiv_within_eq_zero hf.differentiable_on
    (fun x _ =>
      by 
        rw [fderiv_within_univ] <;> exact hf' x)
    trivialₓ trivialₓ

end Convex

namespace Convex

variable{f f' : 𝕜 → G}{s : Set 𝕜}{x y : 𝕜}

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `has_deriv_within`. -/
theorem norm_image_sub_le_of_norm_has_deriv_within_le {C : ℝ} (hf : ∀ x _ : x ∈ s, HasDerivWithinAt f (f' x) s x)
  (bound : ∀ x _ : x ∈ s, ∥f' x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C*∥y - x∥ :=
  Convex.norm_image_sub_le_of_norm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt)
    (fun x hx =>
      le_transₓ
        (by 
          simp )
        (bound x hx))
    hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `has_deriv_within` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_has_deriv_within_le {C :  ℝ≥0 } (hs : Convex ℝ s)
  (hf : ∀ x _ : x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x _ : x ∈ s, ∥f' x∥₊ ≤ C) : LipschitzOnWith C f s :=
  Convex.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (fun x hx => (hf x hx).HasFderivWithinAt)
    (fun x hx =>
      le_transₓ
        (by 
          simp )
        (bound x hx))
    hs

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv_within` -/
theorem norm_image_sub_le_of_norm_deriv_within_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
  (bound : ∀ x _ : x ∈ s, ∥derivWithin f s x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
  ∥f y - f x∥ ≤ C*∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv_within` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_deriv_within_le {C :  ℝ≥0 } (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
  (bound : ∀ x _ : x ∈ s, ∥derivWithin f s x∥₊ ≤ C) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivWithinAt) bound

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀ x _ : x ∈ s, DifferentiableAt 𝕜 f x)
  (bound : ∀ x _ : x ∈ s, ∥deriv f x∥ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ∥f y - f x∥ ≤ C*∥y - x∥ :=
  hs.norm_image_sub_le_of_norm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivAt.HasDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `lipschitz_on_with`. -/
theorem lipschitz_on_with_of_nnnorm_deriv_le {C :  ℝ≥0 } (hf : ∀ x _ : x ∈ s, DifferentiableAt 𝕜 f x)
  (bound : ∀ x _ : x ∈ s, ∥deriv f x∥₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitz_on_with_of_nnnorm_has_deriv_within_le (fun x hx => (hf x hx).HasDerivAt.HasDerivWithinAt) bound

end Convex

end 

/-! ### Functions `[a, b] → ℝ`. -/


section Interval

variable(f f' :
    ℝ →
      ℝ){a b :
    ℝ}(hab :
    a <
      b)(hfc :
    ContinuousOn f
      (Icc a
        b))(hff' :
    ∀ x _ : x ∈ Ioo a b,
      HasDerivAt f (f' x)
        x)(hfd :
    DifferentiableOn ℝ f
      (Ioo a
        b))(g g' :
    ℝ →
      ℝ)(hgc :
    ContinuousOn g (Icc a b))(hgg' : ∀ x _ : x ∈ Ioo a b, HasDerivAt g (g' x) x)(hgd : DifferentiableOn ℝ g (Ioo a b))

include hab hfc hff' hgc hgg'

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy's **Mean Value Theorem**, `has_deriv_at` version. -/
theorem exists_ratio_has_deriv_at_eq_ratio_slope : «expr∃ , »((c «expr ∈ » Ioo a b), «expr = »(«expr * »(«expr - »(g b, g a), f' c), «expr * »(«expr - »(f b, f a), g' c))) :=
begin
  let [ident h] [] [":=", expr λ
   x, «expr - »(«expr * »(«expr - »(g b, g a), f x), «expr * »(«expr - »(f b, f a), g x))],
  have [ident hI] [":", expr «expr = »(h a, h b)] [],
  { simp [] [] ["only"] ["[", expr h, "]"] [] [],
    ring [] },
  let [ident h'] [] [":=", expr λ
   x, «expr - »(«expr * »(«expr - »(g b, g a), f' x), «expr * »(«expr - »(f b, f a), g' x))],
  have [ident hhh'] [":", expr ∀ x «expr ∈ » Ioo a b, has_deriv_at h (h' x) x] [],
  from [expr λ x hx, ((hff' x hx).const_mul «expr - »(g b, g a)).sub ((hgg' x hx).const_mul «expr - »(f b, f a))],
  have [ident hhc] [":", expr continuous_on h (Icc a b)] [],
  from [expr (continuous_on_const.mul hfc).sub (continuous_on_const.mul hgc)],
  rcases [expr exists_has_deriv_at_eq_zero h h' hab hhc hI hhh', "with", "⟨", ident c, ",", ident cmem, ",", ident hc, "⟩"],
  exact [expr ⟨c, cmem, sub_eq_zero.1 hc⟩]
end

omit hfc hgc

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy's **Mean Value Theorem**, extended `has_deriv_at` version. -/
theorem exists_ratio_has_deriv_at_eq_ratio_slope'
{lfa lga lfb lgb : exprℝ()}
(hff' : ∀ x «expr ∈ » Ioo a b, has_deriv_at f (f' x) x)
(hgg' : ∀ x «expr ∈ » Ioo a b, has_deriv_at g (g' x) x)
(hfa : tendsto f «expr𝓝[ ] »(Ioi a, a) (expr𝓝() lfa))
(hga : tendsto g «expr𝓝[ ] »(Ioi a, a) (expr𝓝() lga))
(hfb : tendsto f «expr𝓝[ ] »(Iio b, b) (expr𝓝() lfb))
(hgb : tendsto g «expr𝓝[ ] »(Iio b, b) (expr𝓝() lgb)) : «expr∃ , »((c «expr ∈ » Ioo a b), «expr = »(«expr * »(«expr - »(lgb, lga), f' c), «expr * »(«expr - »(lfb, lfa), g' c))) :=
begin
  let [ident h] [] [":=", expr λ
   x, «expr - »(«expr * »(«expr - »(lgb, lga), f x), «expr * »(«expr - »(lfb, lfa), g x))],
  have [ident hha] [":", expr tendsto h «expr𝓝[ ] »(Ioi a, a) «expr $ »(expr𝓝(), «expr - »(«expr * »(lgb, lfa), «expr * »(lfb, lga)))] [],
  { have [] [":", expr tendsto h «expr𝓝[ ] »(Ioi a, a) «expr $ »(expr𝓝(), «expr - »(«expr * »(«expr - »(lgb, lga), lfa), «expr * »(«expr - »(lfb, lfa), lga)))] [":=", expr (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)],
    convert [] [expr this] ["using", 2],
    ring [] },
  have [ident hhb] [":", expr tendsto h «expr𝓝[ ] »(Iio b, b) «expr $ »(expr𝓝(), «expr - »(«expr * »(lgb, lfa), «expr * »(lfb, lga)))] [],
  { have [] [":", expr tendsto h «expr𝓝[ ] »(Iio b, b) «expr $ »(expr𝓝(), «expr - »(«expr * »(«expr - »(lgb, lga), lfb), «expr * »(«expr - »(lfb, lfa), lgb)))] [":=", expr (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)],
    convert [] [expr this] ["using", 2],
    ring [] },
  let [ident h'] [] [":=", expr λ
   x, «expr - »(«expr * »(«expr - »(lgb, lga), f' x), «expr * »(«expr - »(lfb, lfa), g' x))],
  have [ident hhh'] [":", expr ∀ x «expr ∈ » Ioo a b, has_deriv_at h (h' x) x] [],
  { intros [ident x, ident hx],
    exact [expr ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)] },
  rcases [expr exists_has_deriv_at_eq_zero' hab hha hhb hhh', "with", "⟨", ident c, ",", ident cmem, ",", ident hc, "⟩"],
  exact [expr ⟨c, cmem, sub_eq_zero.1 hc⟩]
end

include hfc

omit hgg'

/-- Lagrange's Mean Value Theorem, `has_deriv_at` version -/
theorem exists_has_deriv_at_eq_slope : ∃ (c : _)(_ : c ∈ Ioo a b), f' c = (f b - f a) / (b - a) :=
  by 
    rcases
      exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff' id 1 continuous_id.continuous_on
        fun x hx => has_deriv_at_id x with
      ⟨c, cmem, hc⟩
    use c, cmem 
    simp only [_root_.id, Pi.one_apply, mul_oneₓ] at hc 
    rw [←hc, mul_div_cancel_left]
    exact ne_of_gtₓ (sub_pos.2 hab)

omit hff'

/-- Cauchy's Mean Value Theorem, `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope :
  ∃ (c : _)(_ : c ∈ Ioo a b), ((g b - g a)*deriv f c) = (f b - f a)*deriv g c :=
  exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
      (fun x hx => ((hfd x hx).DifferentiableAt$ IsOpen.mem_nhds is_open_Ioo hx).HasDerivAt) g (deriv g) hgc$
    fun x hx => ((hgd x hx).DifferentiableAt$ IsOpen.mem_nhds is_open_Ioo hx).HasDerivAt

omit hfc

/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ} (hdf : DifferentiableOn ℝ f$ Ioo a b)
  (hdg : DifferentiableOn ℝ g$ Ioo a b) (hfa : tendsto f (𝓝[Ioi a] a) (𝓝 lfa)) (hga : tendsto g (𝓝[Ioi a] a) (𝓝 lga))
  (hfb : tendsto f (𝓝[Iio b] b) (𝓝 lfb)) (hgb : tendsto g (𝓝[Iio b] b) (𝓝 lgb)) :
  ∃ (c : _)(_ : c ∈ Ioo a b), ((lgb - lga)*deriv f c) = (lfb - lfa)*deriv g c :=
  exists_ratio_has_deriv_at_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).DifferentiableAt$ Ioo_mem_nhds hx.1 hx.2).HasDerivAt)
    (fun x hx => ((hdg x hx).DifferentiableAt$ Ioo_mem_nhds hx.1 hx.2).HasDerivAt) hfa hga hfb hgb

/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
theorem exists_deriv_eq_slope : ∃ (c : _)(_ : c ∈ Ioo a b), deriv f c = (f b - f a) / (b - a) :=
  exists_has_deriv_at_eq_slope f (deriv f) hab hfc
    fun x hx => ((hfd x hx).DifferentiableAt$ IsOpen.mem_nhds is_open_Ioo hx).HasDerivAt

end Interval

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.mul_sub_lt_image_sub_of_lt_deriv
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
{C}
(hf'_gt : ∀
 x «expr ∈ » interior D, «expr < »(C, deriv f x)) : ∀
x y «expr ∈ » D, «expr < »(x, y) → «expr < »(«expr * »(C, «expr - »(y, x)), «expr - »(f y, f x)) :=
begin
  assume [binders (x y hx hy hxy)],
  have [ident hxyD] [":", expr «expr ⊆ »(Icc x y, D)] [],
  from [expr hD.ord_connected.out hx hy],
  have [ident hxyD'] [":", expr «expr ⊆ »(Ioo x y, interior D)] [],
  from [expr subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩],
  obtain ["⟨", ident a, ",", ident a_mem, ",", ident ha, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo x y), «expr = »(deriv f a, «expr / »(«expr - »(f y, f x), «expr - »(y, x))))],
  from [expr exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')],
  have [] [":", expr «expr < »(C, «expr / »(«expr - »(f y, f x), «expr - »(y, x)))] [],
  by { rw ["[", "<-", expr ha, "]"] [],
    exact [expr hf'_gt _ (hxyD' a_mem)] },
  exact [expr (lt_div_iff (sub_pos.2 hxy)).1 this]
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄
  (hxy : x < y) : (C*y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuous_on hf.differentiable_on (fun x _ => hf'_gt x) x
    y trivialₓ trivialₓ hxy

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.mul_sub_le_image_sub_of_le_deriv
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
{C}
(hf'_ge : ∀
 x «expr ∈ » interior D, «expr ≤ »(C, deriv f x)) : ∀
x y «expr ∈ » D, «expr ≤ »(x, y) → «expr ≤ »(«expr * »(C, «expr - »(y, x)), «expr - »(f y, f x)) :=
begin
  assume [binders (x y hx hy hxy)],
  cases [expr eq_or_lt_of_le hxy] ["with", ident hxy', ident hxy'],
  by rw ["[", expr hxy', ",", expr sub_self, ",", expr sub_self, ",", expr mul_zero, "]"] [],
  have [ident hxyD] [":", expr «expr ⊆ »(Icc x y, D)] [],
  from [expr hD.ord_connected.out hx hy],
  have [ident hxyD'] [":", expr «expr ⊆ »(Ioo x y, interior D)] [],
  from [expr subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩],
  obtain ["⟨", ident a, ",", ident a_mem, ",", ident ha, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo x y), «expr = »(deriv f a, «expr / »(«expr - »(f y, f x), «expr - »(y, x))))],
  from [expr exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')],
  have [] [":", expr «expr ≤ »(C, «expr / »(«expr - »(f y, f x), «expr - »(y, x)))] [],
  by { rw ["[", "<-", expr ha, "]"] [],
    exact [expr hf'_ge _ (hxyD' a_mem)] },
  exact [expr (le_div_iff (sub_pos.2 hxy')).1 this]
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄
  (hxy : x ≤ y) : (C*y - x) ≤ f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuous_on hf.differentiable_on (fun x _ => hf'_ge x) x
    y trivialₓ trivialₓ hxy

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
theorem convex.image_sub_lt_mul_sub_of_deriv_lt
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
{C}
(lt_hf' : ∀
 x «expr ∈ » interior D, «expr < »(deriv f x, C)) : ∀
x y «expr ∈ » D, «expr < »(x, y) → «expr < »(«expr - »(f y, f x), «expr * »(C, «expr - »(y, x))) :=
begin
  assume [binders (x y hx hy hxy)],
  have [ident hf'_gt] [":", expr ∀ x «expr ∈ » interior D, «expr < »(«expr- »(C), deriv (λ y, «expr- »(f y)) x)] [],
  { assume [binders (x hx)],
    rw ["[", expr deriv.neg, ",", expr neg_lt_neg_iff, "]"] [],
    exact [expr lt_hf' x hx] },
  simpa [] [] [] ["[", "-", ident neg_lt_neg_iff, "]"] [] ["using", expr neg_lt_neg (hD.mul_sub_lt_image_sub_of_lt_deriv hf.neg hf'.neg hf'_gt x y hx hy hxy)]
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄
  (hxy : x < y) : f y - f x < C*y - x :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuous_on hf.differentiable_on (fun x _ => lt_hf' x) x
    y trivialₓ trivialₓ hxy

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
theorem convex.image_sub_le_mul_sub_of_deriv_le
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
{C}
(le_hf' : ∀
 x «expr ∈ » interior D, «expr ≤ »(deriv f x, C)) : ∀
x y «expr ∈ » D, «expr ≤ »(x, y) → «expr ≤ »(«expr - »(f y, f x), «expr * »(C, «expr - »(y, x))) :=
begin
  assume [binders (x y hx hy hxy)],
  have [ident hf'_ge] [":", expr ∀ x «expr ∈ » interior D, «expr ≤ »(«expr- »(C), deriv (λ y, «expr- »(f y)) x)] [],
  { assume [binders (x hx)],
    rw ["[", expr deriv.neg, ",", expr neg_le_neg_iff, "]"] [],
    exact [expr le_hf' x hx] },
  simpa [] [] [] ["[", "-", ident neg_le_neg_iff, "]"] [] ["using", expr neg_le_neg (hD.mul_sub_le_image_sub_of_le_deriv hf.neg hf'.neg hf'_ge x y hx hy hxy)]
end

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C} (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄
  (hxy : x ≤ y) : f y - f x ≤ C*y - x :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuous_on hf.differentiable_on (fun x _ => le_hf' x) x
    y trivialₓ trivialₓ hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotone function on `D`.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem Convex.strict_mono_on_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : ∀ x _ : x ∈ Interior D, 0 < deriv f x) : StrictMonoOn f D :=
  by 
    rintro x hx y hy 
    simpa only [zero_mul, sub_pos] using hD.mul_sub_lt_image_sub_of_lt_deriv hf _ hf' x y hx hy 
    exact fun z hz => (differentiable_at_of_deriv_ne_zero (hf' z hz).ne').DifferentiableWithinAt

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
theorem strict_mono_of_deriv_pos {f : ℝ → ℝ} (hf' : ∀ x, 0 < deriv f x) : StrictMono f :=
  strict_mono_on_univ.1$
    convex_univ.strict_mono_on_of_deriv_pos
      (fun z _ => (differentiable_at_of_deriv_ne_zero (hf' z).ne').DifferentiableWithinAt.ContinuousWithinAt)
      fun x _ => hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
theorem Convex.monotone_on_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (Interior D)) (hf'_nonneg : ∀ x _ : x ∈ Interior D, 0 ≤ deriv f x) : MonotoneOn f D :=
  fun x hx y hy hxy =>
    by 
      simpa only [zero_mul, sub_nonneg] using hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x y hx hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) : Monotone f :=
  monotone_on_univ.1$
    convex_univ.monotone_on_of_deriv_nonneg hf.continuous.continuous_on hf.differentiable_on fun x _ => hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly antitone function on `D`. -/
theorem Convex.strict_anti_on_of_deriv_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : ∀ x _ : x ∈ Interior D, deriv f x < 0) : StrictAntiOn f D :=
  fun x hx y =>
    by 
      simpa only [zero_mul, sub_lt_zero] using
        hD.image_sub_lt_mul_sub_of_deriv_lt hf
          (fun z hz => (differentiable_at_of_deriv_ne_zero (hf' z hz).Ne).DifferentiableWithinAt) hf' x y hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly antitone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly negative. -/
theorem strict_anti_of_deriv_neg {f : ℝ → ℝ} (hf' : ∀ x, deriv f x < 0) : StrictAnti f :=
  strict_anti_on_univ.1$
    convex_univ.strict_anti_on_of_deriv_neg
      (fun z _ => (differentiable_at_of_deriv_ne_zero (hf' z).Ne).DifferentiableWithinAt.ContinuousWithinAt)
      fun x _ => hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
theorem Convex.antitone_on_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (Interior D)) (hf'_nonpos : ∀ x _ : x ∈ Interior D, deriv f x ≤ 0) : AntitoneOn f D :=
  fun x hx y hy hxy =>
    by 
      simpa only [zero_mul, sub_nonpos] using hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x y hx hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is an antitone function. -/
theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) : Antitone f :=
  antitone_on_univ.1$
    convex_univ.antitone_on_of_deriv_nonpos hf.continuous.continuous_on hf.differentiable_on fun x _ => hf' x

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem monotone_on.convex_on_of_deriv
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
(hf'_mono : monotone_on (deriv f) (interior D)) : convex_on exprℝ() D f :=
convex_on_of_slope_mono_adjacent hD (begin
   intros [ident x, ident y, ident z, ident hx, ident hz, ident hxy, ident hyz],
   have [ident hxzD] [":", expr «expr ⊆ »(Icc x z, D)] [],
   from [expr hD.ord_connected.out hx hz],
   have [ident hxyD] [":", expr «expr ⊆ »(Icc x y, D)] [],
   from [expr subset.trans «expr $ »(Icc_subset_Icc_right, le_of_lt hyz) hxzD],
   have [ident hxyD'] [":", expr «expr ⊆ »(Ioo x y, interior D)] [],
   from [expr subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩],
   have [ident hyzD] [":", expr «expr ⊆ »(Icc y z, D)] [],
   from [expr subset.trans «expr $ »(Icc_subset_Icc_left, le_of_lt hxy) hxzD],
   have [ident hyzD'] [":", expr «expr ⊆ »(Ioo y z, interior D)] [],
   from [expr subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩],
   obtain ["⟨", ident a, ",", "⟨", ident hxa, ",", ident hay, "⟩", ",", ident ha, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo x y), «expr = »(deriv f a, «expr / »(«expr - »(f y, f x), «expr - »(y, x))))],
   from [expr exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')],
   obtain ["⟨", ident b, ",", "⟨", ident hyb, ",", ident hbz, "⟩", ",", ident hb, "⟩", ":", expr «expr∃ , »((b «expr ∈ » Ioo y z), «expr = »(deriv f b, «expr / »(«expr - »(f z, f y), «expr - »(z, y))))],
   from [expr exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')],
   rw ["[", "<-", expr ha, ",", "<-", expr hb, "]"] [],
   exact [expr hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le]
 end)

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
theorem antitone_on.concave_on_of_deriv
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
(h_anti : antitone_on (deriv f) (interior D)) : concave_on exprℝ() D f :=
begin
  have [] [":", expr monotone_on (deriv «expr- »(f)) (interior D)] [],
  { intros [ident x, ident hx, ident y, ident hy, ident hxy],
    convert [] [expr neg_le_neg (h_anti hx hy hxy)] []; convert [] [expr deriv.neg] [] },
  exact [expr neg_convex_on_iff.mp (this.convex_on_of_deriv hD hf.neg hf'.neg)]
end

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is strictly monotone on the interior, then `f` is strictly convex on `D`. -/
theorem strict_mono_on.strict_convex_on_of_deriv
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
(hf'_mono : strict_mono_on (deriv f) (interior D)) : strict_convex_on exprℝ() D f :=
strict_convex_on_of_slope_strict_mono_adjacent hD (begin
   intros [ident x, ident y, ident z, ident hx, ident hz, ident hxy, ident hyz],
   have [ident hxzD] [":", expr «expr ⊆ »(Icc x z, D)] [],
   from [expr hD.ord_connected.out hx hz],
   have [ident hxyD] [":", expr «expr ⊆ »(Icc x y, D)] [],
   from [expr subset.trans «expr $ »(Icc_subset_Icc_right, le_of_lt hyz) hxzD],
   have [ident hxyD'] [":", expr «expr ⊆ »(Ioo x y, interior D)] [],
   from [expr subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hxyD⟩],
   have [ident hyzD] [":", expr «expr ⊆ »(Icc y z, D)] [],
   from [expr subset.trans «expr $ »(Icc_subset_Icc_left, le_of_lt hxy) hxzD],
   have [ident hyzD'] [":", expr «expr ⊆ »(Ioo y z, interior D)] [],
   from [expr subset_sUnion_of_mem ⟨is_open_Ioo, subset.trans Ioo_subset_Icc_self hyzD⟩],
   obtain ["⟨", ident a, ",", "⟨", ident hxa, ",", ident hay, "⟩", ",", ident ha, "⟩", ":", expr «expr∃ , »((a «expr ∈ » Ioo x y), «expr = »(deriv f a, «expr / »(«expr - »(f y, f x), «expr - »(y, x))))],
   from [expr exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')],
   obtain ["⟨", ident b, ",", "⟨", ident hyb, ",", ident hbz, "⟩", ",", ident hb, "⟩", ":", expr «expr∃ , »((b «expr ∈ » Ioo y z), «expr = »(deriv f b, «expr / »(«expr - »(f z, f y), «expr - »(z, y))))],
   from [expr exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')],
   rw ["[", "<-", expr ha, ",", "<-", expr hb, "]"] [],
   exact [expr hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)]
 end)

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is strictly antitone on the interior, then `f` is strictly concave on `D`. -/
theorem strict_anti_on.strict_concave_on_of_deriv
{D : set exprℝ()}
(hD : convex exprℝ() D)
{f : exprℝ() → exprℝ()}
(hf : continuous_on f D)
(hf' : differentiable_on exprℝ() f (interior D))
(h_anti : strict_anti_on (deriv f) (interior D)) : strict_concave_on exprℝ() D f :=
begin
  have [] [":", expr strict_mono_on (deriv «expr- »(f)) (interior D)] [],
  { intros [ident x, ident hx, ident y, ident hy, ident hxy],
    convert [] [expr neg_lt_neg (h_anti hx hy hxy)] []; convert [] [expr deriv.neg] [] },
  exact [expr neg_strict_convex_on_iff.mp (this.strict_convex_on_of_deriv hD hf.neg hf'.neg)]
end

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem Monotone.convex_on_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf'_mono : Monotone (deriv f)) :
  ConvexOn ℝ univ f :=
  (hf'_mono.monotone_on _).convex_on_of_deriv convex_univ hf.continuous.continuous_on hf.differentiable_on

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
theorem Antitone.concave_on_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf'_anti : Antitone (deriv f)) :
  ConcaveOn ℝ univ f :=
  (hf'_anti.antitone_on _).concave_on_of_deriv convex_univ hf.continuous.continuous_on hf.differentiable_on

/-- If a function `f` is differentiable and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. -/
theorem StrictMono.strict_convex_on_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
  (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strict_mono_on _).strict_convex_on_of_deriv convex_univ hf.continuous.continuous_on hf.differentiable_on

/-- If a function `f` is differentiable and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. -/
theorem StrictAnti.strict_concave_on_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
  (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strict_anti_on _).strict_concave_on_of_deriv convex_univ hf.continuous.continuous_on hf.differentiable_on

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convex_on_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (Interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (Interior D))
  (hf''_nonneg : ∀ x _ : x ∈ Interior D, 0 ≤ (deriv^[2]) f x) : ConvexOn ℝ D f :=
  (hD.interior.monotone_on_of_deriv_nonneg hf''.continuous_on
          (by 
            rwa [interior_interior])$
        by 
          rwa [interior_interior]).convex_on_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concave_on_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (Interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (Interior D))
  (hf''_nonpos : ∀ x _ : x ∈ Interior D, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ D f :=
  (hD.interior.antitone_on_of_deriv_nonpos hf''.continuous_on
          (by 
            rwa [interior_interior])$
        by 
          rwa [interior_interior]).concave_on_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is strictly positive on the interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly positive. -/
theorem strict_convex_on_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (Interior D)) (hf'' : ∀ x _ : x ∈ Interior D, 0 < ((deriv^[2]) f) x) :
  StrictConvexOn ℝ D f :=
  ((hD.interior.strict_mono_on_of_deriv_pos
          fun z hz => (differentiable_at_of_deriv_ne_zero (hf'' z hz).ne').DifferentiableWithinAt.ContinuousWithinAt)$
        by 
          rwa [interior_interior]).strict_convex_on_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is strictly negative on the interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative. -/
theorem strict_concave_on_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (Interior D)) (hf'' : ∀ x _ : x ∈ Interior D, (deriv^[2]) f x < 0) :
  StrictConcaveOn ℝ D f :=
  ((hD.interior.strict_anti_on_of_deriv_neg
          fun z hz => (differentiable_at_of_deriv_ne_zero (hf'' z hz).Ne).DifferentiableWithinAt.ContinuousWithinAt)$
        by 
          rwa [interior_interior]).strict_concave_on_of_deriv
    hD hf hf'

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convex_on_open_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) (hD₂ : IsOpen D) {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
  (hf''_nonneg : ∀ x _ : x ∈ D, 0 ≤ ((deriv^[2]) f) x) : ConvexOn ℝ D f :=
  convex_on_of_deriv2_nonneg hD hf'.continuous_on
    (by 
      simpa [hD₂.interior_eq] using hf')
    (by 
      simpa [hD₂.interior_eq] using hf'')
    (by 
      simpa [hD₂.interior_eq] using hf''_nonneg)

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concave_on_open_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) (hD₂ : IsOpen D) {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
  (hf''_nonpos : ∀ x _ : x ∈ D, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ D f :=
  concave_on_of_deriv2_nonpos hD hf'.continuous_on
    (by 
      simpa [hD₂.interior_eq] using hf')
    (by 
      simpa [hD₂.interior_eq] using hf'')
    (by 
      simpa [hD₂.interior_eq] using hf''_nonpos)

/-- If a function `f` is twice differentiable on a open convex set `D ⊆ ℝ` and
`f''` is strictly positive on `D`, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly positive. -/
theorem strict_convex_on_open_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) (hD₂ : IsOpen D) {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f D) (hf'' : ∀ x _ : x ∈ D, 0 < ((deriv^[2]) f) x) : StrictConvexOn ℝ D f :=
  strict_convex_on_of_deriv2_pos hD hf'.continuous_on
      (by 
        simpa [hD₂.interior_eq] using hf')$
    by 
      simpa [hD₂.interior_eq] using hf''

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is strictly negative on `D`, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative. -/
theorem strict_concave_on_open_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) (hD₂ : IsOpen D) {f : ℝ → ℝ}
  (hf' : DifferentiableOn ℝ f D) (hf'' : ∀ x _ : x ∈ D, (deriv^[2]) f x < 0) : StrictConcaveOn ℝ D f :=
  strict_concave_on_of_deriv2_neg hD hf'.continuous_on
      (by 
        simpa [hD₂.interior_eq] using hf')$
    by 
      simpa [hD₂.interior_eq] using hf''

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convex_on_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f) (hf'' : Differentiable ℝ (deriv f))
  (hf''_nonneg : ∀ x, 0 ≤ ((deriv^[2]) f) x) : ConvexOn ℝ univ f :=
  convex_on_open_of_deriv2_nonneg convex_univ is_open_univ hf'.differentiable_on hf''.differentiable_on
    fun x _ => hf''_nonneg x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concave_on_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f) (hf'' : Differentiable ℝ (deriv f))
  (hf''_nonpos : ∀ x, (deriv^[2]) f x ≤ 0) : ConcaveOn ℝ univ f :=
  concave_on_open_of_deriv2_nonpos convex_univ is_open_univ hf'.differentiable_on hf''.differentiable_on
    fun x _ => hf''_nonpos x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly positive. -/
theorem strict_convex_on_univ_of_deriv2_pos {f : ℝ → ℝ} (hf' : Differentiable ℝ f) (hf'' : ∀ x, 0 < ((deriv^[2]) f) x) :
  StrictConvexOn ℝ univ f :=
  strict_convex_on_open_of_deriv2_pos convex_univ is_open_univ hf'.differentiable_on$ fun x _ => hf'' x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative. -/
theorem strict_concave_on_univ_of_deriv2_neg {f : ℝ → ℝ} (hf' : Differentiable ℝ f) (hf'' : ∀ x, (deriv^[2]) f x < 0) :
  StrictConcaveOn ℝ univ f :=
  strict_concave_on_open_of_deriv2_neg convex_univ is_open_univ hf'.differentiable_on$ fun x _ => hf'' x

/-! ### Functions `f : E → ℝ` -/


-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lagrange's Mean Value Theorem, applied to convex domains. -/
theorem domain_mvt
{f : E → exprℝ()}
{s : set E}
{x y : E}
{f' : E → «expr →L[ ] »(E, exprℝ(), exprℝ())}
(hf : ∀ x «expr ∈ » s, has_fderiv_within_at f (f' x) s x)
(hs : convex exprℝ() s)
(xs : «expr ∈ »(x, s))
(ys : «expr ∈ »(y, s)) : «expr∃ , »((z «expr ∈ » segment exprℝ() x y), «expr = »(«expr - »(f y, f x), f' z «expr - »(y, x))) :=
begin
  have [ident hIccIoo] [] [":=", expr @Ioo_subset_Icc_self exprℝ() _ 0 1],
  set [] [ident g] [":", expr exprℝ() → E] [":="] [expr λ t, «expr + »(x, «expr • »(t, «expr - »(y, x)))] [],
  have [ident hseg] [":", expr ∀ t «expr ∈ » Icc (0 : exprℝ()) 1, «expr ∈ »(g t, segment exprℝ() x y)] [],
  { rw [expr segment_eq_image'] [],
    simp [] [] ["only"] ["[", expr mem_image, ",", expr and_imp, ",", expr add_right_inj, "]"] [] [],
    intros [ident t, ident ht],
    exact [expr ⟨t, ht, rfl⟩] },
  have [ident hseg'] [":", expr «expr ⊆ »(Icc 0 1, «expr ⁻¹' »(g, s))] [],
  { rw ["<-", expr image_subset_iff] [],
    unfold [ident image] [],
    change [expr ∀ _, _] [] [],
    intros [ident z, ident Hz],
    rw [expr mem_set_of_eq] ["at", ident Hz],
    rcases [expr Hz, "with", "⟨", ident t, ",", ident Ht, ",", ident hgt, "⟩"],
    rw ["<-", expr hgt] [],
    exact [expr hs.segment_subset xs ys (hseg t Ht)] },
  have [ident hfg] [":", expr ∀
   t «expr ∈ » Icc (0 : exprℝ()) 1, has_deriv_within_at «expr ∘ »(f, g) ((f' (g t) : E → exprℝ()) «expr - »(y, x)) (Icc (0 : exprℝ()) 1) t] [],
  { intros [ident t, ident Ht],
    have [ident hg] [":", expr has_deriv_at g «expr - »(y, x) t] [],
    { have [] [] [":=", expr ((has_deriv_at_id t).smul_const «expr - »(y, x)).const_add x],
      rwa [expr one_smul] ["at", ident this] },
    exact [expr «expr $ »(hf (g t), hseg' Ht).comp_has_deriv_within_at _ hg.has_deriv_within_at hseg'] },
  have [ident hMVT] [":", expr «expr∃ , »((t «expr ∈ » Ioo (0 : exprℝ()) 1), «expr = »((f' (g t) : E → exprℝ()) «expr - »(y, x), «expr / »(«expr - »(f (g 1), f (g 0)), «expr - »(1, 0))))] [],
  { refine [expr exists_has_deriv_at_eq_slope «expr ∘ »(f, g) _ (by norm_num [] []) _ _],
    { unfold [ident continuous_on] [],
      exact [expr λ t Ht, (hfg t Ht).continuous_within_at] },
    { refine [expr λ t Ht, «expr $ »(hfg t, hIccIoo Ht).has_deriv_at _],
      refine [expr _root_.mem_nhds_iff.mpr _],
      use [expr Ioo (0 : exprℝ()) 1],
      refine [expr ⟨hIccIoo, _, Ht⟩],
      simp [] [] [] ["[", expr real.Ioo_eq_ball, ",", expr is_open_ball, "]"] [] [] } },
  rcases [expr hMVT, "with", "⟨", ident t, ",", ident Ht, ",", ident hMVT', "⟩"],
  use [expr g t],
  refine [expr ⟨«expr $ »(hseg t, hIccIoo Ht), _⟩],
  simp [] [] [] ["[", expr g, ",", expr hMVT', "]"] [] []
end

section IsROrC

/-!
### Vector-valued functions `f : E → F`.  Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/


variable{𝕜 :
    Type
      _}[IsROrC
      𝕜]{G :
    Type
      _}[NormedGroup
      G][NormedSpace 𝕜 G]{H : Type _}[NormedGroup H][NormedSpace 𝕜 H]{f : G → H}{f' : G → G →L[𝕜] H}{x : G}

-- error in Analysis.Calculus.MeanValue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at
(hder : «expr∀ᶠ in , »((y), expr𝓝() x, has_fderiv_at f (f' y) y))
(hcont : continuous_at f' x) : has_strict_fderiv_at f (f' x) x :=
begin
  refine [expr is_o_iff.mpr (λ c hc, metric.eventually_nhds_iff_ball.mpr _)],
  rcases [expr metric.mem_nhds_iff.mp (inter_mem hder «expr $ »(hcont, ball_mem_nhds _ hc)), "with", "⟨", ident ε, ",", ident ε0, ",", ident hε, "⟩"],
  refine [expr ⟨ε, ε0, _⟩],
  rintros ["⟨", ident a, ",", ident b, "⟩", ident h],
  rw ["[", "<-", expr ball_prod_same, ",", expr prod_mk_mem_set_prod_eq, "]"] ["at", ident h],
  have [ident hf'] [":", expr ∀ x' «expr ∈ » ball x ε, «expr ≤ »(«expr∥ ∥»(«expr - »(f' x', f' x)), c)] [],
  { intros [ident x', ident H'],
    rw ["<-", expr dist_eq_norm] [],
    exact [expr le_of_lt (hε H').2] },
  letI [] [":", expr normed_space exprℝ() G] [":=", expr restrict_scalars.normed_space exprℝ() 𝕜 G],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 G] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  refine [expr (convex_ball _ _).norm_image_sub_le_of_norm_has_fderiv_within_le' _ hf' h.2 h.1],
  exact [expr λ y hy, (hε hy).1.has_fderiv_within_at]
end

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem has_strict_deriv_at_of_has_deriv_at_of_continuous_at {f f' : 𝕜 → G} {x : 𝕜}
  (hder : ∀ᶠy in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) : HasStrictDerivAt f (f' x) x :=
  has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at (hder.mono fun y hy => hy.has_fderiv_at)$
    (smul_rightL 𝕜 _ _ 1).Continuous.ContinuousAt.comp hcont

end IsROrC

