import Mathbin.Analysis.Convex.SpecificFunctions 
import Mathbin.Data.Real.ConjugateExponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
Young's inequality, Hölder inequality, and Minkowski inequality. Versions for integrals of some of
these inequalities are available in `measure_theory.mean_inequalities`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `real` namespace, and a version for
`nnreal`-valued functions is in the `nnreal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/


universe u v

open Finset

open_locale Classical BigOperators Nnreal Ennreal

noncomputable theory

variable{ι : Type u}(s : Finset ι)

section GeomMeanLeArithMean

/-! ### AM-GM inequality -/


namespace Real

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- AM-GM inequality: the **geometric mean is less than or equal to the arithmetic mean**, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted
(w z : ι → exprℝ())
(hw : ∀ i «expr ∈ » s, «expr ≤ »(0, w i))
(hw' : «expr = »(«expr∑ in , »((i), s, w i), 1))
(hz : ∀
 i «expr ∈ » s, «expr ≤ »(0, z i)) : «expr ≤ »(«expr∏ in , »((i), s, «expr ^ »(z i, w i)), «expr∑ in , »((i), s, «expr * »(w i, z i))) :=
begin
  by_cases [expr A, ":", expr «expr∃ , »((i «expr ∈ » s), «expr ∧ »(«expr = »(z i, 0), «expr ≠ »(w i, 0)))],
  { rcases [expr A, "with", "⟨", ident i, ",", ident his, ",", ident hzi, ",", ident hwi, "⟩"],
    rw ["[", expr prod_eq_zero his, "]"] [],
    { exact [expr sum_nonneg (λ j hj, mul_nonneg (hw j hj) (hz j hj))] },
    { rw [expr hzi] [],
      exact [expr zero_rpow hwi] } },
  { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_and, ",", expr ne.def, ",", expr not_not, "]"] [] ["at", ident A],
    have [] [] [":=", expr convex_on_exp.map_sum_le hw hw' (λ i _, «expr $ »(set.mem_univ, log (z i)))],
    simp [] [] ["only"] ["[", expr exp_sum, ",", expr («expr ∘ »), ",", expr smul_eq_mul, ",", expr mul_comm (w _) (log _), "]"] [] ["at", ident this],
    convert [] [expr this] ["using", 1]; [apply [expr prod_congr rfl], apply [expr sum_congr rfl]]; intros [ident i, ident hi],
    { cases [expr eq_or_lt_of_le (hz i hi)] ["with", ident hz, ident hz],
      { simp [] [] [] ["[", expr A i hi hz.symm, "]"] [] [] },
      { exact [expr rpow_def_of_pos hz _] } },
    { cases [expr eq_or_lt_of_le (hz i hi)] ["with", ident hz, ident hz],
      { simp [] [] [] ["[", expr A i hi hz.symm, "]"] [] [] },
      { rw ["[", expr exp_log hz, "]"] [] } } }
end

end Real

namespace Nnreal

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for `nnreal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι →  ℝ≥0 ) (hw' : (∑i in s, w i) = 1) :
  (∏i in s, z i^(w i : ℝ)) ≤ ∑i in s, w i*z i :=
  by 
    exactModCast
      Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
        (by 
          assumptionModCast)
        fun i _ => (z i).coe_nonneg

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for two `nnreal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ :  ℝ≥0 ) :
  (w₁+w₂) = 1 → ((p₁^(w₁ : ℝ))*p₂^(w₂ : ℝ)) ≤ (w₁*p₁)+w₂*p₂ :=
  by 
    simpa only [Finₓ.prod_univ_succ, Finₓ.sum_univ_succ, Finset.prod_empty, Finset.sum_empty, Fintype.univ_of_is_empty,
      Finₓ.cons_succ, Finₓ.cons_zero, add_zeroₓ, mul_oneₓ] using
      geom_mean_le_arith_mean_weighted (univ : Finset (Finₓ 2)) (Finₓ.cons w₁$ Finₓ.cons w₂ finZeroElim)
        (Finₓ.cons p₁$ Finₓ.cons p₂$ finZeroElim)

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ :  ℝ≥0 ) :
  ((w₁+w₂)+w₃) = 1 → (((p₁^(w₁ : ℝ))*p₂^(w₂ : ℝ))*p₃^(w₃ : ℝ)) ≤ ((w₁*p₁)+w₂*p₂)+w₃*p₃ :=
  by 
    simpa only [Finₓ.prod_univ_succ, Finₓ.sum_univ_succ, Finset.prod_empty, Finset.sum_empty, Fintype.univ_of_is_empty,
      Finₓ.cons_succ, Finₓ.cons_zero, add_zeroₓ, mul_oneₓ, ←add_assocₓ, mul_assocₓ] using
      geom_mean_le_arith_mean_weighted (univ : Finset (Finₓ 3)) (Finₓ.cons w₁$ Finₓ.cons w₂$ Finₓ.cons w₃ finZeroElim)
        (Finₓ.cons p₁$ Finₓ.cons p₂$ Finₓ.cons p₃ finZeroElim)

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ :  ℝ≥0 ) :
  (((w₁+w₂)+w₃)+w₄) = 1 → ((((p₁^(w₁ : ℝ))*p₂^(w₂ : ℝ))*p₃^(w₃ : ℝ))*p₄^(w₄ : ℝ)) ≤ (((w₁*p₁)+w₂*p₂)+w₃*p₃)+w₄*p₄ :=
  by 
    simpa only [Finₓ.prod_univ_succ, Finₓ.sum_univ_succ, Finset.prod_empty, Finset.sum_empty, Fintype.univ_of_is_empty,
      Finₓ.cons_succ, Finₓ.cons_zero, add_zeroₓ, mul_oneₓ, ←add_assocₓ, mul_assocₓ] using
      geom_mean_le_arith_mean_weighted (univ : Finset (Finₓ 4))
        (Finₓ.cons w₁$ Finₓ.cons w₂$ Finₓ.cons w₃$ Finₓ.cons w₄ finZeroElim)
        (Finₓ.cons p₁$ Finₓ.cons p₂$ Finₓ.cons p₃$ Finₓ.cons p₄ finZeroElim)

end Nnreal

namespace Real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
  (hw : (w₁+w₂) = 1) : ((p₁^w₁)*p₂^w₂) ≤ (w₁*p₁)+w₂*p₂ :=
  Nnreal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩$
    Nnreal.coe_eq.1$
      by 
        assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
  (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : ((w₁+w₂)+w₃) = 1) :
  (((p₁^w₁)*p₂^w₂)*p₃^w₃) ≤ ((w₁*p₁)+w₂*p₂)+w₃*p₃ :=
  Nnreal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩$
    Nnreal.coe_eq.1 hw

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
  (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hp₄ : 0 ≤ p₄) (hw : (((w₁+w₂)+w₃)+w₄) = 1) :
  ((((p₁^w₁)*p₂^w₂)*p₃^w₃)*p₄^w₄) ≤ (((w₁*p₁)+w₂*p₂)+w₃*p₃)+w₄*p₄ :=
  Nnreal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩
      ⟨p₄, hp₄⟩$
    Nnreal.coe_eq.1$
      by 
        assumption

end Real

end GeomMeanLeArithMean

section Young

/-! ### Young's inequality -/


namespace Real

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hpq : p.is_conjugate_exponent q) :
  (a*b) ≤ ((a^p) / p)+(b^q) / q :=
  by 
    simpa [←rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul] using
      geom_mean_le_arith_mean2_weighted hpq.one_div_nonneg hpq.symm.one_div_nonneg (rpow_nonneg_of_nonneg ha p)
        (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) : (a*b) ≤ ((|a|^p) / p)+(|b|^q) / q :=
  calc (a*b) ≤ |a*b| := le_abs_self (a*b)
    _ = |a|*|b| := abs_mul a b 
    _ ≤ ((|a|^p) / p)+(|b|^q) / q := Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq
    

end Real

namespace Nnreal

/-- Young's inequality, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.  -/
theorem young_inequality (a b :  ℝ≥0 ) {p q :  ℝ≥0 } (hp : 1 < p) (hpq : ((1 / p)+1 / q) = 1) :
  (a*b) ≤ ((a^(p : ℝ)) / p)+(b^(q : ℝ)) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, Nnreal.coe_eq.2 hpq⟩

/-- Young's inequality, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b :  ℝ≥0 ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  (a*b) ≤ ((a^p) / Real.toNnreal p)+(b^q) / Real.toNnreal q :=
  by 
    nthRw 0[←Real.coe_to_nnreal p hpq.nonneg]
    nthRw 0[←Real.coe_to_nnreal q hpq.symm.nonneg]
    exact young_inequality a b hpq.one_lt_nnreal hpq.inv_add_inv_conj_nnreal

end Nnreal

namespace Ennreal

/-- Young's inequality, `ℝ≥0∞` version with real conjugate exponents. -/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  (a*b) ≤ ((a^p) / Ennreal.ofReal p)+(b^q) / Ennreal.ofReal q :=
  by 
    byCases' h : a = ⊤ ∨ b = ⊤
    ·
      refine' le_transₓ le_top (le_of_eqₓ _)
      repeat' 
        rw [div_eq_mul_inv]
      cases h <;> rw [h] <;> simp [h, hpq.pos, hpq.symm.pos]
    pushNeg  at h 
    rw [←coe_to_nnreal h.left, ←coe_to_nnreal h.right, ←coe_mul, coe_rpow_of_nonneg _ hpq.nonneg,
      coe_rpow_of_nonneg _ hpq.symm.nonneg, Ennreal.ofReal, Ennreal.ofReal,
      ←@coe_div (Real.toNnreal p) _
        (by 
          simp [hpq.pos]),
      ←@coe_div (Real.toNnreal q) _
        (by 
          simp [hpq.symm.pos]),
      ←coe_add, coe_le_coe]
    exact Nnreal.young_inequality_real a.to_nnreal b.to_nnreal hpq

end Ennreal

end Young

section HolderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace Nnreal

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem inner_le_Lp_mul_Lp_of_norm_le_one
(f g : ι → «exprℝ≥0»())
{p q : exprℝ()}
(hpq : p.is_conjugate_exponent q)
(hf : «expr ≤ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), 1))
(hg : «expr ≤ »(«expr∑ in , »((i), s, «expr ^ »(g i, q)), 1)) : «expr ≤ »(«expr∑ in , »((i), s, «expr * »(f i, g i)), 1) :=
begin
  have [ident hp_ne_zero] [":", expr «expr ≠ »(real.to_nnreal p, 0)] [],
  from [expr (zero_lt_one.trans hpq.one_lt_nnreal).ne.symm],
  have [ident hq_ne_zero] [":", expr «expr ≠ »(real.to_nnreal q, 0)] [],
  from [expr (zero_lt_one.trans hpq.symm.one_lt_nnreal).ne.symm],
  calc
    «expr ≤ »(«expr∑ in , »((i), s, «expr * »(f i, g i)), «expr∑ in , »((i), s, «expr + »(«expr / »(«expr ^ »(f i, p), real.to_nnreal p), «expr / »(«expr ^ »(g i, q), real.to_nnreal q)))) : finset.sum_le_sum (λ
     i his, young_inequality_real (f i) (g i) hpq)
    «expr = »(..., «expr + »(«expr / »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), real.to_nnreal p), «expr / »(«expr∑ in , »((i), s, «expr ^ »(g i, q)), real.to_nnreal q))) : by rw ["[", expr sum_add_distrib, ",", expr sum_div, ",", expr sum_div, "]"] []
    «expr ≤ »(..., «expr + »(«expr / »(1, real.to_nnreal p), «expr / »(1, real.to_nnreal q))) : by { refine [expr add_le_add _ _],
      { rwa ["[", expr div_le_iff hp_ne_zero, ",", expr div_mul_cancel _ hp_ne_zero, "]"] [] },
      { rwa ["[", expr div_le_iff hq_ne_zero, ",", expr div_mul_cancel _ hq_ne_zero, "]"] [] } }
    «expr = »(..., 1) : hpq.inv_add_inv_conj_nnreal
end

private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι →  ℝ≥0 ) {p q : ℝ} (hpq : p.is_conjugate_exponent q)
  (hf : (∑i in s, f i^p) = 0) : (∑i in s, f i*g i) ≤ ((∑i in s, f i^p)^1 / p)*(∑i in s, g i^q)^1 / q :=
  by 
    simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul, inv_eq_zero, Ne.def, not_false_iff,
      le_zero_iff, mul_eq_zero]
    intro i his 
    left 
    rw [sum_eq_zero_iff] at hf 
    exact (rpow_eq_zero_iff.mp (hf i his)).left

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq (f g : ι →  ℝ≥0 ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  (∑i in s, f i*g i) ≤ ((∑i in s, f i^p)^1 / p)*(∑i in s, g i^q)^1 / q :=
  by 
    byCases' hF_zero : (∑i in s, f i^p) = 0
    ·
      exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hF_zero 
    byCases' hG_zero : (∑i in s, g i^q) = 0
    ·
      calc (∑i in s, f i*g i) = ∑i in s, g i*f i :=
        by 
          congr with i 
          rw [mul_commₓ]_ ≤ ((∑i in s, g i^q)^1 / q)*(∑i in s, f i^p)^1 / p :=
        inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hG_zero _ = ((∑i in s, f i^p)^1 / p)*(∑i in s, g i^q)^1 / q :=
        mul_commₓ _ _ 
    let f' := fun i => f i / ((∑i in s, f i^p)^1 / p)
    let g' := fun i => g i / ((∑i in s, g i^q)^1 / q)
    suffices  : (∑i in s, f' i*g' i) ≤ 1
    ·
      simpRw [f', g', div_mul_div, ←sum_div]  at this 
      rwa [div_le_iff, one_mulₓ] at this 
      refine' mul_ne_zero _ _
      ·
        rw [Ne.def, rpow_eq_zero_iff, Auto.not_and_eq]
        exact Or.inl hF_zero
      ·
        rw [Ne.def, rpow_eq_zero_iff, Auto.not_and_eq]
        exact Or.inl hG_zero 
    refine' inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eqₓ _) (le_of_eqₓ _)
    ·
      simpRw [f', div_rpow, ←sum_div, ←rpow_mul, one_div, inv_mul_cancel hpq.ne_zero, rpow_one, div_self hF_zero]
    ·
      simpRw [g', div_rpow, ←sum_div, ←rpow_mul, one_div, inv_mul_cancel hpq.symm.ne_zero, rpow_one, div_self hG_zero]

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i in s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem is_greatest_Lp
(f : ι → «exprℝ≥0»())
{p q : exprℝ()}
(hpq : p.is_conjugate_exponent q) : is_greatest «expr '' »(λ
 g : ι → «exprℝ≥0»(), «expr∑ in , »((i), s, «expr * »(f i, g i)), {g | «expr ≤ »(«expr∑ in , »((i), s, «expr ^ »(g i, q)), 1)}) «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)) :=
begin
  split,
  { use [expr λ
     i, «expr / »(«expr / »(«expr ^ »(f i, p), f i), «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, q)))],
    by_cases [expr hf, ":", expr «expr = »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), 0)],
    { simp [] [] [] ["[", expr hf, ",", expr hpq.ne_zero, ",", expr hpq.symm.ne_zero, "]"] [] [] },
    { have [ident A] [":", expr «expr ≠ »(«expr - »(«expr + »(p, q), q), 0)] [],
      by simp [] [] [] ["[", expr hpq.ne_zero, "]"] [] [],
      have [ident B] [":", expr ∀
       y : «exprℝ≥0»(), «expr = »(«expr / »(«expr * »(y, «expr ^ »(y, p)), y), «expr ^ »(y, p))] [],
      { refine [expr λ y, mul_div_cancel_left_of_imp (λ h, _)],
        simpa [] [] [] ["[", expr h, ",", expr hpq.ne_zero, "]"] [] [] },
      simp [] [] ["only"] ["[", expr set.mem_set_of_eq, ",", expr div_rpow, ",", "<-", expr sum_div, ",", "<-", expr rpow_mul, ",", expr div_mul_cancel _ hpq.symm.ne_zero, ",", expr rpow_one, ",", expr div_le_iff hf, ",", expr one_mul, ",", expr hpq.mul_eq_add, ",", "<-", expr rpow_sub' _ A, ",", expr _root_.add_sub_cancel, ",", expr le_refl, ",", expr true_and, ",", "<-", expr mul_div_assoc, ",", expr B, "]"] [] [],
      rw ["[", expr div_eq_iff, ",", "<-", expr rpow_add hf, ",", expr hpq.inv_add_inv_conj, ",", expr rpow_one, "]"] [],
      simpa [] [] [] ["[", expr hpq.symm.ne_zero, "]"] [] ["using", expr hf] } },
  { rintros ["_", "⟨", ident g, ",", ident hg, ",", ident rfl, "⟩"],
    apply [expr le_trans (inner_le_Lp_mul_Lq s f g hpq)],
    simpa [] [] ["only"] ["[", expr mul_one, "]"] [] ["using", expr mul_le_mul_left' (nnreal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) _] }
end

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `nnreal`-valued functions. -/
theorem Lp_add_le
(f g : ι → «exprℝ≥0»())
{p : exprℝ()}
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr + »(f i, g i), p)), «expr / »(1, p)), «expr + »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)), «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(g i, p)), «expr / »(1, p)))) :=
begin
  rcases [expr eq_or_lt_of_le hp, "with", ident rfl, "|", ident hp],
  { simp [] [] [] ["[", expr finset.sum_add_distrib, "]"] [] [] },
  have [ident hpq] [] [":=", expr real.is_conjugate_exponent_conjugate_exponent hp],
  have [] [] [":=", expr is_greatest_Lp s «expr + »(f, g) hpq],
  simp [] [] ["only"] ["[", expr pi.add_apply, ",", expr add_mul, ",", expr sum_add_distrib, "]"] [] ["at", ident this],
  rcases [expr this.1, "with", "⟨", ident φ, ",", ident hφ, ",", ident H, "⟩"],
  rw ["<-", expr H] [],
  exact [expr add_le_add ((is_greatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩) ((is_greatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)]
end

end Nnreal

namespace Real

variable(f g : ι → ℝ){p q : ℝ}

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq
(hpq : is_conjugate_exponent p q) : «expr ≤ »(«expr∑ in , »((i), s, «expr * »(f i, g i)), «expr * »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr $ »(abs, f i), p)), «expr / »(1, p)), «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr $ »(abs, g i), q)), «expr / »(1, q)))) :=
begin
  have [] [] [":=", expr nnreal.coe_le_coe.2 (nnreal.inner_le_Lp_mul_Lq s (λ
     i, ⟨_, abs_nonneg (f i)⟩) (λ i, ⟨_, abs_nonneg (g i)⟩) hpq)],
  push_cast [] ["at", ident this],
  refine [expr le_trans «expr $ »(sum_le_sum, λ i hi, _) this],
  simp [] [] ["only"] ["[", "<-", expr abs_mul, ",", expr le_abs_self, "]"] [] []
end

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued functions. -/
theorem Lp_add_le
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr $ »(abs, «expr + »(f i, g i)), p)), «expr / »(1, p)), «expr + »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr $ »(abs, f i), p)), «expr / »(1, p)), «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr $ »(abs, g i), p)), «expr / »(1, p)))) :=
begin
  have [] [] [":=", expr nnreal.coe_le_coe.2 (nnreal.Lp_add_le s (λ
     i, ⟨_, abs_nonneg (f i)⟩) (λ i, ⟨_, abs_nonneg (g i)⟩) hp)],
  push_cast [] ["at", ident this],
  refine [expr le_trans (rpow_le_rpow _ «expr $ »(sum_le_sum, λ
     i
     hi, _) _) this]; simp [] [] [] ["[", expr sum_nonneg, ",", expr rpow_nonneg_of_nonneg, ",", expr abs_nonneg, ",", expr le_trans zero_le_one hp, ",", expr abs_add, ",", expr rpow_le_rpow, "]"] [] []
end

variable{f g}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : is_conjugate_exponent p q) (hf : ∀ i _ : i ∈ s, 0 ≤ f i)
  (hg : ∀ i _ : i ∈ s, 0 ≤ g i) : (∑i in s, f i*g i) ≤ ((∑i in s, f i^p)^1 / p)*(∑i in s, g i^q)^1 / q :=
  by 
    convert inner_le_Lp_mul_Lq s f g hpq using 3 <;>
      apply sum_congr rfl <;> intro i hi <;> simp only [abs_of_nonneg, hf i hi, hg i hi]

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i _ : i ∈ s, 0 ≤ f i) (hg : ∀ i _ : i ∈ s, 0 ≤ g i) :
  ((∑i in s, (f i+g i)^p)^1 / p) ≤ ((∑i in s, f i^p)^1 / p)+(∑i in s, g i^p)^1 / p :=
  by 
    convert Lp_add_le s f g hp using 2 <;> [skip, congr 1, congr 1] <;>
      apply sum_congr rfl <;> intro i hi <;> simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

end Real

namespace Ennreal

variable(f g : ι → ℝ≥0∞){p q : ℝ}

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
theorem inner_le_Lp_mul_Lq
(hpq : p.is_conjugate_exponent q) : «expr ≤ »(«expr∑ in , »((i), s, «expr * »(f i, g i)), «expr * »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)), «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(g i, q)), «expr / »(1, q)))) :=
begin
  by_cases [expr H, ":", expr «expr ∨ »(«expr = »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)), 0), «expr = »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(g i, q)), «expr / »(1, q)), 0))],
  { replace [ident H] [":", expr «expr ∨ »(∀ i «expr ∈ » s, «expr = »(f i, 0), ∀ i «expr ∈ » s, «expr = »(g i, 0))] [],
    by simpa [] [] [] ["[", expr ennreal.rpow_eq_zero_iff, ",", expr hpq.pos, ",", expr hpq.symm.pos, ",", expr asymm hpq.pos, ",", expr asymm hpq.symm.pos, ",", expr sum_eq_zero_iff_of_nonneg, "]"] [] ["using", expr H],
    have [] [":", expr ∀
     i «expr ∈ » s, «expr = »(«expr * »(f i, g i), 0)] [":=", expr λ
     i hi, by cases [expr H] []; simp [] [] [] ["[", expr H i hi, "]"] [] []],
    have [] [":", expr «expr = »(«expr∑ in , »((i), s, «expr * »(f i, g i)), «expr∑ in , »((i), s, 0))] [":=", expr sum_congr rfl this],
    simp [] [] [] ["[", expr this, "]"] [] [] },
  push_neg ["at", ident H],
  by_cases [expr H', ":", expr «expr ∨ »(«expr = »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)), «expr⊤»()), «expr = »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(g i, q)), «expr / »(1, q)), «expr⊤»()))],
  { cases [expr H'] []; simp [] [] [] ["[", expr H', ",", "-", ident one_div, ",", expr H, "]"] [] [] },
  replace [ident H'] [":", expr «expr ∧ »(∀
    i «expr ∈ » s, «expr ≠ »(f i, «expr⊤»()), ∀ i «expr ∈ » s, «expr ≠ »(g i, «expr⊤»()))] [],
  by simpa [] [] [] ["[", expr ennreal.rpow_eq_top_iff, ",", expr asymm hpq.pos, ",", expr asymm hpq.symm.pos, ",", expr hpq.pos, ",", expr hpq.symm.pos, ",", expr ennreal.sum_eq_top_iff, ",", expr not_or_distrib, "]"] [] ["using", expr H'],
  have [] [] [":=", expr ennreal.coe_le_coe.2 (@nnreal.inner_le_Lp_mul_Lq _ s (λ
     i, ennreal.to_nnreal (f i)) (λ i, ennreal.to_nnreal (g i)) _ _ hpq)],
  simp [] [] [] ["[", "<-", expr ennreal.coe_rpow_of_nonneg, ",", expr le_of_lt hpq.pos, ",", expr le_of_lt hpq.one_div_pos, ",", expr le_of_lt hpq.symm.pos, ",", expr le_of_lt hpq.symm.one_div_pos, "]"] [] ["at", ident this],
  convert [] [expr this] ["using", 1]; [skip, congr' [2] []]; [skip, skip, simp [] [] [] [] [] [], skip, simp [] [] [] [] [] []]; { apply [expr finset.sum_congr rfl (λ
      i hi, _)],
    simp [] [] [] ["[", expr H'.1 i hi, ",", expr H'.2 i hi, ",", "-", ident with_zero.coe_mul, ",", expr with_top.coe_mul.symm, "]"] [] [] }
end

-- error in Analysis.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞` valued nonnegative
functions. -/
theorem Lp_add_le
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(«expr + »(f i, g i), p)), «expr / »(1, p)), «expr + »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)), «expr ^ »(«expr∑ in , »((i), s, «expr ^ »(g i, p)), «expr / »(1, p)))) :=
begin
  by_cases [expr H', ":", expr «expr ∨ »(«expr = »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(f i, p)), «expr / »(1, p)), «expr⊤»()), «expr = »(«expr ^ »(«expr∑ in , »((i), s, «expr ^ »(g i, p)), «expr / »(1, p)), «expr⊤»()))],
  { cases [expr H'] []; simp [] [] [] ["[", expr H', ",", "-", ident one_div, "]"] [] [] },
  have [ident pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one hp],
  replace [ident H'] [":", expr «expr ∧ »(∀
    i «expr ∈ » s, «expr ≠ »(f i, «expr⊤»()), ∀ i «expr ∈ » s, «expr ≠ »(g i, «expr⊤»()))] [],
  by simpa [] [] [] ["[", expr ennreal.rpow_eq_top_iff, ",", expr asymm pos, ",", expr pos, ",", expr ennreal.sum_eq_top_iff, ",", expr not_or_distrib, "]"] [] ["using", expr H'],
  have [] [] [":=", expr ennreal.coe_le_coe.2 (@nnreal.Lp_add_le _ s (λ
     i, ennreal.to_nnreal (f i)) (λ i, ennreal.to_nnreal (g i)) _ hp)],
  push_cast ["[", "<-", expr ennreal.coe_rpow_of_nonneg, ",", expr le_of_lt pos, ",", expr le_of_lt (one_div_pos.2 pos), "]"] ["at", ident this],
  convert [] [expr this] ["using", 2]; [skip, congr' [1] [], congr' [1] []]; { apply [expr finset.sum_congr rfl (λ
      i hi, _)],
    simp [] [] [] ["[", expr H'.1 i hi, ",", expr H'.2 i hi, "]"] [] [] }
end

end Ennreal

end HolderMinkowski

