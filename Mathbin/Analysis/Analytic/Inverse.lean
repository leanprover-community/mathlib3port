import Mathbin.Analysis.Analytic.Composition

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence).

## Main statements

* `p.left_inv i`: the formal left inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.right_inv i`: the formal right inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.left_inv_comp` says that `p.left_inv i` is indeed a left inverse to `p` when `p₁ = i`.
* `p.right_inv_comp` says that `p.right_inv i` is indeed a right inverse to `p` when `p₁ = i`.
* `p.left_inv_eq_right_inv`: the two inverses coincide.
* `p.radius_right_inv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

-/


open_locale BigOperators Classical TopologicalSpace

open Finset Filter

namespace FormalMultilinearSeries

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

/-! ### The left inverse of a formal multilinear series -/


/-- The left inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `(left_inv p i) ∘ p = id`. For this, the linear term
`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def left_inv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : FormalMultilinearSeries 𝕜 F E
| 0 => 0
| 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
| n+2 =>
  -∑c : { c : Composition (n+2) // c.length < n+2 },
      have  : (c : Composition (n+2)).length < n+2 := c.2
      (left_inv (c : Composition (n+2)).length).compAlongComposition (p.comp_continuous_linear_map i.symm) c

@[simp]
theorem left_inv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : p.left_inv i 0 = 0 :=
  by 
    rw [left_inv]

@[simp]
theorem left_inv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.left_inv i 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm :=
  by 
    rw [left_inv]

/-- The left inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem left_inv_remove_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.remove_zero.left_inv i = p.left_inv i :=
  by 
    ext1 n 
    induction' n using Nat.strongRec' with n IH 
    cases n
    ·
      simp 
    cases n
    ·
      simp 
    simp only [left_inv, neg_inj]
    refine' Finset.sum_congr rfl fun c cuniv => _ 
    rcases c with ⟨c, hc⟩
    ext v 
    dsimp 
    simp [IH _ hc]

-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The left inverse to a formal multilinear series is indeed a left inverse, provided its linear
term is invertible. -/
theorem left_inv_comp
(p : formal_multilinear_series 𝕜 E F)
(i : «expr ≃L[ ] »(E, 𝕜, F))
(h : «expr = »(p 1, (continuous_multilinear_curry_fin1 𝕜 E F).symm i)) : «expr = »((left_inv p i).comp p, id 𝕜 E) :=
begin
  ext [] [ident n, ident v] [],
  cases [expr n] [],
  { simp [] [] ["only"] ["[", expr left_inv, ",", expr continuous_multilinear_map.zero_apply, ",", expr id_apply_ne_one, ",", expr ne.def, ",", expr not_false_iff, ",", expr zero_ne_one, ",", expr comp_coeff_zero', "]"] [] [] },
  cases [expr n] [],
  { simp [] [] ["only"] ["[", expr left_inv, ",", expr comp_coeff_one, ",", expr h, ",", expr id_apply_one, ",", expr continuous_linear_equiv.coe_apply, ",", expr continuous_linear_equiv.symm_apply_apply, ",", expr continuous_multilinear_curry_fin1_symm_apply, "]"] [] [] },
  have [ident A] [":", expr «expr = »((finset.univ : finset (composition «expr + »(n, 2))), «expr ∪ »({c | «expr < »(composition.length c, «expr + »(n, 2))}.to_finset, {composition.ones «expr + »(n, 2)}))] [],
  { refine [expr subset.antisymm (λ c hc, _) (subset_univ _)],
    by_cases [expr h, ":", expr «expr < »(c.length, «expr + »(n, 2))],
    { simp [] [] [] ["[", expr h, "]"] [] [] },
    { simp [] [] [] ["[", expr composition.eq_ones_iff_le_length.2 (not_lt.1 h), "]"] [] [] } },
  have [ident B] [":", expr disjoint ({c | «expr < »(composition.length c, «expr + »(n, 2))} : set (composition «expr + »(n, 2))).to_finset {composition.ones «expr + »(n, 2)}] [],
  by simp [] [] [] [] [] [],
  have [ident C] [":", expr «expr = »(p.left_inv i (composition.ones «expr + »(n, 2)).length (λ
     j : fin (composition.ones n.succ.succ).length, p 1 (λ
      k, v (fin.cast_le (composition.length_le _) j))), p.left_inv i «expr + »(n, 2) (λ
     j : fin «expr + »(n, 2), p 1 (λ k, v j)))] [],
  { apply [expr formal_multilinear_series.congr _ (composition.ones_length _) (λ j hj1 hj2, _)],
    exact [expr formal_multilinear_series.congr _ rfl (λ k hk1 hk2, by congr)] },
  have [ident D] [":", expr «expr = »(p.left_inv i «expr + »(n, 2) (λ
     j : fin «expr + »(n, 2), p 1 (λ
      k, v j)), «expr- »(«expr∑ in , »((c : composition «expr + »(n, 2)), {c : composition «expr + »(n, 2) | «expr < »(c.length, «expr + »(n, 2))}.to_finset, p.left_inv i c.length (p.apply_composition c v))))] [],
  { simp [] [] ["only"] ["[", expr left_inv, ",", expr continuous_multilinear_map.neg_apply, ",", expr neg_inj, ",", expr continuous_multilinear_map.sum_apply, "]"] [] [],
    convert [] [expr (sum_to_finset_eq_subtype (λ
       c : composition «expr + »(n, 2), «expr < »(c.length, «expr + »(n, 2))) (λ
       c : composition «expr + »(n, 2), continuous_multilinear_map.comp_along_composition (p.comp_continuous_linear_map «expr↑ »(i.symm)) c (p.left_inv i c.length) (λ
        j : fin «expr + »(n, 2), p 1 (λ k : fin 1, v j)))).symm.trans _] [],
    simp [] [] ["only"] ["[", expr comp_continuous_linear_map_apply_composition, ",", expr continuous_multilinear_map.comp_along_composition_apply, "]"] [] [],
    congr,
    ext [] [ident c] [],
    congr,
    ext [] [ident k] [],
    simp [] [] [] ["[", expr h, "]"] [] [] },
  simp [] [] [] ["[", expr formal_multilinear_series.comp, ",", expr show «expr ≠ »(«expr + »(n, 2), 1), by dec_trivial [], ",", expr A, ",", expr finset.sum_union B, ",", expr apply_composition_ones, ",", expr C, ",", expr D, "]"] [] []
end

/-! ### The right inverse of a formal multilinear series -/


/-- The right inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `p ∘ (right_inv p i) = id`. For this, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `qₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def right_inv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : FormalMultilinearSeries 𝕜 F E
| 0 => 0
| 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
| n+2 =>
  let q : FormalMultilinearSeries 𝕜 F E := fun k => if h : k < n+2 then right_inv k else 0
  -(i.symm : F →L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n+2))

@[simp]
theorem right_inv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : p.right_inv i 0 = 0 :=
  by 
    rw [right_inv]

@[simp]
theorem right_inv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.right_inv i 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm :=
  by 
    rw [right_inv]

/-- The right inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem right_inv_remove_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.remove_zero.right_inv i = p.right_inv i :=
  by 
    ext1 n 
    induction' n using Nat.strongRec' with n IH 
    cases n
    ·
      simp 
    cases n
    ·
      simp 
    simp only [right_inv, neg_inj]
    unfoldCoes 
    congr 1
    rw
      [remove_zero_comp_of_pos _ _
        (show 0 < n+2by 
          decide)]
    congr 1 
    ext k 
    byCases' hk : k < n+2 <;> simp [hk, IH]

-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_right_inv_aux1
{n : exprℕ()}
(hn : «expr < »(0, n))
(p : formal_multilinear_series 𝕜 E F)
(q : formal_multilinear_series 𝕜 F E)
(v : fin n → F) : «expr = »(p.comp q n v, «expr + »(«expr∑ in , »((c : composition n), {c : composition n | «expr < »(1, c.length)}.to_finset, p c.length (q.apply_composition c v)), p 1 (λ
   i, q n v))) :=
begin
  have [ident A] [":", expr «expr = »((finset.univ : finset (composition n)), «expr ∪ »({c | «expr < »(1, composition.length c)}.to_finset, {composition.single n hn}))] [],
  { refine [expr subset.antisymm (λ c hc, _) (subset_univ _)],
    by_cases [expr h, ":", expr «expr < »(1, c.length)],
    { simp [] [] [] ["[", expr h, "]"] [] [] },
    { have [] [":", expr «expr = »(c.length, 1)] [],
      by { refine [expr (eq_iff_le_not_lt.2 ⟨_, h⟩).symm],
        exact [expr c.length_pos_of_pos hn] },
      rw ["<-", expr composition.eq_single_iff_length hn] ["at", ident this],
      simp [] [] [] ["[", expr this, "]"] [] [] } },
  have [ident B] [":", expr disjoint ({c | «expr < »(1, composition.length c)} : set (composition n)).to_finset {composition.single n hn}] [],
  by simp [] [] [] [] [] [],
  have [ident C] [":", expr «expr = »(p (composition.single n hn).length (q.apply_composition (composition.single n hn) v), p 1 (λ
     i : fin 1, q n v))] [],
  { apply [expr p.congr (composition.single_length hn) (λ j hj1 hj2, _)],
    simp [] [] [] ["[", expr apply_composition_single, "]"] [] [] },
  simp [] [] [] ["[", expr formal_multilinear_series.comp, ",", expr A, ",", expr finset.sum_union B, ",", expr C, "]"] [] []
end

-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_right_inv_aux2
(p : formal_multilinear_series 𝕜 E F)
(i : «expr ≃L[ ] »(E, 𝕜, F))
(n : exprℕ())
(v : fin «expr + »(n, 2) → F) : «expr = »(«expr∑ in , »((c : composition «expr + »(n, 2)), {c : composition «expr + »(n, 2) | «expr < »(1, c.length)}.to_finset, p c.length (apply_composition (λ
    k : exprℕ(), ite «expr < »(k, «expr + »(n, 2)) (p.right_inv i k) 0) c v)), «expr∑ in , »((c : composition «expr + »(n, 2)), {c : composition «expr + »(n, 2) | «expr < »(1, c.length)}.to_finset, p c.length ((p.right_inv i).apply_composition c v))) :=
begin
  have [ident N] [":", expr «expr < »(0, «expr + »(n, 2))] [],
  by dec_trivial [],
  refine [expr sum_congr rfl (λ c hc, p.congr rfl (λ j hj1 hj2, _))],
  have [] [":", expr ∀ k, «expr < »(c.blocks_fun k, «expr + »(n, 2))] [],
  { simp [] [] ["only"] ["[", expr set.mem_to_finset, ",", expr set.mem_set_of_eq, "]"] [] ["at", ident hc],
    simp [] [] [] ["[", "<-", expr composition.ne_single_iff N, ",", expr composition.eq_single_iff_length, ",", expr ne_of_gt hc, "]"] [] [] },
  simp [] [] [] ["[", expr apply_composition, ",", expr this, "]"] [] []
end

-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The right inverse to a formal multilinear series is indeed a right inverse, provided its linear
term is invertible and its constant term vanishes. -/
theorem comp_right_inv
(p : formal_multilinear_series 𝕜 E F)
(i : «expr ≃L[ ] »(E, 𝕜, F))
(h : «expr = »(p 1, (continuous_multilinear_curry_fin1 𝕜 E F).symm i))
(h0 : «expr = »(p 0, 0)) : «expr = »(p.comp (right_inv p i), id 𝕜 F) :=
begin
  ext [] [ident n, ident v] [],
  cases [expr n] [],
  { simp [] [] ["only"] ["[", expr h0, ",", expr continuous_multilinear_map.zero_apply, ",", expr id_apply_ne_one, ",", expr ne.def, ",", expr not_false_iff, ",", expr zero_ne_one, ",", expr comp_coeff_zero', "]"] [] [] },
  cases [expr n] [],
  { simp [] [] ["only"] ["[", expr comp_coeff_one, ",", expr h, ",", expr right_inv, ",", expr continuous_linear_equiv.apply_symm_apply, ",", expr id_apply_one, ",", expr continuous_linear_equiv.coe_apply, ",", expr continuous_multilinear_curry_fin1_symm_apply, "]"] [] [] },
  have [ident N] [":", expr «expr < »(0, «expr + »(n, 2))] [],
  by dec_trivial [],
  simp [] [] [] ["[", expr comp_right_inv_aux1 N, ",", expr h, ",", expr right_inv, ",", expr lt_irrefl n, ",", expr show «expr ≠ »(«expr + »(n, 2), 1), by dec_trivial [], ",", "<-", expr sub_eq_add_neg, ",", expr sub_eq_zero, ",", expr comp_right_inv_aux2, "]"] [] []
end

-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem right_inv_coeff
(p : formal_multilinear_series 𝕜 E F)
(i : «expr ≃L[ ] »(E, 𝕜, F))
(n : exprℕ())
(hn : «expr ≤ »(2, n)) : «expr = »(p.right_inv i n, «expr- »((i.symm : «expr →L[ ] »(F, 𝕜, E)).comp_continuous_multilinear_map «expr∑ in , »((c), ({c | «expr < »(1, composition.length c)}.to_finset : finset (composition n)), p.comp_along_composition (p.right_inv i) c))) :=
begin
  cases [expr n] [],
  { exact [expr false.elim (zero_lt_two.not_le hn)] },
  cases [expr n] [],
  { exact [expr false.elim (one_lt_two.not_le hn)] },
  simp [] [] ["only"] ["[", expr right_inv, ",", expr neg_inj, "]"] [] [],
  congr' [1] [],
  ext [] [ident v] [],
  have [ident N] [":", expr «expr < »(0, «expr + »(n, 2))] [],
  by dec_trivial [],
  have [] [":", expr «expr = »(p 1 (λ i : fin 1, 0), 0)] [":=", expr continuous_multilinear_map.map_zero _],
  simp [] [] [] ["[", expr comp_right_inv_aux1 N, ",", expr lt_irrefl n, ",", expr this, ",", expr comp_right_inv_aux2, "]"] [] []
end

/-! ### Coincidence of the left and the right inverse -/


private theorem left_inv_eq_right_inv_aux (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) (h0 : p 0 = 0) : left_inv p i = right_inv p i :=
  calc left_inv p i = (left_inv p i).comp (id 𝕜 F) :=
    by 
      simp 
    _ = (left_inv p i).comp (p.comp (right_inv p i)) :=
    by 
      rw [comp_right_inv p i h h0]
    _ = ((left_inv p i).comp p).comp (right_inv p i) :=
    by 
      rw [comp_assoc]
    _ = (id 𝕜 E).comp (right_inv p i) :=
    by 
      rw [left_inv_comp p i h]
    _ = right_inv p i :=
    by 
      simp 
    

/-- The left inverse and the right inverse of a formal multilinear series coincide. This is not at
all obvious from their definition, but it follows from uniqueness of inverses (which comes from the
fact that composition is associative on formal multilinear series). -/
theorem left_inv_eq_right_invₓ (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : left_inv p i = right_inv p i :=
  calc left_inv p i = left_inv p.remove_zero i :=
    by 
      rw [left_inv_remove_zero]
    _ = right_inv p.remove_zero i :=
    by 
      apply left_inv_eq_right_inv_aux <;> simp [h]
    _ = right_inv p i :=
    by 
      rw [right_inv_remove_zero]
    

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series, and let `q` be its (left or right) inverse.
Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}).
$$
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior.

Let `Qₙ = ∥qₙ∥`. Bounding `∥pₖ∥` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [pöschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/


-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- First technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in a general abstract setup. -/
theorem radius_right_inv_pos_of_radius_pos_aux1
(n : exprℕ())
(p : exprℕ() → exprℝ())
(hp : ∀ k, «expr ≤ »(0, p k))
{r a : exprℝ()}
(hr : «expr ≤ »(0, r))
(ha : «expr ≤ »(0, a)) : «expr ≤ »(«expr∑ in , »((k), Ico 2 «expr + »(n, 1), «expr * »(«expr ^ »(a, k), «expr∑ in , »((c), ({c | «expr < »(1, composition.length c)}.to_finset : finset (composition k)), «expr * »(«expr ^ »(r, c.length), «expr∏ , »((j), p (c.blocks_fun j)))))), «expr∑ in , »((j), Ico 2 «expr + »(n, 1), «expr * »(«expr ^ »(r, j), «expr ^ »(«expr∑ in , »((k), Ico 1 n, «expr * »(«expr ^ »(a, k), p k)), j)))) :=
calc
  «expr = »(«expr∑ in , »((k), Ico 2 «expr + »(n, 1), «expr * »(«expr ^ »(a, k), «expr∑ in , »((c), ({c | «expr < »(1, composition.length c)}.to_finset : finset (composition k)), «expr * »(«expr ^ »(r, c.length), «expr∏ , »((j), p (c.blocks_fun j)))))), «expr∑ in , »((k), Ico 2 «expr + »(n, 1), «expr∑ in , »((c), ({c | «expr < »(1, composition.length c)}.to_finset : finset (composition k)), «expr∏ , »((j), «expr * »(r, «expr * »(«expr ^ »(a, c.blocks_fun j), p (c.blocks_fun j))))))) : begin
    simp_rw ["[", expr mul_sum, "]"] [],
    apply [expr sum_congr rfl (λ k hk, _)],
    apply [expr sum_congr rfl (λ c hc, _)],
    rw ["[", expr prod_mul_distrib, ",", expr prod_mul_distrib, ",", expr prod_pow_eq_pow_sum, ",", expr composition.sum_blocks_fun, ",", expr prod_const, ",", expr card_fin, "]"] [],
    ring []
  end
  «expr ≤ »(..., «expr∑ in , »((d), comp_partial_sum_target 2 «expr + »(n, 1) n, «expr∏ , »((j : fin d.2.length), «expr * »(r, «expr * »(«expr ^ »(a, d.2.blocks_fun j), p (d.2.blocks_fun j)))))) : begin
    rw [expr sum_sigma'] [],
    refine [expr sum_le_sum_of_subset_of_nonneg _ (λ
      x hx1 hx2, prod_nonneg (λ j hj, mul_nonneg hr (mul_nonneg (pow_nonneg ha _) (hp _))))],
    rintros ["⟨", ident k, ",", ident c, "⟩", ident hd],
    simp [] [] ["only"] ["[", expr set.mem_to_finset, ",", expr mem_Ico, ",", expr mem_sigma, ",", expr set.mem_set_of_eq, "]"] [] ["at", ident hd],
    simp [] [] ["only"] ["[", expr mem_comp_partial_sum_target_iff, "]"] [] [],
    refine [expr ⟨hd.2, c.length_le.trans_lt hd.1.2, λ j, _⟩],
    have [] [":", expr «expr ≠ »(c, composition.single k (zero_lt_two.trans_le hd.1.1))] [],
    by simp [] [] [] ["[", expr composition.eq_single_iff_length, ",", expr ne_of_gt hd.2, "]"] [] [],
    rw [expr composition.ne_single_iff] ["at", ident this],
    exact [expr (this j).trans_le (nat.lt_succ_iff.mp hd.1.2)]
  end
  «expr = »(..., «expr∑ in , »((e), comp_partial_sum_source 2 «expr + »(n, 1) n, «expr∏ , »((j : fin e.1), «expr * »(r, «expr * »(«expr ^ »(a, e.2 j), p (e.2 j)))))) : begin
    symmetry,
    apply [expr comp_change_of_variables_sum],
    rintros ["⟨", ident k, ",", ident blocks_fun, "⟩", ident H],
    have [ident K] [":", expr «expr = »((comp_change_of_variables 2 «expr + »(n, 1) n ⟨k, blocks_fun⟩ H).snd.length, k)] [],
    by simp [] [] [] [] [] [],
    congr' [2] []; try { rw [expr K] [] },
    rw [expr fin.heq_fun_iff K.symm] [],
    assume [binders (j)],
    rw [expr comp_change_of_variables_blocks_fun] []
  end
  «expr = »(..., «expr∑ in , »((j), Ico 2 «expr + »(n, 1), «expr * »(«expr ^ »(r, j), «expr ^ »(«expr∑ in , »((k), Ico 1 n, «expr * »(«expr ^ »(a, k), p k)), j)))) : begin
    rw ["[", expr comp_partial_sum_source, ",", "<-", expr sum_sigma' (Ico 2 «expr + »(n, 1)) (λ
      k : exprℕ(), (fintype.pi_finset (λ
       i : fin k, Ico 1 n) : finset (fin k → exprℕ()))) (λ
      n e, «expr∏ , »((j : fin n), «expr * »(r, «expr * »(«expr ^ »(a, e j), p (e j))))), "]"] [],
    apply [expr sum_congr rfl (λ j hj, _)],
    simp [] [] ["only"] ["[", "<-", expr @multilinear_map.mk_pi_algebra_apply exprℝ() (fin j) _ _ exprℝ(), "]"] [] [],
    simp [] [] ["only"] ["[", "<-", expr multilinear_map.map_sum_finset (multilinear_map.mk_pi_algebra exprℝ() (fin j) exprℝ()) (λ
      (k)
      (m : exprℕ()), «expr * »(r, «expr * »(«expr ^ »(a, m), p m))), "]"] [] [],
    simp [] [] ["only"] ["[", expr multilinear_map.mk_pi_algebra_apply, "]"] [] [],
    dsimp [] [] [] [],
    simp [] [] [] ["[", expr prod_const, ",", "<-", expr mul_sum, ",", expr mul_pow, "]"] [] []
  end

/-- Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in the specific setup we are interesting in, by reducing to the general bound in
`radius_right_inv_pos_of_radius_pos_aux1`. -/
theorem radius_right_inv_pos_of_radius_pos_aux2 {n : ℕ} (hn : 2 ≤ n+1) (p : FormalMultilinearSeries 𝕜 E F)
  (i : E ≃L[𝕜] F) {r a C : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hC : 0 ≤ C) (hp : ∀ n, ∥p n∥ ≤ C*r ^ n) :
  (∑k in Ico 1 (n+1), (a ^ k)*∥p.right_inv i k∥) ≤
    (∥(i.symm :
          F →L[𝕜]
            E)∥*a)+(∥(i.symm : F →L[𝕜] E)∥*C)*∑k in Ico 2 (n+1), (r*∑j in Ico 1 n, (a ^ j)*∥p.right_inv i j∥) ^ k :=
  let I := ∥(i.symm : F →L[𝕜] E)∥
  calc (∑k in Ico 1 (n+1), (a ^ k)*∥p.right_inv i k∥) = (a*I)+∑k in Ico 2 (n+1), (a ^ k)*∥p.right_inv i k∥ :=
    by 
      simp only [LinearIsometryEquiv.norm_map, pow_oneₓ, right_inv_coeff_one, Nat.Ico_succ_singleton, sum_singleton,
        ←sum_Ico_consecutive _ one_le_two hn]
    _ =
      (a*I)+∑k in Ico 2 (n+1),
          (a ^
              k)*∥(i.symm : F →L[𝕜] E).compContinuousMultilinearMap
                (∑c in ({ c | 1 < Composition.length c }.toFinset : Finset (Composition k)),
                  p.comp_along_composition (p.right_inv i) c)∥ :=
    by 
      congr 1
      apply sum_congr rfl fun j hj => _ 
      rw [right_inv_coeff _ _ _ (mem_Ico.1 hj).1, norm_neg]
    _ ≤
      (a*∥(i.symm :
            F →L[𝕜]
              E)∥)+∑k in Ico 2 (n+1),
          (a ^
              k)*I*∑c in ({ c | 1 < Composition.length c }.toFinset : Finset (Composition k)),
                (C*r ^ c.length)*∏j, ∥p.right_inv i (c.blocks_fun j)∥ :=
    by 
      applyRules [add_le_add, le_reflₓ, sum_le_sum fun j hj => _, mul_le_mul_of_nonneg_left, pow_nonneg, ha]
      apply (ContinuousLinearMap.norm_comp_continuous_multilinear_map_le _ _).trans 
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_sum_le _ _).trans 
      apply sum_le_sum fun c hc => _ 
      apply (comp_along_composition_norm _ _ _).trans 
      apply mul_le_mul_of_nonneg_right (hp _)
      exact prod_nonneg fun j hj => norm_nonneg _ 
    _ =
      (I*a)+(I*C)*∑k in Ico 2 (n+1),
            (a ^
                k)*∑c in ({ c | 1 < Composition.length c }.toFinset : Finset (Composition k)),
                (r ^ c.length)*∏j, ∥p.right_inv i (c.blocks_fun j)∥ :=
    by 
      simpRw [mul_assocₓ C, ←mul_sum, ←mul_assocₓ, mul_commₓ _ ∥«expr↑ » i.symm∥, mul_assocₓ, ←mul_sum, ←mul_assocₓ,
        mul_commₓ _ C, mul_assocₓ, ←mul_sum]
      ring 
    _ ≤ (I*a)+(I*C)*∑k in Ico 2 (n+1), (r*∑j in Ico 1 n, (a ^ j)*∥p.right_inv i j∥) ^ k :=
    by 
      applyRules [add_le_add, le_reflₓ, mul_le_mul_of_nonneg_left, norm_nonneg, hC, mul_nonneg]
      simpRw [mul_powₓ]
      apply radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ∥p.right_inv i k∥) (fun k => norm_nonneg _) hr ha
    

-- error in Analysis.Analytic.Inverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a a formal multilinear series has a positive radius of convergence, then its right inverse
also has a positive radius of convergence. -/
theorem radius_right_inv_pos_of_radius_pos
(p : formal_multilinear_series 𝕜 E F)
(i : «expr ≃L[ ] »(E, 𝕜, F))
(hp : «expr < »(0, p.radius)) : «expr < »(0, (p.right_inv i).radius) :=
begin
  obtain ["⟨", ident C, ",", ident r, ",", ident Cpos, ",", ident rpos, ",", ident ple, "⟩", ":", expr «expr∃ , »((C r)
    (hC : «expr < »(0, C))
    (hr : «expr < »(0, r)), ∀
    n : exprℕ(), «expr ≤ »(«expr∥ ∥»(p n), «expr * »(C, «expr ^ »(r, n)))), ":=", expr le_mul_pow_of_radius_pos p hp],
  let [ident I] [] [":=", expr «expr∥ ∥»((i.symm : «expr →L[ ] »(F, 𝕜, E)))],
  obtain ["⟨", ident a, ",", ident apos, ",", ident ha1, ",", ident ha2, "⟩", ":", expr «expr∃ , »((a)
    (apos : «expr < »(0, a)), «expr ∧ »(«expr ≤ »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(r, 2)), «expr ^ »(«expr + »(I, 1), 2)), a), 1), «expr ≤ »(«expr * »(«expr * »(r, «expr + »(I, 1)), a), «expr / »(1, 2))))],
  { have [] [":", expr tendsto (λ
      a, «expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(r, 2)), «expr ^ »(«expr + »(I, 1), 2)), a)) (expr𝓝() 0) (expr𝓝() «expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(r, 2)), «expr ^ »(«expr + »(I, 1), 2)), 0))] [":=", expr tendsto_const_nhds.mul tendsto_id],
    have [ident A] [":", expr «expr∀ᶠ in , »((a), expr𝓝() 0, «expr < »(«expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(r, 2)), «expr ^ »(«expr + »(I, 1), 2)), a), 1))] [],
    by { apply [expr (tendsto_order.1 this).2],
      simp [] [] [] ["[", expr zero_lt_one, "]"] [] [] },
    have [] [":", expr tendsto (λ
      a, «expr * »(«expr * »(r, «expr + »(I, 1)), a)) (expr𝓝() 0) (expr𝓝() «expr * »(«expr * »(r, «expr + »(I, 1)), 0))] [":=", expr tendsto_const_nhds.mul tendsto_id],
    have [ident B] [":", expr «expr∀ᶠ in , »((a), expr𝓝() 0, «expr < »(«expr * »(«expr * »(r, «expr + »(I, 1)), a), «expr / »(1, 2)))] [],
    by { apply [expr (tendsto_order.1 this).2],
      simp [] [] [] ["[", expr zero_lt_one, "]"] [] [] },
    have [ident C] [":", expr «expr∀ᶠ in , »((a), «expr𝓝[ ] »(set.Ioi (0 : exprℝ()), (0 : exprℝ())), «expr < »((0 : exprℝ()), a))] [],
    by { filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
      exact [expr λ a ha, ha] },
    rcases [expr (C.and ((A.and B).filter_mono inf_le_left)).exists, "with", "⟨", ident a, ",", ident ha, "⟩"],
    exact [expr ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩] },
  let [ident S] [] [":=", expr λ
   n, «expr∑ in , »((k), Ico 1 n, «expr * »(«expr ^ »(a, k), «expr∥ ∥»(p.right_inv i k)))],
  have [ident IRec] [":", expr ∀ n, «expr ≤ »(1, n) → «expr ≤ »(S n, «expr * »(«expr + »(I, 1), a))] [],
  { apply [expr nat.le_induction],
    { simp [] [] ["only"] ["[", expr S, "]"] [] [],
      rw ["[", expr Ico_eq_empty_of_le (le_refl 1), ",", expr sum_empty, "]"] [],
      exact [expr mul_nonneg (add_nonneg (norm_nonneg _) zero_le_one) apos.le] },
    { assume [binders (n one_le_n hn)],
      have [ident In] [":", expr «expr ≤ »(2, «expr + »(n, 1))] [],
      by linarith [] [] [],
      have [ident Snonneg] [":", expr «expr ≤ »(0, S n)] [":=", expr sum_nonneg (λ
        x hx, mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _))],
      have [ident rSn] [":", expr «expr ≤ »(«expr * »(r, S n), «expr / »(1, 2))] [":=", expr calc
         «expr ≤ »(«expr * »(r, S n), «expr * »(r, «expr * »(«expr + »(I, 1), a))) : mul_le_mul_of_nonneg_left hn rpos.le
         «expr ≤ »(..., «expr / »(1, 2)) : by rwa ["[", "<-", expr mul_assoc, "]"] []],
      calc
        «expr ≤ »(S «expr + »(n, 1), «expr + »(«expr * »(I, a), «expr * »(«expr * »(I, C), «expr∑ in , »((k), Ico 2 «expr + »(n, 1), «expr ^ »(«expr * »(r, S n), k))))) : radius_right_inv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
        «expr = »(..., «expr + »(«expr * »(I, a), «expr * »(«expr * »(I, C), «expr / »(«expr - »(«expr ^ »(«expr * »(r, S n), 2), «expr ^ »(«expr * »(r, S n), «expr + »(n, 1))), «expr - »(1, «expr * »(r, S n)))))) : by { rw [expr geom_sum_Ico' _ In] [],
          exact [expr ne_of_lt (rSn.trans_lt (by norm_num [] []))] }
        «expr ≤ »(..., «expr + »(«expr * »(I, a), «expr * »(«expr * »(I, C), «expr / »(«expr ^ »(«expr * »(r, S n), 2), «expr / »(1, 2))))) : begin
          apply_rules ["[", expr add_le_add, ",", expr le_refl, ",", expr mul_le_mul_of_nonneg_left, ",", expr mul_nonneg, ",", expr norm_nonneg, ",", expr Cpos.le, "]"],
          refine [expr div_le_div (sq_nonneg _) _ (by norm_num [] []) (by linarith [] [] [])],
          simp [] [] ["only"] ["[", expr sub_le_self_iff, "]"] [] [],
          apply [expr pow_nonneg (mul_nonneg rpos.le Snonneg)]
        end
        «expr = »(..., «expr + »(«expr * »(I, a), «expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(«expr * »(r, S n), 2)))) : by ring []
        «expr ≤ »(..., «expr + »(«expr * »(I, a), «expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(«expr * »(r, «expr * »(«expr + »(I, 1), a)), 2)))) : by apply_rules ["[", expr add_le_add, ",", expr le_refl, ",", expr mul_le_mul_of_nonneg_left, ",", expr mul_nonneg, ",", expr norm_nonneg, ",", expr Cpos.le, ",", expr zero_le_two, ",", expr pow_le_pow_of_le_left, ",", expr rpos.le, "]"]
        «expr = »(..., «expr * »(«expr + »(I, «expr * »(«expr * »(«expr * »(«expr * »(«expr * »(2, I), C), «expr ^ »(r, 2)), «expr ^ »(«expr + »(I, 1), 2)), a)), a)) : by ring []
        «expr ≤ »(..., «expr * »(«expr + »(I, 1), a)) : by apply_rules ["[", expr mul_le_mul_of_nonneg_right, ",", expr apos.le, ",", expr add_le_add, ",", expr le_refl, "]"] } },
  let [ident a'] [":", expr nnreal] [":=", expr ⟨a, apos.le⟩],
  suffices [ident H] [":", expr «expr ≤ »((a' : ennreal), (p.right_inv i).radius)],
  by { apply [expr lt_of_lt_of_le _ H],
    exact_mod_cast [expr apos] },
  apply [expr le_radius_of_bound _ «expr * »(«expr + »(I, 1), a) (λ n, _)],
  by_cases [expr hn, ":", expr «expr = »(n, 0)],
  { have [] [":", expr «expr = »(«expr∥ ∥»(p.right_inv i n), «expr∥ ∥»(p.right_inv i 0))] [],
    by congr; try { rw [expr hn] [] },
    simp [] [] ["only"] ["[", expr this, ",", expr norm_zero, ",", expr zero_mul, ",", expr right_inv_coeff_zero, "]"] [] [],
    apply_rules ["[", expr mul_nonneg, ",", expr add_nonneg, ",", expr norm_nonneg, ",", expr zero_le_one, ",", expr apos.le, "]"] },
  { have [ident one_le_n] [":", expr «expr ≤ »(1, n)] [":=", expr bot_lt_iff_ne_bot.2 hn],
    calc
      «expr = »(«expr * »(«expr∥ ∥»(p.right_inv i n), «expr ^ »(«expr↑ »(a'), n)), «expr * »(«expr ^ »(a, n), «expr∥ ∥»(p.right_inv i n))) : mul_comm _ _
      «expr ≤ »(..., «expr∑ in , »((k), Ico 1 «expr + »(n, 1), «expr * »(«expr ^ »(a, k), «expr∥ ∥»(p.right_inv i k)))) : begin
        have [] [":", expr ∀
         k «expr ∈ » Ico 1 «expr + »(n, 1), «expr ≤ »(0, «expr * »(«expr ^ »(a, k), «expr∥ ∥»(p.right_inv i k)))] [":=", expr λ
         k hk, mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _)],
        exact [expr single_le_sum this (by simp [] [] [] ["[", expr one_le_n, "]"] [] [])]
      end
      «expr ≤ »(..., «expr * »(«expr + »(I, 1), a)) : IRec «expr + »(n, 1) (by dec_trivial []) }
end

end FormalMultilinearSeries

