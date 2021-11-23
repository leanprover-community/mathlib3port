import Mathbin.Analysis.NormedSpace.OperatorNorm 
import Mathbin.Topology.Algebra.Multilinear

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `∥f∥` as the
smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `∥f m∥ ≤ C * ∏ i, ∥m i∥` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mk_continuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `∥f∥` is its norm, i.e., the smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for
  all `m`.
* `le_op_norm f m` asserts the fundamental inequality `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥`.
* `norm_image_sub_le f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `∥f∥` and `∥m₁ - m₂∥`.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
continuous multilinear function `f` in `n+1` variables into a continuous linear function taking
values in continuous multilinear functions in `n` variables, and also into a continuous multilinear
function in `n` variables taking values in continuous linear functions. These operations are called
`f.curry_left` and `f.curry_right` respectively (with inverses `f.uncurry_left` and
`f.uncurry_right`). They induce continuous linear equivalences between spaces of
continuous multilinear functions in `n+1` variables and spaces of continuous linear functions into
continuous multilinear functions in `n` variables (resp. continuous multilinear functions in `n`
variables taking values in continuous linear functions), called respectively
`continuous_multilinear_curry_left_equiv` and `continuous_multilinear_curry_right_equiv`.

## Implementation notes

We mostly follow the API (and the proofs) of `operator_norm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables. The currying/uncurrying
constructions are based on those in `multilinear.lean`.

From the mathematical point of view, all the results follow from the results on operator norm in
one variable, by applying them to one variable after the other through currying. However, this
is only well defined when there is an order on the variables (for instance on `fin n`) although
the final result is independent of the order. While everything could be done following this
approach, it turns out that direct proofs are easier and more efficient.
-/


noncomputable theory

open_locale Classical BigOperators Nnreal

open Finset Metric

attribute [local instance] AddCommGroupₓ.toAddCommMonoid NormedGroup.toAddCommGroup NormedSpace.toModule

attribute [-instance] Unique.subsingleton Pi.subsingleton

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `nondiscrete_normed_field`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : fin (nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/


universe u v v' wE wE₁ wE' wEi wG wG'

variable{𝕜 :
    Type
      u}{ι :
    Type
      v}{ι' :
    Type
      v'}{n :
    ℕ}{E :
    ι →
      Type
        wE}{E₁ :
    ι →
      Type
        wE₁}{E' :
    ι' →
      Type
        wE'}{Ei :
    Finₓ n.succ →
      Type
        wEi}{G :
    Type
      wG}{G' :
    Type
      wG'}[DecidableEq
      ι][Fintype
      ι][DecidableEq
      ι'][Fintype
      ι'][NondiscreteNormedField
      𝕜][∀ i,
      NormedGroup
        (E
          i)][∀ i,
      NormedSpace 𝕜
        (E
          i)][∀ i,
      NormedGroup
        (E₁
          i)][∀ i,
      NormedSpace 𝕜
        (E₁
          i)][∀ i,
      NormedGroup
        (E'
          i)][∀ i,
      NormedSpace 𝕜
        (E'
          i)][∀ i,
      NormedGroup (Ei i)][∀ i, NormedSpace 𝕜 (Ei i)][NormedGroup G][NormedSpace 𝕜 G][NormedGroup G'][NormedSpace 𝕜 G']

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, in
both directions. Along the way, we prove useful bounds on the difference `∥f m₁ - f m₂∥`.
-/


namespace MultilinearMap

variable(f : MultilinearMap 𝕜 E G)

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a multilinear map in finitely many variables on normed spaces satisfies the inequality
`∥f m∥ ≤ C * ∏ i, ∥m i∥` on a shell `ε i / ∥c i∥ < ∥m i∥ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ∥c i∥`, then it satisfies this inequality for all `m`. -/
theorem bound_of_shell
{ε : ι → exprℝ()}
{C : exprℝ()}
(hε : ∀ i, «expr < »(0, ε i))
{c : ι → 𝕜}
(hc : ∀ i, «expr < »(1, «expr∥ ∥»(c i)))
(hf : ∀
 m : ∀
 i, E i, ∀
 i, «expr ≤ »(«expr / »(ε i, «expr∥ ∥»(c i)), «expr∥ ∥»(m i)) → ∀
 i, «expr < »(«expr∥ ∥»(m i), ε i) → «expr ≤ »(«expr∥ ∥»(f m), «expr * »(C, «expr∏ , »((i), «expr∥ ∥»(m i)))))
(m : ∀ i, E i) : «expr ≤ »(«expr∥ ∥»(f m), «expr * »(C, «expr∏ , »((i), «expr∥ ∥»(m i)))) :=
begin
  rcases [expr em «expr∃ , »((i), «expr = »(m i, 0)), "with", "⟨", ident i, ",", ident hi, "⟩", "|", ident hm]; [skip, push_neg ["at", ident hm]],
  { simp [] [] [] ["[", expr f.map_coord_zero i hi, ",", expr prod_eq_zero (mem_univ i), ",", expr hi, "]"] [] [] },
  choose [] [ident δ] [ident hδ0, ident hδm_lt, ident hle_δm, ident hδinv] ["using", expr λ
   i, rescale_to_shell (hc i) (hε i) (hm i)],
  have [ident hδ0] [":", expr «expr < »(0, «expr∏ , »((i), «expr∥ ∥»(δ i)))] [],
  from [expr prod_pos (λ i _, norm_pos_iff.2 (hδ0 i))],
  simpa [] [] [] ["[", expr map_smul_univ, ",", expr norm_smul, ",", expr prod_mul_distrib, ",", expr mul_left_comm C, ",", expr mul_le_mul_left hδ0, "]"] [] ["using", expr hf (λ
    i, «expr • »(δ i, m i)) hle_δm hδm_lt]
end

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, for some `C` which can be chosen to be
positive. -/
theorem exists_bound_of_continuous
(hf : continuous f) : «expr∃ , »((C : exprℝ()), «expr ∧ »(«expr < »(0, C), ∀
  m, «expr ≤ »(«expr∥ ∥»(f m), «expr * »(C, «expr∏ , »((i), «expr∥ ∥»(m i)))))) :=
begin
  casesI [expr is_empty_or_nonempty ι] [],
  { refine [expr ⟨«expr + »(«expr∥ ∥»(f 0), 1), add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, λ m, _⟩],
    obtain [ident rfl, ":", expr «expr = »(m, 0)],
    from [expr funext (is_empty.elim «expr‹ ›»(_))],
    simp [] [] [] ["[", expr univ_eq_empty, ",", expr zero_le_one, "]"] [] [] },
  obtain ["⟨", ident ε, ":", expr exprℝ(), ",", ident ε0, ":", expr «expr < »(0, ε), ",", ident hε, ":", expr ∀
   m : ∀
   i, E i, «expr < »(«expr∥ ∥»(«expr - »(m, 0)), ε) → «expr < »(«expr∥ ∥»(«expr - »(f m, f 0)), 1), "⟩", ":=", expr normed_group.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one],
  simp [] [] ["only"] ["[", expr sub_zero, ",", expr f.map_zero, "]"] [] ["at", ident hε],
  rcases [expr normed_field.exists_one_lt_norm 𝕜, "with", "⟨", ident c, ",", ident hc, "⟩"],
  have [] [":", expr «expr < »(0, «expr ^ »(«expr / »(«expr∥ ∥»(c), ε), fintype.card ι))] [],
  from [expr pow_pos (div_pos (zero_lt_one.trans hc) ε0) _],
  refine [expr ⟨_, this, _⟩],
  refine [expr f.bound_of_shell (λ _, ε0) (λ _, hc) (λ m hcm hm, _)],
  refine [expr (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans _],
  rw ["[", "<-", expr div_le_iff' this, ",", expr one_div, ",", "<-", expr inv_pow₀, ",", expr inv_div, ",", expr fintype.card, ",", "<-", expr prod_const, "]"] [],
  exact [expr prod_le_prod (λ _ _, div_nonneg ε0.le (norm_nonneg _)) (λ i _, hcm i)]
end

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a precise but hard to use version. See
`norm_image_sub_le_of_bound` for a less precise but more usable version. The bound reads
`∥f m - f m'∥ ≤
  C * ∥m 1 - m' 1∥ * max ∥m 2∥ ∥m' 2∥ * max ∥m 3∥ ∥m' 3∥ * ... * max ∥m n∥ ∥m' n∥ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
theorem norm_image_sub_le_of_bound'
{C : exprℝ()}
(hC : «expr ≤ »(0, C))
(H : ∀ m, «expr ≤ »(«expr∥ ∥»(f m), «expr * »(C, «expr∏ , »((i), «expr∥ ∥»(m i)))))
(m₁
 m₂ : ∀
 i, E i) : «expr ≤ »(«expr∥ ∥»(«expr - »(f m₁, f m₂)), «expr * »(C, «expr∑ , »((i), «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j))))) :=
begin
  have [ident A] [":", expr ∀
   s : finset ι, «expr ≤ »(«expr∥ ∥»(«expr - »(f m₁, f (s.piecewise m₂ m₁))), «expr * »(C, «expr∑ in , »((i), s, «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j)))))] [],
  { refine [expr finset.induction (by simp [] [] [] [] [] []) _],
    assume [binders (i s his Hrec)],
    have [ident I] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(f (s.piecewise m₂ m₁), f ((insert i s).piecewise m₂ m₁))), «expr * »(C, «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j))))] [],
    { have [ident A] [":", expr «expr = »((insert i s).piecewise m₂ m₁, function.update (s.piecewise m₂ m₁) i (m₂ i))] [":=", expr s.piecewise_insert _ _ _],
      have [ident B] [":", expr «expr = »(s.piecewise m₂ m₁, function.update (s.piecewise m₂ m₁) i (m₁ i))] [],
      { ext [] [ident j] [],
        by_cases [expr h, ":", expr «expr = »(j, i)],
        { rw [expr h] [],
          simp [] [] [] ["[", expr his, "]"] [] [] },
        { simp [] [] [] ["[", expr h, "]"] [] [] } },
      rw ["[", expr B, ",", expr A, ",", "<-", expr f.map_sub, "]"] [],
      apply [expr le_trans (H _) (mul_le_mul_of_nonneg_left _ hC)],
      refine [expr prod_le_prod (λ j hj, norm_nonneg _) (λ j hj, _)],
      by_cases [expr h, ":", expr «expr = »(j, i)],
      { rw [expr h] [],
        simp [] [] [] [] [] [] },
      { by_cases [expr h', ":", expr «expr ∈ »(j, s)]; simp [] [] [] ["[", expr h', ",", expr h, ",", expr le_refl, "]"] [] [] } },
    calc
      «expr ≤ »(«expr∥ ∥»(«expr - »(f m₁, f ((insert i s).piecewise m₂ m₁))), «expr + »(«expr∥ ∥»(«expr - »(f m₁, f (s.piecewise m₂ m₁))), «expr∥ ∥»(«expr - »(f (s.piecewise m₂ m₁), f ((insert i s).piecewise m₂ m₁))))) : by { rw ["[", "<-", expr dist_eq_norm, ",", "<-", expr dist_eq_norm, ",", "<-", expr dist_eq_norm, "]"] [],
        exact [expr dist_triangle _ _ _] }
      «expr ≤ »(..., «expr + »(«expr * »(C, «expr∑ in , »((i), s, «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j)))), «expr * »(C, «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j))))) : add_le_add Hrec I
      «expr = »(..., «expr * »(C, «expr∑ in , »((i), insert i s, «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j))))) : by simp [] [] [] ["[", expr his, ",", expr add_comm, ",", expr left_distrib, "]"] [] [] },
  convert [] [expr A univ] [],
  simp [] [] [] [] [] []
end

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bound is
`∥f m - f m'∥ ≤ C * card ι * ∥m - m'∥ * (max ∥m∥ ∥m'∥) ^ (card ι - 1)`. -/
theorem norm_image_sub_le_of_bound
{C : exprℝ()}
(hC : «expr ≤ »(0, C))
(H : ∀ m, «expr ≤ »(«expr∥ ∥»(f m), «expr * »(C, «expr∏ , »((i), «expr∥ ∥»(m i)))))
(m₁
 m₂ : ∀
 i, E i) : «expr ≤ »(«expr∥ ∥»(«expr - »(f m₁, f m₂)), «expr * »(«expr * »(«expr * »(C, fintype.card ι), «expr ^ »(max «expr∥ ∥»(m₁) «expr∥ ∥»(m₂), «expr - »(fintype.card ι, 1))), «expr∥ ∥»(«expr - »(m₁, m₂)))) :=
begin
  have [ident A] [":", expr ∀
   i : ι, «expr ≤ »(«expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j)), «expr * »(«expr∥ ∥»(«expr - »(m₁, m₂)), «expr ^ »(max «expr∥ ∥»(m₁) «expr∥ ∥»(m₂), «expr - »(fintype.card ι, 1))))] [],
  { assume [binders (i)],
    calc
      «expr ≤ »(«expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j)), «expr∏ , »((j : ι), function.update (λ
         j, max «expr∥ ∥»(m₁) «expr∥ ∥»(m₂)) i «expr∥ ∥»(«expr - »(m₁, m₂)) j)) : begin
        apply [expr prod_le_prod],
        { assume [binders (j hj)],
          by_cases [expr h, ":", expr «expr = »(j, i)]; simp [] [] [] ["[", expr h, ",", expr norm_nonneg, "]"] [] [] },
        { assume [binders (j hj)],
          by_cases [expr h, ":", expr «expr = »(j, i)],
          { rw [expr h] [],
            simp [] [] [] [] [] [],
            exact [expr norm_le_pi_norm «expr - »(m₁, m₂) i] },
          { simp [] [] [] ["[", expr h, ",", expr max_le_max, ",", expr norm_le_pi_norm, "]"] [] [] } }
      end
      «expr = »(..., «expr * »(«expr∥ ∥»(«expr - »(m₁, m₂)), «expr ^ »(max «expr∥ ∥»(m₁) «expr∥ ∥»(m₂), «expr - »(fintype.card ι, 1)))) : by { rw [expr prod_update_of_mem (finset.mem_univ _)] [],
        simp [] [] [] ["[", expr card_univ_diff, "]"] [] [] } },
  calc
    «expr ≤ »(«expr∥ ∥»(«expr - »(f m₁, f m₂)), «expr * »(C, «expr∑ , »((i), «expr∏ , »((j), if «expr = »(j, i) then «expr∥ ∥»(«expr - »(m₁ i, m₂ i)) else max «expr∥ ∥»(m₁ j) «expr∥ ∥»(m₂ j))))) : f.norm_image_sub_le_of_bound' hC H m₁ m₂
    «expr ≤ »(..., «expr * »(C, «expr∑ , »((i), «expr * »(«expr∥ ∥»(«expr - »(m₁, m₂)), «expr ^ »(max «expr∥ ∥»(m₁) «expr∥ ∥»(m₂), «expr - »(fintype.card ι, 1)))))) : mul_le_mul_of_nonneg_left (sum_le_sum (λ
      i hi, A i)) hC
    «expr = »(..., «expr * »(«expr * »(«expr * »(C, fintype.card ι), «expr ^ »(max «expr∥ ∥»(m₁) «expr∥ ∥»(m₂), «expr - »(fintype.card ι, 1))), «expr∥ ∥»(«expr - »(m₁, m₂)))) : by { rw ["[", expr sum_const, ",", expr card_univ, ",", expr nsmul_eq_mul, "]"] [],
      ring [] }
end

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a multilinear map satisfies an inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, then it is
continuous. -/
theorem continuous_of_bound
(C : exprℝ())
(H : ∀ m, «expr ≤ »(«expr∥ ∥»(f m), «expr * »(C, «expr∏ , »((i), «expr∥ ∥»(m i))))) : continuous f :=
begin
  let [ident D] [] [":=", expr max C 1],
  have [ident D_pos] [":", expr «expr ≤ »(0, D)] [":=", expr le_trans zero_le_one (le_max_right _ _)],
  replace [ident H] [":", expr ∀ m, «expr ≤ »(«expr∥ ∥»(f m), «expr * »(D, «expr∏ , »((i), «expr∥ ∥»(m i))))] [],
  { assume [binders (m)],
    apply [expr le_trans (H m) (mul_le_mul_of_nonneg_right (le_max_left _ _) _)],
    exact [expr prod_nonneg (λ (i : ι) (hi), norm_nonneg (m i))] },
  refine [expr continuous_iff_continuous_at.2 (λ m, _)],
  refine [expr continuous_at_of_locally_lipschitz zero_lt_one «expr * »(«expr * »(D, fintype.card ι), «expr ^ »(«expr + »(«expr∥ ∥»(m), 1), «expr - »(fintype.card ι, 1))) (λ
    m' h', _)],
  rw ["[", expr dist_eq_norm, ",", expr dist_eq_norm, "]"] [],
  have [] [":", expr «expr ≤ »(0, max «expr∥ ∥»(m') «expr∥ ∥»(m))] [],
  by simp [] [] [] [] [] [],
  have [] [":", expr «expr ≤ »(max «expr∥ ∥»(m') «expr∥ ∥»(m), «expr + »(«expr∥ ∥»(m), 1))] [],
  by simp [] [] [] ["[", expr zero_le_one, ",", expr norm_le_of_mem_closed_ball (le_of_lt h'), ",", "-", ident add_comm, "]"] [] [],
  calc
    «expr ≤ »(«expr∥ ∥»(«expr - »(f m', f m)), «expr * »(«expr * »(«expr * »(D, fintype.card ι), «expr ^ »(max «expr∥ ∥»(m') «expr∥ ∥»(m), «expr - »(fintype.card ι, 1))), «expr∥ ∥»(«expr - »(m', m)))) : f.norm_image_sub_le_of_bound D_pos H m' m
    «expr ≤ »(..., «expr * »(«expr * »(«expr * »(D, fintype.card ι), «expr ^ »(«expr + »(«expr∥ ∥»(m), 1), «expr - »(fintype.card ι, 1))), «expr∥ ∥»(«expr - »(m', m)))) : by apply_rules ["[", expr mul_le_mul_of_nonneg_right, ",", expr mul_le_mul_of_nonneg_left, ",", expr mul_nonneg, ",", expr norm_nonneg, ",", expr nat.cast_nonneg, ",", expr pow_le_pow_of_le_left, "]"]
end

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
def mk_continuous (C : ℝ) (H : ∀ m, ∥f m∥ ≤ C*∏i, ∥m i∥) : ContinuousMultilinearMap 𝕜 E G :=
  { f with cont := f.continuous_of_bound C H }

@[simp]
theorem coe_mk_continuous (C : ℝ) (H : ∀ m, ∥f m∥ ≤ C*∏i, ∥m i∥) : «expr⇑ » (f.mk_continuous C H) = f :=
  rfl

/-- Given a multilinear map in `n` variables, if one restricts it to `k` variables putting `z` on
the other coordinates, then the resulting restricted function satisfies an inequality
`∥f.restr v∥ ≤ C * ∥z∥^(n-k) * Π ∥v i∥` if the original function satisfies `∥f v∥ ≤ C * Π ∥v i∥`. -/
theorem restr_norm_le {k n : ℕ} (f : (MultilinearMap 𝕜 (fun i : Finₓ n => G) G' : _)) (s : Finset (Finₓ n))
  (hk : s.card = k) (z : G) {C : ℝ} (H : ∀ m, ∥f m∥ ≤ C*∏i, ∥m i∥) (v : Finₓ k → G) :
  ∥f.restr s hk z v∥ ≤ (C*∥z∥ ^ (n - k))*∏i, ∥v i∥ :=
  by 
    rw [mul_right_commₓ, mul_assocₓ]
    convert H _ using 2
    simp only [apply_dite norm, Fintype.prod_dite, prod_const ∥z∥, Finset.card_univ,
      Fintype.card_of_subtype («expr ᶜ» s) fun x => mem_compl, card_compl, Fintype.card_fin, hk, mk_coe,
      ←(s.order_iso_of_fin hk).symm.Bijective.prod_comp fun x => ∥v x∥]
    rfl

end MultilinearMap

/-!
### Continuous multilinear maps

We define the norm `∥f∥` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for all `m`. We show that this
defines a normed space structure on `continuous_multilinear_map 𝕜 E G`.
-/


namespace ContinuousMultilinearMap

variable(c : 𝕜)(f g : ContinuousMultilinearMap 𝕜 E G)(m : ∀ i, E i)

theorem bound : ∃ C : ℝ, 0 < C ∧ ∀ m, ∥f m∥ ≤ C*∏i, ∥m i∥ :=
  f.to_multilinear_map.exists_bound_of_continuous f.2

open Real

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
def op_norm :=
  Inf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ∥f m∥ ≤ c*∏i, ∥m i∥ }

instance has_op_norm : HasNorm (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨op_norm⟩

theorem norm_def : ∥f∥ = Inf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ∥f m∥ ≤ c*∏i, ∥m i∥ } :=
  rfl

theorem bounds_nonempty {f : ContinuousMultilinearMap 𝕜 E G} : ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ m, ∥f m∥ ≤ c*∏i, ∥m i∥ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_ltₓ hMp, hMb⟩

theorem bounds_bdd_below {f : ContinuousMultilinearMap 𝕜 E G} : BddBelow { c | 0 ≤ c ∧ ∀ m, ∥f m∥ ≤ c*∏i, ∥m i∥ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem op_norm_nonneg : 0 ≤ ∥f∥ :=
  le_cInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The fundamental property of the operator norm of a continuous multilinear map:
`∥f m∥` is bounded by `∥f∥` times the product of the `∥m i∥`. -/
theorem le_op_norm : «expr ≤ »(«expr∥ ∥»(f m), «expr * »(«expr∥ ∥»(f), «expr∏ , »((i), «expr∥ ∥»(m i)))) :=
begin
  have [ident A] [":", expr «expr ≤ »(0, «expr∏ , »((i), «expr∥ ∥»(m i)))] [":=", expr prod_nonneg (λ
    j hj, norm_nonneg _)],
  cases [expr A.eq_or_lt] ["with", ident h, ident hlt],
  { rcases [expr prod_eq_zero_iff.1 h.symm, "with", "⟨", ident i, ",", "_", ",", ident hi, "⟩"],
    rw [expr norm_eq_zero] ["at", ident hi],
    have [] [":", expr «expr = »(f m, 0)] [":=", expr f.map_coord_zero i hi],
    rw ["[", expr this, ",", expr norm_zero, "]"] [],
    exact [expr mul_nonneg (op_norm_nonneg f) A] },
  { rw ["[", "<-", expr div_le_iff hlt, "]"] [],
    apply [expr le_cInf bounds_nonempty],
    rintro [ident c, "⟨", "_", ",", ident hc, "⟩"],
    rw ["[", expr div_le_iff hlt, "]"] [],
    apply [expr hc] }
end

theorem le_of_op_norm_le {C : ℝ} (h : ∥f∥ ≤ C) : ∥f m∥ ≤ C*∏i, ∥m i∥ :=
  (f.le_op_norm m).trans$ mul_le_mul_of_nonneg_right h (prod_nonneg$ fun i _ => norm_nonneg (m i))

theorem ratio_le_op_norm : (∥f m∥ / ∏i, ∥m i∥) ≤ ∥f∥ :=
  div_le_of_nonneg_of_le_mul (prod_nonneg$ fun i _ => norm_nonneg _) (op_norm_nonneg _) (f.le_op_norm m)

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
theorem unit_le_op_norm (h : ∥m∥ ≤ 1) : ∥f m∥ ≤ ∥f∥ :=
  calc ∥f m∥ ≤ ∥f∥*∏i, ∥m i∥ := f.le_op_norm m 
    _ ≤ ∥f∥*∏i : ι, 1 :=
    mul_le_mul_of_nonneg_left (prod_le_prod (fun i hi => norm_nonneg _) fun i hi => le_transₓ (norm_le_pi_norm _ _) h)
      (op_norm_nonneg f)
    _ = ∥f∥ :=
    by 
      simp 
    

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem op_norm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ m, ∥f m∥ ≤ M*∏i, ∥m i∥) : ∥f∥ ≤ M :=
  cInf_le bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f+g∥ ≤ ∥f∥+∥g∥ :=
  cInf_le bounds_bdd_below
    ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _),
      fun x =>
        by 
          rw [add_mulₓ]
          exact norm_add_le_of_le (le_op_norm _ _) (le_op_norm _ _)⟩

/-- A continuous linear map is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
  by 
    split 
    ·
      intro h 
      ext m 
      simpa [h] using f.le_op_norm m
    ·
      rintro rfl 
      apply le_antisymmₓ (op_norm_le_bound 0 le_rfl fun m => _) (op_norm_nonneg _)
      simp 

variable{𝕜' : Type _}[NondiscreteNormedField 𝕜'][NormedAlgebra 𝕜' 𝕜][NormedSpace 𝕜' G][IsScalarTower 𝕜' 𝕜 G]

theorem op_norm_smul_le (c : 𝕜') : ∥c • f∥ ≤ ∥c∥*∥f∥ :=
  (c • f).op_norm_le_bound (mul_nonneg (norm_nonneg _) (op_norm_nonneg _))
    (by 
      intro m 
      erw [norm_smul, mul_assocₓ]
      exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _))

theorem op_norm_neg : ∥-f∥ = ∥f∥ :=
  by 
    rw [norm_def]
    apply congr_argₓ 
    ext 
    simp 

/-- Continuous multilinear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : NormedGroup (ContinuousMultilinearMap 𝕜 E G) :=
  NormedGroup.ofCore _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨fun c f => f.op_norm_smul_le c⟩

theorem le_op_norm_mul_prod_of_le {b : ι → ℝ} (hm : ∀ i, ∥m i∥ ≤ b i) : ∥f m∥ ≤ ∥f∥*∏i, b i :=
  (f.le_op_norm m).trans$
    mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hm i) (norm_nonneg f)

theorem le_op_norm_mul_pow_card_of_le {b : ℝ} (hm : ∀ i, ∥m i∥ ≤ b) : ∥f m∥ ≤ ∥f∥*b ^ Fintype.card ι :=
  by 
    simpa only [prod_const] using f.le_op_norm_mul_prod_of_le m hm

theorem le_op_norm_mul_pow_of_le {Ei : Finₓ n → Type _} [∀ i, NormedGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)]
  (f : ContinuousMultilinearMap 𝕜 Ei G) (m : ∀ i, Ei i) {b : ℝ} (hm : ∥m∥ ≤ b) : ∥f m∥ ≤ ∥f∥*b ^ n :=
  by 
    simpa only [Fintype.card_fin] using f.le_op_norm_mul_pow_card_of_le m fun i => (norm_le_pi_norm m i).trans hm

/-- The fundamental property of the operator norm of a continuous multilinear map:
`∥f m∥` is bounded by `∥f∥` times the product of the `∥m i∥`, `nnnorm` version. -/
theorem le_op_nnnorm : nnnorm (f m) ≤ nnnorm f*∏i, nnnorm (m i) :=
  Nnreal.coe_le_coe.1$
    by 
      pushCast 
      exact f.le_op_norm m

theorem le_of_op_nnnorm_le {C :  ℝ≥0 } (h : nnnorm f ≤ C) : nnnorm (f m) ≤ C*∏i, nnnorm (m i) :=
  (f.le_op_nnnorm m).trans$ mul_le_mul' h le_rfl

theorem op_norm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
  ∥f.prod g∥ = max ∥f∥ ∥g∥ :=
  le_antisymmₓ
      (op_norm_le_bound _ (norm_nonneg (f, g))
        fun m =>
          have H : 0 ≤ ∏i, ∥m i∥ := prod_nonneg$ fun _ _ => norm_nonneg _ 
          by 
            simpa only [prod_apply, Prod.norm_def, max_mul_of_nonneg, H] using
              max_le_max (f.le_op_norm m) (g.le_op_norm m))$
    max_leₓ (f.op_norm_le_bound (norm_nonneg _)$ fun m => (le_max_leftₓ _ _).trans ((f.prod g).le_op_norm _))
      (g.op_norm_le_bound (norm_nonneg _)$ fun m => (le_max_rightₓ _ _).trans ((f.prod g).le_op_norm _))

theorem norm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedGroup (E' i')]
  [∀ i', NormedSpace 𝕜 (E' i')] (f : ∀ i', ContinuousMultilinearMap 𝕜 E (E' i')) : ∥pi f∥ = ∥f∥ :=
  by 
    apply le_antisymmₓ
    ·
      refine' op_norm_le_bound _ (norm_nonneg f) fun m => _ 
      dsimp 
      rw [pi_norm_le_iff]
      exacts[fun i => (f i).le_of_op_norm_le m (norm_le_pi_norm f i),
        mul_nonneg (norm_nonneg f) (prod_nonneg$ fun _ _ => norm_nonneg _)]
    ·
      refine' (pi_norm_le_iff (norm_nonneg _)).2 fun i => _ 
      refine' op_norm_le_bound _ (norm_nonneg _) fun m => _ 
      refine' le_transₓ _ ((pi f).le_op_norm m)
      convert norm_le_pi_norm (fun j => f j m) i

section 

variable(𝕜 E E' G G')

/-- `continuous_multilinear_map.prod` as a `linear_isometry_equiv`. -/
def prodL :
  ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G' ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 E (G × G') :=
  { toFun := fun f => f.1.Prod f.2,
    invFun :=
      fun f =>
        ((ContinuousLinearMap.fst 𝕜 G G').compContinuousMultilinearMap f,
        (ContinuousLinearMap.snd 𝕜 G G').compContinuousMultilinearMap f),
    map_add' := fun f g => rfl, map_smul' := fun c f => rfl,
    left_inv :=
      fun f =>
        by 
          ext <;> rfl,
    right_inv :=
      fun f =>
        by 
          ext <;> rfl,
    norm_map' := fun f => op_norm_prod f.1 f.2 }

/-- `continuous_multilinear_map.pi` as a `linear_isometry_equiv`. -/
def piₗᵢ {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedGroup (E' i')] [∀ i', NormedSpace 𝕜 (E' i')] :
  @LinearIsometryEquiv 𝕜 𝕜 _ _ (RingHom.id 𝕜) _ _ _ (∀ i', ContinuousMultilinearMap 𝕜 E (E' i'))
    (ContinuousMultilinearMap 𝕜 E (∀ i, E' i)) _ _ (@Pi.module ι' _ 𝕜 _ _ fun i' => inferInstance) _ :=
  { toLinearEquiv := { pi_equiv with map_add' := fun f g => rfl, map_smul' := fun c f => rfl }, norm_map' := norm_pi }

end 

section RestrictScalars

variable[∀ i, NormedSpace 𝕜' (E i)][∀ i, IsScalarTower 𝕜' 𝕜 (E i)]

@[simp]
theorem norm_restrict_scalars : ∥f.restrict_scalars 𝕜'∥ = ∥f∥ :=
  by 
    simp only [norm_def, coe_restrict_scalars]

variable(𝕜')

/-- `continuous_multilinear_map.restrict_scalars` as a `continuous_multilinear_map`. -/
def restrict_scalars_linear : ContinuousMultilinearMap 𝕜 E G →L[𝕜'] ContinuousMultilinearMap 𝕜' E G :=
  LinearMap.mkContinuous { toFun := RestrictScalars 𝕜', map_add' := fun m₁ m₂ => rfl, map_smul' := fun c m => rfl } 1$
    fun f =>
      by 
        simp 

variable{𝕜'}

theorem continuous_restrict_scalars :
  Continuous (RestrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E G → ContinuousMultilinearMap 𝕜' E G) :=
  (restrict_scalars_linear 𝕜').Continuous

end RestrictScalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`∥f m - f m'∥ ≤
  ∥f∥ * ∥m 1 - m' 1∥ * max ∥m 2∥ ∥m' 2∥ * max ∥m 3∥ ∥m' 3∥ * ... * max ∥m n∥ ∥m' n∥ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`.-/
theorem norm_image_sub_le' (m₁ m₂ : ∀ i, E i) :
  ∥f m₁ - f m₂∥ ≤ ∥f∥*∑i, ∏j, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥ :=
  f.to_multilinear_map.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_op_norm _ _

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `∥f m - f m'∥ ≤ ∥f∥ * card ι * ∥m - m'∥ * (max ∥m∥ ∥m'∥) ^ (card ι - 1)`.-/
theorem norm_image_sub_le (m₁ m₂ : ∀ i, E i) :
  ∥f m₁ - f m₂∥ ≤ ((∥f∥*Fintype.card ι)*max ∥m₁∥ ∥m₂∥ ^ (Fintype.card ι - 1))*∥m₁ - m₂∥ :=
  f.to_multilinear_map.norm_image_sub_le_of_bound (norm_nonneg _) f.le_op_norm _ _

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Applying a multilinear map to a vector is continuous in both coordinates. -/
theorem continuous_eval : continuous (λ p : «expr × »(continuous_multilinear_map 𝕜 E G, ∀ i, E i), p.1 p.2) :=
begin
  apply [expr continuous_iff_continuous_at.2 (λ p, _)],
  apply [expr continuous_at_of_locally_lipschitz zero_lt_one «expr + »(«expr * »(«expr * »(«expr + »(«expr∥ ∥»(p), 1), fintype.card ι), «expr ^ »(«expr + »(«expr∥ ∥»(p), 1), «expr - »(fintype.card ι, 1))), «expr∏ , »((i), «expr∥ ∥»(p.2 i))) (λ
    q hq, _)],
  have [] [":", expr «expr ≤ »(0, max «expr∥ ∥»(q.2) «expr∥ ∥»(p.2))] [],
  by simp [] [] [] [] [] [],
  have [] [":", expr «expr ≤ »(0, «expr + »(«expr∥ ∥»(p), 1))] [],
  by simp [] [] [] ["[", expr le_trans zero_le_one, "]"] [] [],
  have [ident A] [":", expr «expr ≤ »(«expr∥ ∥»(q), «expr + »(«expr∥ ∥»(p), 1))] [":=", expr norm_le_of_mem_closed_ball (le_of_lt hq)],
  have [] [":", expr «expr ≤ »(max «expr∥ ∥»(q.2) «expr∥ ∥»(p.2), «expr + »(«expr∥ ∥»(p), 1))] [":=", expr le_trans (max_le_max (norm_snd_le q) (norm_snd_le p)) (by simp [] [] [] ["[", expr A, ",", "-", ident add_comm, ",", expr zero_le_one, "]"] [] [])],
  have [] [":", expr ∀ i : ι, «expr ∈ »(i, univ) → «expr ≤ »(0, «expr∥ ∥»(p.2 i))] [":=", expr λ i hi, norm_nonneg _],
  calc
    «expr ≤ »(dist (q.1 q.2) (p.1 p.2), «expr + »(dist (q.1 q.2) (q.1 p.2), dist (q.1 p.2) (p.1 p.2))) : dist_triangle _ _ _
    «expr = »(..., «expr + »(«expr∥ ∥»(«expr - »(q.1 q.2, q.1 p.2)), «expr∥ ∥»(«expr - »(q.1 p.2, p.1 p.2)))) : by rw ["[", expr dist_eq_norm, ",", expr dist_eq_norm, "]"] []
    «expr ≤ »(..., «expr + »(«expr * »(«expr * »(«expr * »(«expr∥ ∥»(q.1), fintype.card ι), «expr ^ »(max «expr∥ ∥»(q.2) «expr∥ ∥»(p.2), «expr - »(fintype.card ι, 1))), «expr∥ ∥»(«expr - »(q.2, p.2))), «expr * »(«expr∥ ∥»(«expr - »(q.1, p.1)), «expr∏ , »((i), «expr∥ ∥»(p.2 i))))) : add_le_add (norm_image_sub_le _ _ _) («expr - »(q.1, p.1).le_op_norm p.2)
    «expr ≤ »(..., «expr + »(«expr * »(«expr * »(«expr * »(«expr + »(«expr∥ ∥»(p), 1), fintype.card ι), «expr ^ »(«expr + »(«expr∥ ∥»(p), 1), «expr - »(fintype.card ι, 1))), «expr∥ ∥»(«expr - »(q, p))), «expr * »(«expr∥ ∥»(«expr - »(q, p)), «expr∏ , »((i), «expr∥ ∥»(p.2 i))))) : by apply_rules ["[", expr add_le_add, ",", expr mul_le_mul, ",", expr le_refl, ",", expr le_trans (norm_fst_le q) A, ",", expr nat.cast_nonneg, ",", expr mul_nonneg, ",", expr pow_le_pow_of_le_left, ",", expr pow_nonneg, ",", expr norm_snd_le «expr - »(q, p), ",", expr norm_nonneg, ",", expr norm_fst_le «expr - »(q, p), ",", expr prod_nonneg, "]"]
    «expr = »(..., «expr * »(«expr + »(«expr * »(«expr * »(«expr + »(«expr∥ ∥»(p), 1), fintype.card ι), «expr ^ »(«expr + »(«expr∥ ∥»(p), 1), «expr - »(fintype.card ι, 1))), «expr∏ , »((i), «expr∥ ∥»(p.2 i))), dist q p)) : by { rw [expr dist_eq_norm] [],
      ring [] }
end

theorem continuous_eval_left (m : ∀ i, E i) : Continuous fun p : ContinuousMultilinearMap 𝕜 E G => p m :=
  continuous_eval.comp (continuous_id.prod_mk continuous_const)

theorem has_sum_eval {α : Type _} {p : α → ContinuousMultilinearMap 𝕜 E G} {q : ContinuousMultilinearMap 𝕜 E G}
  (h : HasSum p q) (m : ∀ i, E i) : HasSum (fun a => p a m) (q m) :=
  by 
    dsimp [HasSum]  at h⊢
    convert ((continuous_eval_left m).Tendsto _).comp h 
    ext s 
    simp 

theorem tsum_eval {α : Type _} {p : α → ContinuousMultilinearMap 𝕜 E G} (hp : Summable p) (m : ∀ i, E i) :
  (∑'a, p a) m = ∑'a, p a m :=
  (has_sum_eval hp.has_sum m).tsum_eq.symm

open_locale TopologicalSpace

open Filter

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the target space is complete, the space of continuous multilinear maps with its norm is also
complete. The proof is essentially the same as for the space of continuous linear maps (modulo the
addition of `finset.prod` where needed. The duplication could be avoided by deducing the linear
case from the multilinear case via a currying isomorphism. However, this would mess up imports,
and it is more satisfactory to have the simplest case as a standalone proof. -/
instance [complete_space G] : complete_space (continuous_multilinear_map 𝕜 E G) :=
begin
  have [ident nonneg] [":", expr ∀
   v : ∀
   i, E i, «expr ≤ »(0, «expr∏ , »((i), «expr∥ ∥»(v i)))] [":=", expr λ v, finset.prod_nonneg (λ i hi, norm_nonneg _)],
  refine [expr metric.complete_of_cauchy_seq_tendsto (λ f hf, _)],
  rcases [expr cauchy_seq_iff_le_tendsto_0.1 hf, "with", "⟨", ident b, ",", ident b0, ",", ident b_bound, ",", ident b_lim, "⟩"],
  have [ident cau] [":", expr ∀ v, cauchy_seq (λ n, f n v)] [],
  { assume [binders (v)],
    apply [expr cauchy_seq_iff_le_tendsto_0.2 ⟨λ n, «expr * »(b n, «expr∏ , »((i), «expr∥ ∥»(v i))), λ n, _, _, _⟩],
    { exact [expr mul_nonneg (b0 n) (nonneg v)] },
    { assume [binders (n m N hn hm)],
      rw [expr dist_eq_norm] [],
      apply [expr le_trans («expr - »(f n, f m).le_op_norm v) _],
      exact [expr mul_le_mul_of_nonneg_right (b_bound n m N hn hm) (nonneg v)] },
    { simpa [] [] [] [] [] ["using", expr b_lim.mul tendsto_const_nhds] } },
  choose [] [ident F] [ident hF] ["using", expr λ v, cauchy_seq_tendsto_of_complete (cau v)],
  let [ident Fmult] [":", expr multilinear_map 𝕜 E G] [":=", expr { to_fun := F,
     map_add' := λ v i x y, begin
       have [ident A] [] [":=", expr hF (function.update v i «expr + »(x, y))],
       have [ident B] [] [":=", expr (hF (function.update v i x)).add (hF (function.update v i y))],
       simp [] [] [] [] [] ["at", ident A, ident B],
       exact [expr tendsto_nhds_unique A B]
     end,
     map_smul' := λ v i c x, begin
       have [ident A] [] [":=", expr hF (function.update v i «expr • »(c, x))],
       have [ident B] [] [":=", expr filter.tendsto.smul (@tendsto_const_nhds _ exprℕ() _ c _) (hF (function.update v i x))],
       simp [] [] [] [] [] ["at", ident A, ident B],
       exact [expr tendsto_nhds_unique A B]
     end }],
  have [ident Fnorm] [":", expr ∀
   v, «expr ≤ »(«expr∥ ∥»(F v), «expr * »(«expr + »(b 0, «expr∥ ∥»(f 0)), «expr∏ , »((i), «expr∥ ∥»(v i))))] [],
  { assume [binders (v)],
    have [ident A] [":", expr ∀
     n, «expr ≤ »(«expr∥ ∥»(f n v), «expr * »(«expr + »(b 0, «expr∥ ∥»(f 0)), «expr∏ , »((i), «expr∥ ∥»(v i))))] [],
    { assume [binders (n)],
      apply [expr le_trans ((f n).le_op_norm _) _],
      apply [expr mul_le_mul_of_nonneg_right _ (nonneg v)],
      calc
        «expr = »(«expr∥ ∥»(f n), «expr∥ ∥»(«expr + »(«expr - »(f n, f 0), f 0))) : by { congr' [1] [],
          abel [] [] [] }
        «expr ≤ »(..., «expr + »(«expr∥ ∥»(«expr - »(f n, f 0)), «expr∥ ∥»(f 0))) : norm_add_le _ _
        «expr ≤ »(..., «expr + »(b 0, «expr∥ ∥»(f 0))) : begin
          apply [expr add_le_add_right],
          simpa [] [] [] ["[", expr dist_eq_norm, "]"] [] ["using", expr b_bound n 0 0 (zero_le _) (zero_le _)]
        end },
    exact [expr le_of_tendsto (hF v).norm (eventually_of_forall A)] },
  let [ident Fcont] [] [":=", expr Fmult.mk_continuous _ Fnorm],
  use [expr Fcont],
  have [] [":", expr ∀ n, «expr ≤ »(«expr∥ ∥»(«expr - »(f n, Fcont)), b n)] [],
  { assume [binders (n)],
    apply [expr op_norm_le_bound _ (b0 n) (λ v, _)],
    have [ident A] [":", expr «expr∀ᶠ in , »((m), at_top, «expr ≤ »(«expr∥ ∥»(«expr - »(f n, f m) v), «expr * »(b n, «expr∏ , »((i), «expr∥ ∥»(v i)))))] [],
    { refine [expr eventually_at_top.2 ⟨n, λ m hm, _⟩],
      apply [expr le_trans («expr - »(f n, f m).le_op_norm _) _],
      exact [expr mul_le_mul_of_nonneg_right (b_bound n m n (le_refl _) hm) (nonneg v)] },
    have [ident B] [":", expr tendsto (λ
      m, «expr∥ ∥»(«expr - »(f n, f m) v)) at_top (expr𝓝() «expr∥ ∥»(«expr - »(f n, Fcont) v))] [":=", expr tendsto.norm (tendsto_const_nhds.sub (hF v))],
    exact [expr le_of_tendsto B A] },
  erw [expr tendsto_iff_norm_tendsto_zero] [],
  exact [expr squeeze_zero (λ n, norm_nonneg _) this b_lim]
end

end ContinuousMultilinearMap

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem MultilinearMap.mk_continuous_norm_le (f : MultilinearMap 𝕜 E G) {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C*∏i, ∥m i∥) : ∥f.mk_continuous C H∥ ≤ C :=
  ContinuousMultilinearMap.op_norm_le_bound _ hC fun m => H m

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem MultilinearMap.mk_continuous_norm_le' (f : MultilinearMap 𝕜 E G) {C : ℝ} (H : ∀ m, ∥f m∥ ≤ C*∏i, ∥m i∥) :
  ∥f.mk_continuous C H∥ ≤ max C 0 :=
  ContinuousMultilinearMap.op_norm_le_bound _ (le_max_rightₓ _ _)$
    fun m => (H m).trans$ mul_le_mul_of_nonneg_right (le_max_leftₓ _ _) (prod_nonneg$ fun _ _ => norm_nonneg _)

namespace ContinuousMultilinearMap

/-- Given a continuous multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `fin k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is denoted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The implicit
identification between `fin k` and `s` that we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : (G[×n]→L[𝕜] G' : _)) (s : Finset (Finₓ n)) (hk : s.card = k) (z : G) : G[×k]→L[𝕜] G' :=
  (f.to_multilinear_map.restr s hk z).mkContinuous (∥f∥*∥z∥ ^ (n - k))$
    fun v => MultilinearMap.restr_norm_le _ _ _ _ f.le_op_norm _

theorem norm_restr {k n : ℕ} (f : G[×n]→L[𝕜] G') (s : Finset (Finₓ n)) (hk : s.card = k) (z : G) :
  ∥f.restr s hk z∥ ≤ ∥f∥*∥z∥ ^ (n - k) :=
  by 
    apply MultilinearMap.mk_continuous_norm_le 
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

section 

variable(𝕜 ι)(A : Type _)[NormedCommRing A][NormedAlgebra 𝕜 A]

/-- The continuous multilinear map on `A^ι`, where `A` is a normed commutative algebra
over `𝕜`, associating to `m` the product of all the `m i`.

See also `continuous_multilinear_map.mk_pi_algebra_fin`. -/
protected def mk_pi_algebra : ContinuousMultilinearMap 𝕜 (fun i : ι => A) A :=
  MultilinearMap.mkContinuous (MultilinearMap.mkPiAlgebra 𝕜 ι A) (if Nonempty ι then 1 else ∥(1 : A)∥)$
    by 
      intro m 
      cases' is_empty_or_nonempty ι with hι hι
      ·
        simp [eq_empty_of_is_empty univ, not_nonempty_iff.2 hι]
      ·
        simp [norm_prod_le' univ univ_nonempty, hι]

variable{A 𝕜 ι}

@[simp]
theorem mk_pi_algebra_apply (m : ι → A) : ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A m = ∏i, m i :=
  rfl

theorem norm_mk_pi_algebra_le [Nonempty ι] : ∥ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A∥ ≤ 1 :=
  calc ∥ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A∥ ≤ if Nonempty ι then 1 else ∥(1 : A)∥ :=
    MultilinearMap.mk_continuous_norm_le _
      (by 
        splitIfs <;> simp [zero_le_one])
      _ 
    _ = _ := if_pos ‹_›
    

theorem norm_mk_pi_algebra_of_empty [IsEmpty ι] : ∥ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A∥ = ∥(1 : A)∥ :=
  by 
    apply le_antisymmₓ 
    calc ∥ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A∥ ≤ if Nonempty ι then 1 else ∥(1 : A)∥ :=
      MultilinearMap.mk_continuous_norm_le _
        (by 
          splitIfs <;> simp [zero_le_one])
        _ _ = ∥(1 : A)∥ :=
      if_neg (not_nonempty_iff.mpr ‹_›)
    convert ratio_le_op_norm _ fun _ => (1 : A)
    simp [eq_empty_of_is_empty (univ : Finset ι)]

@[simp]
theorem norm_mk_pi_algebra [NormOneClass A] : ∥ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A∥ = 1 :=
  by 
    cases' is_empty_or_nonempty ι
    ·
      simp [norm_mk_pi_algebra_of_empty]
    ·
      refine' le_antisymmₓ norm_mk_pi_algebra_le _ 
      convert ratio_le_op_norm _ fun _ => 1 <;> [skip, infer_instance]
      simp 

end 

section 

variable(𝕜 n)(A : Type _)[NormedRing A][NormedAlgebra 𝕜 A]

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The continuous multilinear map on `A^n`, where `A` is a normed algebra over `𝕜`, associating to
`m` the product of all the `m i`.

See also: `multilinear_map.mk_pi_algebra`. -/
protected
def mk_pi_algebra_fin : continuous_multilinear_map 𝕜 (λ i : fin n, A) A :=
«expr $ »(multilinear_map.mk_continuous (multilinear_map.mk_pi_algebra_fin 𝕜 n A) (nat.cases_on n «expr∥ ∥»((1 : A)) (λ
   _, 1)), begin
   intro [ident m],
   cases [expr n] [],
   { simp [] [] [] [] [] [] },
   { have [] [":", expr «expr ≠ »(@list.of_fn A n.succ m, «expr[ , ]»([]))] [":=", expr by simp [] [] [] [] [] []],
     simpa [] [] [] ["[", "<-", expr fin.prod_of_fn, "]"] [] ["using", expr list.norm_prod_le' this] }
 end)

variable{A 𝕜 n}

@[simp]
theorem mk_pi_algebra_fin_apply (m : Finₓ n → A) :
  ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A m = (List.ofFn m).Prod :=
  rfl

theorem norm_mk_pi_algebra_fin_succ_le : ∥ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A∥ ≤ 1 :=
  MultilinearMap.mk_continuous_norm_le _ zero_le_one _

theorem norm_mk_pi_algebra_fin_le_of_pos (hn : 0 < n) : ∥ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A∥ ≤ 1 :=
  by 
    cases n <;> [exact hn.false.elim, exact norm_mk_pi_algebra_fin_succ_le]

theorem norm_mk_pi_algebra_fin_zero : ∥ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A∥ = ∥(1 : A)∥ :=
  by 
    refine' le_antisymmₓ (MultilinearMap.mk_continuous_norm_le _ (norm_nonneg _) _) _ 
    convert ratio_le_op_norm _ fun _ => 1 <;> [simp , infer_instance]

@[simp]
theorem norm_mk_pi_algebra_fin [NormOneClass A] : ∥ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A∥ = 1 :=
  by 
    cases n
    ·
      simp [norm_mk_pi_algebra_fin_zero]
    ·
      refine' le_antisymmₓ norm_mk_pi_algebra_fin_succ_le _ 
      convert ratio_le_op_norm _ fun _ => 1 <;> [skip, infer_instance]
      simp 

end 

variable(𝕜 ι)

/-- The canonical continuous multilinear map on `𝕜^ι`, associating to `m` the product of all the
`m i` (multiplied by a fixed reference element `z` in the target module) -/
protected def mk_pi_field (z : G) : ContinuousMultilinearMap 𝕜 (fun i : ι => 𝕜) G :=
  MultilinearMap.mkContinuous (MultilinearMap.mkPiRing 𝕜 ι z) ∥z∥
    fun m =>
      by 
        simp only [MultilinearMap.mk_pi_ring_apply, norm_smul, NormedField.norm_prod, mul_commₓ]

variable{𝕜 ι}

@[simp]
theorem mk_pi_field_apply (z : G) (m : ι → 𝕜) :
  (ContinuousMultilinearMap.mkPiField 𝕜 ι z : (ι → 𝕜) → G) m = (∏i, m i) • z :=
  rfl

theorem mk_pi_field_apply_one_eq_self (f : ContinuousMultilinearMap 𝕜 (fun i : ι => 𝕜) G) :
  ContinuousMultilinearMap.mkPiField 𝕜 ι (f fun i => 1) = f :=
  to_multilinear_map_inj f.to_multilinear_map.mk_pi_ring_apply_one_eq_self

variable(𝕜 ι G)

/-- Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear equivalence in
`continuous_multilinear_map.pi_field_equiv_aux`. The continuous linear equivalence is
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv_aux : G ≃ₗ[𝕜] ContinuousMultilinearMap 𝕜 (fun i : ι => 𝕜) G :=
  { toFun := fun z => ContinuousMultilinearMap.mkPiField 𝕜 ι z, invFun := fun f => f fun i => 1,
    map_add' :=
      fun z z' =>
        by 
          ext m 
          simp [smul_add],
    map_smul' :=
      fun c z =>
        by 
          ext m 
          simp [smul_smul, mul_commₓ],
    left_inv :=
      fun z =>
        by 
          simp ,
    right_inv := fun f => f.mk_pi_field_apply_one_eq_self }

/-- Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a continuous linear equivalence in
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv : G ≃L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : ι => 𝕜) G :=
  { ContinuousMultilinearMap.piFieldEquivAux 𝕜 ι G with
    continuous_to_fun :=
      by 
        refine' (ContinuousMultilinearMap.piFieldEquivAux 𝕜 ι G).toLinearMap.continuous_of_bound (1 : ℝ) fun z => _ 
        rw [one_mulₓ]
        change ∥ContinuousMultilinearMap.mkPiField 𝕜 ι z∥ ≤ ∥z∥
        exact MultilinearMap.mk_continuous_norm_le _ (norm_nonneg _) _,
    continuous_inv_fun :=
      by 
        refine'
          (ContinuousMultilinearMap.piFieldEquivAux 𝕜 ι G).symm.toLinearMap.continuous_of_bound (1 : ℝ) fun f => _ 
        rw [one_mulₓ]
        change ∥f fun i => 1∥ ≤ ∥f∥
        apply @ContinuousMultilinearMap.unit_le_op_norm 𝕜 ι (fun i : ι => 𝕜) G _ _ _ _ _ _ _ f 
        simp only [pi_norm_le_iff zero_le_one, norm_one]
        exact fun _ => le_rfl }

end ContinuousMultilinearMap

namespace ContinuousLinearMap

theorem norm_comp_continuous_multilinear_map_le (g : G →L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) :
  ∥g.comp_continuous_multilinear_map f∥ ≤ ∥g∥*∥f∥ :=
  ContinuousMultilinearMap.op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))$
    fun m =>
      calc ∥g (f m)∥ ≤ ∥g∥*∥f∥*∏i, ∥m i∥ := g.le_op_norm_of_le$ f.le_op_norm _ 
        _ = _ := (mul_assocₓ _ _ _).symm
        

/-- `continuous_linear_map.comp_continuous_multilinear_map` as a bundled continuous bilinear map. -/
def comp_continuous_multilinear_mapL :
  (G →L[𝕜] G') →L[𝕜] ContinuousMultilinearMap 𝕜 E G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous₂
      (LinearMap.mk₂ 𝕜 comp_continuous_multilinear_map (fun f₁ f₂ g => rfl) (fun c f g => rfl)
        (fun f g₁ g₂ =>
          by 
            ext1 
            apply f.map_add)
        fun c f g =>
          by 
            ext1 
            simp )
      1$
    fun f g =>
      by 
        rw [one_mulₓ]
        exact f.norm_comp_continuous_multilinear_map_le g

/-- Flip arguments in `f : G →L[𝕜] continuous_multilinear_map 𝕜 E G'` to get
`continuous_multilinear_map 𝕜 E (G →L[𝕜] G')` -/
def flip_multilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') : ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G') :=
  MultilinearMap.mkContinuous
      { toFun :=
          fun m =>
            LinearMap.mkContinuous
                { toFun := fun x => f x m,
                  map_add' :=
                    fun x y =>
                      by 
                        simp only [map_add, ContinuousMultilinearMap.add_apply],
                  map_smul' :=
                    fun c x =>
                      by 
                        simp only [ContinuousMultilinearMap.smul_apply, map_smul, RingHom.id_apply] }
                (∥f∥*∏i, ∥m i∥)$
              fun x =>
                by 
                  rw [mul_right_commₓ]
                  exact (f x).le_of_op_norm_le _ (f.le_op_norm x),
        map_add' :=
          fun m i x y =>
            by 
              ext1 
              simp only [add_apply, ContinuousMultilinearMap.map_add, LinearMap.coe_mk, LinearMap.mk_continuous_apply],
        map_smul' :=
          fun m i c x =>
            by 
              ext1 
              simp only [coe_smul', ContinuousMultilinearMap.map_smul, LinearMap.coe_mk, LinearMap.mk_continuous_apply,
                Pi.smul_apply] }
      ∥f∥$
    fun m =>
      LinearMap.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg f) (prod_nonneg$ fun i hi => norm_nonneg (m i))) _

end ContinuousLinearMap

open ContinuousMultilinearMap

namespace MultilinearMap

/-- Given a map `f : G →ₗ[𝕜] multilinear_map 𝕜 E G'` and an estimate
`H : ∀ x m, ∥f x m∥ ≤ C * ∥x∥ * ∏ i, ∥m i∥`, construct a continuous linear
map from `G` to `continuous_multilinear_map 𝕜 E G'`.

In order to lift, e.g., a map `f : (multilinear_map 𝕜 E G) →ₗ[𝕜] multilinear_map 𝕜 E' G'`
to a map `(continuous_multilinear_map 𝕜 E G) →L[𝕜] continuous_multilinear_map 𝕜 E' G'`,
one can apply this construction to `f.comp continuous_multilinear_map.to_multilinear_map_linear`
which is a linear map from `continuous_multilinear_map 𝕜 E G` to `multilinear_map 𝕜 E' G'`. -/
def mk_continuous_linear (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ) (H : ∀ x m, ∥f x m∥ ≤ (C*∥x∥)*∏i, ∥m i∥) :
  G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous
      { toFun := fun x => (f x).mkContinuous (C*∥x∥)$ H x,
        map_add' :=
          fun x y =>
            by 
              ext1 
              simp ,
        map_smul' :=
          fun c x =>
            by 
              ext1 
              simp  }
      (max C 0)$
    fun x =>
      ((f x).mk_continuous_norm_le' _).trans_eq$
        by 
          rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

theorem mk_continuous_linear_norm_le' (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ)
  (H : ∀ x m, ∥f x m∥ ≤ (C*∥x∥)*∏i, ∥m i∥) : ∥mk_continuous_linear f C H∥ ≤ max C 0 :=
  by 
    dunfold mk_continuous_linear 
    exact LinearMap.mk_continuous_norm_le _ (le_max_rightₓ _ _) _

theorem mk_continuous_linear_norm_le (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ x m, ∥f x m∥ ≤ (C*∥x∥)*∏i, ∥m i∥) : ∥mk_continuous_linear f C H∥ ≤ C :=
  (mk_continuous_linear_norm_le' f C H).trans_eq (max_eq_leftₓ hC)

/-- Given a map `f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)` and an estimate
`H : ∀ m m', ∥f m m'∥ ≤ C * ∏ i, ∥m i∥ * ∏ i, ∥m' i∥`, upgrade all `multilinear_map`s in the type to
`continuous_multilinear_map`s. -/
def mk_continuous_multilinear (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
  (H : ∀ m₁ m₂, ∥f m₁ m₂∥ ≤ (C*∏i, ∥m₁ i∥)*∏i, ∥m₂ i∥) :
  ContinuousMultilinearMap 𝕜 E (ContinuousMultilinearMap 𝕜 E' G) :=
  mk_continuous
      { toFun := fun m => mk_continuous (f m) (C*∏i, ∥m i∥)$ H m,
        map_add' :=
          fun m i x y =>
            by 
              ext1 
              simp ,
        map_smul' :=
          fun m i c x =>
            by 
              ext1 
              simp  }
      (max C 0)$
    fun m =>
      ((f m).mk_continuous_norm_le' _).trans_eq$
        by 
          rw [max_mul_of_nonneg, zero_mul]
          exact prod_nonneg fun _ _ => norm_nonneg _

@[simp]
theorem mk_continuous_multilinear_apply (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : ℝ}
  (H : ∀ m₁ m₂, ∥f m₁ m₂∥ ≤ (C*∏i, ∥m₁ i∥)*∏i, ∥m₂ i∥) (m : ∀ i, E i) :
  «expr⇑ » (mk_continuous_multilinear f C H m) = f m :=
  rfl

theorem mk_continuous_multilinear_norm_le' (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
  (H : ∀ m₁ m₂, ∥f m₁ m₂∥ ≤ (C*∏i, ∥m₁ i∥)*∏i, ∥m₂ i∥) : ∥mk_continuous_multilinear f C H∥ ≤ max C 0 :=
  by 
    dunfold mk_continuous_multilinear 
    exact mk_continuous_norm_le _ (le_max_rightₓ _ _) _

theorem mk_continuous_multilinear_norm_le (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m₁ m₂, ∥f m₁ m₂∥ ≤ (C*∏i, ∥m₁ i∥)*∏i, ∥m₂ i∥) : ∥mk_continuous_multilinear f C H∥ ≤ C :=
  (mk_continuous_multilinear_norm_le' f C H).trans_eq (max_eq_leftₓ hC)

end MultilinearMap

namespace ContinuousMultilinearMap

theorem norm_comp_continuous_linear_le (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : ∀ i, E i →L[𝕜] E₁ i) :
  ∥g.comp_continuous_linear_map f∥ ≤ ∥g∥*∏i, ∥f i∥ :=
  op_norm_le_bound _ (mul_nonneg (norm_nonneg _)$ prod_nonneg$ fun i hi => norm_nonneg _)$
    fun m =>
      calc ∥g fun i => f i (m i)∥ ≤ ∥g∥*∏i, ∥f i (m i)∥ := g.le_op_norm _ 
        _ ≤ ∥g∥*∏i, ∥f i∥*∥m i∥ :=
        mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => (f i).le_op_norm (m i))
          (norm_nonneg g)
        _ = (∥g∥*∏i, ∥f i∥)*∏i, ∥m i∥ :=
        by 
          rw [prod_mul_distrib, mul_assocₓ]
        

/-- `continuous_multilinear_map.comp_continuous_linear_map` as a bundled continuous linear map.
This implementation fixes `f : Π i, E i →L[𝕜] E₁ i`.

TODO: Actually, the map is multilinear in `f` but an attempt to formalize this failed because of
issues with class instances. -/
def comp_continuous_linear_mapL (f : ∀ i, E i →L[𝕜] E₁ i) :
  ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous
      { toFun := fun g => g.comp_continuous_linear_map f, map_add' := fun g₁ g₂ => rfl, map_smul' := fun c g => rfl }
      (∏i, ∥f i∥)$
    fun g => (norm_comp_continuous_linear_le _ _).trans_eq (mul_commₓ _ _)

@[simp]
theorem comp_continuous_linear_mapL_apply (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : ∀ i, E i →L[𝕜] E₁ i) :
  comp_continuous_linear_mapL f g = g.comp_continuous_linear_map f :=
  rfl

theorem norm_comp_continuous_linear_mapL_le (f : ∀ i, E i →L[𝕜] E₁ i) :
  ∥@comp_continuous_linear_mapL 𝕜 ι E E₁ G _ _ _ _ _ _ _ _ _ f∥ ≤ ∏i, ∥f i∥ :=
  LinearMap.mk_continuous_norm_le _ (prod_nonneg$ fun i _ => norm_nonneg _) _

end ContinuousMultilinearMap

section Currying

/-!
### Currying

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `fin n.succ`) two
curried functions, named `f.curry_left` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curry_right` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register continuous linear equiv versions of these correspondences, in
`continuous_multilinear_curry_left_equiv` and `continuous_multilinear_curry_right_equiv`.
-/


open Finₓ Function

theorem ContinuousLinearMap.norm_map_tail_le (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G)
  (m : ∀ i, Ei i) : ∥f (m 0) (tail m)∥ ≤ ∥f∥*∏i, ∥m i∥ :=
  calc ∥f (m 0) (tail m)∥ ≤ ∥f (m 0)∥*∏i, ∥(tail m) i∥ := (f (m 0)).le_op_norm _ 
    _ ≤ (∥f∥*∥m 0∥)*∏i, ∥(tail m) i∥ :=
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (prod_nonneg fun i hi => norm_nonneg _)
    _ = ∥f∥*∥m 0∥*∏i, ∥(tail m) i∥ :=
    by 
      ring 
    _ = ∥f∥*∏i, ∥m i∥ :=
    by 
      rw [prod_univ_succ]
      rfl
    

theorem ContinuousMultilinearMap.norm_map_init_le
  (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) (m : ∀ i, Ei i) :
  ∥f (init m) (m (last n))∥ ≤ ∥f∥*∏i, ∥m i∥ :=
  calc ∥f (init m) (m (last n))∥ ≤ ∥f (init m)∥*∥m (last n)∥ := (f (init m)).le_op_norm _ 
    _ ≤ (∥f∥*∏i, ∥(init m) i∥)*∥m (last n)∥ := mul_le_mul_of_nonneg_right (f.le_op_norm _) (norm_nonneg _)
    _ = ∥f∥*(∏i, ∥(init m) i∥)*∥m (last n)∥ := mul_assocₓ _ _ _ 
    _ = ∥f∥*∏i, ∥m i∥ :=
    by 
      rw [prod_univ_cast_succ]
      rfl
    

theorem ContinuousMultilinearMap.norm_map_cons_le (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
  (m : ∀ i : Finₓ n, Ei i.succ) : ∥f (cons x m)∥ ≤ (∥f∥*∥x∥)*∏i, ∥m i∥ :=
  calc ∥f (cons x m)∥ ≤ ∥f∥*∏i, ∥cons x m i∥ := f.le_op_norm _ 
    _ = (∥f∥*∥x∥)*∏i, ∥m i∥ :=
    by 
      rw [prod_univ_succ]
      simp [mul_assocₓ]
    

theorem ContinuousMultilinearMap.norm_map_snoc_le (f : ContinuousMultilinearMap 𝕜 Ei G)
  (m : ∀ i : Finₓ n, Ei i.cast_succ) (x : Ei (last n)) : ∥f (snoc m x)∥ ≤ (∥f∥*∏i, ∥m i∥)*∥x∥ :=
  calc ∥f (snoc m x)∥ ≤ ∥f∥*∏i, ∥snoc m x i∥ := f.le_op_norm _ 
    _ = (∥f∥*∏i, ∥m i∥)*∥x∥ :=
    by 
      rw [prod_univ_cast_succ]
      simp [mul_assocₓ]
    

/-! #### Left currying -/


/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def ContinuousLinearMap.uncurryLeft (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G) :
  ContinuousMultilinearMap 𝕜 Ei G :=
  (@LinearMap.uncurryLeft 𝕜 n Ei G _ _ _ _ _
        (ContinuousMultilinearMap.toMultilinearMapLinear.comp f.to_linear_map)).mkContinuous
    ∥f∥ fun m => ContinuousLinearMap.norm_map_tail_le f m

@[simp]
theorem ContinuousLinearMap.uncurry_left_apply
  (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G) (m : ∀ i, Ei i) :
  f.uncurry_left m = f (m 0) (tail m) :=
  rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
def ContinuousMultilinearMap.curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
  Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G :=
  LinearMap.mkContinuous
    { toFun := fun x => (f.to_multilinear_map.curry_left x).mkContinuous (∥f∥*∥x∥) (f.norm_map_cons_le x),
      map_add' :=
        fun x y =>
          by 
            ext m 
            exact f.cons_add m x y,
      map_smul' :=
        fun c x =>
          by 
            ext m 
            exact f.cons_smul m c x }
    ∥f∥ fun x => MultilinearMap.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

@[simp]
theorem ContinuousMultilinearMap.curry_left_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
  (m : ∀ i : Finₓ n, Ei i.succ) : f.curry_left x m = f (cons x m) :=
  rfl

@[simp]
theorem ContinuousLinearMap.curry_uncurry_left
  (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G) : f.uncurry_left.curry_left = f :=
  by 
    ext m x 
    simp only [tail_cons, ContinuousLinearMap.uncurry_left_apply, ContinuousMultilinearMap.curry_left_apply]
    rw [cons_zero]

@[simp]
theorem ContinuousMultilinearMap.uncurry_curry_left (f : ContinuousMultilinearMap 𝕜 Ei G) :
  f.curry_left.uncurry_left = f :=
  ContinuousMultilinearMap.to_multilinear_map_inj$ f.to_multilinear_map.uncurry_curry_left

variable(𝕜 Ei G)

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism in
`continuous_multilinear_curry_left_equiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuousMultilinearCurryLeftEquiv :
  (Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G) ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 Ei G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousLinearMap.uncurryLeft,
      map_add' :=
        fun f₁ f₂ =>
          by 
            ext m 
            rfl,
      map_smul' :=
        fun c f =>
          by 
            ext m 
            rfl,
      invFun := ContinuousMultilinearMap.curryLeft, left_inv := ContinuousLinearMap.curry_uncurry_left,
      right_inv := ContinuousMultilinearMap.uncurry_curry_left }
    (fun f => MultilinearMap.mk_continuous_norm_le _ (norm_nonneg f) _)
    fun f => LinearMap.mk_continuous_norm_le _ (norm_nonneg f) _

variable{𝕜 Ei G}

@[simp]
theorem continuous_multilinear_curry_left_equiv_apply
  (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G) (v : ∀ i, Ei i) :
  continuousMultilinearCurryLeftEquiv 𝕜 Ei G f v = f (v 0) (tail v) :=
  rfl

@[simp]
theorem continuous_multilinear_curry_left_equiv_symm_apply (f : ContinuousMultilinearMap 𝕜 Ei G) (x : Ei 0)
  (v : ∀ i : Finₓ n, Ei i.succ) : (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm f x v = f (cons x v) :=
  rfl

@[simp]
theorem ContinuousMultilinearMap.curry_left_norm (f : ContinuousMultilinearMap 𝕜 Ei G) : ∥f.curry_left∥ = ∥f∥ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).symm.norm_map f

@[simp]
theorem ContinuousLinearMap.uncurry_left_norm
  (f : Ei 0 →L[𝕜] ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.succ) G) : ∥f.uncurry_left∥ = ∥f∥ :=
  (continuousMultilinearCurryLeftEquiv 𝕜 Ei G).norm_map f

/-! #### Right currying -/


/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
def ContinuousMultilinearMap.uncurryRight
  (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  ContinuousMultilinearMap 𝕜 Ei G :=
  let f' : MultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →ₗ[𝕜] G) :=
    { toFun := fun m => (f m).toLinearMap,
      map_add' :=
        fun m i x y =>
          by 
            simp ,
      map_smul' :=
        fun m i c x =>
          by 
            simp  }
  (@MultilinearMap.uncurryRight 𝕜 n Ei G _ _ _ _ _ f').mkContinuous ∥f∥ fun m => f.norm_map_init_le m

@[simp]
theorem ContinuousMultilinearMap.uncurry_right_apply
  (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) (m : ∀ i, Ei i) :
  f.uncurry_right m = f (init m) (m (last n)) :=
  rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def ContinuousMultilinearMap.curryRight (f : ContinuousMultilinearMap 𝕜 Ei G) :
  ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G) :=
  let f' : MultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G) :=
    { toFun :=
        fun m => (f.to_multilinear_map.curry_right m).mkContinuous (∥f∥*∏i, ∥m i∥)$ fun x => f.norm_map_snoc_le m x,
      map_add' :=
        fun m i x y =>
          by 
            simp 
            rfl,
      map_smul' :=
        fun m i c x =>
          by 
            simp 
            rfl }
  f'.mk_continuous ∥f∥
    fun m => LinearMap.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg _) (prod_nonneg fun j hj => norm_nonneg _)) _

@[simp]
theorem ContinuousMultilinearMap.curry_right_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
  (m : ∀ i : Finₓ n, Ei i.cast_succ) (x : Ei (last n)) : f.curry_right m x = f (snoc m x) :=
  rfl

@[simp]
theorem ContinuousMultilinearMap.curry_uncurry_right
  (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  f.uncurry_right.curry_right = f :=
  by 
    ext m x 
    simp only [snoc_last, ContinuousMultilinearMap.curry_right_apply, ContinuousMultilinearMap.uncurry_right_apply]
    rw [init_snoc]

@[simp]
theorem ContinuousMultilinearMap.uncurry_curry_right (f : ContinuousMultilinearMap 𝕜 Ei G) :
  f.curry_right.uncurry_right = f :=
  by 
    ext m 
    simp 

variable(𝕜 Ei G)

/--
The space of continuous multilinear maps on `Π(i : fin (n+1)), Ei i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), Ei i.cast_succ` with values in the space
of continuous linear maps on `Ei (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv 𝕜 Ei G`.
The algebraic version (without topology) is given in `multilinear_curry_right_equiv 𝕜 Ei G`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear isometric equivs.
-/
def continuousMultilinearCurryRightEquiv :
  ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G) ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 Ei G :=
  LinearIsometryEquiv.ofBounds
    { toFun := ContinuousMultilinearMap.uncurryRight,
      map_add' :=
        fun f₁ f₂ =>
          by 
            ext m 
            rfl,
      map_smul' :=
        fun c f =>
          by 
            ext m 
            rfl,
      invFun := ContinuousMultilinearMap.curryRight, left_inv := ContinuousMultilinearMap.curry_uncurry_right,
      right_inv := ContinuousMultilinearMap.uncurry_curry_right }
    (fun f => MultilinearMap.mk_continuous_norm_le _ (norm_nonneg f) _)
    fun f => MultilinearMap.mk_continuous_norm_le _ (norm_nonneg f) _

variable(n G')

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), G` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), G` with values in the space
of continuous linear maps on `G`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv' 𝕜 n G G'`.
For a version allowing dependent types, see `continuous_multilinear_curry_right_equiv`. When there
are no dependent types, use the primed version as it helps Lean a lot for unification.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuousMultilinearCurryRightEquiv' : (G[×n]→L[𝕜] G →L[𝕜] G') ≃ₗᵢ[𝕜] G[×n.succ]→L[𝕜] G' :=
  continuousMultilinearCurryRightEquiv 𝕜 (fun i : Finₓ n.succ => G) G'

variable{n 𝕜 G Ei G'}

@[simp]
theorem continuous_multilinear_curry_right_equiv_apply
  (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) (v : ∀ i, Ei i) :
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G) f v = f (init v) (v (last n)) :=
  rfl

@[simp]
theorem continuous_multilinear_curry_right_equiv_symm_apply (f : ContinuousMultilinearMap 𝕜 Ei G)
  (v : ∀ i : Finₓ n, Ei i.cast_succ) (x : Ei (last n)) :
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm f v x = f (snoc v x) :=
  rfl

@[simp]
theorem continuous_multilinear_curry_right_equiv_apply' (f : G[×n]→L[𝕜] G →L[𝕜] G') (v : ∀ i : Finₓ n.succ, G) :
  continuousMultilinearCurryRightEquiv' 𝕜 n G G' f v = f (init v) (v (last n)) :=
  rfl

@[simp]
theorem continuous_multilinear_curry_right_equiv_symm_apply' (f : G[×n.succ]→L[𝕜] G') (v : ∀ i : Finₓ n, G) (x : G) :
  (continuousMultilinearCurryRightEquiv' 𝕜 n G G').symm f v x = f (snoc v x) :=
  rfl

@[simp]
theorem ContinuousMultilinearMap.curry_right_norm (f : ContinuousMultilinearMap 𝕜 Ei G) : ∥f.curry_right∥ = ∥f∥ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map f

@[simp]
theorem ContinuousMultilinearMap.uncurry_right_norm
  (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) : ∥f.uncurry_right∥ = ∥f∥ :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map f

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/


section 

attribute [local instance] Unique.subsingleton

variable{𝕜 G G'}

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
def ContinuousMultilinearMap.uncurry0 (f : ContinuousMultilinearMap 𝕜 (fun i : Finₓ 0 => G) G') : G' :=
  f 0

variable(𝕜 G)

/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
def ContinuousMultilinearMap.curry0 (x : G') : G[×0]→L[𝕜] G' :=
  { toFun := fun m => x, map_add' := fun m i => Finₓ.elim0 i, map_smul' := fun m i => Finₓ.elim0 i,
    cont := continuous_const }

variable{G}

@[simp]
theorem ContinuousMultilinearMap.curry0_apply (x : G') (m : Finₓ 0 → G) : ContinuousMultilinearMap.curry0 𝕜 G x m = x :=
  rfl

variable{𝕜}

@[simp]
theorem ContinuousMultilinearMap.uncurry0_apply (f : G[×0]→L[𝕜] G') : f.uncurry0 = f 0 :=
  rfl

@[simp]
theorem ContinuousMultilinearMap.apply_zero_curry0 (f : G[×0]→L[𝕜] G') {x : Finₓ 0 → G} :
  ContinuousMultilinearMap.curry0 𝕜 G (f x) = f :=
  by 
    ext m 
    simp [(Subsingleton.elimₓ _ _ : x = m)]

theorem ContinuousMultilinearMap.uncurry0_curry0 (f : G[×0]→L[𝕜] G') :
  ContinuousMultilinearMap.curry0 𝕜 G f.uncurry0 = f :=
  by 
    simp 

variable(𝕜 G)

@[simp]
theorem ContinuousMultilinearMap.curry0_uncurry0 (x : G') : (ContinuousMultilinearMap.curry0 𝕜 G x).uncurry0 = x :=
  rfl

@[simp]
theorem ContinuousMultilinearMap.curry0_norm (x : G') : ∥ContinuousMultilinearMap.curry0 𝕜 G x∥ = ∥x∥ :=
  by 
    apply le_antisymmₓ
    ·
      exact
        ContinuousMultilinearMap.op_norm_le_bound _ (norm_nonneg _)
          fun m =>
            by 
              simp 
    ·
      simpa using (ContinuousMultilinearMap.curry0 𝕜 G x).le_op_norm 0

variable{𝕜 G}

-- error in Analysis.NormedSpace.Multilinear: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem continuous_multilinear_map.fin0_apply_norm
(f : «expr [× ]→L[ ] »(G, 0, 𝕜, G'))
{x : fin 0 → G} : «expr = »(«expr∥ ∥»(f x), «expr∥ ∥»(f)) :=
begin
  have [] [":", expr «expr = »(x, 0)] [":=", expr subsingleton.elim _ _],
  subst [expr this],
  refine [expr le_antisymm (by simpa [] [] [] [] [] ["using", expr f.le_op_norm 0]) _],
  have [] [":", expr «expr ≤ »(«expr∥ ∥»(continuous_multilinear_map.curry0 𝕜 G f.uncurry0), «expr∥ ∥»(f.uncurry0))] [":=", expr continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λ
    m, by simp [] [] [] ["[", "-", ident continuous_multilinear_map.apply_zero_curry0, "]"] [] [])],
  simpa [] [] [] [] [] []
end

theorem ContinuousMultilinearMap.uncurry0_norm (f : G[×0]→L[𝕜] G') : ∥f.uncurry0∥ = ∥f∥ :=
  by 
    simp 

variable(𝕜 G G')

/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear isometric equivs. -/
def continuousMultilinearCurryFin0 : (G[×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' :=
  { toFun := fun f => ContinuousMultilinearMap.uncurry0 f, invFun := fun f => ContinuousMultilinearMap.curry0 𝕜 G f,
    map_add' := fun f g => rfl, map_smul' := fun c f => rfl, left_inv := ContinuousMultilinearMap.uncurry0_curry0,
    right_inv := ContinuousMultilinearMap.curry0_uncurry0 𝕜 G, norm_map' := ContinuousMultilinearMap.uncurry0_norm }

variable{𝕜 G G'}

@[simp]
theorem continuous_multilinear_curry_fin0_apply (f : G[×0]→L[𝕜] G') : continuousMultilinearCurryFin0 𝕜 G G' f = f 0 :=
  rfl

@[simp]
theorem continuous_multilinear_curry_fin0_symm_apply (x : G') (v : Finₓ 0 → G) :
  (continuousMultilinearCurryFin0 𝕜 G G').symm x v = x :=
  rfl

end 

/-! #### With 1 variable -/


variable(𝕜 G G')

/-- Continuous multilinear maps from `G^1` to `G'` are isomorphic with continuous linear maps from
`G` to `G'`. -/
def continuousMultilinearCurryFin1 : (G[×1]→L[𝕜] G') ≃ₗᵢ[𝕜] G →L[𝕜] G' :=
  (continuousMultilinearCurryRightEquiv 𝕜 (fun i : Finₓ 1 => G) G').symm.trans
    (continuousMultilinearCurryFin0 𝕜 G (G →L[𝕜] G'))

variable{𝕜 G G'}

@[simp]
theorem continuous_multilinear_curry_fin1_apply (f : G[×1]→L[𝕜] G') (x : G) :
  continuousMultilinearCurryFin1 𝕜 G G' f x = f (Finₓ.snoc 0 x) :=
  rfl

@[simp]
theorem continuous_multilinear_curry_fin1_symm_apply (f : G →L[𝕜] G') (v : Finₓ 1 → G) :
  (continuousMultilinearCurryFin1 𝕜 G G').symm f v = f (v 0) :=
  rfl

namespace ContinuousMultilinearMap

variable(𝕜 G G')

/-- An equivalence of the index set defines a linear isometric equivalence between the spaces
of multilinear maps. -/
def dom_dom_congr (σ : ι ≃ ι') :
  ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G' ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G' :=
  LinearIsometryEquiv.ofBounds
    { toFun :=
        fun f =>
          (MultilinearMap.domDomCongr σ f.to_multilinear_map).mkContinuous ∥f∥$
            fun m =>
              (f.le_op_norm fun i => m (σ i)).trans_eq$
                by 
                  rw [←σ.prod_comp],
      invFun :=
        fun f =>
          (MultilinearMap.domDomCongr σ.symm f.to_multilinear_map).mkContinuous ∥f∥$
            fun m =>
              (f.le_op_norm fun i => m (σ.symm i)).trans_eq$
                by 
                  rw [←σ.symm.prod_comp],
      left_inv :=
        fun f =>
          ext$
            fun m =>
              congr_argₓ f$
                by 
                  simp only [σ.symm_apply_apply],
      right_inv :=
        fun f =>
          ext$
            fun m =>
              congr_argₓ f$
                by 
                  simp only [σ.apply_symm_apply],
      map_add' := fun f g => rfl, map_smul' := fun c f => rfl }
    (fun f => MultilinearMap.mk_continuous_norm_le _ (norm_nonneg f) _)
    fun f => MultilinearMap.mk_continuous_norm_le _ (norm_nonneg f) _

variable{𝕜 G G'}

section 

variable[DecidableEq (Sum ι ι')]

/-- A continuous multilinear map with variables indexed by `ι ⊕ ι'` defines a continuous multilinear
map with variables indexed by `ι` taking values in the space of continuous multilinear maps with
variables indexed by `ι'`. -/
def curry_sum (f : ContinuousMultilinearMap 𝕜 (fun x : Sum ι ι' => G) G') :
  ContinuousMultilinearMap 𝕜 (fun x : ι => G) (ContinuousMultilinearMap 𝕜 (fun x : ι' => G) G') :=
  MultilinearMap.mkContinuousMultilinear (MultilinearMap.currySum f.to_multilinear_map) ∥f∥$
    fun m m' =>
      by 
        simpa [Fintype.prod_sum_type, mul_assocₓ] using f.le_op_norm (Sum.elim m m')

@[simp]
theorem curry_sum_apply (f : ContinuousMultilinearMap 𝕜 (fun x : Sum ι ι' => G) G') (m : ι → G) (m' : ι' → G) :
  f.curry_sum m m' = f (Sum.elim m m') :=
  rfl

/-- A continuous multilinear map with variables indexed by `ι` taking values in the space of
continuous multilinear maps with variables indexed by `ι'` defines a continuous multilinear map with
variables indexed by `ι ⊕ ι'`. -/
def uncurry_sum (f : ContinuousMultilinearMap 𝕜 (fun x : ι => G) (ContinuousMultilinearMap 𝕜 (fun x : ι' => G) G')) :
  ContinuousMultilinearMap 𝕜 (fun x : Sum ι ι' => G) G' :=
  MultilinearMap.mkContinuous (to_multilinear_map_linear.compMultilinearMap f.to_multilinear_map).uncurrySum ∥f∥$
    fun m =>
      by 
        simpa [Fintype.prod_sum_type, mul_assocₓ] using
          (f (m ∘ Sum.inl)).le_of_op_norm_le (m ∘ Sum.inr) (f.le_op_norm _)

@[simp]
theorem uncurry_sum_apply
  (f : ContinuousMultilinearMap 𝕜 (fun x : ι => G) (ContinuousMultilinearMap 𝕜 (fun x : ι' => G) G'))
  (m : Sum ι ι' → G) : f.uncurry_sum m = f (m ∘ Sum.inl) (m ∘ Sum.inr) :=
  rfl

variable(𝕜 ι ι' G G')

/-- Linear isometric equivalence between the space of continuous multilinear maps with variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed by `ι'`.

The forward and inverse functions are `continuous_multilinear_map.curry_sum`
and `continuous_multilinear_map.uncurry_sum`. Use this definition only if you need
some properties of `linear_isometry_equiv`. -/
def curry_sum_equiv :
  ContinuousMultilinearMap 𝕜 (fun x : Sum ι ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun x : ι => G) (ContinuousMultilinearMap 𝕜 (fun x : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := curry_sum, invFun := uncurry_sum,
      map_add' :=
        fun f g =>
          by 
            ext 
            rfl,
      map_smul' :=
        fun c f =>
          by 
            ext 
            rfl,
      left_inv :=
        fun f =>
          by 
            ext m 
            exact congr_argₓ f (Sum.elim_comp_inl_inr m),
      right_inv :=
        fun f =>
          by 
            ext m₁ m₂ 
            change f _ _ = f _ _ 
            rw [Sum.elim_comp_inl, Sum.elim_comp_inr] }
    (fun f => MultilinearMap.mk_continuous_multilinear_norm_le _ (norm_nonneg f) _)
    fun f => MultilinearMap.mk_continuous_norm_le _ (norm_nonneg f) _

end 

section 

variable(𝕜 G G'){k l : ℕ}{s : Finset (Finₓ n)}

/-- If `s : finset (fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of continuous multilinear maps `G [×n]→L[𝕜] G'` of `n` variables is isomorphic
to the space of continuous multilinear maps `G [×k]→L[𝕜] G [×l]→L[𝕜] G'` of `k` variables taking
values in the space of continuous multilinear maps of `l` variables. -/
def curry_fin_finset {k l n : ℕ} {s : Finset (Finₓ n)} (hk : s.card = k) (hl : («expr ᶜ» s).card = l) :
  (G[×n]→L[𝕜] G') ≃ₗᵢ[𝕜] G[×k]→L[𝕜] G[×l]→L[𝕜] G' :=
  (dom_dom_congr 𝕜 G G' (finSumEquivOfFinset hk hl).symm).trans (curry_sum_equiv 𝕜 (Finₓ k) (Finₓ l) G G')

variable{𝕜 G G'}

@[simp]
theorem curry_fin_finset_apply (hk : s.card = k) (hl : («expr ᶜ» s).card = l) (f : G[×n]→L[𝕜] G') (mk : Finₓ k → G)
  (ml : Finₓ l → G) :
  curry_fin_finset 𝕜 G G' hk hl f mk ml = f fun i => Sum.elim mk ml ((finSumEquivOfFinset hk hl).symm i) :=
  rfl

@[simp]
theorem curry_fin_finset_symm_apply (hk : s.card = k) (hl : («expr ᶜ» s).card = l) (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G')
  (m : Finₓ n → G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f m =
    f (fun i => m$ finSumEquivOfFinset hk hl (Sum.inl i)) fun i => m$ finSumEquivOfFinset hk hl (Sum.inr i) :=
  rfl

@[simp]
theorem curry_fin_finset_symm_apply_piecewise_const (hk : s.card = k) (hl : («expr ᶜ» s).card = l)
  (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G') (x y : G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f (s.piecewise (fun _ => x) fun _ => y) = f (fun _ => x) fun _ => y :=
  MultilinearMap.curry_fin_finset_symm_apply_piecewise_const hk hl _ x y

@[simp]
theorem curry_fin_finset_symm_apply_const (hk : s.card = k) (hl : («expr ᶜ» s).card = l) (f : G[×k]→L[𝕜] G[×l]→L[𝕜] G')
  (x : G) : ((curry_fin_finset 𝕜 G G' hk hl).symm f fun _ => x) = f (fun _ => x) fun _ => x :=
  rfl

@[simp]
theorem curry_fin_finset_apply_const (hk : s.card = k) (hl : («expr ᶜ» s).card = l) (f : G[×n]→L[𝕜] G') (x y : G) :
  (curry_fin_finset 𝕜 G G' hk hl f (fun _ => x) fun _ => y) = f (s.piecewise (fun _ => x) fun _ => y) :=
  by 
    refine' (curry_fin_finset_symm_apply_piecewise_const hk hl _ _ _).symm.trans _ 
    rw [LinearIsometryEquiv.symm_apply_apply]

end 

end ContinuousMultilinearMap

end Currying

