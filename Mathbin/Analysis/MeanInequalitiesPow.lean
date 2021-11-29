import Mathbin.Analysis.Convex.SpecificFunctions

/-!
# Mean value inequalities

In this file we prove several mean inequalities for finite sums. Versions for integrals of some of
these inequalities are available in `measure_theory.mean_inequalities`.

## Main theorems: generalized mean inequality

The inequality says that for two non-negative vectors $w$ and $z$ with $\sum_{i\in s} w_i=1$
and $p ≤ q$ we have
$$
\sqrt[p]{\sum_{i\in s} w_i z_i^p} ≤ \sqrt[q]{\sum_{i\in s} w_i z_i^q}.
$$

Currently we only prove this inequality for $p=1$. As in the rest of `mathlib`, we provide
different theorems for natural exponents (`pow_arith_mean_le_arith_mean_pow`), integer exponents
(`zpow_arith_mean_le_arith_mean_zpow`), and real exponents (`rpow_arith_mean_le_arith_mean_rpow` and
`arith_mean_le_rpow_mean`). In the first two cases we prove
$$
\left(\sum_{i\in s} w_i z_i\right)^n ≤ \sum_{i\in s} w_i z_i^n
$$
in order to avoid using real exponents. For real exponents we prove both this and standard versions.

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

variable {ι : Type u} (s : Finset ι)

namespace Real

theorem pow_arith_mean_le_arith_mean_pow (w z : ι → ℝ) (hw : ∀ i _ : i ∈ s, 0 ≤ w i) (hw' : (∑i in s, w i) = 1)
  (hz : ∀ i _ : i ∈ s, 0 ≤ z i) (n : ℕ) : ((∑i in s, w i*z i)^n) ≤ ∑i in s, w i*z i^n :=
  (convex_on_pow n).map_sum_le hw hw' hz

theorem pow_arith_mean_le_arith_mean_pow_of_even (w z : ι → ℝ) (hw : ∀ i _ : i ∈ s, 0 ≤ w i) (hw' : (∑i in s, w i) = 1)
  {n : ℕ} (hn : Even n) : ((∑i in s, w i*z i)^n) ≤ ∑i in s, w i*z i^n :=
  hn.convex_on_pow.map_sum_le hw hw' fun _ _ => trivialₓ

theorem zpow_arith_mean_le_arith_mean_zpow (w z : ι → ℝ) (hw : ∀ i _ : i ∈ s, 0 ≤ w i) (hw' : (∑i in s, w i) = 1)
  (hz : ∀ i _ : i ∈ s, 0 < z i) (m : ℤ) : ((∑i in s, w i*z i)^m) ≤ ∑i in s, w i*z i^m :=
  (convex_on_zpow m).map_sum_le hw hw' hz

theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι → ℝ) (hw : ∀ i _ : i ∈ s, 0 ≤ w i) (hw' : (∑i in s, w i) = 1)
  (hz : ∀ i _ : i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) : ((∑i in s, w i*z i)^p) ≤ ∑i in s, w i*z i^p :=
  (convex_on_rpow hp).map_sum_le hw hw' hz

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem arith_mean_le_rpow_mean
(w z : ι → exprℝ())
(hw : ∀ i «expr ∈ » s, «expr ≤ »(0, w i))
(hw' : «expr = »(«expr∑ in , »((i), s, w i), 1))
(hz : ∀ i «expr ∈ » s, «expr ≤ »(0, z i))
{p : exprℝ()}
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr∑ in , »((i), s, «expr * »(w i, z i)), «expr ^ »(«expr∑ in , »((i), s, «expr * »(w i, «expr ^ »(z i, p))), «expr / »(1, p))) :=
begin
  have [] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one hp],
  rw ["[", "<-", expr rpow_le_rpow_iff _ _ this, ",", "<-", expr rpow_mul, ",", expr one_div_mul_cancel (ne_of_gt this), ",", expr rpow_one, "]"] [],
  exact [expr rpow_arith_mean_le_arith_mean_rpow s w z hw hw' hz hp],
  all_goals { apply_rules ["[", expr sum_nonneg, ",", expr rpow_nonneg_of_nonneg, "]"],
    intros [ident i, ident hi],
    apply_rules ["[", expr mul_nonneg, ",", expr rpow_nonneg_of_nonneg, ",", expr hw i hi, ",", expr hz i hi, "]"] }
end

end Real

namespace Nnreal

/-- Weighted generalized mean inequality, version sums over finite sets, with `ℝ≥0`-valued
functions and natural exponent. -/
theorem pow_arith_mean_le_arith_mean_pow (w z : ι →  ℝ≥0 ) (hw' : (∑i in s, w i) = 1) (n : ℕ) :
  ((∑i in s, w i*z i)^n) ≤ ∑i in s, w i*z i^n :=
  by 
    exactModCast
      Real.pow_arith_mean_le_arith_mean_pow s _ _ (fun i _ => (w i).coe_nonneg)
        (by 
          exactModCast hw')
        (fun i _ => (z i).coe_nonneg) n

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow (w z : ι →  ℝ≥0 ) (hw' : (∑i in s, w i) = 1) {p : ℝ} (hp : 1 ≤ p) :
  ((∑i in s, w i*z i)^p) ≤ ∑i in s, w i*z i^p :=
  by 
    exactModCast
      Real.rpow_arith_mean_le_arith_mean_rpow s _ _ (fun i _ => (w i).coe_nonneg)
        (by 
          exactModCast hw')
        (fun i _ => (z i).coe_nonneg) hp

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0` and real exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow
(w₁ w₂ z₁ z₂ : «exprℝ≥0»())
(hw' : «expr = »(«expr + »(w₁, w₂), 1))
{p : exprℝ()}
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr + »(«expr * »(w₁, z₁), «expr * »(w₂, z₂)), p), «expr + »(«expr * »(w₁, «expr ^ »(z₁, p)), «expr * »(w₂, «expr ^ »(z₂, p)))) :=
begin
  have [ident h] [] [":=", expr rpow_arith_mean_le_arith_mean_rpow (univ : finset (fin 2)) «expr $ »(fin.cons w₁, fin.cons w₂ fin_zero_elim) «expr $ »(fin.cons z₁, «expr $ »(fin.cons z₂, fin_zero_elim)) _ hp],
  { simpa [] [] [] ["[", expr fin.sum_univ_succ, ",", expr fin.sum_univ_zero, ",", expr fin.cons_succ, ",", expr fin.cons_zero, "]"] [] ["using", expr h] },
  { simp [] [] [] ["[", expr hw', ",", expr fin.sum_univ_succ, ",", expr fin.sum_univ_zero, ",", expr fin.cons_succ, ",", expr fin.cons_zero, "]"] [] [] }
end

/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0`-valued
functions and real exponents. -/
theorem arith_mean_le_rpow_mean (w z : ι →  ℝ≥0 ) (hw' : (∑i in s, w i) = 1) {p : ℝ} (hp : 1 ≤ p) :
  (∑i in s, w i*z i) ≤ ((∑i in s, w i*z i^p)^1 / p) :=
  by 
    exactModCast
      Real.arith_mean_le_rpow_mean s _ _ (fun i _ => (w i).coe_nonneg)
        (by 
          exactModCast hw')
        (fun i _ => (z i).coe_nonneg) hp

end Nnreal

namespace Ennreal

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Weighted generalized mean inequality, version for sums over finite sets, with `ℝ≥0∞`-valued
functions and real exponents. -/
theorem rpow_arith_mean_le_arith_mean_rpow
(w z : ι → «exprℝ≥0∞»())
(hw' : «expr = »(«expr∑ in , »((i), s, w i), 1))
{p : exprℝ()}
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr∑ in , »((i), s, «expr * »(w i, z i)), p), «expr∑ in , »((i), s, «expr * »(w i, «expr ^ »(z i, p)))) :=
begin
  have [ident hp_pos] [":", expr «expr < »(0, p)] [],
  from [expr lt_of_lt_of_le zero_lt_one hp],
  have [ident hp_nonneg] [":", expr «expr ≤ »(0, p)] [],
  from [expr le_of_lt hp_pos],
  have [ident hp_not_nonpos] [":", expr «expr¬ »(«expr ≤ »(p, 0))] [],
  by simp [] [] [] ["[", expr hp_pos, "]"] [] [],
  have [ident hp_not_neg] [":", expr «expr¬ »(«expr < »(p, 0))] [],
  by simp [] [] [] ["[", expr hp_nonneg, "]"] [] [],
  have [ident h_top_iff_rpow_top] [":", expr ∀
   (i : ι)
   (hi : «expr ∈ »(i, s)), «expr ↔ »(«expr = »(«expr * »(w i, z i), «expr⊤»()), «expr = »(«expr * »(w i, «expr ^ »(z i, p)), «expr⊤»()))] [],
  by simp [] [] [] ["[", expr hp_pos, ",", expr hp_nonneg, ",", expr hp_not_nonpos, ",", expr hp_not_neg, "]"] [] [],
  refine [expr le_of_top_imp_top_of_to_nnreal_le _ _],
  { rw ["[", expr rpow_eq_top_iff, ",", expr sum_eq_top_iff, ",", expr sum_eq_top_iff, "]"] [],
    intro [ident h],
    simp [] [] ["only"] ["[", expr and_false, ",", expr hp_not_neg, ",", expr false_or, "]"] [] ["at", ident h],
    rcases [expr h.left, "with", "⟨", ident a, ",", ident H, ",", ident ha, "⟩"],
    use ["[", expr a, ",", expr H, "]"],
    rwa ["<-", expr h_top_iff_rpow_top a H] [] },
  { intros [ident h_top_rpow_sum, "_"],
    have [ident h_top] [":", expr ∀ a : ι, «expr ∈ »(a, s) → «expr ≠ »(«expr * »(w a, z a), «expr⊤»())] [],
    { have [ident h_top_sum] [":", expr «expr ≠ »(«expr∑ in , »((i : ι), s, «expr * »(w i, z i)), «expr⊤»())] [],
      { intro [ident h],
        rw ["[", expr h, ",", expr top_rpow_of_pos hp_pos, "]"] ["at", ident h_top_rpow_sum],
        exact [expr h_top_rpow_sum rfl] },
      exact [expr λ a ha, (lt_top_of_sum_ne_top h_top_sum ha).ne] },
    have [ident h_top_rpow] [":", expr ∀
     a : ι, «expr ∈ »(a, s) → «expr ≠ »(«expr * »(w a, «expr ^ »(z a, p)), «expr⊤»())] [],
    { intros [ident i, ident hi],
      specialize [expr h_top i hi],
      rwa ["[", expr ne.def, ",", "<-", expr h_top_iff_rpow_top i hi, "]"] [] },
    simp_rw ["[", expr to_nnreal_sum h_top_rpow, ",", "<-", expr to_nnreal_rpow, ",", expr to_nnreal_sum h_top, ",", expr to_nnreal_mul, ",", "<-", expr to_nnreal_rpow, "]"] [],
    refine [expr nnreal.rpow_arith_mean_le_arith_mean_rpow s (λ i, (w i).to_nnreal) (λ i, (z i).to_nnreal) _ hp],
    have [ident h_sum_nnreal] [":", expr «expr = »(«expr∑ in , »((i), s, w i), «expr↑ »(«expr∑ in , »((i), s, (w i).to_nnreal)))] [],
    { rw [expr coe_finset_sum] [],
      refine [expr sum_congr rfl (λ i hi, (coe_to_nnreal _).symm)],
      refine [expr (lt_top_of_sum_ne_top _ hi).ne],
      exact [expr «expr ▸ »(hw'.symm, ennreal.one_ne_top)] },
    rwa ["[", "<-", expr coe_eq_coe, ",", "<-", expr h_sum_nnreal, "]"] [] }
end

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Weighted generalized mean inequality, version for two elements of `ℝ≥0∞` and real
exponents. -/
theorem rpow_arith_mean_le_arith_mean2_rpow
(w₁ w₂ z₁ z₂ : «exprℝ≥0∞»())
(hw' : «expr = »(«expr + »(w₁, w₂), 1))
{p : exprℝ()}
(hp : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr + »(«expr * »(w₁, z₁), «expr * »(w₂, z₂)), p), «expr + »(«expr * »(w₁, «expr ^ »(z₁, p)), «expr * »(w₂, «expr ^ »(z₂, p)))) :=
begin
  have [ident h] [] [":=", expr rpow_arith_mean_le_arith_mean_rpow (univ : finset (fin 2)) «expr $ »(fin.cons w₁, fin.cons w₂ fin_zero_elim) «expr $ »(fin.cons z₁, «expr $ »(fin.cons z₂, fin_zero_elim)) _ hp],
  { simpa [] [] [] ["[", expr fin.sum_univ_succ, ",", expr fin.sum_univ_zero, ",", expr fin.cons_succ, ",", expr fin.cons_zero, "]"] [] ["using", expr h] },
  { simp [] [] [] ["[", expr hw', ",", expr fin.sum_univ_succ, ",", expr fin.sum_univ_zero, ",", expr fin.cons_succ, ",", expr fin.cons_zero, "]"] [] [] }
end

end Ennreal

namespace Ennreal

variable (f g : ι → ℝ≥0∞) {p q : ℝ}

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem add_rpow_le_one_of_add_le_one
{p : exprℝ()}
(a b : «exprℝ≥0∞»())
(hab : «expr ≤ »(«expr + »(a, b), 1))
(hp1 : «expr ≤ »(1, p)) : «expr ≤ »(«expr + »(«expr ^ »(a, p), «expr ^ »(b, p)), 1) :=
begin
  have [ident h_le_one] [":", expr ∀ x : «exprℝ≥0∞»(), «expr ≤ »(x, 1) → «expr ≤ »(«expr ^ »(x, p), x)] [],
  from [expr λ x hx, rpow_le_self_of_le_one hx hp1],
  have [ident ha] [":", expr «expr ≤ »(a, 1)] [],
  from [expr (self_le_add_right a b).trans hab],
  have [ident hb] [":", expr «expr ≤ »(b, 1)] [],
  from [expr (self_le_add_left b a).trans hab],
  exact [expr (add_le_add (h_le_one a ha) (h_le_one b hb)).trans hab]
end

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_rpow_le_rpow_add
{p : exprℝ()}
(a b : «exprℝ≥0∞»())
(hp1 : «expr ≤ »(1, p)) : «expr ≤ »(«expr + »(«expr ^ »(a, p), «expr ^ »(b, p)), «expr ^ »(«expr + »(a, b), p)) :=
begin
  have [ident hp_pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le zero_lt_one hp1],
  by_cases [expr h_top, ":", expr «expr = »(«expr + »(a, b), «expr⊤»())],
  { rw ["<-", expr @ennreal.rpow_eq_top_iff_of_pos «expr + »(a, b) p hp_pos] ["at", ident h_top],
    rw [expr h_top] [],
    exact [expr le_top] },
  obtain ["⟨", ident ha_top, ",", ident hb_top, "⟩", ":=", expr add_ne_top.mp h_top],
  by_cases [expr h_zero, ":", expr «expr = »(«expr + »(a, b), 0)],
  { simp [] [] [] ["[", expr add_eq_zero_iff.mp h_zero, ",", expr ennreal.zero_rpow_of_pos hp_pos, "]"] [] [] },
  have [ident h_nonzero] [":", expr «expr¬ »(«expr ∧ »(«expr = »(a, 0), «expr = »(b, 0)))] [],
  by rwa [expr add_eq_zero_iff] ["at", ident h_zero],
  have [ident h_add] [":", expr «expr = »(«expr + »(«expr / »(a, «expr + »(a, b)), «expr / »(b, «expr + »(a, b))), 1)] [],
  by rw ["[", expr div_add_div_same, ",", expr div_self h_zero h_top, "]"] [],
  have [ident h] [] [":=", expr add_rpow_le_one_of_add_le_one «expr / »(a, «expr + »(a, b)) «expr / »(b, «expr + »(a, b)) h_add.le hp1],
  rw ["[", expr div_rpow_of_nonneg a «expr + »(a, b) hp_pos.le, ",", expr div_rpow_of_nonneg b «expr + »(a, b) hp_pos.le, "]"] ["at", ident h],
  have [ident hab_0] [":", expr «expr ≠ »(«expr ^ »(«expr + »(a, b), p), 0)] [],
  by simp [] [] [] ["[", expr ha_top, ",", expr hb_top, ",", expr hp_pos, ",", expr h_nonzero, "]"] [] [],
  have [ident hab_top] [":", expr «expr ≠ »(«expr ^ »(«expr + »(a, b), p), «expr⊤»())] [],
  by simp [] [] [] ["[", expr ha_top, ",", expr hb_top, ",", expr hp_pos, ",", expr h_nonzero, "]"] [] [],
  have [ident h_mul] [":", expr «expr ≤ »(«expr * »(«expr ^ »(«expr + »(a, b), p), «expr + »(«expr / »(«expr ^ »(a, p), «expr ^ »(«expr + »(a, b), p)), «expr / »(«expr ^ »(b, p), «expr ^ »(«expr + »(a, b), p)))), «expr ^ »(«expr + »(a, b), p))] [],
  { nth_rewrite [3] ["<-", expr mul_one «expr ^ »(«expr + »(a, b), p)] [],
    exact [expr (mul_le_mul_left hab_0 hab_top).mpr h] },
  rwa ["[", expr div_eq_mul_inv, ",", expr div_eq_mul_inv, ",", expr mul_add, ",", expr mul_comm «expr ^ »(a, p), ",", expr mul_comm «expr ^ »(b, p), ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, ",", expr mul_inv_cancel hab_0 hab_top, ",", expr one_mul, ",", expr one_mul, "]"] ["at", ident h_mul]
end

theorem rpow_add_rpow_le_add {p : ℝ} (a b : ℝ≥0∞) (hp1 : 1 ≤ p) : (((a^p)+b^p)^1 / p) ≤ a+b :=
  by 
    rw
      [←@Ennreal.le_rpow_one_div_iff _ _ (1 / p)
        (by 
          simp [lt_of_lt_of_leₓ zero_lt_one hp1])]
    rw [one_div_one_div]
    exact add_rpow_le_rpow_add _ _ hp1

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rpow_add_rpow_le
{p q : exprℝ()}
(a b : «exprℝ≥0∞»())
(hp_pos : «expr < »(0, p))
(hpq : «expr ≤ »(p, q)) : «expr ≤ »(«expr ^ »(«expr + »(«expr ^ »(a, q), «expr ^ »(b, q)), «expr / »(1, q)), «expr ^ »(«expr + »(«expr ^ »(a, p), «expr ^ »(b, p)), «expr / »(1, p))) :=
begin
  have [ident h_rpow] [":", expr ∀
   a : «exprℝ≥0∞»(), «expr = »(«expr ^ »(a, q), «expr ^ »(«expr ^ »(a, p), «expr / »(q, p)))] [],
  from [expr λ
   a, by rw ["[", "<-", expr ennreal.rpow_mul, ",", expr div_eq_inv_mul, ",", "<-", expr mul_assoc, ",", expr _root_.mul_inv_cancel hp_pos.ne.symm, ",", expr one_mul, "]"] []],
  have [ident h_rpow_add_rpow_le_add] [":", expr «expr ≤ »(«expr ^ »(«expr + »(«expr ^ »(«expr ^ »(a, p), «expr / »(q, p)), «expr ^ »(«expr ^ »(b, p), «expr / »(q, p))), «expr / »(1, «expr / »(q, p))), «expr + »(«expr ^ »(a, p), «expr ^ »(b, p)))] [],
  { refine [expr rpow_add_rpow_le_add «expr ^ »(a, p) «expr ^ »(b, p) _],
    rwa [expr one_le_div hp_pos] [] },
  rw ["[", expr h_rpow a, ",", expr h_rpow b, ",", expr ennreal.le_rpow_one_div_iff hp_pos, ",", "<-", expr ennreal.rpow_mul, ",", expr mul_comm, ",", expr mul_one_div, "]"] [],
  rwa [expr one_div_div] ["at", ident h_rpow_add_rpow_le_add]
end

-- error in Analysis.MeanInequalitiesPow: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rpow_add_le_add_rpow
{p : exprℝ()}
(a b : «exprℝ≥0∞»())
(hp_pos : «expr < »(0, p))
(hp1 : «expr ≤ »(p, 1)) : «expr ≤ »(«expr ^ »(«expr + »(a, b), p), «expr + »(«expr ^ »(a, p), «expr ^ »(b, p))) :=
begin
  have [ident h] [] [":=", expr rpow_add_rpow_le a b hp_pos hp1],
  rw [expr one_div_one] ["at", ident h],
  repeat { rw [expr ennreal.rpow_one] ["at", ident h] },
  exact [expr (ennreal.le_rpow_one_div_iff hp_pos).mp h]
end

end Ennreal

