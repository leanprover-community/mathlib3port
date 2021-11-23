import Mathbin.Analysis.SpecificLimits

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The first main result is `is_open`:  the group of units of a complete normed ring is an open subset
of the ring.

The function `inverse` (defined in `algebra.ring`), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is
a unit and 0 if not.  The other major results of this file (notably `inverse_add`,
`inverse_add_norm` and `inverse_add_norm_diff_nth_order`) cover the asymptotic properties of
`inverse (x + t)` as `t → 0`.

-/


noncomputable theory

open_locale TopologicalSpace

variable{R : Type _}[NormedRing R][CompleteSpace R]

namespace Units

/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
@[simps coe]
def one_sub (t : R) (h : ∥t∥ < 1) : Units R :=
  { val := 1 - t, inv := ∑'n : ℕ, t ^ n, val_inv := mul_neg_geom_series t h, inv_val := geom_series_mul_neg t h }

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`∥x⁻¹∥⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
@[simps #[ident coe]]
def add
(x : units R)
(t : R)
(h : «expr < »(«expr∥ ∥»(t), «expr ⁻¹»(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R))))) : units R :=
units.copy «expr * »(x, units.one_sub «expr- »(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t)) (begin
    nontriviality [expr R] ["using", "[", expr zero_lt_one, "]"],
    have [ident hpos] [":", expr «expr < »(0, «expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)))] [":=", expr units.norm_pos «expr ⁻¹»(x)],
    calc
      «expr = »(«expr∥ ∥»(«expr- »(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t))), «expr∥ ∥»(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t))) : by { rw [expr norm_neg] [] }
      «expr ≤ »(..., «expr * »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), «expr∥ ∥»(t))) : norm_mul_le «expr↑ »(«expr ⁻¹»(x)) _
      «expr < »(..., «expr * »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), «expr ⁻¹»(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R))))) : by nlinarith [] ["only"] ["[", expr h, ",", expr hpos, "]"]
      «expr = »(..., 1) : mul_inv_cancel (ne_of_gt hpos)
  end)) «expr + »(x, t) (by simp [] [] [] ["[", expr mul_add, "]"] [] []) _ rfl

/-- In a complete normed ring, an element `y` of distance less than `∥x⁻¹∥⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
@[simps coe]
def unit_of_nearby (x : Units R) (y : R) (h : ∥y - x∥ < ∥(«expr↑ » (x⁻¹) : R)∥⁻¹) : Units R :=
  Units.copy (x.add (y - x : R) h) y
    (by 
      simp )
    _ rfl

/-- The group of units of a complete normed ring is an open subset of the ring. -/
protected theorem IsOpen : IsOpen { x:R | IsUnit x } :=
  by 
    nontriviality R 
    apply metric.is_open_iff.mpr 
    rintro x' ⟨x, rfl⟩
    refine' ⟨∥(«expr↑ » (x⁻¹) : R)∥⁻¹, inv_pos.mpr (Units.norm_pos (x⁻¹)), _⟩
    intro y hy 
    rw [Metric.mem_ball, dist_eq_norm] at hy 
    exact (x.unit_of_nearby y hy).IsUnit

protected theorem nhds (x : Units R) : { x:R | IsUnit x } ∈ 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.is_open x.is_unit

end Units

namespace NormedRing

open_locale Classical BigOperators

open Asymptotics Filter Metric Finset Ringₓ

theorem inverse_one_sub (t : R) (h : ∥t∥ < 1) : inverse (1 - t) = «expr↑ » (Units.oneSub t h⁻¹) :=
  by 
    rw [←inverse_unit (Units.oneSub t h), Units.coe_one_sub]

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The formula `inverse (x + t) = inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently small. -/
theorem inverse_add
(x : units R) : «expr∀ᶠ in , »((t), expr𝓝() 0, «expr = »(inverse «expr + »((x : R), t), «expr * »(inverse «expr + »(1, «expr * »(«expr↑ »(«expr ⁻¹»(x)), t)), «expr↑ »(«expr ⁻¹»(x))))) :=
begin
  nontriviality [expr R] [],
  rw ["[", expr eventually_iff, ",", expr metric.mem_nhds_iff, "]"] [],
  have [ident hinv] [":", expr «expr < »(0, «expr ⁻¹»(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R))))] [],
  by cancel_denoms [],
  use ["[", expr «expr ⁻¹»(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R))), ",", expr hinv, "]"],
  intros [ident t, ident ht],
  simp [] [] ["only"] ["[", expr mem_ball, ",", expr dist_zero_right, "]"] [] ["at", ident ht],
  have [ident ht'] [":", expr «expr < »(«expr∥ ∥»(«expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t)), 1)] [],
  { refine [expr lt_of_le_of_lt (norm_mul_le _ _) _],
    rw [expr norm_neg] [],
    refine [expr lt_of_lt_of_le (mul_lt_mul_of_pos_left ht «expr ⁻¹»(x).norm_pos) _],
    cancel_denoms [] },
  have [ident hright] [] [":=", expr inverse_one_sub «expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t) ht'],
  have [ident hleft] [] [":=", expr inverse_unit (x.add t ht)],
  simp [] [] ["only"] ["[", "<-", expr neg_mul_eq_neg_mul, ",", expr sub_neg_eq_add, "]"] [] ["at", ident hright],
  simp [] [] ["only"] ["[", expr units.coe_add, "]"] [] ["at", ident hleft],
  simp [] [] [] ["[", expr hleft, ",", expr hright, ",", expr units.add, "]"] [] []
end

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inverse_one_sub_nth_order
(n : exprℕ()) : «expr∀ᶠ in , »((t), expr𝓝() 0, «expr = »(inverse «expr - »((1 : R), t), «expr + »(«expr∑ in , »((i), range n, «expr ^ »(t, i)), «expr * »(«expr ^ »(t, n), inverse «expr - »(1, t))))) :=
begin
  simp [] [] ["only"] ["[", expr eventually_iff, ",", expr metric.mem_nhds_iff, "]"] [] [],
  use ["[", expr 1, ",", expr by norm_num [] [], "]"],
  intros [ident t, ident ht],
  simp [] [] ["only"] ["[", expr mem_ball, ",", expr dist_zero_right, "]"] [] ["at", ident ht],
  simp [] [] ["only"] ["[", expr inverse_one_sub t ht, ",", expr set.mem_set_of_eq, "]"] [] [],
  have [ident h] [":", expr «expr = »(1, «expr + »(«expr * »((range n).sum (λ
       i, «expr ^ »(t, i)), units.one_sub t ht), «expr ^ »(t, n)))] [],
  { simp [] [] ["only"] ["[", expr units.coe_one_sub, "]"] [] [],
    rw ["[", "<-", expr geom_sum, ",", expr geom_sum_mul_neg, "]"] [],
    simp [] [] [] [] [] [] },
  rw ["[", "<-", expr one_mul «expr↑ »(«expr ⁻¹»(units.one_sub t ht)), ",", expr h, ",", expr add_mul, "]"] [],
  congr,
  { rw ["[", expr mul_assoc, ",", expr (units.one_sub t ht).mul_inv, "]"] [],
    simp [] [] [] [] [] [] },
  { simp [] [] ["only"] ["[", expr units.coe_one_sub, "]"] [] [],
    rw ["[", "<-", expr add_mul, ",", "<-", expr geom_sum, ",", expr geom_sum_mul_neg, "]"] [],
    simp [] [] [] [] [] [] }
end

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The formula
`inverse (x + t) = (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * inverse (x + t)`
holds for `t` sufficiently small. -/
theorem inverse_add_nth_order
(x : units R)
(n : exprℕ()) : «expr∀ᶠ in , »((t), expr𝓝() 0, «expr = »(inverse «expr + »((x : R), t), «expr + »(«expr * »(«expr∑ in , »((i), range n, «expr ^ »(«expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t), i)), «expr↑ »(«expr ⁻¹»(x))), «expr * »(«expr ^ »(«expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t), n), inverse «expr + »(x, t))))) :=
begin
  refine [expr (inverse_add x).mp _],
  have [ident hzero] [":", expr tendsto (λ
    t : R, «expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t)) (expr𝓝() 0) (expr𝓝() 0)] [],
  { convert [] [expr ((mul_left_continuous «expr- »((«expr↑ »(«expr ⁻¹»(x)) : R))).tendsto 0).comp tendsto_id] [],
    simp [] [] [] [] [] [] },
  refine [expr (hzero.eventually (inverse_one_sub_nth_order n)).mp (eventually_of_forall _)],
  simp [] [] ["only"] ["[", expr neg_mul_eq_neg_mul_symm, ",", expr sub_neg_eq_add, "]"] [] [],
  intros [ident t, ident h1, ident h2],
  have [ident h] [] [":=", expr congr_arg (λ a : R, «expr * »(a, «expr↑ »(«expr ⁻¹»(x)))) h1],
  dsimp [] [] [] ["at", ident h],
  convert [] [expr h] [],
  rw ["[", expr add_mul, ",", expr mul_assoc, "]"] [],
  simp [] [] [] ["[", expr h2.symm, "]"] [] []
end

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inverse_one_sub_norm : is_O (λ t, inverse «expr - »((1 : R), t)) (λ t, (1 : exprℝ())) (expr𝓝() (0 : R)) :=
begin
  simp [] [] ["only"] ["[", expr is_O, ",", expr is_O_with, ",", expr eventually_iff, ",", expr metric.mem_nhds_iff, "]"] [] [],
  refine [expr ⟨«expr + »(«expr∥ ∥»((1 : R)), 1), «expr ⁻¹»((2 : exprℝ())), by norm_num [] [], _⟩],
  intros [ident t, ident ht],
  simp [] [] ["only"] ["[", expr ball, ",", expr dist_zero_right, ",", expr set.mem_set_of_eq, "]"] [] ["at", ident ht],
  have [ident ht'] [":", expr «expr < »(«expr∥ ∥»(t), 1)] [],
  { have [] [":", expr «expr < »(«expr ⁻¹»((2 : exprℝ())), 1)] [":=", expr by cancel_denoms []],
    linarith [] [] [] },
  simp [] [] ["only"] ["[", expr inverse_one_sub t ht', ",", expr norm_one, ",", expr mul_one, ",", expr set.mem_set_of_eq, "]"] [] [],
  change [expr «expr ≤ »(«expr∥ ∥»(«expr∑' , »((n : exprℕ()), «expr ^ »(t, n))), _)] [] [],
  have [] [] [":=", expr normed_ring.tsum_geometric_of_norm_lt_1 t ht'],
  have [] [":", expr «expr ≤ »(«expr ⁻¹»(«expr - »(1, «expr∥ ∥»(t))), 2)] [],
  { rw ["<-", expr inv_inv₀ (2 : exprℝ())] [],
    refine [expr inv_le_inv_of_le (by norm_num [] []) _],
    have [] [":", expr «expr = »(«expr + »(«expr ⁻¹»((2 : exprℝ())), «expr ⁻¹»((2 : exprℝ()))), 1)] [":=", expr by ring []],
    linarith [] [] [] },
  linarith [] [] []
end

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function `λ t, inverse (x + t)` is O(1) as `t → 0`. -/
theorem inverse_add_norm
(x : units R) : is_O (λ t, inverse «expr + »(«expr↑ »(x), t)) (λ t, (1 : exprℝ())) (expr𝓝() (0 : R)) :=
begin
  nontriviality [expr R] [],
  simp [] [] ["only"] ["[", expr is_O_iff, ",", expr norm_one, ",", expr mul_one, "]"] [] [],
  cases [expr is_O_iff.mp (@inverse_one_sub_norm R _ _)] ["with", ident C, ident hC],
  use [expr «expr * »(C, «expr∥ ∥»(((«expr ⁻¹»(x) : units R) : R)))],
  have [ident hzero] [":", expr tendsto (λ
    t, «expr * »(«expr- »((«expr↑ »(«expr ⁻¹»(x)) : R)), t)) (expr𝓝() 0) (expr𝓝() 0)] [],
  { convert [] [expr ((mul_left_continuous («expr- »(«expr↑ »(«expr ⁻¹»(x))) : R)).tendsto 0).comp tendsto_id] [],
    simp [] [] [] [] [] [] },
  refine [expr (inverse_add x).mp ((hzero.eventually hC).mp (eventually_of_forall _))],
  intros [ident t, ident bound, ident iden],
  rw [expr iden] [],
  simp [] [] [] [] [] ["at", ident bound],
  have [ident hmul] [] [":=", expr norm_mul_le (inverse «expr + »(1, «expr * »(«expr↑ »(«expr ⁻¹»(x)), t))) «expr↑ »(«expr ⁻¹»(x))],
  nlinarith [] [] ["[", expr norm_nonneg («expr↑ »(«expr ⁻¹»(x)) : R), "]"]
end

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function
`λ t, inverse (x + t) - (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
theorem inverse_add_norm_diff_nth_order
(x : units R)
(n : exprℕ()) : is_O (λ
 t : R, «expr - »(inverse «expr + »(«expr↑ »(x), t), «expr * »(«expr∑ in , »((i), range n, «expr ^ »(«expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t), i)), «expr↑ »(«expr ⁻¹»(x))))) (λ
 t, «expr ^ »(«expr∥ ∥»(t), n)) (expr𝓝() (0 : R)) :=
begin
  by_cases [expr h, ":", expr «expr = »(n, 0)],
  { simpa [] [] [] ["[", expr h, "]"] [] ["using", expr inverse_add_norm x] },
  have [ident hn] [":", expr «expr < »(0, n)] [":=", expr nat.pos_of_ne_zero h],
  simp [] [] [] ["[", expr is_O_iff, "]"] [] [],
  cases [expr is_O_iff.mp (inverse_add_norm x)] ["with", ident C, ident hC],
  use [expr «expr * »(«expr * »(C, «expr∥ ∥»((1 : exprℝ()))), «expr ^ »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), n))],
  have [ident h] [":", expr eventually_eq (expr𝓝() (0 : R)) (λ
    t, «expr - »(inverse «expr + »(«expr↑ »(x), t), «expr * »(«expr∑ in , »((i), range n, «expr ^ »(«expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t), i)), «expr↑ »(«expr ⁻¹»(x))))) (λ
    t, «expr * »(«expr ^ »(«expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t), n), inverse «expr + »(x, t)))] [],
  { refine [expr (inverse_add_nth_order x n).mp (eventually_of_forall _)],
    intros [ident t, ident ht],
    convert [] [expr congr_arg (λ
      a, «expr - »(a, «expr * »((range n).sum (pow «expr * »(«expr- »(«expr↑ »(«expr ⁻¹»(x))), t)), «expr↑ »(«expr ⁻¹»(x))))) ht] [],
    simp [] [] [] [] [] [] },
  refine [expr h.mp (hC.mp (eventually_of_forall _))],
  intros [ident t, "_", ident hLHS],
  simp [] [] ["only"] ["[", expr neg_mul_eq_neg_mul_symm, "]"] [] ["at", ident hLHS],
  rw [expr hLHS] [],
  refine [expr le_trans (norm_mul_le _ _) _],
  have [ident h'] [":", expr «expr ≤ »(«expr∥ ∥»(«expr ^ »(«expr- »(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t)), n)), «expr * »(«expr ^ »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), n), «expr ^ »(«expr∥ ∥»(t), n)))] [],
  { calc
      «expr ≤ »(«expr∥ ∥»(«expr ^ »(«expr- »(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t)), n)), «expr ^ »(«expr∥ ∥»(«expr- »(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t))), n)) : norm_pow_le' _ hn
      «expr = »(..., «expr ^ »(«expr∥ ∥»(«expr * »(«expr↑ »(«expr ⁻¹»(x)), t)), n)) : by rw [expr norm_neg] []
      «expr ≤ »(..., «expr ^ »(«expr * »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), «expr∥ ∥»(t)), n)) : _
      «expr = »(..., «expr * »(«expr ^ »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), n), «expr ^ »(«expr∥ ∥»(t), n))) : mul_pow _ _ n,
    exact [expr pow_le_pow_of_le_left (norm_nonneg _) (norm_mul_le «expr↑ »(«expr ⁻¹»(x)) t) n] },
  have [ident h''] [":", expr «expr ≤ »(0, «expr * »(«expr ^ »(«expr∥ ∥»((«expr↑ »(«expr ⁻¹»(x)) : R)), n), «expr ^ »(«expr∥ ∥»(t), n)))] [],
  { refine [expr mul_nonneg _ _]; exact [expr pow_nonneg (norm_nonneg _) n] },
  nlinarith [] [] ["[", expr norm_nonneg (inverse «expr + »(«expr↑ »(x), t)), "]"]
end

/-- The function `λ t, inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
theorem inverse_add_norm_diff_first_order (x : Units R) :
  is_O (fun t => inverse («expr↑ » x+t) - «expr↑ » (x⁻¹)) (fun t => ∥t∥) (𝓝 (0 : R)) :=
  by 
    convert inverse_add_norm_diff_nth_order x 1 <;> simp 

/-- The function
`λ t, inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹`
is `O(t ^ 2)` as `t → 0`. -/
theorem inverse_add_norm_diff_second_order (x : Units R) :
  is_O (fun t => (inverse («expr↑ » x+t) - «expr↑ » (x⁻¹))+(«expr↑ » (x⁻¹)*t)*«expr↑ » (x⁻¹)) (fun t => ∥t∥ ^ 2)
    (𝓝 (0 : R)) :=
  by 
    convert inverse_add_norm_diff_nth_order x 2 
    ext t 
    simp only [range_succ, range_one, sum_insert, mem_singleton, sum_singleton, not_false_iff, one_ne_zero, pow_zeroₓ,
      add_mulₓ, pow_oneₓ, one_mulₓ, neg_mul_eq_neg_mul_symm, sub_add_eq_sub_sub_swap, sub_neg_eq_add]

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function `inverse` is continuous at each unit of `R`. -/
theorem inverse_continuous_at (x : units R) : continuous_at inverse (x : R) :=
begin
  have [ident h_is_o] [":", expr is_o (λ
    t : R, «expr∥ ∥»(«expr - »(inverse «expr + »(«expr↑ »(x), t), «expr↑ »(«expr ⁻¹»(x))))) (λ
    t : R, (1 : exprℝ())) (expr𝓝() 0)] [],
  { refine [expr is_o_norm_left.mpr ((inverse_add_norm_diff_first_order x).trans_is_o _)],
    exact [expr is_o_norm_left.mpr (is_o_id_const one_ne_zero)] },
  have [ident h_lim] [":", expr tendsto (λ y : R, «expr - »(y, x)) (expr𝓝() x) (expr𝓝() 0)] [],
  { refine [expr tendsto_zero_iff_norm_tendsto_zero.mpr _],
    exact [expr tendsto_iff_norm_tendsto_zero.mp tendsto_id] },
  simp [] [] ["only"] ["[", expr continuous_at, "]"] [] [],
  rw ["[", expr tendsto_iff_norm_tendsto_zero, ",", expr inverse_unit, "]"] [],
  convert [] [expr h_is_o.tendsto_0.comp h_lim] [],
  ext [] [] [],
  simp [] [] [] [] [] []
end

end NormedRing

namespace Units

open MulOpposite Filter NormedRing

-- error in Analysis.NormedSpace.Units: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a normed ring, the coercion from `units R` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open map. -/ theorem is_open_map_coe : is_open_map (coe : units R → R) :=
begin
  rw [expr is_open_map_iff_nhds_le] [],
  intros [ident x, ident s],
  rw ["[", expr mem_map, ",", expr mem_nhds_induced, "]"] [],
  rintros ["⟨", ident t, ",", ident ht, ",", ident hts, "⟩"],
  obtain ["⟨", ident u, ",", ident hu, ",", ident v, ",", ident hv, ",", ident huvt, "⟩", ":", expr «expr∃ , »((u : set R), «expr ∧ »(«expr ∈ »(u, expr𝓝() «expr↑ »(x)), «expr∃ , »((v : set «expr ᵐᵒᵖ»(R)), «expr ∧ »(«expr ∈ »(v, expr𝓝() (op «expr↑ »(«expr ⁻¹»(x)))), «expr ⊆ »(u.prod v, t)))))],
  { simpa [] [] [] ["[", expr embed_product, ",", expr mem_nhds_prod_iff, "]"] [] ["using", expr ht] },
  have [] [":", expr «expr ∈ »(«expr ∩ »(«expr ∩ »(u, «expr ⁻¹' »(«expr ∘ »(op, ring.inverse), v)), set.range (coe : units R → R)), expr𝓝() «expr↑ »(x))] [],
  { refine [expr inter_mem (inter_mem hu _) (units.nhds x)],
    refine [expr (continuous_op.continuous_at.comp (inverse_continuous_at x)).preimage_mem_nhds _],
    simpa [] [] [] [] [] ["using", expr hv] },
  refine [expr mem_of_superset this _],
  rintros ["_", "⟨", "⟨", ident huy, ",", ident hvy, "⟩", ",", "⟨", ident y, ",", ident rfl, "⟩", "⟩"],
  have [] [":", expr «expr ∈ »(embed_product R y, u.prod v)] [":=", expr ⟨huy, by simpa [] [] [] [] [] ["using", expr hvy]⟩],
  simpa [] [] [] [] [] ["using", expr hts (huvt this)]
end

/-- In a normed ring, the coercion from `units R` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open embedding. -/
theorem open_embedding_coe : OpenEmbedding (coeₓ : Units R → R) :=
  open_embedding_of_continuous_injective_open continuous_coe ext is_open_map_coe

end Units

