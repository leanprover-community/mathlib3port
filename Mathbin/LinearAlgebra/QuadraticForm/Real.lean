import Mathbin.LinearAlgebra.QuadraticForm.Basic 
import Mathbin.Analysis.SpecialFunctions.Pow 
import Mathbin.Data.Real.Sign

/-!
# Real quadratic forms

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegerate we can take the weights to be ±1,
as in `equivalent_one_zero_neg_one_weighted_sum_squared`.

-/


namespace QuadraticForm

open_locale BigOperators

open Real Finset

variable{ι : Type _}[Fintype ι]

-- error in LinearAlgebra.QuadraticForm.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable
def isometry_sign_weighted_sum_squares
[decidable_eq ι]
(w : ι → exprℝ()) : isometry (weighted_sum_squares exprℝ() w) (weighted_sum_squares exprℝ() «expr ∘ »(sign, w)) :=
begin
  let [ident u] [] [":=", expr λ i, if h : «expr = »(w i, 0) then (1 : units exprℝ()) else units.mk0 (w i) h],
  have [ident hu'] [":", expr ∀
   i : ι, «expr ≠ »(«expr ^ »(«expr * »(sign (u i), u i), «expr- »((«expr / »(1, 2) : exprℝ()))), 0)] [],
  { intro [ident i],
    refine [expr (ne_of_lt (real.rpow_pos_of_pos «expr $ »(sign_mul_pos_of_ne_zero _, units.ne_zero _) _)).symm] },
  convert [] [expr (weighted_sum_squares exprℝ() w).isometry_basis_repr ((pi.basis_fun exprℝ() ι).units_smul (λ
     i, «expr $ »(is_unit_iff_ne_zero.2, hu' i).unit))] [],
  ext1 [] [ident v],
  rw ["[", expr basis_repr_apply, ",", expr weighted_sum_squares_apply, ",", expr weighted_sum_squares_apply, "]"] [],
  refine [expr sum_congr rfl (λ j hj, _)],
  have [ident hsum] [":", expr «expr = »(«expr∑ , »((i : ι), «expr • »(v i, «expr • »((«expr $ »(is_unit_iff_ne_zero.2, hu' i).unit : exprℝ()), pi.basis_fun exprℝ() ι i))) j, «expr • »(v j, «expr ^ »(«expr * »(sign (u j), u j), «expr- »((«expr / »(1, 2) : exprℝ())))))] [],
  { rw ["[", expr finset.sum_apply, ",", expr sum_eq_single j, ",", expr pi.basis_fun_apply, ",", expr is_unit.unit_spec, ",", expr linear_map.std_basis_apply, ",", expr pi.smul_apply, ",", expr pi.smul_apply, ",", expr function.update_same, ",", expr smul_eq_mul, ",", expr smul_eq_mul, ",", expr smul_eq_mul, ",", expr mul_one, "]"] [],
    intros [ident i, "_", ident hij],
    rw ["[", expr pi.basis_fun_apply, ",", expr linear_map.std_basis_apply, ",", expr pi.smul_apply, ",", expr pi.smul_apply, ",", expr function.update_noteq hij.symm, ",", expr pi.zero_apply, ",", expr smul_eq_mul, ",", expr smul_eq_mul, ",", expr mul_zero, ",", expr mul_zero, "]"] [],
    intro [ident hj'],
    exact [expr false.elim (hj' hj)] },
  simp_rw [expr basis.units_smul_apply] [],
  erw ["[", expr hsum, "]"] [],
  simp [] [] ["only"] ["[", expr u, ",", expr function.comp, ",", expr smul_eq_mul, "]"] [] [],
  split_ifs [] [],
  { simp [] [] ["only"] ["[", expr h, ",", expr zero_smul, ",", expr zero_mul, ",", expr sign_zero, "]"] [] [] },
  have [ident hwu] [":", expr «expr = »(w j, u j)] [],
  { simp [] [] ["only"] ["[", expr u, ",", expr dif_neg h, ",", expr units.coe_mk0, "]"] [] [] },
  simp [] [] ["only"] ["[", expr hwu, ",", expr units.coe_mk0, "]"] [] [],
  suffices [] [":", expr «expr = »(«expr * »(«expr * »((u j : exprℝ()).sign, v j), v j), «expr * »(«expr * »(«expr * »(«expr * »(«expr ^ »(«expr * »(sign (u j), u j), «expr- »((«expr / »(1, 2) : exprℝ()))), «expr ^ »(«expr * »(sign (u j), u j), «expr- »((«expr / »(1, 2) : exprℝ())))), u j), v j), v j))],
  { erw ["[", "<-", expr mul_assoc, ",", expr this, "]"] [],
    ring [] },
  rw ["[", "<-", expr real.rpow_add «expr $ »(sign_mul_pos_of_ne_zero _, units.ne_zero _), ",", expr show «expr = »(«expr + »(«expr- »((«expr / »(1, 2) : exprℝ())), «expr- »(«expr / »(1, 2))), «expr- »(1)), by ring [], ",", expr real.rpow_neg_one, ",", expr mul_inv₀, ",", expr inv_sign, ",", expr mul_assoc (sign (u j)) «expr ⁻¹»(u j), ",", expr inv_mul_cancel (units.ne_zero _), ",", expr mul_one, "]"] [],
  apply_instance
end

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared {M : Type _} [AddCommGroupₓ M] [Module ℝ M] [FiniteDimensional ℝ M]
  (Q : QuadraticForm ℝ M) (hQ : (Associated Q).Nondegenerate) :
  ∃ w : Finₓ (FiniteDimensional.finrank ℝ M) → ℝ, (∀ i, w i = -1 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ
  ⟨sign ∘ coeₓ ∘ w, fun i => sign_apply_eq_of_ne_zero (w i) (w i).ne_zero,
    ⟨hw₁.trans (isometry_sign_weighted_sum_squares (coeₓ ∘ w))⟩⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type _} [AddCommGroupₓ M] [Module ℝ M]
  [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
  ∃ w : Finₓ (FiniteDimensional.finrank ℝ M) → ℝ,
    (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares
  ⟨sign ∘ coeₓ ∘ w, fun i => sign_apply_eq (w i), ⟨hw₁.trans (isometry_sign_weighted_sum_squares w)⟩⟩

end QuadraticForm

