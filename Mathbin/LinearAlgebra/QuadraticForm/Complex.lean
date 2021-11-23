import Mathbin.LinearAlgebra.QuadraticForm.Basic 
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Quadratic forms over the complex numbers

`equivalent_sum_squares`: A nondegenerate quadratic form over the complex numbers is equivalent to
a sum of squares.

-/


namespace QuadraticForm

open_locale BigOperators

open Finset

variable{ι : Type _}[Fintype ι]

-- error in LinearAlgebra.QuadraticForm.Complex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weights 1 or 0. -/
noncomputable
def isometry_sum_squares
[decidable_eq ι]
(w' : ι → exprℂ()) : isometry (weighted_sum_squares exprℂ() w') (weighted_sum_squares exprℂ() (λ
 i, if «expr = »(w' i, 0) then 0 else 1 : ι → exprℂ())) :=
begin
  let [ident w] [] [":=", expr λ i, if h : «expr = »(w' i, 0) then (1 : units exprℂ()) else units.mk0 (w' i) h],
  have [ident hw'] [":", expr ∀
   i : ι, «expr ≠ »(«expr ^ »((w i : exprℂ()), «expr- »((«expr / »(1, 2) : exprℂ()))), 0)] [],
  { intros [ident i, ident hi],
    exact [expr (w i).ne_zero ((complex.cpow_eq_zero_iff _ _).1 hi).1] },
  convert [] [expr (weighted_sum_squares exprℂ() w').isometry_basis_repr ((pi.basis_fun exprℂ() ι).units_smul (λ
     i, «expr $ »(is_unit_iff_ne_zero.2, hw' i).unit))] [],
  ext1 [] [ident v],
  erw ["[", expr basis_repr_apply, ",", expr weighted_sum_squares_apply, ",", expr weighted_sum_squares_apply, "]"] [],
  refine [expr sum_congr rfl (λ j hj, _)],
  have [ident hsum] [":", expr «expr = »(«expr∑ , »((i : ι), «expr • »(v i, «expr • »((«expr $ »(is_unit_iff_ne_zero.2, hw' i).unit : exprℂ()), pi.basis_fun exprℂ() ι i))) j, «expr • »(v j, «expr ^ »(w j, «expr- »((«expr / »(1, 2) : exprℂ())))))] [],
  { rw ["[", expr finset.sum_apply, ",", expr sum_eq_single j, ",", expr pi.basis_fun_apply, ",", expr is_unit.unit_spec, ",", expr linear_map.std_basis_apply, ",", expr pi.smul_apply, ",", expr pi.smul_apply, ",", expr function.update_same, ",", expr smul_eq_mul, ",", expr smul_eq_mul, ",", expr smul_eq_mul, ",", expr mul_one, "]"] [],
    intros [ident i, "_", ident hij],
    rw ["[", expr pi.basis_fun_apply, ",", expr linear_map.std_basis_apply, ",", expr pi.smul_apply, ",", expr pi.smul_apply, ",", expr function.update_noteq hij.symm, ",", expr pi.zero_apply, ",", expr smul_eq_mul, ",", expr smul_eq_mul, ",", expr mul_zero, ",", expr mul_zero, "]"] [],
    intro [ident hj'],
    exact [expr false.elim (hj' hj)] },
  simp_rw [expr basis.units_smul_apply] [],
  erw ["[", expr hsum, ",", expr smul_eq_mul, "]"] [],
  split_ifs [] [],
  { simp [] [] ["only"] ["[", expr h, ",", expr zero_smul, ",", expr zero_mul, "]"] [] [] },
  have [ident hww'] [":", expr «expr = »(w' j, w j)] [],
  { simp [] [] ["only"] ["[", expr w, ",", expr dif_neg h, ",", expr units.coe_mk0, "]"] [] [] },
  simp [] [] ["only"] ["[", expr hww', ",", expr one_mul, "]"] [] [],
  change [expr «expr = »(«expr * »(v j, v j), «expr * »(«expr↑ »(w j), «expr * »(«expr * »(v j, «expr ^ »(«expr↑ »(w j), «expr- »((«expr / »(1, 2) : exprℂ())))), «expr * »(v j, «expr ^ »(«expr↑ »(w j), «expr- »((«expr / »(1, 2) : exprℂ())))))))] [] [],
  suffices [] [":", expr «expr = »(«expr * »(v j, v j), «expr * »(«expr * »(«expr * »(«expr * »(«expr ^ »(w j, «expr- »((«expr / »(1, 2) : exprℂ()))), «expr ^ »(w j, «expr- »((«expr / »(1, 2) : exprℂ())))), w j), v j), v j))],
  { rw ["[", expr this, "]"] [],
    ring [] },
  rw ["[", "<-", expr complex.cpow_add _ _ (w j).ne_zero, ",", expr show «expr = »(«expr + »(«expr- »((«expr / »(1, 2) : exprℂ())), «expr- »(«expr / »(1, 2))), «expr- »(1)), by ring [], ",", expr complex.cpow_neg_one, ",", expr inv_mul_cancel (w j).ne_zero, ",", expr one_mul, "]"] []
end

-- error in LinearAlgebra.QuadraticForm.Complex: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable
def isometry_sum_squares_units
[decidable_eq ι]
(w : ι → units exprℂ()) : isometry (weighted_sum_squares exprℂ() w) (weighted_sum_squares exprℂ() (1 : ι → exprℂ())) :=
begin
  have [ident hw1] [":", expr «expr = »((λ i, if «expr = »((w i : exprℂ()), 0) then 0 else 1 : ι → exprℂ()), 1)] [],
  { ext [] [ident i] [":", 1],
    exact [expr dif_neg (w i).ne_zero] },
  have [] [] [":=", expr isometry_sum_squares «expr ∘ »(coe, w)],
  rw [expr hw1] ["at", ident this],
  exact [expr this]
end

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squares {M : Type _} [AddCommGroupₓ M] [Module ℂ M] [FiniteDimensional ℂ M]
  (Q : QuadraticForm ℂ M) (hQ : (Associated Q).Nondegenerate) :
  equivalent Q (weighted_sum_squares ℂ (1 : Finₓ (FiniteDimensional.finrank ℂ M) → ℂ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometry_sum_squares_units w)⟩

end QuadraticForm

