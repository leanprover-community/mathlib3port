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

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weights 1 or 0. -/
noncomputable def isometry_sum_squares [DecidableEq ι] (w' : ι → ℂ) :
  Isometry (weighted_sum_squares ℂ w') (weighted_sum_squares ℂ (fun i => if w' i = 0 then 0 else 1 : ι → ℂ)) :=
  by 
    let w := fun i => if h : w' i = 0 then (1 : Units ℂ) else Units.mk0 (w' i) h 
    have hw' : ∀ i : ι, ((w i : ℂ)^-(1 / 2 : ℂ)) ≠ 0
    ·
      intro i hi 
      exact (w i).ne_zero ((Complex.cpow_eq_zero_iff _ _).1 hi).1
    convert
      (weighted_sum_squares ℂ w').isometryBasisRepr
        ((Pi.basisFun ℂ ι).units_smul fun i => (is_unit_iff_ne_zero.2$ hw' i).Unit)
    ext1 v 
    erw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply]
    refine' sum_congr rfl fun j hj => _ 
    have hsum :
      (∑i : ι, v i • ((is_unit_iff_ne_zero.2$ hw' i).Unit : ℂ) • (Pi.basisFun ℂ ι) i) j = v j • (w j^-(1 / 2 : ℂ))
    ·
      rw [Finset.sum_apply, sum_eq_single j, Pi.basis_fun_apply, IsUnit.unit_spec, LinearMap.std_basis_apply,
        Pi.smul_apply, Pi.smul_apply, Function.update_same, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_oneₓ]
      intro i _ hij 
      rw [Pi.basis_fun_apply, LinearMap.std_basis_apply, Pi.smul_apply, Pi.smul_apply, Function.update_noteq hij.symm,
        Pi.zero_apply, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero]
      intro hj' 
      exact False.elim (hj' hj)
    simpRw [Basis.units_smul_apply]
    erw [hsum, smul_eq_mul]
    splitIfs
    ·
      simp only [h, zero_smul, zero_mul]
    have hww' : w' j = w j
    ·
      simp only [w, dif_neg h, Units.coe_mk0]
    simp only [hww', one_mulₓ]
    change (v j*v j) = «expr↑ » (w j)*(v j*«expr↑ » (w j)^-(1 / 2 : ℂ))*v j*«expr↑ » (w j)^-(1 / 2 : ℂ)
    suffices  : (v j*v j) = ((((w j^-(1 / 2 : ℂ))*w j^-(1 / 2 : ℂ))*w j)*v j)*v j
    ·
      rw [this]
      ring 
    rw [←Complex.cpow_add _ _ (w j).ne_zero,
      show ((-(1 / 2 : ℂ))+-(1 / 2)) = -1by 
        ring,
      Complex.cpow_neg_one, inv_mul_cancel (w j).ne_zero, one_mulₓ]

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable def isometry_sum_squares_units [DecidableEq ι] (w : ι → Units ℂ) :
  Isometry (weighted_sum_squares ℂ w) (weighted_sum_squares ℂ (1 : ι → ℂ)) :=
  by 
    have hw1 : (fun i => if (w i : ℂ) = 0 then 0 else 1 : ι → ℂ) = 1
    ·
      ext i : 1 
      exact dif_neg (w i).ne_zero 
    have  := isometry_sum_squares (coeₓ ∘ w)
    rw [hw1] at this 
    exact this

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squares {M : Type _} [AddCommGroupₓ M] [Module ℂ M] [FiniteDimensional ℂ M]
  (Q : QuadraticForm ℂ M) (hQ : (Associated Q).Nondegenerate) :
  equivalent Q (weighted_sum_squares ℂ (1 : Finₓ (FiniteDimensional.finrank ℂ M) → ℂ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometry_sum_squares_units w)⟩

end QuadraticForm

