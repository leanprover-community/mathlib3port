import Mathbin.Data.W.Cardinal 
import Mathbin.Data.MvPolynomial.Basic

/-!
# Cardinality of Polynomial Ring

The main result in this file is `mv_polynomial.cardinal_mk_le_max`, which says that
the cardinality of `mv_polynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ω`.

-/


universe u

open Cardinal

open_locale Cardinal

/-- A type used to prove theorems about the cardinality of `mv_polynomial σ R`. The
`W_type (arity σ R)` has a constant for every element of `R` and `σ` and two binary functions. -/
private def mv_polynomial_fun (σ R : Type u) : Type u :=
  Sum R (Sum σ (Ulift.{u} Bool))

variable (σ R : Type u)

/-- A function used to prove theorems about the cardinality of `mv_polynomial σ R`.
  The type ``W_type (arity σ R)` has a constant for every element of `R` and `σ` and two binary
  functions. -/
private def arity : mv_polynomial_fun σ R → Type u
| Sum.inl _ => Pempty
| Sum.inr (Sum.inl _) => Pempty
| Sum.inr (Sum.inr ⟨ff⟩) => Ulift Bool
| Sum.inr (Sum.inr ⟨tt⟩) => Ulift Bool

private def arity_fintype (x : mv_polynomial_fun σ R) : Fintype (arity σ R x) :=
  by 
    rcases x with (x | x | ⟨_ | _⟩) <;> dsimp [arity] <;> infer_instance

attribute [local instance] arity_fintype

variable {σ R}

variable [CommSemiringₓ R]

/-- The surjection from `W_type (arity σ R)` into `mv_polynomial σ R`. -/
private noncomputable def to_mv_polynomial : WType (arity σ R) → MvPolynomial σ R
| ⟨Sum.inl r, _⟩ => MvPolynomial.c r
| ⟨Sum.inr (Sum.inl i), _⟩ => MvPolynomial.x i
| ⟨Sum.inr (Sum.inr ⟨ff⟩), f⟩ => to_mv_polynomial (f (Ulift.up tt))*to_mv_polynomial (f (Ulift.up ff))
| ⟨Sum.inr (Sum.inr ⟨tt⟩), f⟩ => to_mv_polynomial (f (Ulift.up tt))+to_mv_polynomial (f (Ulift.up ff))

private theorem to_mv_polynomial_surjective : Function.Surjective (@to_mv_polynomial σ R _) :=
  by 
    intro p 
    induction' p using MvPolynomial.induction_on with x p₁ p₂ ih₁ ih₂ p i ih
    ·
      exact ⟨WType.mk (Sum.inl x) Pempty.elimₓ, rfl⟩
    ·
      rcases ih₁ with ⟨w₁, rfl⟩
      rcases ih₂ with ⟨w₂, rfl⟩
      exact
        ⟨WType.mk (Sum.inr (Sum.inr ⟨tt⟩)) fun x => cond x.down w₁ w₂,
          by 
            simp [to_mv_polynomial]⟩
    ·
      rcases ih with ⟨w, rfl⟩
      exact
        ⟨WType.mk (Sum.inr (Sum.inr ⟨ff⟩)) fun x => cond x.down w (WType.mk (Sum.inr (Sum.inl i)) Pempty.elimₓ),
          by 
            simp [to_mv_polynomial]⟩

-- error in Data.MvPolynomial.Cardinal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem cardinal_mv_polynomial_fun_le : «expr ≤ »(«expr#»() (mv_polynomial_fun σ R), max (max («expr#»() R) («expr#»() σ)) exprω()) :=
calc
  «expr = »(«expr#»() (mv_polynomial_fun σ R), «expr + »(«expr + »(«expr#»() R, «expr#»() σ), «expr#»() (ulift bool))) : by dsimp [] ["[", expr mv_polynomial_fun, "]"] [] []; simp [] [] ["only"] ["[", "<-", expr add_def, ",", expr add_assoc, ",", expr cardinal.mk_ulift, "]"] [] []
  «expr ≤ »(..., max (max «expr + »(«expr#»() R, «expr#»() σ) («expr#»() (ulift bool))) exprω()) : add_le_max _ _
  «expr ≤ »(..., max (max (max (max («expr#»() R) («expr#»() σ)) exprω()) («expr#»() (ulift bool))) exprω()) : max_le_max (max_le_max (add_le_max _ _) (le_refl _)) (le_refl _)
  «expr ≤ »(..., _) : begin
    have [] [":", expr «expr ≤ »(«expr#»() (ulift.{u} bool), exprω())] [],
    from [expr le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩)],
    simp [] [] ["only"] ["[", expr max_comm omega.{u}, ",", expr max_assoc, ",", expr max_left_comm omega.{u}, ",", expr max_self, ",", expr max_eq_left this, "]"] [] []
  end

namespace MvPolynomial

/-- The cardinality of the multivariate polynomial ring, `mv_polynomial σ R` is at most the maximum
of `#R`, `#σ` and `ω` -/
theorem cardinal_mk_le_max {σ R : Type u} [CommSemiringₓ R] : # (MvPolynomial σ R) ≤ max (max (# R) (# σ)) ω :=
  calc # (MvPolynomial σ R) ≤ # (WType (arity σ R)) := Cardinal.mk_le_of_surjective to_mv_polynomial_surjective 
    _ ≤ max (# (mv_polynomial_fun σ R)) ω := WType.cardinal_mk_le_max_omega_of_fintype 
    _ ≤ _ := max_le_max cardinal_mv_polynomial_fun_le (le_reflₓ _)
    _ ≤ _ :=
    by 
      simp only [max_assocₓ, max_selfₓ]
    

end MvPolynomial

