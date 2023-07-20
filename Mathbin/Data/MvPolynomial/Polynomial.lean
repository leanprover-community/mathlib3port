/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.MvPolynomial.Equiv
import Mathbin.Data.Polynomial.Eval

#align_import data.mv_polynomial.polynomial from "leanprover-community/mathlib"@"ef55335933293309ff8c0b1d20ffffeecbe5c39f"

/-!
# Some lemmas relating polynomials and multivariable polynomials.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace MvPolynomial

variable {R S : Type _} [CommSemiring R] [CommSemiring S] {σ : Type _}

#print MvPolynomial.polynomial_eval_eval₂ /-
theorem polynomial_eval_eval₂ (f : R →+* Polynomial S) (g : σ → Polynomial S) (p : MvPolynomial σ R)
    (x : S) :
    Polynomial.eval x (MvPolynomial.eval₂ f g p) =
      MvPolynomial.eval₂ ((Polynomial.evalRingHom x).comp f) (fun s => Polynomial.eval x (g s)) p :=
  by
  apply MvPolynomial.induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]
#align mv_polynomial.polynomial_eval_eval₂ MvPolynomial.polynomial_eval_eval₂
-/

#print MvPolynomial.eval_polynomial_eval_finSuccEquiv /-
theorem eval_polynomial_eval_finSuccEquiv {n : ℕ} (f : MvPolynomial (Fin (n + 1)) R)
    (q : MvPolynomial (Fin n) R) (x : Fin n → R) :
    (eval x) (Polynomial.eval q (finSuccEquiv R n f)) =
      eval (show Fin (n + 1) → R from @Fin.cases _ (fun _ => R) (eval x q) x) f :=
  by
  simp only [fin_succ_equiv_apply, coe_eval₂_hom, eval_eval₂, polynomial_eval_eval₂]
  have : (eval x).comp ((Polynomial.evalRingHom q).comp (polynomial.C.comp C)) = RingHom.id _ := by
    ext; simp
  simp only [this, eval₂_id]
  congr
  funext i
  refine' Fin.cases (by simp) (by simp) i
#align mv_polynomial.eval_polynomial_eval_fin_succ_equiv MvPolynomial.eval_polynomial_eval_finSuccEquiv
-/

end MvPolynomial

