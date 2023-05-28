/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.mv_polynomial.polynomial
! leanprover-community/mathlib commit ef55335933293309ff8c0b1d20ffffeecbe5c39f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Equiv
import Mathbin.Data.Polynomial.Eval

/-!
# Some lemmas relating polynomials and multivariable polynomials.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace MvPolynomial

variable {R S : Type _} [CommSemiring R] [CommSemiring S] {σ : Type _}

/- warning: mv_polynomial.polynomial_eval_eval₂ -> MvPolynomial.polynomial_eval_eval₂ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommSemiring.{u2} S] {σ : Type.{u3}} (f : RingHom.{u1, u2} R (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Polynomial.semiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (g : σ -> (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (p : MvPolynomial.{u3, u1} σ R _inst_1) (x : S), Eq.{succ u2} S (Polynomial.eval.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2) x (MvPolynomial.eval₂.{u1, u2, u3} R (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) σ _inst_1 (Polynomial.commSemiring.{u2} S _inst_2) f g p)) (MvPolynomial.eval₂.{u1, u2, u3} R S σ _inst_1 _inst_2 (RingHom.comp.{u1, u2, u2} R (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Polynomial.semiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Polynomial.evalRingHom.{u2} S _inst_2 x) f) (fun (s : σ) => Polynomial.eval.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2) x (g s)) p)
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} {_inst_1 : Type.{u1}} {_inst_2 : S} [σ : CommSemiring.{u3} R] [f : CommSemiring.{u2} S] (g : RingHom.{u3, u2} R (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S f)) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R σ)) (Semiring.toNonAssocSemiring.{u2} (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S f)) (Polynomial.semiring.{u2} S (CommSemiring.toSemiring.{u2} S f)))) (p : _inst_1 -> (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S f))) (x : MvPolynomial.{u1, u3} _inst_1 R σ), Eq.{succ u2} S (Polynomial.eval.{u2} S (CommSemiring.toSemiring.{u2} S f) _inst_2 (MvPolynomial.eval₂.{u3, u2, u1} R (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S f)) _inst_1 σ (Polynomial.commSemiring.{u2} S f) g p x)) (MvPolynomial.eval₂.{u3, u2, u1} R S _inst_1 σ f (RingHom.comp.{u3, u2, u2} R (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S f)) S (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R σ)) (Semiring.toNonAssocSemiring.{u2} (Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S f)) (Polynomial.semiring.{u2} S (CommSemiring.toSemiring.{u2} S f))) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S f)) (Polynomial.evalRingHom.{u2} S f _inst_2) g) (fun (s : _inst_1) => Polynomial.eval.{u2} S (CommSemiring.toSemiring.{u2} S f) _inst_2 (p s)) x)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.polynomial_eval_eval₂ MvPolynomial.polynomial_eval_eval₂ₓ'. -/
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

/- warning: mv_polynomial.eval_polynomial_eval_fin_succ_equiv -> MvPolynomial.eval_polynomial_eval_finSuccEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval_polynomial_eval_fin_succ_equiv MvPolynomial.eval_polynomial_eval_finSuccEquivₓ'. -/
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

end MvPolynomial

