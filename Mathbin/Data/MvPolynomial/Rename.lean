/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro

! This file was ported from Lean 3 source module data.mv_polynomial.rename
! leanprover-community/mathlib commit 2f5b500a507264de86d666a5f87ddb976e2d8de4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Basic

/-!
# Renaming variables of polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `mv_polynomial.rename`
* `mv_polynomial.rename_equiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/


noncomputable section

open BigOperators

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

variable {σ τ α R S : Type _} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

#print MvPolynomial.rename /-
/-- Rename all the variables in a multivariable polynomial. -/
def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)
#align mv_polynomial.rename MvPolynomial.rename
-/

/- warning: mv_polynomial.rename_C -> MvPolynomial.rename_C is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_C MvPolynomial.rename_Cₓ'. -/
@[simp]
theorem rename_C (f : σ → τ) (r : R) : rename f (C r) = C r :=
  eval₂_C _ _ _
#align mv_polynomial.rename_C MvPolynomial.rename_C

/- warning: mv_polynomial.rename_X -> MvPolynomial.rename_X is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_X MvPolynomial.rename_Xₓ'. -/
@[simp]
theorem rename_X (f : σ → τ) (i : σ) : rename f (X i : MvPolynomial σ R) = X (f i) :=
  eval₂_X _ _ _
#align mv_polynomial.rename_X MvPolynomial.rename_X

/- warning: mv_polynomial.map_rename -> MvPolynomial.map_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.map_rename MvPolynomial.map_renameₓ'. -/
theorem map_rename (f : R →+* S) (g : σ → τ) (p : MvPolynomial σ R) :
    map f (rename g p) = rename g (map f p) :=
  MvPolynomial.induction_on p (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, AlgHom.map_add, RingHom.map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, RingHom.map_mul, AlgHom.map_mul]
#align mv_polynomial.map_rename MvPolynomial.map_rename

/- warning: mv_polynomial.rename_rename -> MvPolynomial.rename_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_rename MvPolynomial.rename_renameₓ'. -/
@[simp]
theorem rename_rename (f : σ → τ) (g : τ → α) (p : MvPolynomial σ R) :
    rename g (rename f p) = rename (g ∘ f) p :=
  show rename g (eval₂ C (X ∘ f) p) = _
    by
    simp only [rename, aeval_eq_eval₂_hom]
    simp [eval₂_comp_left _ C (X ∘ f) p, (· ∘ ·), eval₂_C, eval_X]
    apply eval₂_hom_congr _ rfl rfl
    ext1; simp only [comp_app, RingHom.coe_comp, eval₂_hom_C]
#align mv_polynomial.rename_rename MvPolynomial.rename_rename

/- warning: mv_polynomial.rename_id -> MvPolynomial.rename_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_id MvPolynomial.rename_idₓ'. -/
@[simp]
theorem rename_id (p : MvPolynomial σ R) : rename id p = p :=
  eval₂_eta p
#align mv_polynomial.rename_id MvPolynomial.rename_id

/- warning: mv_polynomial.rename_monomial -> MvPolynomial.rename_monomial is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_monomial MvPolynomial.rename_monomialₓ'. -/
theorem rename_monomial (f : σ → τ) (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r :=
  by
  rw [rename, aeval_monomial, monomial_eq, Finsupp.prod_mapDomain_index]
  · rfl
  · exact fun n => pow_zero _
  · exact fun n i₁ i₂ => pow_add _ _ _
#align mv_polynomial.rename_monomial MvPolynomial.rename_monomial

/- warning: mv_polynomial.rename_eq -> MvPolynomial.rename_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_eq MvPolynomial.rename_eqₓ'. -/
theorem rename_eq (f : σ → τ) (p : MvPolynomial σ R) :
    rename f p = Finsupp.mapDomain (Finsupp.mapDomain f) p :=
  by
  simp only [rename, aeval_def, eval₂, Finsupp.mapDomain, algebra_map_eq, X_pow_eq_monomial, ←
    monomial_finsupp_sum_index]
  rfl
#align mv_polynomial.rename_eq MvPolynomial.rename_eq

/- warning: mv_polynomial.rename_injective -> MvPolynomial.rename_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_injective MvPolynomial.rename_injectiveₓ'. -/
theorem rename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  by
  have :
    (rename f : MvPolynomial σ R → MvPolynomial τ R) = Finsupp.mapDomain (Finsupp.mapDomain f) :=
    funext (rename_eq f)
  rw [this]
  exact Finsupp.mapDomain_injective (Finsupp.mapDomain_injective hf)
#align mv_polynomial.rename_injective MvPolynomial.rename_injective

section

variable {f : σ → τ} (hf : Function.Injective f)

open Classical

#print MvPolynomial.killCompl /-
/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
  `kill_compl hf` is the `alg_hom` from `R[τ]` to `R[σ]` that is left inverse to
  `rename f : R[σ] → R[τ]` and sends the variables in the complement of the range of `f` to `0`. -/
def killCompl : MvPolynomial τ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if h : i ∈ Set.range f then X <| (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0
#align mv_polynomial.kill_compl MvPolynomial.killCompl
-/

/- warning: mv_polynomial.kill_compl_comp_rename -> MvPolynomial.killCompl_comp_rename is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {τ : Type.{u2}} {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] {f : σ -> τ} (hf : Function.Injective.{succ u1, succ u2} σ τ f), Eq.{succ (max u1 u3)} (AlgHom.{u3, max u1 u3, max u1 u3} R (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.{u1, u3} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1))) (AlgHom.comp.{u3, max u1 u3, max u2 u3, max u1 u3} R (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.{u2, u3} τ R _inst_1) (MvPolynomial.{u1, u3} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u3} (MvPolynomial.{u2, u3} τ R _inst_1) (MvPolynomial.commSemiring.{u3, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.algebra.{u3, u3, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.killCompl.{u1, u2, u3} σ τ R _inst_1 f hf) (MvPolynomial.rename.{u1, u2, u3} σ τ R _inst_1 f)) (AlgHom.id.{u3, max u1 u3} R (MvPolynomial.{u1, u3} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)))
but is expected to have type
  forall {σ : Type.{u3}} {τ : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {f : σ -> τ} (hf : Function.Injective.{succ u3, succ u1} σ τ f), Eq.{max (succ u3) (succ u2)} (AlgHom.{u2, max u2 u3, max u3 u2} R (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.{u3, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u3} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)) (MvPolynomial.algebra.{u2, u2, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1))) (AlgHom.comp.{u2, max u2 u3, max u1 u2, max u3 u2} R (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.{u1, u2} τ R _inst_1) (MvPolynomial.{u3, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} τ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u3} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)) (MvPolynomial.algebra.{u2, u2, u1} R R τ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)) (MvPolynomial.algebra.{u2, u2, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)) (MvPolynomial.killCompl.{u3, u1, u2} σ τ R _inst_1 f hf) (MvPolynomial.rename.{u3, u1, u2} σ τ R _inst_1 f)) (AlgHom.id.{u2, max u3 u2} R (MvPolynomial.{u3, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u2} (MvPolynomial.{u3, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u3} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.kill_compl_comp_rename MvPolynomial.killCompl_comp_renameₓ'. -/
theorem killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _ :=
  algHom_ext fun i => by dsimp;
    rw [rename, kill_compl, aeval_X, aeval_X, dif_pos, Equiv.ofInjective_symm_apply]
#align mv_polynomial.kill_compl_comp_rename MvPolynomial.killCompl_comp_rename

/- warning: mv_polynomial.kill_compl_rename_app -> MvPolynomial.killCompl_rename_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.kill_compl_rename_app MvPolynomial.killCompl_rename_appₓ'. -/
@[simp]
theorem killCompl_rename_app (p : MvPolynomial σ R) : killCompl hf (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p
#align mv_polynomial.kill_compl_rename_app MvPolynomial.killCompl_rename_app

end

section

variable (R)

#print MvPolynomial.renameEquiv /-
/-- `mv_polynomial.rename e` is an equivalence when `e` is. -/
@[simps apply]
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id] }
#align mv_polynomial.rename_equiv MvPolynomial.renameEquiv
-/

/- warning: mv_polynomial.rename_equiv_refl -> MvPolynomial.renameEquiv_refl is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} (R : Type.{u2}) [_inst_1 : CommSemiring.{u2} R], Eq.{succ (max u1 u2)} (AlgEquiv.{u2, max u1 u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.{u1, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)) (MvPolynomial.algebra.{u2, u2, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1))) (MvPolynomial.renameEquiv.{u1, u1, u2} σ σ R _inst_1 (Equiv.refl.{succ u1} σ)) (AlgEquiv.refl.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)))
but is expected to have type
  forall {σ : Type.{u2}} (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R], Eq.{max (succ u2) (succ u1)} (AlgEquiv.{u1, max u1 u2, max u1 u2} R (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.{u2, u1} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1))) (MvPolynomial.renameEquiv.{u2, u2, u1} σ σ R _inst_1 (Equiv.refl.{succ u2} σ)) (AlgEquiv.refl.{u1, max u2 u1} R (MvPolynomial.{u2, u1} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_equiv_refl MvPolynomial.renameEquiv_reflₓ'. -/
@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext rename_id
#align mv_polynomial.rename_equiv_refl MvPolynomial.renameEquiv_refl

/- warning: mv_polynomial.rename_equiv_symm -> MvPolynomial.renameEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {τ : Type.{u2}} (R : Type.{u3}) [_inst_1 : CommSemiring.{u3} R] (f : Equiv.{succ u1, succ u2} σ τ), Eq.{max (succ (max u2 u3)) (succ (max u1 u3))} (AlgEquiv.{u3, max u2 u3, max u1 u3} R (MvPolynomial.{u2, u3} τ R _inst_1) (MvPolynomial.{u1, u3} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u3} (MvPolynomial.{u2, u3} τ R _inst_1) (MvPolynomial.commSemiring.{u3, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (MvPolynomial.algebra.{u3, u3, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1))) (AlgEquiv.symm.{u3, max u1 u3, max u2 u3} R (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.{u2, u3} τ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u3} (MvPolynomial.{u1, u3} σ R _inst_1) (MvPolynomial.commSemiring.{u3, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u3} (MvPolynomial.{u2, u3} τ R _inst_1) (MvPolynomial.commSemiring.{u3, u2} R τ _inst_1)) (MvPolynomial.algebra.{u3, u3, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.algebra.{u3, u3, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u3} R _inst_1)) (MvPolynomial.renameEquiv.{u1, u2, u3} σ τ R _inst_1 f)) (MvPolynomial.renameEquiv.{u2, u1, u3} τ σ R _inst_1 (Equiv.symm.{succ u1, succ u2} σ τ f))
but is expected to have type
  forall {σ : Type.{u3}} {τ : Type.{u2}} (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (f : Equiv.{succ u3, succ u2} σ τ), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (AlgEquiv.{u1, max u2 u1, max u3 u1} R (MvPolynomial.{u2, u1} τ R _inst_1) (MvPolynomial.{u3, u1} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} τ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.algebra.{u1, u1, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1))) (AlgEquiv.symm.{u1, max u3 u1, max u2 u1} R (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.{u2, u1} τ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} τ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R τ _inst_1)) (MvPolynomial.algebra.{u1, u1, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.renameEquiv.{u3, u2, u1} σ τ R _inst_1 f)) (MvPolynomial.renameEquiv.{u2, u3, u1} τ σ R _inst_1 (Equiv.symm.{succ u3, succ u2} σ τ f))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_equiv_symm MvPolynomial.renameEquiv_symmₓ'. -/
@[simp]
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl
#align mv_polynomial.rename_equiv_symm MvPolynomial.renameEquiv_symm

/- warning: mv_polynomial.rename_equiv_trans -> MvPolynomial.renameEquiv_trans is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {τ : Type.{u2}} {α : Type.{u3}} (R : Type.{u4}) [_inst_1 : CommSemiring.{u4} R] (e : Equiv.{succ u1, succ u2} σ τ) (f : Equiv.{succ u2, succ u3} τ α), Eq.{max (succ (max u1 u4)) (succ (max u3 u4))} (AlgEquiv.{u4, max u1 u4, max u3 u4} R (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.{u3, u4} α R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} α R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R α _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R α _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (AlgEquiv.trans.{u4, max u1 u4, max u2 u4, max u3 u4} R (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u3, u4} α R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} α R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R α _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R α _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.renameEquiv.{u1, u2, u4} σ τ R _inst_1 e) (MvPolynomial.renameEquiv.{u2, u3, u4} τ α R _inst_1 f)) (MvPolynomial.renameEquiv.{u1, u3, u4} σ α R _inst_1 (Equiv.trans.{succ u1, succ u2, succ u3} σ τ α e f))
but is expected to have type
  forall {σ : Type.{u4}} {τ : Type.{u3}} {α : Type.{u2}} (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R] (e : Equiv.{succ u4, succ u3} σ τ) (f : Equiv.{succ u3, succ u2} τ α), Eq.{max (max (succ u4) (succ u2)) (succ u1)} (AlgEquiv.{u1, max u4 u1, max u1 u2} R (MvPolynomial.{u4, u1} σ R _inst_1) (MvPolynomial.{u2, u1} α R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u4 u1} (MvPolynomial.{u4, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u4} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} α R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R α _inst_1)) (MvPolynomial.algebra.{u1, u1, u4} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R α _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1))) (AlgEquiv.trans.{u1, max u4 u1, max u3 u1, max u1 u2} R (MvPolynomial.{u4, u1} σ R _inst_1) (MvPolynomial.{u3, u1} τ R _inst_1) (MvPolynomial.{u2, u1} α R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u4 u1} (MvPolynomial.{u4, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u4} R σ _inst_1)) (CommSemiring.toSemiring.{max u3 u1} (MvPolynomial.{u3, u1} τ R _inst_1) (MvPolynomial.commSemiring.{u1, u3} R τ _inst_1)) (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} α R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R α _inst_1)) (MvPolynomial.algebra.{u1, u1, u4} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.algebra.{u1, u1, u3} R R τ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R α _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)) (MvPolynomial.renameEquiv.{u4, u3, u1} σ τ R _inst_1 e) (MvPolynomial.renameEquiv.{u3, u2, u1} τ α R _inst_1 f)) (MvPolynomial.renameEquiv.{u4, u2, u1} σ α R _inst_1 (Equiv.trans.{succ u4, succ u3, succ u2} σ τ α e f))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_equiv_trans MvPolynomial.renameEquiv_transₓ'. -/
@[simp]
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext (rename_rename e f)
#align mv_polynomial.rename_equiv_trans MvPolynomial.renameEquiv_trans

end

section

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

#print MvPolynomial.eval₂_rename /-
theorem eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) := by
  apply MvPolynomial.induction_on p <;> · intros ; simp [*]
#align mv_polynomial.eval₂_rename MvPolynomial.eval₂_rename
-/

/- warning: mv_polynomial.eval₂_hom_rename -> MvPolynomial.eval₂Hom_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval₂_hom_rename MvPolynomial.eval₂Hom_renameₓ'. -/
theorem eval₂Hom_rename : eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p :=
  eval₂_rename _ _ _ _
#align mv_polynomial.eval₂_hom_rename MvPolynomial.eval₂Hom_rename

/- warning: mv_polynomial.aeval_rename -> MvPolynomial.aeval_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.aeval_rename MvPolynomial.aeval_renameₓ'. -/
theorem aeval_rename [Algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p :=
  eval₂Hom_rename _ _ _ _
#align mv_polynomial.aeval_rename MvPolynomial.aeval_rename

/- warning: mv_polynomial.rename_eval₂ -> MvPolynomial.rename_eval₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_eval₂ MvPolynomial.rename_eval₂ₓ'. -/
theorem rename_eval₂ (g : τ → MvPolynomial σ R) :
    rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) := by
  apply MvPolynomial.induction_on p <;> · intros ; simp [*]
#align mv_polynomial.rename_eval₂ MvPolynomial.rename_eval₂

/- warning: mv_polynomial.rename_prodmk_eval₂ -> MvPolynomial.rename_prod_mk_eval₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.rename_prodmk_eval₂ MvPolynomial.rename_prod_mk_eval₂ₓ'. -/
theorem rename_prod_mk_eval₂ (j : τ) (g : σ → MvPolynomial σ R) :
    rename (Prod.mk j) (p.eval₂ C g) = p.eval₂ C fun x => rename (Prod.mk j) (g x) := by
  apply MvPolynomial.induction_on p <;> · intros ; simp [*]
#align mv_polynomial.rename_prodmk_eval₂ MvPolynomial.rename_prod_mk_eval₂

/- warning: mv_polynomial.eval₂_rename_prodmk -> MvPolynomial.eval₂_rename_prod_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval₂_rename_prodmk MvPolynomial.eval₂_rename_prod_mkₓ'. -/
theorem eval₂_rename_prod_mk (g : σ × τ → S) (i : σ) (p : MvPolynomial τ R) :
    (rename (Prod.mk i) p).eval₂ f g = eval₂ f (fun j => g (i, j)) p := by
  apply MvPolynomial.induction_on p <;> · intros ; simp [*]
#align mv_polynomial.eval₂_rename_prodmk MvPolynomial.eval₂_rename_prod_mk

/- warning: mv_polynomial.eval_rename_prodmk -> MvPolynomial.eval_rename_prod_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval_rename_prodmk MvPolynomial.eval_rename_prod_mkₓ'. -/
theorem eval_rename_prod_mk (g : σ × τ → R) (i : σ) (p : MvPolynomial τ R) :
    eval g (rename (Prod.mk i) p) = eval (fun j => g (i, j)) p :=
  eval₂_rename_prod_mk (RingHom.id _) _ _ _
#align mv_polynomial.eval_rename_prodmk MvPolynomial.eval_rename_prod_mk

end

/- warning: mv_polynomial.exists_finset_rename -> MvPolynomial.exists_finset_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.exists_finset_rename MvPolynomial.exists_finset_renameₓ'. -/
/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename (p : MvPolynomial σ R) :
    ∃ (s : Finset σ)(q : MvPolynomial { x // x ∈ s } R), p = rename coe q := by
  classical
    apply induction_on p
    · intro r; exact ⟨∅, C r, by rw [rename_C]⟩
    · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
      refine' ⟨s ∪ t, ⟨_, _⟩⟩
      ·
        refine' rename (Subtype.map id _) p + rename (Subtype.map id _) q <;>
          simp (config := { contextual := true }) only [id.def, true_or_iff, or_true_iff,
            Finset.mem_union, forall_true_iff]
      · simp only [rename_rename, AlgHom.map_add]; rfl
    · rintro p n ⟨s, p, rfl⟩
      refine' ⟨insert n s, ⟨_, _⟩⟩
      · refine' rename (Subtype.map id _) p * X ⟨n, s.mem_insert_self n⟩
        simp (config := { contextual := true }) only [id.def, or_true_iff, Finset.mem_insert,
          forall_true_iff]
      · simp only [rename_rename, rename_X, Subtype.coe_mk, AlgHom.map_mul]; rfl
#align mv_polynomial.exists_finset_rename MvPolynomial.exists_finset_rename

/- warning: mv_polynomial.exists_finset_rename₂ -> MvPolynomial.exists_finset_rename₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.exists_finset_rename₂ MvPolynomial.exists_finset_rename₂ₓ'. -/
/-- `exists_finset_rename` for two polyonomials at once: for any two polynomials `p₁`, `p₂` in a
  polynomial semiring `R[σ]` of possibly infinitely many variables, `exists_finset_rename₂` yields
  a finite subset `s` of `σ` such that both `p₁` and `p₂` are contained in the polynomial semiring
  `R[s]` of finitely many variables. -/
theorem exists_finset_rename₂ (p₁ p₂ : MvPolynomial σ R) :
    ∃ (s : Finset σ)(q₁ q₂ : MvPolynomial s R), p₁ = rename coe q₁ ∧ p₂ = rename coe q₂ :=
  by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  classical
    use s₁ ∪ s₂
    use rename (Set.inclusion <| s₁.subset_union_left s₂) q₁
    use rename (Set.inclusion <| s₁.subset_union_right s₂) q₂
    constructor <;> simpa
#align mv_polynomial.exists_finset_rename₂ MvPolynomial.exists_finset_rename₂

/- warning: mv_polynomial.exists_fin_rename -> MvPolynomial.exists_fin_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.exists_fin_rename MvPolynomial.exists_fin_renameₓ'. -/
/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename (p : MvPolynomial σ R) :
    ∃ (n : ℕ)(f : Fin n → σ)(hf : Injective f)(q : MvPolynomial (Fin n) R), p = rename f q :=
  by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let n := Fintype.card { x // x ∈ s }
  let e := Fintype.equivFin { x // x ∈ s }
  refine' ⟨n, coe ∘ e.symm, subtype.val_injective.comp e.symm.injective, rename e q, _⟩
  rw [← rename_rename, rename_rename e]
  simp only [Function.comp, Equiv.symm_apply_apply, rename_rename]
#align mv_polynomial.exists_fin_rename MvPolynomial.exists_fin_rename

end Rename

/- warning: mv_polynomial.eval₂_cast_comp -> MvPolynomial.eval₂_cast_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.eval₂_cast_comp MvPolynomial.eval₂_cast_compₓ'. -/
theorem eval₂_cast_comp (f : σ → τ) (c : ℤ →+* R) (g : τ → R) (p : MvPolynomial σ ℤ) :
    eval₂ c (g ∘ f) p = eval₂ c g (rename f p) :=
  MvPolynomial.induction_on p (fun n => by simp only [eval₂_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, rename, eval₂_add, AlgHom.map_add]) fun p n hp => by
    simp only [hp, rename, aeval_def, eval₂_X, eval₂_mul]
#align mv_polynomial.eval₂_cast_comp MvPolynomial.eval₂_cast_comp

section Coeff

/- warning: mv_polynomial.coeff_rename_map_domain -> MvPolynomial.coeff_rename_mapDomain is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.coeff_rename_map_domain MvPolynomial.coeff_rename_mapDomainₓ'. -/
@[simp]
theorem coeff_rename_mapDomain (f : σ → τ) (hf : Injective f) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (rename f φ).coeff (d.mapDomain f) = φ.coeff d := by
  classical
    apply induction_on' φ
    · intro u r
      rw [rename_monomial, coeff_monomial, coeff_monomial]
      simp only [(Finsupp.mapDomain_injective hf).eq_iff]
    · intros ; simp only [*, AlgHom.map_add, coeff_add]
#align mv_polynomial.coeff_rename_map_domain MvPolynomial.coeff_rename_mapDomain

/- warning: mv_polynomial.coeff_rename_eq_zero -> MvPolynomial.coeff_rename_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.coeff_rename_eq_zero MvPolynomial.coeff_rename_eq_zeroₓ'. -/
theorem coeff_rename_eq_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
  classical
    rw [rename_eq, ← not_mem_support_iff]
    intro H
    replace H := map_domain_support H
    rw [Finset.mem_image] at H
    obtain ⟨u, hu, rfl⟩ := H
    specialize h u rfl
    simp at h hu
    contradiction
#align mv_polynomial.coeff_rename_eq_zero MvPolynomial.coeff_rename_eq_zero

/- warning: mv_polynomial.coeff_rename_ne_zero -> MvPolynomial.coeff_rename_ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.coeff_rename_ne_zero MvPolynomial.coeff_rename_ne_zeroₓ'. -/
theorem coeff_rename_ne_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : (rename f φ).coeff d ≠ 0) : ∃ u : σ →₀ ℕ, u.mapDomain f = d ∧ φ.coeff u ≠ 0 := by
  contrapose! h; apply coeff_rename_eq_zero _ _ _ h
#align mv_polynomial.coeff_rename_ne_zero MvPolynomial.coeff_rename_ne_zero

/- warning: mv_polynomial.constant_coeff_rename -> MvPolynomial.constantCoeff_rename is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.constant_coeff_rename MvPolynomial.constantCoeff_renameₓ'. -/
@[simp]
theorem constantCoeff_rename {τ : Type _} (f : σ → τ) (φ : MvPolynomial σ R) :
    constantCoeff (rename f φ) = constantCoeff φ :=
  by
  apply φ.induction_on
  · intro a; simp only [constant_coeff_C, rename_C]
  · intro p q hp hq; simp only [hp, hq, RingHom.map_add, AlgHom.map_add]
  · intro p n hp; simp only [hp, rename_X, constant_coeff_X, RingHom.map_mul, AlgHom.map_mul]
#align mv_polynomial.constant_coeff_rename MvPolynomial.constantCoeff_rename

end Coeff

section Support

/- warning: mv_polynomial.support_rename_of_injective -> MvPolynomial.support_rename_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.support_rename_of_injective MvPolynomial.support_rename_of_injectiveₓ'. -/
theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} [DecidableEq τ]
    (h : Function.Injective f) : (rename f p).support = Finset.image (mapDomain f) p.support :=
  by
  rw [rename_eq]
  exact Finsupp.mapDomain_support_of_injective (map_domain_injective h) _
#align mv_polynomial.support_rename_of_injective MvPolynomial.support_rename_of_injective

end Support

end MvPolynomial

