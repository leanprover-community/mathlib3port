/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.polynomial.group_ring_action
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Monic
import Mathbin.GroupTheory.GroupAction.Quotient

/-!
# Group action on rings applied to polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains instances and definitions relating `mul_semiring_action` to `polynomial`.
-/


variable (M : Type _) [Monoid M]

open scoped Polynomial

namespace Polynomial

variable (R : Type _) [Semiring R]

variable {M}

#print Polynomial.smul_eq_map /-
theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    (· • ·) m = map (MulSemiringAction.toRingHom M R m) :=
  by
  suffices
    DistribMulAction.toAddMonoidHom R[X] m =
      (map_ring_hom (MulSemiringAction.toRingHom M R m)).toAddMonoidHom
    by ext1 r; exact AddMonoidHom.congr_fun this r
  ext (n r) : 2
  change m • monomial n r = map (MulSemiringAction.toRingHom M R m) (monomial n r)
  simpa only [Polynomial.map_monomial, Polynomial.smul_monomial]
#align polynomial.smul_eq_map Polynomial.smul_eq_map
-/

variable (M)

noncomputable instance [MulSemiringAction M R] : MulSemiringAction M R[X] :=
  { Polynomial.distribMulAction with
    smul := (· • ·)
    smul_one := fun m =>
      (smul_eq_map R m).symm ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m p q =>
      (smul_eq_map R m).symm ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

variable {M R}

variable [MulSemiringAction M R]

#print Polynomial.smul_X /-
@[simp]
theorem smul_X (m : M) : (m • X : R[X]) = X :=
  (smul_eq_map R m).symm ▸ map_X _
#align polynomial.smul_X Polynomial.smul_X
-/

variable (S : Type _) [CommSemiring S] [MulSemiringAction M S]

#print Polynomial.smul_eval_smul /-
theorem smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.eval x :=
  Polynomial.induction_on f (fun r => by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg => by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r ih => by
    rw [smul_mul', smul_pow', smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X, eval_mul, eval_C,
      eval_pow, eval_X, smul_mul', smul_pow']
#align polynomial.smul_eval_smul Polynomial.smul_eval_smul
-/

variable (G : Type _) [Group G]

#print Polynomial.eval_smul' /-
theorem eval_smul' [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    f.eval (g • x) = g • (g⁻¹ • f).eval x := by rw [← smul_eval_smul, smul_inv_smul]
#align polynomial.eval_smul' Polynomial.eval_smul'
-/

#print Polynomial.smul_eval /-
theorem smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    (g • f).eval x = g • f.eval (g⁻¹ • x) := by rw [← smul_eval_smul, smul_inv_smul]
#align polynomial.smul_eval Polynomial.smul_eval
-/

end Polynomial

section CommRing

variable (G : Type _) [Group G] [Fintype G]

variable (R : Type _) [CommRing R] [MulSemiringAction G R]

open MulAction

open scoped Classical

#print prodXSubSmul /-
/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prodXSubSmul (x : R) : R[X] :=
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).Prod fun g =>
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)
#align prod_X_sub_smul prodXSubSmul
-/

#print prodXSubSmul.monic /-
theorem prodXSubSmul.monic (x : R) : (prodXSubSmul G R x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun g _ => Polynomial.monic_X_sub_C _
#align prod_X_sub_smul.monic prodXSubSmul.monic
-/

#print prodXSubSmul.eval /-
theorem prodXSubSmul.eval (x : R) : (prodXSubSmul G R x).eval x = 0 :=
  (MonoidHom.map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] →* R) _ _).trans <|
    Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) <| by simp
#align prod_X_sub_smul.eval prodXSubSmul.eval
-/

#print prodXSubSmul.smul /-
theorem prodXSubSmul.smul (x : R) (g : G) : g • prodXSubSmul G R x = prodXSubSmul G R x :=
  Finset.smul_prod.trans <|
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' => by
      rw [of_quotient_stabilizer_smul, smul_sub, Polynomial.smul_X, Polynomial.smul_C]
#align prod_X_sub_smul.smul prodXSubSmul.smul
-/

#print prodXSubSmul.coeff /-
theorem prodXSubSmul.coeff (x : R) (g : G) (n : ℕ) :
    g • (prodXSubSmul G R x).coeff n = (prodXSubSmul G R x).coeff n := by
  rw [← Polynomial.coeff_smul, prodXSubSmul.smul]
#align prod_X_sub_smul.coeff prodXSubSmul.coeff
-/

end CommRing

namespace MulSemiringActionHom

variable {M}

variable {P : Type _} [CommSemiring P] [MulSemiringAction M P]

variable {Q : Type _} [CommSemiring Q] [MulSemiringAction M Q]

open Polynomial

#print MulSemiringActionHom.polynomial /-
/-- An equivariant map induces an equivariant map on polynomials. -/
protected noncomputable def polynomial (g : P →+*[M] Q) : P[X] →+*[M] Q[X]
    where
  toFun := map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b => by rw [smul_C, map_C, coe_fn_coe, g.map_smul, map_C, coe_fn_coe, smul_C])
      (fun p q ihp ihq => by
        rw [smul_add, Polynomial.map_add, ihp, ihq, Polynomial.map_add, smul_add])
      fun n b ih => by
      rw [smul_mul', smul_C, smul_pow', smul_X, Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, coe_fn_coe, g.map_smul, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        smul_mul', smul_C, smul_pow', smul_X, coe_fn_coe]
  map_zero' := Polynomial.map_zero g
  map_add' p q := Polynomial.map_add g
  map_one' := Polynomial.map_one g
  map_mul' p q := Polynomial.map_mul g
#align mul_semiring_action_hom.polynomial MulSemiringActionHom.polynomial
-/

#print MulSemiringActionHom.coe_polynomial /-
@[simp]
theorem coe_polynomial (g : P →+*[M] Q) : (g.Polynomial : P[X] → Q[X]) = map g :=
  rfl
#align mul_semiring_action_hom.coe_polynomial MulSemiringActionHom.coe_polynomial
-/

end MulSemiringActionHom

