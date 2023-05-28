/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module data.polynomial.module
! leanprover-community/mathlib commit 4f81bc21e32048db7344b7867946e992cf5f68cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.FiniteType

/-!
# Polynomial module

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as an type alias `polynomial_module R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `polynomial_module` for details.

-/


universe u v

open Polynomial

open Polynomial BigOperators

variable (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

include R

#print PolynomialModule /-
/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `module S (polynomial_module R M)` to factor through `R` except
`module R[X] (polynomial_module R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `polynomial_module R R[X]`
- `R[X]` acts on `polynomial_module R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `polynomial_module R[X] R[X]`
- `R[X]` acts on `polynomial_module R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `polynomial_module R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `module R[X] (polynomial_module R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules
for the full discussion.
-/
@[nolint unused_arguments]
def PolynomialModule :=
  ℕ →₀ M deriving AddCommGroup, Inhabited
#align polynomial_module PolynomialModule
-/

omit R

variable {M}

variable {S : Type _} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule

/-- This is required to have the `is_scalar_tower S R M` instance to avoid diamonds. -/
@[nolint unused_arguments]
noncomputable instance : Module S (PolynomialModule R M) :=
  Finsupp.module ℕ M

instance : CoeFun (PolynomialModule R M) fun _ => ℕ → M :=
  Finsupp.coeFun

#print PolynomialModule.single /-
/-- The monomial `m * x ^ i`. This is defeq to `finsupp.single_add_hom`, and is redefined here
so that it has the desired type signature.  -/
noncomputable def single (i : ℕ) : M →+ PolynomialModule R M :=
  Finsupp.singleAddHom i
#align polynomial_module.single PolynomialModule.single
-/

/- warning: polynomial_module.single_apply -> PolynomialModule.single_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.single_apply PolynomialModule.single_applyₓ'. -/
theorem single_apply (i : ℕ) (m : M) (n : ℕ) : single R i m n = ite (i = n) m 0 :=
  Finsupp.single_apply
#align polynomial_module.single_apply PolynomialModule.single_apply

#print PolynomialModule.lsingle /-
/-- `polynomial_module.single` as a linear map. -/
noncomputable def lsingle (i : ℕ) : M →ₗ[R] PolynomialModule R M :=
  Finsupp.lsingle i
#align polynomial_module.lsingle PolynomialModule.lsingle
-/

/- warning: polynomial_module.lsingle_apply -> PolynomialModule.lsingle_apply is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (i : Nat) (m : M) (n : Nat), Eq.{succ u2} M (coeFn.{succ u2, succ u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (fun (_x : PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) => Nat -> M) (PolynomialModule.hasCoeToFun.{u1, u2} R M _inst_1 _inst_2 _inst_3) (coeFn.{succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PolynomialModule.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3)) _inst_3 (PolynomialModule.module.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_3 (PolynomialModule.lsingle._proof_1.{u1, u2} R M _inst_1 _inst_2 _inst_3))) (fun (_x : LinearMap.{u1, u1, u2, u2} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PolynomialModule.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3)) _inst_3 (PolynomialModule.module.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_3 (PolynomialModule.lsingle._proof_1.{u1, u2} R M _inst_1 _inst_2 _inst_3))) => M -> (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (LinearMap.hasCoeToFun.{u1, u1, u2, u2} R R M (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PolynomialModule.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3)) _inst_3 (PolynomialModule.module.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_3 (PolynomialModule.lsingle._proof_1.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (PolynomialModule.lsingle.{u1, u2} R M _inst_1 _inst_2 _inst_3 i) m) n) (ite.{succ u2} M (Eq.{1} Nat i n) (Nat.decidableEq i n) m (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))))))
but is expected to have type
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (i : Nat) (m : M) (n : Nat), Eq.{succ u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : Nat) => M) n) (FunLike.coe.{succ u2, 1, succ u2} (Finsupp.{0, u2} Nat M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2)))))) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : Nat) => M) _x) (Finsupp.funLike.{0, u2} Nat M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2)))))) (FunLike.coe.{succ u2, succ u2, succ u2} (LinearMap.{u1, u1, u2, u2} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) M (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (instAddCommGroupPolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) _inst_3 (PolynomialModule.instModulePolynomialModuleToSemiringToAddCommMonoidInstAddCommGroupPolynomialModule.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u2, u2} R R M (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (instAddCommGroupPolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) _inst_3 (PolynomialModule.instModulePolynomialModuleToSemiringToAddCommMonoidInstAddCommGroupPolynomialModule.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (PolynomialModule.lsingle.{u1, u2} R M _inst_1 _inst_2 _inst_3 i) m) n) (ite.{succ u2} M (Eq.{1} Nat i n) (instDecidableEqNat i n) m (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align polynomial_module.lsingle_apply PolynomialModule.lsingle_applyₓ'. -/
theorem lsingle_apply (i : ℕ) (m : M) (n : ℕ) : lsingle R i m n = ite (i = n) m 0 :=
  Finsupp.single_apply
#align polynomial_module.lsingle_apply PolynomialModule.lsingle_apply

/- warning: polynomial_module.single_smul -> PolynomialModule.single_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.single_smul PolynomialModule.single_smulₓ'. -/
theorem single_smul (i : ℕ) (r : R) (m : M) : single R i (r • m) = r • single R i m :=
  (lsingle R i).map_smul r m
#align polynomial_module.single_smul PolynomialModule.single_smul

variable {R}

/- warning: polynomial_module.induction_linear -> PolynomialModule.induction_linear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.induction_linear PolynomialModule.induction_linearₓ'. -/
theorem induction_linear {P : PolynomialModule R M → Prop} (f : PolynomialModule R M) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsingle : ∀ a b, P (single R a b)) : P f :=
  Finsupp.induction_linear f h0 hadd hsingle
#align polynomial_module.induction_linear PolynomialModule.induction_linear

#print PolynomialModule.polynomialModule /-
@[semireducible]
noncomputable instance polynomialModule : Module R[X] (PolynomialModule R M) :=
  modulePolynomialOfEndo (Finsupp.lmapDomain _ _ Nat.succ)
#align polynomial_module.polynomial_module PolynomialModule.polynomialModule
-/

instance (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (PolynomialModule R M) :=
  Finsupp.isScalarTower _ _

#print PolynomialModule.isScalarTower' /-
instance isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M) :=
  by
  haveI : IsScalarTower R R[X] (PolynomialModule R M) := modulePolynomialOfEndo.isScalarTower _
  constructor
  intro x y z
  rw [← @IsScalarTower.algebraMap_smul S R, ← @IsScalarTower.algebraMap_smul S R, smul_assoc]
#align polynomial_module.is_scalar_tower' PolynomialModule.isScalarTower'
-/

/- warning: polynomial_module.monomial_smul_single -> PolynomialModule.monomial_smul_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.monomial_smul_single PolynomialModule.monomial_smul_singleₓ'. -/
@[simp]
theorem monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
    monomial i r • single R j m = single R (i + j) (r • m) :=
  by
  simp only [LinearMap.mul_apply, Polynomial.aeval_monomial, LinearMap.pow_apply,
    Module.algebraMap_end_apply, modulePolynomialOfEndo_smul_def]
  induction i generalizing r j m
  · simp [single]
  · rw [Function.iterate_succ, Function.comp_apply, Nat.succ_eq_add_one, add_assoc, ← i_ih]
    congr 2
    ext a
    dsimp [single]
    rw [Finsupp.mapDomain_single, Nat.succ_eq_one_add]
#align polynomial_module.monomial_smul_single PolynomialModule.monomial_smul_single

/- warning: polynomial_module.monomial_smul_apply -> PolynomialModule.monomial_smul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.monomial_smul_apply PolynomialModule.monomial_smul_applyₓ'. -/
@[simp]
theorem monomial_smul_apply (i : ℕ) (r : R) (g : PolynomialModule R M) (n : ℕ) :
    (monomial i r • g) n = ite (i ≤ n) (r • g (n - i)) 0 :=
  by
  induction' g using PolynomialModule.induction_linear with p q hp hq
  · simp only [smul_zero, Finsupp.zero_apply, if_t_t]
  · simp only [smul_add, Finsupp.add_apply, hp, hq]
    split_ifs
    exacts[rfl, zero_add 0]
  · rw [monomial_smul_single, single_apply, single_apply, smul_ite, smul_zero, ← ite_and]
    congr
    rw [eq_iff_iff]
    constructor
    · rintro rfl
      simp
    · rintro ⟨e, rfl⟩
      rw [add_comm, tsub_add_cancel_of_le e]
#align polynomial_module.monomial_smul_apply PolynomialModule.monomial_smul_apply

/- warning: polynomial_module.smul_single_apply -> PolynomialModule.smul_single_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.smul_single_apply PolynomialModule.smul_single_applyₓ'. -/
@[simp]
theorem smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
    (f • single R i m) n = ite (i ≤ n) (f.coeff (n - i) • m) 0 :=
  by
  induction' f using Polynomial.induction_on' with p q hp hq
  · rw [add_smul, Finsupp.add_apply, hp, hq, coeff_add, add_smul]
    split_ifs
    exacts[rfl, zero_add 0]
  · rw [monomial_smul_single, single_apply, coeff_monomial, ite_smul, zero_smul]
    by_cases h : i ≤ n
    · simp_rw [eq_tsub_iff_add_eq_of_le h, if_pos h]
    · rw [if_neg h, ite_eq_right_iff]
      intro e
      exfalso
      linarith
#align polynomial_module.smul_single_apply PolynomialModule.smul_single_apply

/- warning: polynomial_module.smul_apply -> PolynomialModule.smul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.smul_apply PolynomialModule.smul_applyₓ'. -/
theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
    (f • g) n = ∑ x in Finset.Nat.antidiagonal n, f.coeff x.1 • g x.2 :=
  by
  induction' f using Polynomial.induction_on' with p q hp hq
  · rw [add_smul, Finsupp.add_apply, hp, hq, ← Finset.sum_add_distrib]
    congr
    ext
    rw [coeff_add, add_smul]
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => (monomial f_n f_a).coeff i • g j,
      monomial_smul_apply]
    dsimp [monomial]
    simp_rw [Finsupp.single_smul, Finsupp.single_apply]
    rw [Finset.sum_ite_eq]
    simp [Nat.lt_succ_iff]
#align polynomial_module.smul_apply PolynomialModule.smul_apply

#print PolynomialModule.equivPolynomialSelf /-
/-- `polynomial_module R R` is isomorphic to `R[X]` as an `R[X]` module. -/
noncomputable def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] :=
  { (Polynomial.toFinsuppIso R).symm with
    map_smul' := fun r x =>
      by
      induction' r using Polynomial.induction_on' with _ _ _ _ n p
      · simp_all only [add_smul, map_add, [anonymous]]
      · ext i
        dsimp
        rw [monomial_smul_apply, ← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', mul_ite, MulZeroClass.mul_zero]
        simp }
#align polynomial_module.equiv_polynomial_self PolynomialModule.equivPolynomialSelf
-/

#print PolynomialModule.equivPolynomial /-
/-- `polynomial_module R S` is isomorphic to `S[X]` as an `R` module. -/
noncomputable def equivPolynomial {S : Type _} [CommRing S] [Algebra R S] :
    PolynomialModule R S ≃ₗ[R] S[X] :=
  { (Polynomial.toFinsuppIso S).symm with map_smul' := fun r x => rfl }
#align polynomial_module.equiv_polynomial PolynomialModule.equivPolynomial
-/

variable (R' : Type _) {M' : Type _} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Algebra R R'] [Module R M'] [IsScalarTower R R' M']

/- warning: polynomial_module.map -> PolynomialModule.map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (R' : Type.{u3}) {M' : Type.{u4}} [_inst_8 : CommRing.{u3} R'] [_inst_9 : AddCommGroup.{u4} M'] [_inst_10 : Module.{u3, u4} R' M' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)] [_inst_11 : Algebra.{u1, u3} R R' (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8))] [_inst_12 : Module.{u1, u4} R M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)] [_inst_13 : IsScalarTower.{u1, u3, u4} R R' M' (SMulZeroClass.toHasSmul.{u1, u3} R R' (AddZeroClass.toHasZero.{u3} R' (AddMonoid.toAddZeroClass.{u3} R' (AddCommMonoid.toAddMonoid.{u3} R' (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R' (Semiring.toNonAssocSemiring.{u3} R' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)))))))) (SMulWithZero.toSmulZeroClass.{u1, u3} R R' (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u3} R' (AddMonoid.toAddZeroClass.{u3} R' (AddCommMonoid.toAddMonoid.{u3} R' (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R' (Semiring.toNonAssocSemiring.{u3} R' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)))))))) (MulActionWithZero.toSMulWithZero.{u1, u3} R R' (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u3} R' (AddMonoid.toAddZeroClass.{u3} R' (AddCommMonoid.toAddMonoid.{u3} R' (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R' (Semiring.toNonAssocSemiring.{u3} R' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)))))))) (Module.toMulActionWithZero.{u1, u3} R R' (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R' (Semiring.toNonAssocSemiring.{u3} R' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8))))) (Algebra.toModule.{u1, u3} R R' (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)) _inst_11))))) (SMulZeroClass.toHasSmul.{u3, u4} R' M' (AddZeroClass.toHasZero.{u4} M' (AddMonoid.toAddZeroClass.{u4} M' (AddCommMonoid.toAddMonoid.{u4} M' (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)))) (SMulWithZero.toSmulZeroClass.{u3, u4} R' M' (MulZeroClass.toHasZero.{u3} R' (MulZeroOneClass.toMulZeroClass.{u3} R' (MonoidWithZero.toMulZeroOneClass.{u3} R' (Semiring.toMonoidWithZero.{u3} R' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)))))) (AddZeroClass.toHasZero.{u4} M' (AddMonoid.toAddZeroClass.{u4} M' (AddCommMonoid.toAddMonoid.{u4} M' (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)))) (MulActionWithZero.toSMulWithZero.{u3, u4} R' M' (Semiring.toMonoidWithZero.{u3} R' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8))) (AddZeroClass.toHasZero.{u4} M' (AddMonoid.toAddZeroClass.{u4} M' (AddCommMonoid.toAddMonoid.{u4} M' (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)))) (Module.toMulActionWithZero.{u3, u4} R' M' (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_8)) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9) _inst_10)))) (SMulZeroClass.toHasSmul.{u1, u4} R M' (AddZeroClass.toHasZero.{u4} M' (AddMonoid.toAddZeroClass.{u4} M' (AddCommMonoid.toAddMonoid.{u4} M' (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)))) (SMulWithZero.toSmulZeroClass.{u1, u4} R M' (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u4} M' (AddMonoid.toAddZeroClass.{u4} M' (AddCommMonoid.toAddMonoid.{u4} M' (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)))) (MulActionWithZero.toSMulWithZero.{u1, u4} R M' (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u4} M' (AddMonoid.toAddZeroClass.{u4} M' (AddCommMonoid.toAddMonoid.{u4} M' (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)))) (Module.toMulActionWithZero.{u1, u4} R M' (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9) _inst_12))))], (LinearMap.{u1, u1, u2, u4} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9) _inst_3 _inst_12) -> (LinearMap.{u1, u1, u2, u4} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PolynomialModule.{u3, u4} R' M' _inst_8 _inst_9 _inst_10) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PolynomialModule.addCommGroup.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (AddCommGroup.toAddCommMonoid.{u4} (PolynomialModule.{u3, u4} R' M' _inst_8 _inst_9 _inst_10) (PolynomialModule.addCommGroup.{u3, u4} R' M' _inst_8 _inst_9 _inst_10)) (PolynomialModule.module.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) (Algebra.id.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) _inst_3 (PolynomialModule.map._proof_1.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (PolynomialModule.module.{u3, u4, u1} R' M' _inst_8 _inst_9 _inst_10 R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_11 _inst_12 _inst_13))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] (R' : Type.{u3}) {M' : Type.{u4}} [_inst_8 : CommRing.{u3} R'] [_inst_9 : AddCommGroup.{u4} M'] [_inst_10 : Module.{u3, u4} R' M' (CommSemiring.toSemiring.{u3} R' (CommRing.toCommSemiring.{u3} R' _inst_8)) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)] [_inst_11 : Module.{u1, u4} R M' (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9)], (LinearMap.{u1, u1, u2, u4} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) M M' (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u4} M' _inst_9) _inst_3 _inst_11) -> (LinearMap.{u1, u1, u2, u4} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (PolynomialModule.{u3, u4} R' M' _inst_8 _inst_9 _inst_10) (AddCommGroup.toAddCommMonoid.{u2} (PolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3) (instAddCommGroupPolynomialModule.{u1, u2} R M _inst_1 _inst_2 _inst_3)) (AddCommGroup.toAddCommMonoid.{u4} (PolynomialModule.{u3, u4} R' M' _inst_8 _inst_9 _inst_10) (instAddCommGroupPolynomialModule.{u3, u4} R' M' _inst_8 _inst_9 _inst_10)) (PolynomialModule.instModulePolynomialModuleToSemiringToAddCommMonoidInstAddCommGroupPolynomialModule.{u1, u2, u1} R M _inst_1 _inst_2 _inst_3 R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_3) (PolynomialModule.instModulePolynomialModuleToSemiringToAddCommMonoidInstAddCommGroupPolynomialModule.{u3, u4, u1} R' M' _inst_8 _inst_9 _inst_10 R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_11))
Case conversion may be inaccurate. Consider using '#align polynomial_module.map PolynomialModule.mapₓ'. -/
/-- The image of a polynomial under a linear map. -/
noncomputable def map (f : M →ₗ[R] M') : PolynomialModule R M →ₗ[R] PolynomialModule R' M' :=
  Finsupp.mapRange.linearMap f
#align polynomial_module.map PolynomialModule.map

/- warning: polynomial_module.map_single -> PolynomialModule.map_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.map_single PolynomialModule.map_singleₓ'. -/
@[simp]
theorem map_single (f : M →ₗ[R] M') (i : ℕ) (m : M) : map R' f (single R i m) = single R' i (f m) :=
  Finsupp.mapRange_single
#align polynomial_module.map_single PolynomialModule.map_single

/- warning: polynomial_module.map_smul -> PolynomialModule.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.map_smul PolynomialModule.map_smulₓ'. -/
theorem map_smul (f : M →ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) :
    map R' f (p • q) = p.map (algebraMap R R') • map R' f q :=
  by
  apply induction_linear q
  · rw [smul_zero, map_zero, smul_zero]
  · intro f g e₁ e₂
    rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  intro i m
  apply Polynomial.induction_on' p
  · intro p q e₁ e₂
    rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
  · intro j s
    rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single, monomial_smul_single,
      f.map_smul, algebraMap_smul]
#align polynomial_module.map_smul PolynomialModule.map_smul

#print PolynomialModule.eval /-
/-- Evaulate a polynomial `p : polynomial_module R M` at `r : R`. -/
@[simps (config := lemmasOnly)]
def eval (r : R) : PolynomialModule R M →ₗ[R] M
    where
  toFun p := p.Sum fun i m => r ^ i • m
  map_add' x y := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine' (Finsupp.sum_smul_index' _).trans _
    · exact fun i => smul_zero _
    · simp_rw [← smul_comm s, ← Finsupp.smul_sum]
      rfl
#align polynomial_module.eval PolynomialModule.eval
-/

/- warning: polynomial_module.eval_single -> PolynomialModule.eval_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.eval_single PolynomialModule.eval_singleₓ'. -/
@[simp]
theorem eval_single (r : R) (i : ℕ) (m : M) : eval r (single R i m) = r ^ i • m :=
  Finsupp.sum_single_index (smul_zero _)
#align polynomial_module.eval_single PolynomialModule.eval_single

/- warning: polynomial_module.eval_lsingle -> PolynomialModule.eval_lsingle is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.eval_lsingle PolynomialModule.eval_lsingleₓ'. -/
@[simp]
theorem eval_lsingle (r : R) (i : ℕ) (m : M) : eval r (lsingle R i m) = r ^ i • m :=
  eval_single r i m
#align polynomial_module.eval_lsingle PolynomialModule.eval_lsingle

/- warning: polynomial_module.eval_smul -> PolynomialModule.eval_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.eval_smul PolynomialModule.eval_smulₓ'. -/
theorem eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (p • q) = p.eval r • eval r q :=
  by
  apply induction_linear q
  · rw [smul_zero, map_zero, smul_zero]
  · intro f g e₁ e₂
    rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  intro i m
  apply Polynomial.induction_on' p
  · intro p q e₁ e₂
    rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
  · intro j s
    rw [monomial_smul_single, eval_single, Polynomial.eval_monomial, eval_single, smul_comm, ←
      smul_smul, pow_add, mul_smul]
#align polynomial_module.eval_smul PolynomialModule.eval_smul

/- warning: polynomial_module.eval_map -> PolynomialModule.eval_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.eval_map PolynomialModule.eval_mapₓ'. -/
@[simp]
theorem eval_map (f : M →ₗ[R] M') (q : PolynomialModule R M) (r : R) :
    eval (algebraMap R R' r) (map R' f q) = f (eval r q) :=
  by
  apply induction_linear q
  · simp_rw [map_zero]
  · intro f g e₁ e₂
    simp_rw [map_add, e₁, e₂]
  · intro i m
    rw [map_single, eval_single, eval_single, f.map_smul, ← map_pow, algebraMap_smul]
#align polynomial_module.eval_map PolynomialModule.eval_map

/- warning: polynomial_module.eval_map' -> PolynomialModule.eval_map' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.eval_map' PolynomialModule.eval_map'ₓ'. -/
@[simp]
theorem eval_map' (f : M →ₗ[R] M) (q : PolynomialModule R M) (r : R) :
    eval r (map R f q) = f (eval r q) :=
  eval_map R f q r
#align polynomial_module.eval_map' PolynomialModule.eval_map'

#print PolynomialModule.comp /-
/-- `comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`.  -/
@[simps]
noncomputable def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
  ((eval p).restrictScalars R).comp (map R[X] (lsingle R 0))
#align polynomial_module.comp PolynomialModule.comp
-/

/- warning: polynomial_module.comp_single -> PolynomialModule.comp_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.comp_single PolynomialModule.comp_singleₓ'. -/
theorem comp_single (p : R[X]) (i : ℕ) (m : M) : comp p (single R i m) = p ^ i • single R 0 m :=
  by
  rw [comp_apply]
  erw [map_single, eval_single]
  rfl
#align polynomial_module.comp_single PolynomialModule.comp_single

/- warning: polynomial_module.comp_eval -> PolynomialModule.comp_eval is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.comp_eval PolynomialModule.comp_evalₓ'. -/
theorem comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (comp p q) = eval (p.eval r) q :=
  by
  rw [← LinearMap.comp_apply]
  apply induction_linear q
  · rw [map_zero, map_zero]
  · intro _ _ e₁ e₂
    rw [map_add, map_add, e₁, e₂]
  · intro i m
    rw [LinearMap.comp_apply, comp_single, eval_single, eval_smul, eval_single, pow_zero, one_smul,
      Polynomial.eval_pow]
#align polynomial_module.comp_eval PolynomialModule.comp_eval

/- warning: polynomial_module.comp_smul -> PolynomialModule.comp_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_module.comp_smul PolynomialModule.comp_smulₓ'. -/
theorem comp_smul (p p' : R[X]) (q : PolynomialModule R M) :
    comp p (p' • q) = p'.comp p • comp p q :=
  by
  rw [comp_apply, map_smul, eval_smul, Polynomial.comp, Polynomial.eval_map, comp_apply]
  rfl
#align polynomial_module.comp_smul PolynomialModule.comp_smul

end PolynomialModule

