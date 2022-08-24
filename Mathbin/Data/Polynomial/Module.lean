/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.Finiteness

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as an type alias `polynomial_module R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `polynomial_module` for details.

-/


universe u v

open Polynomial

open Polynomial BigOperators

variable (R M : Type _) [CommRingₓ R] [AddCommGroupₓ M] [Module R M] (I : Ideal R)

include R

/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `polynomial M` when `M` is a ring.

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
  ℕ →₀ M deriving AddCommGroupₓ, Inhabited

omit R

variable {M}

variable {S : Type _} [CommSemiringₓ S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule

/-- This is required to have the `is_scalar_tower S R M` instance to avoid diamonds. -/
@[nolint unused_arguments]
noncomputable instance : Module S (PolynomialModule R M) :=
  Finsupp.module ℕ M

instance : CoeFun (PolynomialModule R M) fun _ => ℕ → M :=
  Finsupp.hasCoeToFun

/-- The monomial `m * x ^ i`. This is defeq to `finsupp.single_add_hom`, and is redefined here
so that it has the desired type signature.  -/
noncomputable def single (i : ℕ) : M →+ PolynomialModule R M :=
  Finsupp.singleAddHom i

theorem single_apply (i : ℕ) (m : M) (n : ℕ) : single R i m n = ite (i = n) m 0 :=
  Finsupp.single_apply

/-- `polynomial_module.single` as a linear map. -/
noncomputable def lsingle (i : ℕ) : M →ₗ[R] PolynomialModule R M :=
  Finsupp.lsingle i

theorem lsingle_apply (i : ℕ) (m : M) (n : ℕ) : lsingle R i m n = ite (i = n) m 0 :=
  Finsupp.single_apply

theorem single_smul (i : ℕ) (r : R) (m : M) : single R i (r • m) = r • single R i m :=
  (lsingle R i).map_smul r m

variable {R}

theorem induction_linear {P : PolynomialModule R M → Prop} (f : PolynomialModule R M) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsingle : ∀ a b, P (single R a b)) : P f :=
  Finsupp.induction_linear f h0 hadd hsingle

@[semireducible]
noncomputable instance polynomialModule : Module R[X] (PolynomialModule R M) :=
  modulePolynomialOfEndo (Finsupp.lmapDomain _ _ Nat.succ)

instance (M : Type u) [AddCommGroupₓ M] [Module R M] : IsScalarTower R R[X] (PolynomialModule R M) :=
  modulePolynomialOfEndo.is_scalar_tower _

@[simp]
theorem monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) : monomial i r • single R j m = single R (i + j) (r • m) :=
  by
  simp only [LinearMap.mul_apply, Polynomial.aeval_monomial, LinearMap.pow_apply, Module.algebra_map_End_apply,
    module_polynomial_of_endo_smul_def]
  induction i generalizing r j m
  · simp [single]
    
  · rw [Function.iterate_succ, Function.comp_app, Nat.succ_eq_add_one, add_assocₓ, ← i_ih]
    congr 2
    ext a
    dsimp' [single]
    rw [Finsupp.map_domain_single, Nat.succ_eq_one_add]
    

@[simp]
theorem monomial_smul_apply (i : ℕ) (r : R) (g : PolynomialModule R M) (n : ℕ) :
    (monomial i r • g) n = ite (i ≤ n) (r • g (n - i)) 0 := by
  induction' g using PolynomialModule.induction_linear with p q hp hq
  · simp only [smul_zero, Finsupp.zero_apply, if_t_t]
    
  · simp only [smul_add, Finsupp.add_apply, hp, hq]
    split_ifs
    exacts[rfl, zero_addₓ 0]
    
  · rw [monomial_smul_single, single_apply, single_apply, smul_ite, smul_zero, ← ite_and]
    congr
    rw [eq_iff_iff]
    constructor
    · rintro rfl
      simp
      
    · rintro ⟨e, rfl⟩
      rw [add_commₓ, tsub_add_cancel_of_le e]
      
    

@[simp]
theorem smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
    (f • single R i m) n = ite (i ≤ n) (f.coeff (n - i) • m) 0 := by
  induction' f using Polynomial.induction_on' with p q hp hq
  · rw [add_smul, Finsupp.add_apply, hp, hq, coeff_add, add_smul]
    split_ifs
    exacts[rfl, zero_addₓ 0]
    
  · rw [monomial_smul_single, single_apply, coeff_monomial, ite_smul, zero_smul]
    by_cases' h : i ≤ n
    · simp_rw [eq_tsub_iff_add_eq_of_le h, if_pos h]
      
    · rw [if_neg h, ite_eq_right_iff]
      intro e
      exfalso
      linarith
      
    

theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
    (f • g) n = ∑ x in Finset.Nat.antidiagonal n, f.coeff x.1 • g x.2 := by
  induction' f using Polynomial.induction_on' with p q hp hq
  · rw [add_smul, Finsupp.add_apply, hp, hq, ← Finset.sum_add_distrib]
    congr
    ext
    rw [coeff_add, add_smul]
    
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => (monomial f_n f_a).coeff i • g j, monomial_smul_apply]
    dsimp' [monomial]
    simp_rw [Finsupp.single_smul, Finsupp.single_apply]
    rw [Finset.sum_ite_eq]
    simp [Nat.lt_succ_iffₓ]
    

/-- `polynomial R R` is isomorphic to `R[X]` as an `R[X]` module. -/
noncomputable def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] :=
  { (Polynomial.toFinsuppIso R).symm with
    map_smul' := fun r x => by
      induction' r using Polynomial.induction_on' with _ _ _ _ n p
      · simp_all only [add_smul, map_add, RingEquiv.to_fun_eq_coe]
        
      · ext i
        dsimp'
        rw [monomial_smul_apply, Polynomial.monomial_eq_C_mul_X, mul_assoc, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow_mul', mul_ite, mul_zero]
        simp
         }

/-- `polynomial R S` is isomorphic to `S[X]` as an `R` module. -/
noncomputable def equivPolynomial {S : Type _} [CommRingₓ S] [Algebra R S] : PolynomialModule R S ≃ₗ[R] S[X] :=
  { (Polynomial.toFinsuppIso S).symm with map_smul' := fun r x => rfl }

end PolynomialModule

