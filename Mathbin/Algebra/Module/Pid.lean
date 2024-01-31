/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Algebra.Module.DedekindDomain
import LinearAlgebra.FreeModule.Pid
import Algebra.Module.Projective
import Algebra.Category.Module.Biproducts

#align_import algebra.module.pid from "leanprover-community/mathlib"@"1a51edf13debfcbe223fa06b1cb353b9ed9751cc"

/-!
# Structure of finitely generated modules over a PID

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main statements

* `module.equiv_direct_sum_of_is_torsion` : A finitely generated torsion module over a PID is
  isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
* `module.equiv_free_prod_direct_sum` : A finitely generated module over a PID is isomorphic to the
  product of a free module (its torsion free part) and a direct sum of the form above (its torsion
  submodule).

## Notation

* `R` is a PID and `M` is a (finitely generated for main statements) `R`-module, with additional
  torsion hypotheses in the intermediate lemmas.
* `N` is a `R`-module lying over a higher type universe than `R`. This assumption is needed on the
  final statement for technical reasons.
* `p` is an irreducible element of `R` or a tuple of these.

## Implementation details

We first prove (`submodule.is_internal_prime_power_torsion_of_pid`) that a finitely generated
torsion module is the internal direct sum of its `p i ^ e i`-torsion submodules for some
(finitely many) prime powers `p i ^ e i`. This is proved in more generality for a Dedekind domain
at `submodule.is_internal_prime_power_torsion`.

Then we treat the case of a `p ^ ∞`-torsion module (that is, a module where all elements are
cancelled by scalar multiplication by some power of `p`) and apply it to the `p i ^ e i`-torsion
submodules (that are `p i ^ ∞`-torsion) to get the result for torsion modules.

Then we get the general result using that a torsion free module is free (which has been proved at
`module.free_of_finite_type_torsion_free'` at `linear_algebra/free_module/pid.lean`.)

## Tags

Finitely generated module, principal ideal domain, classification, structure theorem
-/


universe u v

open scoped BigOperators Classical

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {N : Type max u v} [AddCommGroup N] [Module R N]

open scoped DirectSum

open Submodule

open UniqueFactorizationMonoid

#print Submodule.isInternal_prime_power_torsion_of_pid /-
/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.-/
theorem Submodule.isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBy R M
        (IsPrincipal.generator (p : Ideal R) ^ (factors (⊤ : Submodule R M).annihilator).count p) :=
  by
  convert is_internal_prime_power_torsion hM
  ext p : 1
  rw [← torsion_by_span_singleton_eq, Ideal.submodule_span_eq, ← Ideal.span_singleton_pow,
    Ideal.span_singleton_generator]
#align submodule.is_internal_prime_power_torsion_of_pid Submodule.isInternal_prime_power_torsion_of_pid
-/

#print Submodule.exists_isInternal_prime_power_torsion_of_pid /-
/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.-/
theorem Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (h : ∀ i, Irreducible <| p i) (e
      : ι → ℕ), DirectSum.IsInternal fun i => torsion_by R M <| p i ^ e i :=
  by
  refine' ⟨_, _, _, _, _, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  exact Finset.fintypeCoeSort _
  · rintro ⟨p, hp⟩
    have hP := prime_of_factor p (multiset.mem_to_finset.mp hp)
    haveI := Ideal.isPrime_of_prime hP
    exact (is_principal.prime_generator_of_is_prime p hP.ne_zero).Irreducible
#align submodule.exists_is_internal_prime_power_torsion_of_pid Submodule.exists_isInternal_prime_power_torsion_of_pid
-/

namespace Module

section PTorsion

variable {p : R} (hp : Irreducible p) (hM : Module.IsTorsion' M (Submonoid.powers p))

variable [dec : ∀ x : M, Decidable (x = 0)]

open Ideal Submodule.IsPrincipal

#print Ideal.torsionOf_eq_span_pow_pOrder /-
theorem Ideal.torsionOf_eq_span_pow_pOrder (x : M) : torsionOf R M x = span {p ^ pOrder hM x} :=
  by
  dsimp only [p_order]
  rw [← (torsion_of R M x).span_singleton_generator, Ideal.span_singleton_eq_span_singleton, ←
    Associates.mk_eq_mk_iff_associated, Associates.mk_pow]
  have prop :
    (fun n : ℕ => p ^ n • x = 0) = fun n : ℕ =>
      (Associates.mk <| generator <| torsion_of R M x) ∣ Associates.mk p ^ n :=
    by ext n; rw [← Associates.mk_pow, Associates.mk_dvd_mk, ← mem_iff_generator_dvd]; rfl
  have := (is_torsion'_powers_iff p).mp hM x; rw [prop] at this 
  classical
#align ideal.torsion_of_eq_span_pow_p_order Ideal.torsionOf_eq_span_pow_pOrder
-/

#print Module.p_pow_smul_lift /-
theorem p_pow_smul_lift {x y : M} {k : ℕ} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
    (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y :=
  by
  by_cases hk : k ≤ p_order hM y
  · let f :=
      ((R ∙ p ^ (p_order hM y - k) * p ^ k).quotEquivOfEq _ _).trans
        (quot_torsion_of_equiv_span_singleton R M y)
    have :
      f.symm ⟨p ^ k • x, h⟩ ∈ R ∙ Ideal.Quotient.mk (R ∙ p ^ (p_order hM y - k) * p ^ k) (p ^ k) :=
      by
      rw [← quotient.torsion_by_eq_span_singleton, mem_torsion_by_iff, ← f.symm.map_smul]
      convert f.symm.map_zero; ext
      rw [coe_smul_of_tower, coe_mk, coe_zero, smul_smul, ← pow_add, Nat.sub_add_cancel hk, @hM' x]
      · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp.ne_zero)
    rw [Submodule.mem_span_singleton] at this ; obtain ⟨a, ha⟩ := this; use a
    rw [f.eq_symm_apply, ← Ideal.Quotient.mk_eq_mk, ← quotient.mk_smul] at ha 
    dsimp only [smul_eq_mul, f, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      quot_torsion_of_equiv_span_singleton_apply_mk] at ha 
    rw [smul_smul, mul_comm]; exact congr_arg coe ha.symm
    · symm; convert Ideal.torsionOf_eq_span_pow_pOrder hp hM y
      rw [← pow_add, Nat.sub_add_cancel hk]
  · use 0;
    rw [zero_smul, smul_zero, ← Nat.sub_add_cancel (le_of_not_le hk), pow_add, mul_smul, hM',
      smul_zero]
#align module.p_pow_smul_lift Module.p_pow_smul_lift
-/

open Submodule.Quotient

#print Module.exists_smul_eq_zero_and_mk_eq /-
theorem exists_smul_eq_zero_and_mk_eq {z : M} (hz : Module.IsTorsionBy R M (p ^ pOrder hM z))
    {k : ℕ} (f : (R ⧸ R ∙ p ^ k) →ₗ[R] M ⧸ R ∙ z) :
    ∃ x : M, p ^ k • x = 0 ∧ Submodule.Quotient.mk x = f 1 :=
  by
  have f1 := mk_surjective (R ∙ z) (f 1)
  have : p ^ k • f1.some ∈ R ∙ z :=
    by
    rw [← quotient.mk_eq_zero, mk_smul, f1.some_spec, ← f.map_smul]
    convert f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul, quotient.mk_eq_zero, Algebra.id.smul_eq_mul, mul_one]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := p_pow_smul_lift hp hM hz this
  refine' ⟨f1.some - a • z, by rw [smul_sub, sub_eq_zero, ha], _⟩
  rw [mk_sub, mk_smul, (quotient.mk_eq_zero _).mpr <| Submodule.mem_span_singleton_self _,
    smul_zero, sub_zero, f1.some_spec]
#align module.exists_smul_eq_zero_and_mk_eq Module.exists_smul_eq_zero_and_mk_eq
-/

open Finset Multiset

#print Module.torsion_by_prime_power_decomposition /-
/-- A finitely generated `p ^ ∞`-torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p ^ e i)` for some `e i`.-/
theorem torsion_by_prime_power_decomposition (hN : Module.IsTorsion' N (Submonoid.powers p))
    [h' : Module.Finite R N] :
    ∃ (d : ℕ) (k : Fin d → ℕ), Nonempty <| N ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ (k i : ℕ) :=
  by
  obtain ⟨d, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ h'; use d; clear h'
  induction' d with d IH generalizing N
  · use fun i => finZeroElim i
    rw [Set.range_eq_empty, Submodule.span_empty] at hs 
    haveI : Unique N := ⟨⟨0⟩, fun x => by rw [← mem_bot _, hs]; trivial⟩
    exact ⟨0⟩
  · have : ∀ x : N, Decidable (x = 0)
    classical
#align module.torsion_by_prime_power_decomposition Module.torsion_by_prime_power_decomposition
-/

end PTorsion

#print Module.equiv_directSum_of_isTorsion /-
/-- A finitely generated torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.-/
theorem equiv_directSum_of_isTorsion [h' : Module.Finite R N] (hN : Module.IsTorsion R N) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R) (h : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| N ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i :=
  by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hN
  haveI := fI
  have :
    ∀ i,
      ∃ (d : ℕ) (k : Fin d → ℕ),
        Nonempty <| torsion_by R N (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j :=
    by
    haveI := isNoetherian_of_isNoetherianRing_of_finite (module.finite_def.mp h')
    haveI := fun i => isNoetherian_submodule' (torsion_by R N <| p i ^ e i)
    exact fun i =>
      torsion_by_prime_power_decomposition (hp i)
        ((is_torsion'_powers_iff <| p i).mpr fun x => ⟨e i, smul_torsion_by _ _⟩)
  classical
#align module.equiv_direct_sum_of_is_torsion Module.equiv_directSum_of_isTorsion
-/

#print Module.equiv_free_prod_directSum /-
/-- **Structure theorem of finitely generated modules over a PID** : A finitely generated
  module over a PID is isomorphic to the product of a free module and a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.-/
theorem equiv_free_prod_directSum [h' : Module.Finite R N] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (h : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| N ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i :=
  by
  haveI := isNoetherian_of_isNoetherianRing_of_finite (module.finite_def.mp h')
  haveI := isNoetherian_submodule' (torsion R N)
  haveI := Module.Finite.of_surjective _ (torsion R N).mkQ_surjective
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ := equiv_direct_sum_of_is_torsion (@torsion_is_torsion R N _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ _ _ (N ⧸ torsion R N) _ _ _ _
  haveI : Module.Projective R (N ⧸ torsion R N) := Module.Projective.of_basis ⟨g⟩
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R N).mkQ_surjective
  refine'
    ⟨n, I, fI, p, hp, e,
      ⟨(lequivProdOfRightSplitExact (torsion R N).injective_subtype _ hf).symm.trans <|
          (h.prod g).trans <| LinearEquiv.prodComm R _ _⟩⟩
  rw [range_subtype, ker_mkq]
#align module.equiv_free_prod_direct_sum Module.equiv_free_prod_directSum
-/

end Module

