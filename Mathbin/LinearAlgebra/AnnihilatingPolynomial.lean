/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas

! This file was ported from Lean 3 source module linear_algebra.annihilating_polynomial
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.Minpoly
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Annihilating Ideal

Given a commutative ring `R` and an `R`-algebra `A`
Every element `a : A` defines
an ideal `polynomial.ann_ideal a ⊆ R[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(a)` is 0.

## Special case where the ground ring is a field

In the special case that `R` is a field, we use the notation `R = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ polynomial.ann_ideal a`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `a`,
as defined in `field_theory.minpoly`.

## Special case: endomorphism algebra

Given an `R`-module `M` (`[add_comm_group M] [module R M]`)
there are some common specializations which may be more familiar.
* Example 1: `A = M →ₗ[R] M`, the endomorphism algebra of an `R`-module M.
* Example 2: `A = n × n` matrices with entries in `R`.
-/


open Polynomial

namespace Polynomial

section Semiring

variable {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

variable (R)

/-- `ann_ideal R a` is the *annihilating ideal* of all `p : R[X]` such that `p(a) = 0`.

The informal notation `p(a)` stand for `polynomial.aeval a p`.
Again informally, the annihilating ideal of `a` is
`{ p ∈ R[X] | p(a) = 0 }`. This is an ideal in `R[X]`.
The formal definition uses the kernel of the aeval map. -/
noncomputable def annIdeal (a : A) : Ideal R[X] :=
  ((aeval a).toRingHom : R[X] →+* A).ker
#align polynomial.ann_ideal Polynomial.annIdeal

variable {R}

/-- It is useful to refer to ideal membership sometimes
 and the annihilation condition other times. -/
theorem mem_ann_ideal_iff_aeval_eq_zero {a : A} {p : R[X]} : p ∈ annIdeal R a ↔ aeval a p = 0 :=
  Iff.rfl
#align polynomial.mem_ann_ideal_iff_aeval_eq_zero Polynomial.mem_ann_ideal_iff_aeval_eq_zero

end Semiring

section Field

variable {𝕜 A : Type _} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

variable (𝕜)

open Submodule

/-- `ann_ideal_generator 𝕜 a` is the monic generator of `ann_ideal 𝕜 a`
if one exists, otherwise `0`.

Since `𝕜[X]` is a principal ideal domain there is a polynomial `g` such that
 `span 𝕜 {g} = ann_ideal a`. This picks some generator.
 We prefer the monic generator of the ideal. -/
noncomputable def annIdealGenerator (a : A) : 𝕜[X] :=
  let g := is_principal.generator <| annIdeal 𝕜 a
  g * c g.leadingCoeff⁻¹
#align polynomial.ann_ideal_generator Polynomial.annIdealGenerator

section

variable {𝕜}

@[simp]
theorem ann_ideal_generator_eq_zero_iff {a : A} : annIdealGenerator 𝕜 a = 0 ↔ annIdeal 𝕜 a = ⊥ := by
  simp only [ann_ideal_generator, mul_eq_zero, is_principal.eq_bot_iff_generator_eq_zero,
    Polynomial.C_eq_zero, inv_eq_zero, Polynomial.leading_coeff_eq_zero, or_self_iff]
#align polynomial.ann_ideal_generator_eq_zero_iff Polynomial.ann_ideal_generator_eq_zero_iff

end

/-- `ann_ideal_generator 𝕜 a` is indeed a generator. -/
@[simp]
theorem span_singleton_ann_ideal_generator (a : A) :
    Ideal.span {annIdealGenerator 𝕜 a} = annIdeal 𝕜 a := by
  by_cases h : ann_ideal_generator 𝕜 a = 0
  · rw [h, ann_ideal_generator_eq_zero_iff.mp h, Set.singleton_zero, Ideal.span_zero]
  · rw [ann_ideal_generator, Ideal.span_singleton_mul_right_unit, Ideal.span_singleton_generator]
    apply polynomial.is_unit_C.mpr
    apply IsUnit.mk0
    apply inv_eq_zero.not.mpr
    apply polynomial.leading_coeff_eq_zero.not.mpr
    apply (mul_ne_zero_iff.mp h).1
#align polynomial.span_singleton_ann_ideal_generator Polynomial.span_singleton_ann_ideal_generator

/-- The annihilating ideal generator is a member of the annihilating ideal. -/
theorem ann_ideal_generator_mem (a : A) : annIdealGenerator 𝕜 a ∈ annIdeal 𝕜 a :=
  Ideal.mul_mem_right _ _ (Submodule.IsPrincipal.generator_mem _)
#align polynomial.ann_ideal_generator_mem Polynomial.ann_ideal_generator_mem

theorem mem_iff_eq_smul_ann_ideal_generator {p : 𝕜[X]} (a : A) :
    p ∈ annIdeal 𝕜 a ↔ ∃ s : 𝕜[X], p = s • annIdealGenerator 𝕜 a := by
  simp_rw [@eq_comm _ p, ← mem_span_singleton, ← span_singleton_ann_ideal_generator 𝕜 a, Ideal.span]
#align polynomial.mem_iff_eq_smul_ann_ideal_generator Polynomial.mem_iff_eq_smul_ann_ideal_generator

/-- The generator we chose for the annihilating ideal is monic when the ideal is non-zero. -/
theorem monic_ann_ideal_generator (a : A) (hg : annIdealGenerator 𝕜 a ≠ 0) :
    Monic (annIdealGenerator 𝕜 a) :=
  monic_mul_leading_coeff_inv (mul_ne_zero_iff.mp hg).1
#align polynomial.monic_ann_ideal_generator Polynomial.monic_ann_ideal_generator

/-! We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial.

This is the first condition: it must annihilate the original element `a : A`. -/


theorem ann_ideal_generator_aeval_eq_zero (a : A) : aeval a (annIdealGenerator 𝕜 a) = 0 :=
  mem_ann_ideal_iff_aeval_eq_zero.mp (ann_ideal_generator_mem 𝕜 a)
#align polynomial.ann_ideal_generator_aeval_eq_zero Polynomial.ann_ideal_generator_aeval_eq_zero

variable {𝕜}

theorem mem_iff_ann_ideal_generator_dvd {p : 𝕜[X]} {a : A} :
    p ∈ annIdeal 𝕜 a ↔ annIdealGenerator 𝕜 a ∣ p := by
  rw [← Ideal.mem_span_singleton, span_singleton_ann_ideal_generator]
#align polynomial.mem_iff_ann_ideal_generator_dvd Polynomial.mem_iff_ann_ideal_generator_dvd

/-- The generator of the annihilating ideal has minimal degree among
 the non-zero members of the annihilating ideal -/
theorem degree_ann_ideal_generator_le_of_mem (a : A) (p : 𝕜[X]) (hp : p ∈ annIdeal 𝕜 a)
    (hpn0 : p ≠ 0) : degree (annIdealGenerator 𝕜 a) ≤ degree p :=
  degree_le_of_dvd (mem_iff_ann_ideal_generator_dvd.1 hp) hpn0
#align
  polynomial.degree_ann_ideal_generator_le_of_mem Polynomial.degree_ann_ideal_generator_le_of_mem

variable (𝕜)

/-- The generator of the annihilating ideal is the minimal polynomial. -/
theorem ann_ideal_generator_eq_minpoly (a : A) : annIdealGenerator 𝕜 a = minpoly 𝕜 a := by
  by_cases h : ann_ideal_generator 𝕜 a = 0
  · rw [h, minpoly.eq_zero]
    rintro ⟨p, p_monic, hp : aeval a p = 0⟩
    refine' p_monic.ne_zero (ideal.mem_bot.mp _)
    simpa only [ann_ideal_generator_eq_zero_iff.mp h] using mem_ann_ideal_iff_aeval_eq_zero.mpr hp
  ·
    exact
      minpoly.unique _ _ (monic_ann_ideal_generator _ _ h) (ann_ideal_generator_aeval_eq_zero _ _)
        fun q q_monic hq =>
        degree_ann_ideal_generator_le_of_mem a q (mem_ann_ideal_iff_aeval_eq_zero.mpr hq)
          q_monic.NeZero
#align polynomial.ann_ideal_generator_eq_minpoly Polynomial.ann_ideal_generator_eq_minpoly

/-- If a monic generates the annihilating ideal, it must match our choice
 of the annihilating ideal generator. -/
theorem monic_generator_eq_minpoly (a : A) (p : 𝕜[X]) (p_monic : p.Monic)
    (p_gen : Ideal.span {p} = annIdeal 𝕜 a) : annIdealGenerator 𝕜 a = p := by
  by_cases h : p = 0
  · rwa [h, ann_ideal_generator_eq_zero_iff, ← p_gen, ideal.span_singleton_eq_bot.mpr]
  · rw [← span_singleton_ann_ideal_generator, Ideal.span_singleton_eq_span_singleton] at p_gen
    rw [eq_comm]
    apply eq_of_monic_of_associated p_monic _ p_gen
    · apply monic_ann_ideal_generator _ _ ((Associated.ne_zero_iff p_gen).mp h)
#align polynomial.monic_generator_eq_minpoly Polynomial.monic_generator_eq_minpoly

end Field

end Polynomial

