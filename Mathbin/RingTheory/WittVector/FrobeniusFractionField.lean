/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.RingTheory.WittVector.DiscreteValuationRing

/-!
# Solving equations about the Frobenius map on the field of fractions of `๐ k`

The goal of this file is to prove `witt_vector.exists_frobenius_solution_fraction_ring`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `ฯ b * a = p ^ m * b`, where `ฯ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `๐ k` directly,
moving to the field of fractions at the end.
See `witt_vector.frobenius_rotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`witt_vector.witt_mul`, `witt_polynomial`) to show that they satisfy the desired equation.

Preliminary work is done in the dependency `ring_theory.witt_vector.mul_coeff`
to isolate the `n+1`st coefficients of `x` and `y` in the `n+1`st coefficient of `x*y`.

This construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].
We approximately follow an approach sketched on MathOverflow:
<https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors>

The result is a dependency for the proof of `witt_vector.isocrystal_classification`,
the classification of one-dimensional isocrystals over an algebraically closed field.
-/


noncomputable section

namespace WittVector

variable (p : โ) [hp : Fact p.Prime]

-- mathport name: ยซexpr๐ยป
local notation "๐" => WittVector p

namespace RecursionMain

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `witt_poly_prod n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.

-/


section CommRingโ

include hp

variable {k : Type _} [CommRingโ k] [CharP k p]

open Polynomial

/-- The root of this polynomial determines the `n+1`st coefficient of our solution. -/
def succNthDefiningPoly (n : โ) (aโ aโ : ๐ k) (bs : Finโ (n + 1) โ k) : Polynomial k :=
  X ^ p * c (aโ.coeff 0 ^ p ^ (n + 1)) - X * c (aโ.coeff 0 ^ p ^ (n + 1)) +
    c
      (aโ.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) + nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) aโ) -
          aโ.coeff (n + 1) * bs 0 ^ p ^ (n + 1) -
        nthRemainder p n bs (truncateFun (n + 1) aโ))

theorem succ_nth_defining_poly_degree [IsDomain k] (n : โ) (aโ aโ : ๐ k) (bs : Finโ (n + 1) โ k) (haโ : aโ.coeff 0 โ? 0)
    (haโ : aโ.coeff 0 โ? 0) : (succNthDefiningPoly p n aโ aโ bs).degree = p := by
  have : (X ^ p * C (aโ.coeff 0 ^ p ^ (n + 1))).degree = p := by
    rw [degree_mul, degree_C]
    ยท simp only [โ Nat.cast_with_bot, โ add_zeroโ, โ degree_X, โ degree_pow, โ Nat.smul_one_eq_coe]
      
    ยท exact pow_ne_zero _ haโ
      
  have : (X ^ p * C (aโ.coeff 0 ^ p ^ (n + 1)) - X * C (aโ.coeff 0 ^ p ^ (n + 1))).degree = p := by
    rw [degree_sub_eq_left_of_degree_lt, this]
    rw [this, degree_mul, degree_C, degree_X, add_zeroโ]
    ยท exact_mod_cast hp.out.one_lt
      
    ยท exact pow_ne_zero _ haโ
      
  rw [succ_nth_defining_poly, degree_add_eq_left_of_degree_lt, this]
  apply lt_of_le_of_ltโ degree_C_le
  rw [this]
  exact_mod_cast hp.out.pos

end CommRingโ

section IsAlgClosed

include hp

variable {k : Type _} [Field k] [CharP k p] [IsAlgClosed k]

theorem root_exists (n : โ) (aโ aโ : ๐ k) (bs : Finโ (n + 1) โ k) (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) :
    โ b : k, (succNthDefiningPoly p n aโ aโ bs).IsRoot b :=
  IsAlgClosed.exists_root _ <| by
    simp [โ succ_nth_defining_poly_degree p n aโ aโ bs haโ haโ, โ hp.out.ne_zero]

/-- This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/
def succNthVal (n : โ) (aโ aโ : ๐ k) (bs : Finโ (n + 1) โ k) (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) : k :=
  Classical.some (root_exists p n aโ aโ bs haโ haโ)

theorem succ_nth_val_spec (n : โ) (aโ aโ : ๐ k) (bs : Finโ (n + 1) โ k) (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) :
    (succNthDefiningPoly p n aโ aโ bs).IsRoot (succNthVal p n aโ aโ bs haโ haโ) :=
  Classical.some_spec (root_exists p n aโ aโ bs haโ haโ)

theorem succ_nth_val_spec' (n : โ) (aโ aโ : ๐ k) (bs : Finโ (n + 1) โ k) (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) :
    succNthVal p n aโ aโ bs haโ haโ ^ p * aโ.coeff 0 ^ p ^ (n + 1) + aโ.coeff (n + 1) * (bs 0 ^ p) ^ p ^ (n + 1) +
        nthRemainder p n (fun v => bs v ^ p) (truncateFun (n + 1) aโ) =
      succNthVal p n aโ aโ bs haโ haโ * aโ.coeff 0 ^ p ^ (n + 1) + aโ.coeff (n + 1) * bs 0 ^ p ^ (n + 1) +
        nthRemainder p n bs (truncateFun (n + 1) aโ) :=
  by
  rw [โ sub_eq_zero]
  have := succ_nth_val_spec p n aโ aโ bs haโ haโ
  simp only [โ Polynomial.map_add, โ Polynomial.eval_X, โ Polynomial.map_pow, โ Polynomial.eval_C, โ
    Polynomial.eval_pow, โ succ_nth_defining_poly, โ Polynomial.eval_mul, โ Polynomial.eval_add, โ Polynomial.eval_sub,
    โ Polynomial.map_mul, โ Polynomial.map_sub, โ Polynomial.IsRoot.def] at this
  convert this using 1
  ring

end IsAlgClosed

end RecursionMain

namespace RecursionBase

include hp

variable {k : Type _} [Field k] [IsAlgClosed k]

theorem solution_pow (aโ aโ : ๐ k) : โ x : k, x ^ (p - 1) = aโ.coeff 0 / aโ.coeff 0 :=
  IsAlgClosed.exists_pow_nat_eq _ <| by
    linarith [hp.out.one_lt, le_of_ltโ hp.out.one_lt]

/-- The base case (0th coefficient) of our solution vector. -/
def solution (aโ aโ : ๐ k) : k :=
  Classical.some <| solution_pow p aโ aโ

theorem solution_spec (aโ aโ : ๐ k) : solution p aโ aโ ^ (p - 1) = aโ.coeff 0 / aโ.coeff 0 :=
  Classical.some_spec <| solution_pow p aโ aโ

theorem solution_nonzero {aโ aโ : ๐ k} (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) : solution p aโ aโ โ? 0 := by
  intro h
  have := solution_spec p aโ aโ
  rw [h, zero_pow] at this
  ยท simpa [โ haโ, โ haโ] using _root_.div_eq_zero_iff.mp this.symm
    
  ยท linarith [hp.out.one_lt, le_of_ltโ hp.out.one_lt]
    

theorem solution_spec' {aโ : ๐ k} (haโ : aโ.coeff 0 โ? 0) (aโ : ๐ k) :
    solution p aโ aโ ^ p * aโ.coeff 0 = solution p aโ aโ * aโ.coeff 0 := by
  have := solution_spec p aโ aโ
  cases' Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero with q hq
  have hq' : q = p - 1 := by
    simp only [โ hq, โ tsub_zero, โ Nat.succ_sub_succ_eq_sub]
  conv_lhs => congr congr skip rw [hq]
  rw [pow_succ'โ, hq', this]
  field_simp [โ haโ, โ mul_comm]

end RecursionBase

open RecursionMain RecursionBase

section FrobeniusRotation

section IsAlgClosed

include hp

variable {k : Type _} [Field k] [CharP k p] [IsAlgClosed k]

/-- Recursively defines the sequence of coefficients for `witt_vector.frobenius_rotation`.
-/
noncomputable def frobeniusRotationCoeff {aโ aโ : ๐ k} (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) : โ โ k
  | 0 => solution p aโ aโ
  | n + 1 => succNthVal p n aโ aโ (fun i => frobenius_rotation_coeff i.val) haโ haโ

/-- For nonzero `aโ` and `aโ`, `frobenius_rotation aโ aโ` is a Witt vector that satisfies the
equation `frobenius (frobenius_rotation aโ aโ) * aโ = (frobenius_rotation aโ aโ) * aโ`.
-/
def frobeniusRotation {aโ aโ : ๐ k} (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) : ๐ k :=
  WittVector.mk p (frobeniusRotationCoeff p haโ haโ)

theorem frobenius_rotation_nonzero {aโ aโ : ๐ k} (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) :
    frobeniusRotation p haโ haโ โ? 0 := by
  intro h
  apply solution_nonzero p haโ haโ
  simpa [h, โ frobenius_rotation, โ frobenius_rotation_coeff] using WittVector.zero_coeff p k 0

theorem frobenius_frobenius_rotation {aโ aโ : ๐ k} (haโ : aโ.coeff 0 โ? 0) (haโ : aโ.coeff 0 โ? 0) :
    frobenius (frobeniusRotation p haโ haโ) * aโ = frobeniusRotation p haโ haโ * aโ := by
  ext n
  induction' n with n ih
  ยท simp only [โ WittVector.mul_coeff_zero, โ WittVector.coeff_frobenius_char_p, โ frobenius_rotation, โ
      frobenius_rotation_coeff]
    apply solution_spec' _ haโ
    
  ยท simp only [โ nth_remainder_spec, โ WittVector.coeff_frobenius_char_p, โ frobenius_rotation_coeff, โ
      frobenius_rotation, โ Finโ.val_eq_coe]
    have := succ_nth_val_spec' p n aโ aโ (fun i : Finโ (n + 1) => frobenius_rotation_coeff p haโ haโ i.val) haโ haโ
    simp only [โ frobenius_rotation_coeff, โ Finโ.val_eq_coe, โ Finโ.val_zero] at this
    convert this using 4
    apply TruncatedWittVector.ext
    intro i
    simp only [โ Finโ.val_eq_coe, โ WittVector.coeff_truncate_fun, โ WittVector.coeff_frobenius_char_p]
    rfl
    

-- mathport name: ยซexprฯยป
local notation "ฯ" => IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k)

theorem exists_frobenius_solution_fraction_ring_aux (m n : โ) (r' q' : ๐ k) (hr' : r'.coeff 0 โ? 0)
    (hq' : q'.coeff 0 โ? 0) (hq : โp ^ n * q' โ nonZeroDivisors (๐ k)) :
    let b : ๐ k := frobeniusRotation p hr' hq'
    IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k) (algebraMap (๐ k) (FractionRing (๐ k)) b) *
        Localization.mk (โp ^ m * r') โจโp ^ n * q', hqโฉ =
      โp ^ (m - n : โค) * algebraMap (๐ k) (FractionRing (๐ k)) b :=
  by
  intro b
  have key : WittVector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q') := by
    have H := congr_arg (fun x : ๐ k => x * p ^ m * p ^ n) (frobenius_frobenius_rotation p hr' hq')
    dsimp'  at H
    refine' (Eq.trans _ H).trans _ <;> ring
  have hq'' : algebraMap (๐ k) (FractionRing (๐ k)) q' โ? 0 := by
    have hq''' : q' โ? 0 := fun h =>
      hq'
        (by
          simp [โ h])
    simpa only [โ Ne.def, โ map_zero] using (IsFractionRing.injective (๐ k) (FractionRing (๐ k))).Ne hq'''
  rw [zpow_subโ (fraction_ring.p_nonzero p k)]
  field_simp [โ fraction_ring.p_nonzero p k]
  simp only [โ IsFractionRing.fieldEquivOfRingEquiv, โ IsLocalization.ring_equiv_of_ring_equiv_eq, โ
    RingEquiv.coe_of_bijective]
  convert congr_arg (fun x => algebraMap (๐ k) (FractionRing (๐ k)) x) key using 1
  ยท simp only [โ RingHom.map_mul, โ RingHom.map_pow, โ map_nat_cast, โ frobenius_equiv_apply]
    ring
    
  ยท simp only [โ RingHom.map_mul, โ RingHom.map_pow, โ map_nat_cast]
    

theorem exists_frobenius_solution_fraction_ring {a : FractionRing (๐ k)} (ha : a โ? 0) :
    โ (b : FractionRing (๐ k))(hb : b โ? 0)(m : โค), ฯ b * a = p ^ m * b := by
  revert ha
  refine' Localization.induction_on a _
  rintro โจr, q, hqโฉ hrq
  have hq0 : q โ? 0 := mem_non_zero_divisors_iff_ne_zero.1 hq
  have hr0 : r โ? 0 := fun h =>
    hrq
      (by
        simp [โ h])
  obtain โจm, r', hr', rflโฉ := exists_eq_pow_p_mul r hr0
  obtain โจn, q', hq', rflโฉ := exists_eq_pow_p_mul q hq0
  let b := frobenius_rotation p hr' hq'
  refine' โจalgebraMap (๐ k) _ b, _, m - n, _โฉ
  ยท simpa only [โ map_zero] using
      (IsFractionRing.injective (WittVector p k) (FractionRing (WittVector p k))).Ne
        (frobenius_rotation_nonzero p hr' hq')
    
  exact exists_frobenius_solution_fraction_ring_aux p m n r' q' hr' hq' hq

end IsAlgClosed

end FrobeniusRotation

end WittVector

