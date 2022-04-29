/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathbin.RingTheory.DedekindDomain.Ideal

/-!
# Adic valuations on Dedekind domains
Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R`.
We prove several properties of this valuation, including the existence of uniformizers.
TODO: extend the valuation to the field of fractions `K` of `R`.

## Main definitions
 - `is_dedekind_domain.height_one_spectrum.int_valuation v` is the `v`-adic valuation on `R`.

## Main results
- `is_dedekind_domain.height_one_spectrum.int_valuation_le_one` : The `v`-adic valuation on `R` is
  bounded above by 1.
- `is_dedekind_domain.height_one_spectrum.int_valuation_lt_one_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`.
- `is_dedekind_domain.height_one_spectrum.int_valuation_le_pow_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than or equal to `multiplicative.of_add (-n)` if and only if `vⁿ` divides the
  ideal `(r)`.
- `is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer` : There exists `π ∈ R`
  with `v`-adic valuation `multiplicative.of_add (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/


noncomputable section

open Classical

open Multiplicative IsDedekindDomain

variable {R : Type _} [CommRingₓ R] [IsDomain R] [IsDedekindDomain R] {K : Type _} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Adic valuations on the Dedekind domain R -/


/-- The additive `v`-adic valuation of `r ∈ R` is the exponent of `v` in the factorization of the
ideal `(r)`, if `r` is nonzero, or infinity, if `r = 0`. `int_valuation_def` is the corresponding
multiplicative valuation. -/
def intValuationDef (r : R) : WithZero (Multiplicative ℤ) :=
  if r = 0 then 0
  else Multiplicative.ofAdd (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)

theorem int_valuation_def_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0 :=
  if_pos hr

theorem int_valuation_def_if_neg {r : R} (hr : r ≠ 0) :
    v.intValuationDef r =
      Multiplicative.ofAdd (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) :=
  if_neg hr

/-- Nonzero elements have nonzero adic valuation. -/
theorem int_valuation_ne_zero (x : R) (hx : x ≠ 0) : v.intValuationDef x ≠ 0 := by
  rw [int_valuation_def, if_neg hx]
  exact WithZero.coe_ne_zero

/-- Nonzero divisors have nonzero valuation. -/
theorem int_valuation_ne_zero' (x : nonZeroDivisors R) : v.intValuationDef x ≠ 0 :=
  v.int_valuation_ne_zero x (nonZeroDivisors.coe_ne_zero x)

/-- Nonzero divisors have valuation greater than zero. -/
theorem int_valuation_zero_le (x : nonZeroDivisors R) : 0 < v.intValuationDef x := by
  rw [v.int_valuation_def_if_neg (nonZeroDivisors.coe_ne_zero x)]
  exact WithZero.zero_lt_coe _

/-- The `v`-adic valuation on `R` is bounded above by 1. -/
theorem int_valuation_le_one (x : R) : v.intValuationDef x ≤ 1 := by
  rw [int_valuation_def]
  by_cases' hx : x = 0
  · rw [if_pos hx]
    exact WithZero.zero_le 1
    
  · rw [if_neg hx, ← WithZero.coe_one, ← of_add_zero, WithZero.coe_le_coe, of_add_le, Right.neg_nonpos_iff]
    exact Int.coe_nat_nonneg _
    

/-- The `v`-adic valuation of `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`. -/
theorem int_valuation_lt_one_iff_dvd (r : R) : v.intValuationDef r < 1 ↔ v.asIdeal ∣ Ideal.span {r} := by
  rw [int_valuation_def]
  split_ifs with hr
  · simpa [hr] using WithZero.zero_lt_coe _
    
  · rw [← WithZero.coe_one, ← of_add_zero, WithZero.coe_lt_coe, of_add_lt, neg_lt_zero, ← Int.coe_nat_zero,
      Int.coe_nat_lt, zero_lt_iff]
    have h : (Ideal.span {r} : Ideal R) ≠ 0 := by
      rw [Ne.def, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hr
    apply
      Associates.count_ne_zero_iff_dvd h
        (by
          apply v.irreducible)
    

/-- The `v`-adic valuation of `r ∈ R` is less than `multiplicative.of_add (-n)` if and only if
`vⁿ` divides the ideal `(r)`. -/
theorem int_valuation_le_pow_iff_dvd (r : R) (n : ℕ) :
    v.intValuationDef r ≤ Multiplicative.ofAdd (-(n : ℤ)) ↔ v.asIdeal ^ n ∣ Ideal.span {r} := by
  rw [int_valuation_def]
  split_ifs with hr
  · simp_rw [hr, Ideal.dvd_span_singleton, zero_le', Submodule.zero_mem]
    
  · rw [WithZero.coe_le_coe, of_add_le, neg_le_neg_iff, Int.coe_nat_le, Ideal.dvd_span_singleton, ←
      Associates.le_singleton_iff,
      Associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hr)
        (by
          apply v.associates_irreducible)]
    

/-- The `v`-adic valuation of `0 : R` equals 0. -/
theorem IntValuation.map_zero' : v.intValuationDef 0 = 0 :=
  v.int_valuation_def_if_pos (Eq.refl 0)

/-- The `v`-adic valuation of `1 : R` equals 1. -/
theorem IntValuation.map_one' : v.intValuationDef 1 = 1 := by
  rw [v.int_valuation_def_if_neg (zero_ne_one.symm : (1 : R) ≠ 0), Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one,
    Associates.count_zero
      (by
        apply v.associates_irreducible),
    Int.coe_nat_zero, neg_zero, of_add_zero, WithZero.coe_one]

/-- The `v`-adic valuation of a product equals the product of the valuations. -/
theorem IntValuation.map_mul' (x y : R) : v.intValuationDef (x * y) = v.intValuationDef x * v.intValuationDef y := by
  simp only [int_valuation_def]
  by_cases' hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
    
  · by_cases' hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
      
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithZero.coe_mul, WithZero.coe_inj, ← of_add_add, ←
        Ideal.span_singleton_mul_span_singleton, ← Associates.mk_mul_mk, ← neg_add,
        Associates.count_mul
          (by
            apply associates.mk_ne_zero'.mpr hx)
          (by
            apply associates.mk_ne_zero'.mpr hy)
          (by
            apply v.associates_irreducible)]
      rfl
      
    

theorem IntValuation.le_max_iff_min_le {a b c : ℕ} :
    Multiplicative.ofAdd (-c : ℤ) ≤ max (Multiplicative.ofAdd (-a : ℤ)) (Multiplicative.ofAdd (-b : ℤ)) ↔ min a b ≤ c :=
  by
  rw [le_max_iff, of_add_le, of_add_le, neg_le_neg_iff, neg_le_neg_iff, Int.coe_nat_le, Int.coe_nat_le, ← min_le_iff]

/-- The `v`-adic valuation of a sum is bounded above by the maximum of the valuations. -/
theorem IntValuation.map_add_le_max' (x y : R) :
    v.intValuationDef (x + y) ≤ max (v.intValuationDef x) (v.intValuationDef y) := by
  by_cases' hx : x = 0
  · rw [hx, zero_addₓ]
    conv_rhs => rw [int_valuation_def, if_pos (Eq.refl _)]
    rw [max_eq_rightₓ (WithZero.zero_le (v.int_valuation_def y))]
    exact le_reflₓ _
    
  · by_cases' hy : y = 0
    · rw [hy, add_zeroₓ]
      conv_rhs => rw [max_commₓ, int_valuation_def, if_pos (Eq.refl _)]
      rw [max_eq_rightₓ (WithZero.zero_le (v.int_valuation_def x))]
      exact le_reflₓ _
      
    · by_cases' hxy : x + y = 0
      · rw [int_valuation_def, if_pos hxy]
        exact zero_le'
        
      · rw [v.int_valuation_def_if_neg hxy, v.int_valuation_def_if_neg hx, v.int_valuation_def_if_neg hy,
          WithZero.le_max_iff, int_valuation.le_max_iff_min_le]
        set nmin :=
          min ((Associates.mk v.as_ideal).count (Associates.mk (Ideal.span {x})).factors)
            ((Associates.mk v.as_ideal).count (Associates.mk (Ideal.span {y})).factors)
        have h_dvd_x : x ∈ v.as_ideal ^ nmin := by
          rw [← Associates.le_singleton_iff x nmin _, Associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hx) _]
          exact min_le_leftₓ _ _
          apply v.associates_irreducible
        have h_dvd_y : y ∈ v.as_ideal ^ nmin := by
          rw [← Associates.le_singleton_iff y nmin _, Associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hy) _]
          exact min_le_rightₓ _ _
          apply v.associates_irreducible
        have h_dvd_xy : Associates.mk v.as_ideal ^ nmin ≤ Associates.mk (Ideal.span {x + y}) := by
          rw [Associates.le_singleton_iff]
          exact Ideal.add_mem (v.as_ideal ^ nmin) h_dvd_x h_dvd_y
        rw [Associates.prime_pow_dvd_iff_le (associates.mk_ne_zero'.mpr hxy) _] at h_dvd_xy
        exact h_dvd_xy
        apply v.associates_irreducible
        
      
    

/-- The `v`-adic valuation on `R`. -/
def intValuation : Valuation R (WithZero (Multiplicative ℤ)) where
  toFun := v.intValuationDef
  map_zero' := IntValuation.map_zero' v
  map_one' := IntValuation.map_one' v
  map_mul' := IntValuation.map_mul' v
  map_add_le_max' := IntValuation.map_add_le_max' v

/-- There exists `π ∈ R` with `v`-adic valuation `multiplicative.of_add (-1)`. -/
theorem int_valuation_exists_uniformizer : ∃ π : R, v.intValuationDef π = Multiplicative.ofAdd (-1 : ℤ) := by
  have hv : _root_.irreducible (Associates.mk v.as_ideal) := v.associates_irreducible
  have hlt : v.as_ideal ^ 2 < v.as_ideal := by
    rw [← Ideal.dvd_not_unit_iff_lt]
    exact ⟨v.ne_bot, v.as_ideal, (not_congr Ideal.is_unit_iff).mpr (Ideal.IsPrime.ne_top v.is_prime), sq v.as_ideal⟩
  obtain ⟨π, mem, nmem⟩ := SetLike.exists_of_lt hlt
  have hπ : Associates.mk (Ideal.span {π}) ≠ 0 := by
    rw [Associates.mk_ne_zero']
    intro h
    rw [h] at nmem
    exact nmem (Submodule.zero_mem (v.as_ideal ^ 2))
  use π
  rw [int_valuation_def, if_neg (associates.mk_ne_zero'.mp hπ), WithZero.coe_inj]
  apply congr_argₓ
  rw [neg_inj, ← Int.coe_nat_one, Int.coe_nat_inj']
  rw [← Ideal.dvd_span_singleton, ← Associates.mk_le_mk_iff_dvd_iff] at mem nmem
  rw [← pow_oneₓ (Associates.mk v.as_ideal), Associates.prime_pow_dvd_iff_le hπ hv] at mem
  rw [Associates.mk_pow, Associates.prime_pow_dvd_iff_le hπ hv, not_leₓ] at nmem
  exact Nat.eq_of_le_of_lt_succ mem nmem

end IsDedekindDomain.HeightOneSpectrum

