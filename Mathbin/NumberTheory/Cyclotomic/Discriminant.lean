/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathbin.RingTheory.Discriminant

/-!
# Discriminant of cyclotomic fields
We compute the discriminant of a `p`-th cyclotomic extension.

## Main results
* `is_cyclotomic_extension.discr_odd_prime` : if `p` is an odd prime and
  `is_cyclotomic_extension {p} K L`, then
  `discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` for any primitive `n`-th
  root `ζ`.

## Implementation details
We prove the result for any `K` such that `linear_ordered_field K` and
`irreducible (cyclotomic p K)`. In practice these assumptions are satisfied for `K = ℚ`.

-/


universe u v

variable {p : ℕ+} (k : ℕ) {K : Type u} {L : Type v} {ζ : L} [LinearOrderedField K] [Field L]

variable [Algebra K L] [NeZero ((p : ℕ) : K)]

open Algebra Polynomial Nat IsPrimitiveRoot

namespace IsCyclotomicExtension

attribute [local instance] IsCyclotomicExtension.finite_dimensional

/-- If `p` is an odd prime and `is_cyclotomic_extension {p} K L`, then
`discr K (hζ.power_basis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)`. -/
theorem discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact (p : ℕ).Prime] (hζ : IsPrimitiveRoot ζ p)
    (hirr : Irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
    discr K (hζ.PowerBasis K).Basis = -1 ^ (((p : ℕ) - 1) / 2) * p ^ ((p : ℕ) - 2) := by
  have hodd' : (p : ℕ) ≠ 2 := fun hn => hodd.symm (Pnat.coe_inj.1 hn.symm)
  have hpos := pos_iff_ne_zero.2 fun h => (tsub_pos_of_lt (prime.one_lt hp.out)).Ne.symm h
  rw [discr_power_basis_eq_norm, finrank _ hirr, hζ.power_basis_gen _, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
    totient_prime hp.out]
  congr 1
  · have h := even_sub_one_of_prime_ne_two hp.out hodd'
    rw [← mul_oneₓ 2, ← Nat.div_mul_div (even_iff_two_dvd.1 h) (one_dvd _), Nat.div_oneₓ, mul_oneₓ, mul_comm, pow_mulₓ]
    congr 1
    exact neg_one_pow_of_odd (even.sub_odd (one_le_iff_ne_zero.2 hpos.ne.symm) h (odd_iff.2 rfl))
    
  · have H := congr_argₓ derivative (cyclotomic_prime_mul_X_sub_one K p)
    rw [derivative_mul, derivative_sub, derivative_one, derivative_X, sub_zero, mul_oneₓ, derivative_sub,
      derivative_one, sub_zero, derivative_X_pow] at H
    replace H := congr_argₓ (fun P => aeval ζ P) H
    simp only [hζ.minpoly_eq_cyclotomic_of_irreducible hirr, aeval_add, _root_.map_mul, aeval_one, _root_.map_sub,
      aeval_X, minpoly.aeval, add_zeroₓ, aeval_nat_cast, aeval_X_pow] at H
    replace H := congr_argₓ (Algebra.norm K) H
    rw [MonoidHom.map_mul, hζ.sub_one_norm_prime hirr hodd, MonoidHom.map_mul, MonoidHom.map_pow,
      norm_eq_one K hζ (odd_iff.2 (or_iff_not_imp_left.1 (Nat.Prime.eq_two_or_odd hp.out) hodd')), one_pow, mul_oneₓ, ←
      map_nat_cast (algebraMap K L), norm_algebra_map, finrank _ hirr, totient_prime hp.out, ← succ_pred_eq_of_pos hpos,
      pow_succₓ, mul_comm _ (p : K), coe_coe, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H
    simpa [(mul_right_inj' (cast_ne_zero.2 hp.out.ne_zero : (p : K) ≠ 0)).1 H]
    infer_instance
    
  · infer_instance
    

end IsCyclotomicExtension

