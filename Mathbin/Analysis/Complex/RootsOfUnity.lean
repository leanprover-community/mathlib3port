/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Log
import Mathbin.RingTheory.RootsOfUnity

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `e ^ (2 * real.pi * complex.I * (i / n))` for `i ∈ finset.range n`.

## Main declarations

* `complex.mem_roots_of_unity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`.
* `complex.card_roots_of_unity`: the number of `n`-th roots of unity is exactly `n`.

-/


namespace Complex

open Polynomial Real

open_locale Nat Real

theorem is_primitive_root_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.Coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n := by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast h0
  constructor
  · use i
    field_simp [hn0, mul_comm (i : ℂ), mul_comm (n : ℂ)]
    
  · simp' only [hn0, mul_right_commₓ _ _ ↑n, mul_left_inj' two_pi_I_ne_zero, Ne.def, not_false_iff, mul_comm _ (i : ℂ),
      ← mul_assoc _ (i : ℂ), exists_imp_distrib] with field_simps
    norm_cast
    rintro l k hk
    have : n ∣ i * l := by
      rw [← Int.coe_nat_dvd, hk]
      apply dvd_mul_left
    exact hi.symm.dvd_of_dvd_mul_left this
    

theorem is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n := by
  simpa only [Nat.cast_oneₓ, one_div] using is_primitive_root_exp_of_coprime 1 n h0 n.coprime_one_left

theorem is_primitive_root_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot ζ n ↔ ∃ i < (n : ℕ), ∃ hi : i.Coprime n, exp (2 * π * I * (i / n)) = ζ := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  constructor
  swap
  · rintro ⟨i, -, hi, rfl⟩
    exact is_primitive_root_exp_of_coprime i n hn hi
    
  intro h
  obtain ⟨i, hi, rfl⟩ := (is_primitive_root_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (Nat.pos_of_ne_zeroₓ hn)
  refine' ⟨i, hi, ((is_primitive_root_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zeroₓ hn) i).mp h, _⟩
  rw [← exp_nat_mul]
  congr 1
  field_simp [hn0, mul_comm (i : ℂ)]

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
theorem mem_roots_of_unity (n : ℕ+) (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < (n : ℕ), exp (2 * π * I * (i / n)) = x := by
  rw [mem_roots_of_unity, Units.ext_iff, Units.coe_pow, Units.coe_one]
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast n.ne_zero
  constructor
  · intro h
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / n) ^ i = x := by
      simpa only using (is_primitive_root_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos
    refine' ⟨i, hi, _⟩
    rw [← H, ← exp_nat_mul]
    congr 1
    field_simp [hn0, mul_comm (i : ℂ)]
    
  · rintro ⟨i, hi, H⟩
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    use i
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)]
    

theorem card_roots_of_unity (n : ℕ+) : Fintype.card (rootsOfUnity n ℂ) = n :=
  (is_primitive_root_exp n n.ne_zero).card_roots_of_unity

theorem card_primitive_roots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases' h : k = 0
  · simp [h]
    
  exact (is_primitive_root_exp k h).card_primitive_roots

end Complex

