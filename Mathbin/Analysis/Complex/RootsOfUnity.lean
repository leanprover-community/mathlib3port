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

theorem is_primitive_root_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.coprime n) :
  IsPrimitiveRoot (exp (((2*π)*I)*i / n)) n :=
  by 
    rw [IsPrimitiveRoot.iff_def]
    simp only [←exp_nat_mul, exp_eq_one_iff]
    have hn0 : (n : ℂ) ≠ 0
    ·
      exactModCast h0 
    constructor
    ·
      use i 
      fieldSimp [hn0, mul_commₓ (i : ℂ), mul_commₓ (n : ℂ)]
    ·
      simp' only [hn0, mul_right_commₓ _ _ (↑n), mul_left_inj' two_pi_I_ne_zero, Ne.def, not_false_iff,
        mul_commₓ _ (i : ℂ), ←mul_assocₓ _ (i : ℂ), exists_imp_distrib] with field_simps 
      normCast 
      rintro l k hk 
      have  : n ∣ i*l
      ·
        rw [←Int.coe_nat_dvd, hk]
        apply dvd_mul_left 
      exact hi.symm.dvd_of_dvd_mul_left this

theorem is_primitive_root_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (((2*π)*I) / n)) n :=
  by 
    simpa only [Nat.cast_one, one_div] using is_primitive_root_exp_of_coprime 1 n h0 n.coprime_one_left

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr < » (n : exprℕ()))
theorem is_primitive_root_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
  IsPrimitiveRoot ζ n ↔ ∃ (i : _)(_ : i < (n : ℕ))(hi : i.coprime n), exp (((2*π)*I)*i / n) = ζ :=
  by 
    have hn0 : (n : ℂ) ≠ 0 :=
      by 
        exactModCast hn 
    constructor 
    swap
    ·
      rintro ⟨i, -, hi, rfl⟩
      exact is_primitive_root_exp_of_coprime i n hn hi 
    intro h 
    obtain ⟨i, hi, rfl⟩ := (is_primitive_root_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one (Nat.pos_of_ne_zeroₓ hn)
    refine' ⟨i, hi, ((is_primitive_root_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zeroₓ hn) i).mp h, _⟩
    rw [←exp_nat_mul]
    congr 1
    fieldSimp [hn0, mul_commₓ (i : ℂ)]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr < » (n : exprℕ()))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr < » (n : exprℕ()))
/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `e ^ (2 * real.pi * complex.I * (i / n))` for some `i < n`. -/
theorem mem_roots_of_unity (n : ℕ+) (x : Units ℂ) :
  x ∈ rootsOfUnity n ℂ ↔ ∃ (i : _)(_ : i < (n : ℕ)), exp (((2*π)*I)*i / n) = x :=
  by 
    rw [mem_roots_of_unity, Units.ext_iff, Units.coe_pow, Units.coe_one]
    have hn0 : (n : ℂ) ≠ 0 :=
      by 
        exactModCast n.ne_zero 
    constructor
    ·
      intro h 
      obtain ⟨i, hi, H⟩ : ∃ (i : _)(_ : i < (n : ℕ)), (exp (((2*π)*I) / n)^i) = x
      ·
        simpa only using (is_primitive_root_exp n n.ne_zero).eq_pow_of_pow_eq_one h n.pos 
      refine' ⟨i, hi, _⟩
      rw [←H, ←exp_nat_mul]
      congr 1
      fieldSimp [hn0, mul_commₓ (i : ℂ)]
    ·
      rintro ⟨i, hi, H⟩
      rw [←H, ←exp_nat_mul, exp_eq_one_iff]
      use i 
      fieldSimp [hn0, mul_commₓ ((n : ℕ) : ℂ), mul_commₓ (i : ℂ)]

theorem card_roots_of_unity (n : ℕ+) : Fintype.card (rootsOfUnity n ℂ) = n :=
  (is_primitive_root_exp n n.ne_zero).card_roots_of_unity

theorem card_primitive_roots (k : ℕ) (h : k ≠ 0) : (primitiveRoots k ℂ).card = φ k :=
  (is_primitive_root_exp k h).card_primitive_roots (Nat.pos_of_ne_zeroₓ h)

end Complex

