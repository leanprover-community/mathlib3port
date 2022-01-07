import Mathbin.RingTheory.HahnSeries
import Mathbin.RingTheory.Localization

/-!
# Laurent Series

## Main Definitions
* Defines `laurent_series` as an abbreviation for `hahn_series ℤ`.
* Provides a coercion `power_series R` into `laurent_series R` given by
  `hahn_series.of_power_series`.
* Defines `laurent_series.power_series_part`
* Defines the localization map `laurent_series.of_power_series_localization` which evaluates to
  `hahn_series.of_power_series`.

-/


open HahnSeries

open_locale BigOperators Classical

noncomputable section

universe u

/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type _) [HasZero R] :=
  HahnSeries ℤ R

variable {R : Type u}

namespace LaurentSeries

section Semiringₓ

variable [Semiringₓ R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

theorem coe_power_series (x : PowerSeries R) : (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl

@[simp]
theorem coeff_coe_power_series (x : PowerSeries R) (n : ℕ) :
    HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x := by
  rw [← Int.nat_cast_eq_coe_nat, coe_power_series, of_power_series_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def power_series_part (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order + n)

@[simp]
theorem power_series_part_coeff (x : LaurentSeries R) (n : ℕ) :
    PowerSeries.coeff R n x.power_series_part = x.coeff (x.order + n) :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem power_series_part_zero : power_series_part (0 : LaurentSeries R) = 0 := by
  ext
  simp

@[simp]
theorem power_series_part_eq_zero (x : LaurentSeries R) : x.power_series_part = 0 ↔ x = 0 := by
  constructor
  · contrapose!
    intro h
    rw [PowerSeries.ext_iff, not_forall]
    refine' ⟨0, _⟩
    simp [coeff_order_ne_zero h]
    
  · rintro rfl
    simp
    

@[simp]
theorem single_order_mul_power_series_part (x : LaurentSeries R) :
    (single x.order 1 : LaurentSeries R) * x.power_series_part = x := by
  ext n
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mulₓ]
  by_cases' h : x.order ≤ n
  · rw [Int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series, power_series_part_coeff, ←
      Int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), add_sub_cancel'_right]
    
  · rw [coe_power_series, of_power_series_apply, emb_domain_notin_range]
    · contrapose! h
      exact order_le_of_coeff_ne_zero h.symm
      
    · contrapose! h
      simp only [Set.mem_range, RelEmbedding.coe_fn_mk, Function.Embedding.coe_fn_mk, Int.nat_cast_eq_coe_nat] at h
      obtain ⟨m, hm⟩ := h
      rw [← sub_nonneg, ← hm]
      exact Int.zero_le_of_nat _
      
    

theorem of_power_series_power_series_part (x : LaurentSeries R) :
    of_power_series ℤ R x.power_series_part = single (-x.order) 1 * x := by
  refine' Eq.trans _ (congr rfl x.single_order_mul_power_series_part)
  rw [← mul_assocₓ, single_mul_single, neg_add_selfₓ, mul_oneₓ, ← C_apply, C_one, one_mulₓ, coe_power_series]

@[simp]
theorem of_power_series_X : of_power_series ℤ R PowerSeries.x = single 1 1 := by
  ext n
  cases n
  · rw [Int.of_nat_eq_coe, ← Int.nat_cast_eq_coe_nat, of_power_series_apply_coeff]
    by_cases' h1 : n = 1
    · simp [h1]
      
    · rw [PowerSeries.coeff_X, single_coeff, if_neg h1, if_neg]
      contrapose! h1
      rw [← Nat.cast_one] at h1
      exact Nat.cast_injective h1
      
    
  · rw [of_power_series_apply, emb_domain_notin_range, single_coeff_of_ne]
    · decide
      
    rw [Set.mem_range, not_exists]
    intro m
    simp only [RelEmbedding.coe_fn_mk, Function.Embedding.coe_fn_mk, Int.nat_cast_eq_coe_nat]
    decide
    

end Semiringₓ

@[simp]
theorem of_power_series_X_pow [CommSemiringₓ R] (n : ℕ) : of_power_series ℤ R (PowerSeries.x ^ n) = single (n : ℤ) 1 :=
  by
  rw [RingHom.map_pow]
  induction' n with n ih
  · rfl
    
  rw [pow_succₓ, Int.coe_nat_succ, ih, of_power_series_X, mul_commₓ, single_mul_single, one_mulₓ]

instance [CommSemiringₓ R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebra_map [CommSemiringₓ R] :
    ⇑algebraMap (PowerSeries R) (LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R :=
  rfl

/-- The localization map from power series to Laurent series. -/
@[simps]
instance of_power_series_localization [CommRingₓ R] :
    IsLocalization (Submonoid.powers (PowerSeries.x : PowerSeries R)) (LaurentSeries R) where
  map_units := by
    rintro ⟨_, n, rfl⟩
    refine' ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩
    · simp only [single_mul_single, mul_oneₓ, add_right_negₓ]
      rfl
      
    · simp only [single_mul_single, mul_oneₓ, add_left_negₓ]
      rfl
      
    · simp
      
  surj := by
    intro z
    by_cases' h : 0 ≤ z.order
    · refine' ⟨⟨PowerSeries.x ^ Int.natAbs z.order * power_series_part z, 1⟩, _⟩
      simp only [RingHom.map_one, mul_oneₓ, RingHom.map_mul, coe_algebra_map, of_power_series_X_pow, Submonoid.coe_one]
      rw [Int.nat_abs_of_nonneg h, ← coe_power_series, single_order_mul_power_series_part]
      
    · refine' ⟨⟨power_series_part z, PowerSeries.x ^ Int.natAbs z.order, ⟨_, rfl⟩⟩, _⟩
      simp only [coe_algebra_map, of_power_series_power_series_part]
      rw [mul_commₓ _ z]
      refine' congr rfl _
      rw [Subtype.coe_mk, of_power_series_X_pow, Int.of_nat_nat_abs_of_nonpos]
      exact le_of_not_geₓ h
      
  eq_iff_exists := by
    intro x y
    rw [coe_algebra_map, of_power_series_injective.eq_iff]
    constructor
    · rintro rfl
      exact ⟨1, rfl⟩
      
    · rintro ⟨⟨_, n, rfl⟩, hc⟩
      rw [← sub_eq_zero, ← sub_mul, PowerSeries.ext_iff] at hc
      rw [← sub_eq_zero, PowerSeries.ext_iff]
      intro m
      have h := hc (m + n)
      rw [LinearMap.map_zero, Subtype.coe_mk, PowerSeries.X_pow_eq, PowerSeries.monomial, PowerSeries.coeff,
        Finsupp.single_add, MvPowerSeries.coeff_add_mul_monomial, mul_oneₓ] at h
      exact h
      

instance {K : Type u} [Field K] : IsFractionRing (PowerSeries K) (LaurentSeries K) :=
  IsLocalization.of_le (Submonoid.powers (PowerSeries.x : PowerSeries K)) _
    (powers_le_non_zero_divisors_of_no_zero_divisors PowerSeries.X_ne_zero) fun f hf =>
    is_unit_of_mem_non_zero_divisors $ RingHom.map_mem_non_zero_divisors _ HahnSeries.of_power_series_injective hf

end LaurentSeries

