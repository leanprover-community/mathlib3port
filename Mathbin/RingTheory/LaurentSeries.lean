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

noncomputable theory

/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbrev LaurentSeries (R : Type _) [HasZero R] :=
  HahnSeries ℤ R

variable {R : Type _}

namespace LaurentSeries

section Semiringₓ

variable [Semiringₓ R]

instance : Coe (PowerSeries R) (LaurentSeries R) :=
  ⟨HahnSeries.ofPowerSeries ℤ R⟩

theorem coe_power_series (x : PowerSeries R) : (x : LaurentSeries R) = HahnSeries.ofPowerSeries ℤ R x :=
  rfl

@[simp]
theorem coeff_coe_power_series (x : PowerSeries R) (n : ℕ) :
  HahnSeries.coeff (x : LaurentSeries R) n = PowerSeries.coeff R n x :=
  by 
    rw [←Int.nat_cast_eq_coe_nat, coe_power_series, of_power_series_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def power_series_part (x : LaurentSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => x.coeff (x.order+n)

@[simp]
theorem power_series_part_coeff (x : LaurentSeries R) (n : ℕ) :
  PowerSeries.coeff R n x.power_series_part = x.coeff (x.order+n) :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem power_series_part_zero : power_series_part (0 : LaurentSeries R) = 0 :=
  by 
    ext 
    simp 

@[simp]
theorem power_series_part_eq_zero (x : LaurentSeries R) : x.power_series_part = 0 ↔ x = 0 :=
  by 
    split 
    ·
      contrapose! 
      intro h 
      rw [PowerSeries.ext_iff, not_forall]
      refine' ⟨0, _⟩
      simp [coeff_order_ne_zero h]
    ·
      rintro rfl 
      simp 

@[simp]
theorem single_order_mul_power_series_part (x : LaurentSeries R) :
  ((single x.order 1 : LaurentSeries R)*x.power_series_part) = x :=
  by 
    ext n 
    rw [←sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mulₓ]
    byCases' h : x.order ≤ n
    ·
      rw [Int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series, power_series_part_coeff,
        ←Int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), add_sub_cancel'_right]
    ·
      rw [coe_power_series, of_power_series_apply, emb_domain_notin_range]
      ·
        contrapose! h 
        exact order_le_of_coeff_ne_zero h.symm
      ·
        contrapose! h 
        simp only [Set.mem_range, RelEmbedding.coe_fn_mk, Function.Embedding.coe_fn_mk, Int.nat_cast_eq_coe_nat] at h 
        obtain ⟨m, hm⟩ := h 
        rw [←sub_nonneg, ←hm]
        exact Int.zero_le_of_nat _

theorem of_power_series_power_series_part (x : LaurentSeries R) :
  of_power_series ℤ R x.power_series_part = single (-x.order) 1*x :=
  by 
    refine' Eq.trans _ (congr rfl x.single_order_mul_power_series_part)
    rw [←mul_assocₓ, single_mul_single, neg_add_selfₓ, mul_oneₓ, ←C_apply, C_one, one_mulₓ, coe_power_series]

@[simp]
theorem of_power_series_X : of_power_series ℤ R PowerSeries.x = single 1 1 :=
  by 
    ext n 
    cases n
    ·
      rw [Int.of_nat_eq_coe, ←Int.nat_cast_eq_coe_nat, of_power_series_apply_coeff]
      byCases' h1 : n = 1
      ·
        simp [h1]
      ·
        rw [PowerSeries.coeff_X, single_coeff, if_neg h1, if_neg]
        contrapose! h1 
        rw [←Nat.cast_one] at h1 
        exact Nat.cast_injective h1
    ·
      rw [of_power_series_apply, emb_domain_notin_range, single_coeff_of_ne]
      ·
        decide 
      rw [Set.mem_range, not_exists]
      intro m 
      simp only [RelEmbedding.coe_fn_mk, Function.Embedding.coe_fn_mk, Int.nat_cast_eq_coe_nat]
      decide

end Semiringₓ

@[simp]
theorem of_power_series_X_pow [CommSemiringₓ R] (n : ℕ) : of_power_series ℤ R (PowerSeries.x^n) = single (n : ℤ) 1 :=
  by 
    rw [RingHom.map_pow]
    induction' n with n ih
    ·
      rfl 
    rw [pow_succₓ, Int.coe_nat_succ, ih, of_power_series_X, mul_commₓ, single_mul_single, one_mulₓ]

instance [CommSemiringₓ R] : Algebra (PowerSeries R) (LaurentSeries R) :=
  (HahnSeries.ofPowerSeries ℤ R).toAlgebra

@[simp]
theorem coe_algebra_map [CommSemiringₓ R] :
  «expr⇑ » (algebraMap (PowerSeries R) (LaurentSeries R)) = HahnSeries.ofPowerSeries ℤ R :=
  rfl

-- error in RingTheory.LaurentSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The localization map from power series to Laurent series. -/
@[simps #[]]
instance of_power_series_localization
[comm_ring R] : is_localization (submonoid.powers (power_series.X : power_series R)) (laurent_series R) :=
{ map_units := begin
    rintro ["⟨", "_", ",", ident n, ",", ident rfl, "⟩"],
    refine [expr ⟨⟨single (n : exprℤ()) 1, single («expr- »(n) : exprℤ()) 1, _, _⟩, _⟩],
    { simp [] [] ["only"] ["[", expr single_mul_single, ",", expr mul_one, ",", expr add_right_neg, "]"] [] [],
      refl },
    { simp [] [] ["only"] ["[", expr single_mul_single, ",", expr mul_one, ",", expr add_left_neg, "]"] [] [],
      refl },
    { simp [] [] [] [] [] [] }
  end,
  surj := begin
    intro [ident z],
    by_cases [expr h, ":", expr «expr ≤ »(0, z.order)],
    { refine [expr ⟨⟨«expr * »(«expr ^ »(power_series.X, int.nat_abs z.order), power_series_part z), 1⟩, _⟩],
      simp [] [] ["only"] ["[", expr ring_hom.map_one, ",", expr mul_one, ",", expr ring_hom.map_mul, ",", expr coe_algebra_map, ",", expr of_power_series_X_pow, ",", expr submonoid.coe_one, "]"] [] [],
      rw ["[", expr int.nat_abs_of_nonneg h, ",", "<-", expr coe_power_series, ",", expr single_order_mul_power_series_part, "]"] [] },
    { refine [expr ⟨⟨power_series_part z, «expr ^ »(power_series.X, int.nat_abs z.order), ⟨_, rfl⟩⟩, _⟩],
      simp [] [] ["only"] ["[", expr coe_algebra_map, ",", expr of_power_series_power_series_part, "]"] [] [],
      rw ["[", expr mul_comm _ z, "]"] [],
      refine [expr congr rfl _],
      rw ["[", expr subtype.coe_mk, ",", expr of_power_series_X_pow, ",", expr int.of_nat_nat_abs_of_nonpos, "]"] [],
      exact [expr le_of_not_ge h] }
  end,
  eq_iff_exists := begin
    intros [ident x, ident y],
    rw ["[", expr coe_algebra_map, ",", expr of_power_series_injective.eq_iff, "]"] [],
    split,
    { rintro [ident rfl],
      exact [expr ⟨1, rfl⟩] },
    { rintro ["⟨", "⟨", "_", ",", ident n, ",", ident rfl, "⟩", ",", ident hc, "⟩"],
      rw ["[", "<-", expr sub_eq_zero, ",", "<-", expr sub_mul, ",", expr power_series.ext_iff, "]"] ["at", ident hc],
      rw ["[", "<-", expr sub_eq_zero, ",", expr power_series.ext_iff, "]"] [],
      intro [ident m],
      have [ident h] [] [":=", expr hc «expr + »(m, n)],
      rw ["[", expr linear_map.map_zero, ",", expr subtype.coe_mk, ",", expr power_series.X_pow_eq, ",", expr power_series.monomial, ",", expr power_series.coeff, ",", expr finsupp.single_add, ",", expr mv_power_series.coeff_add_mul_monomial, ",", expr mul_one, "]"] ["at", ident h],
      exact [expr h] }
  end }

end LaurentSeries

