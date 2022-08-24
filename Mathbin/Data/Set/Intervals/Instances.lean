/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Scott Morrison
-/
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Data.Set.Intervals.ProjIcc

/-!
# Algebraic instances for unit intervals

For suitably structured underlying type `α`, we exhibit the structure of
the unit intervals (`set.Icc`, `set.Ioc`, `set.Ioc`, and `set.Ioo`) from `0` to `1`.

Note: Instances for the interval `Ici 0` are dealt with in `algebra/order/nonneg.lean`.

## Main definitions
The strongest typeclass provided on each interval is:
* `set.Icc.cancel_comm_monoid_with_zero`
* `set.Ico.comm_semigroup`
* `set.Ioc.comm_monoid`
* `set.Ioo.comm_semigroup`

## TODO
* algebraic instances for intervals -1 to 1
* algebraic instances for `Ici 1`
* algebraic instances for `(Ioo (-1) 1)ᶜ`
* provide `has_distrib_neg` instances where applicable
* prove versions of `mul_le_{left,right}` for other intervals
* prove versions of the lemmas in `topology/unit_interval` with `ℝ` generalized to
  some arbitrary ordered semiring

-/


variable {α : Type _} [OrderedSemiring α]

open Set

/-! ### Instances for `↥(set.Icc 0 1)` -/


namespace Set.Icc

instance hasZero : Zero (Icc (0 : α) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩

instance hasOne : One (Icc (0 : α) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩

@[simp, norm_cast]
theorem coe_zero : ↑(0 : Icc (0 : α) 1) = (0 : α) :=
  rfl

@[simp, norm_cast]
theorem coe_one : ↑(1 : Icc (0 : α) 1) = (1 : α) :=
  rfl

@[simp]
theorem mk_zero (h : (0 : α) ∈ Icc (0 : α) 1) : (⟨0, h⟩ : Icc (0 : α) 1) = 0 :=
  rfl

@[simp]
theorem mk_one (h : (1 : α) ∈ Icc (0 : α) 1) : (⟨1, h⟩ : Icc (0 : α) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : Icc (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero {x : Icc (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]
theorem coe_eq_one {x : Icc (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : Icc (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

theorem coe_nonneg (x : Icc (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1

theorem coe_le_one (x : Icc (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Icc (0:α) 1`. -/
theorem nonneg {t : Icc (0 : α) 1} : 0 ≤ t :=
  t.2.1

/-- like `coe_le_one`, but with the inequality in `Icc (0:α) 1`. -/
theorem le_one {t : Icc (0 : α) 1} : t ≤ 1 :=
  t.2.2

instance hasMul :
    Mul (Icc (0 : α) 1) where mul := fun p q => ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩

instance hasPow :
    Pow (Icc (0 : α) 1) ℕ where pow := fun p n => ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Icc (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : Icc (0 : α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) :=
  rfl

theorem mul_le_left {x y : Icc (0 : α) 1} : x * y ≤ x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_oneₓ x)

theorem mul_le_right {x y : Icc (0 : α) 1} : x * y ≤ y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mulₓ y)

instance monoidWithZero : MonoidWithZeroₓ (Icc (0 : α) 1) :=
  Subtype.coe_injective.MonoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance commMonoidWithZero {α : Type _} [OrderedCommSemiring α] : CommMonoidWithZero (Icc (0 : α) 1) :=
  Subtype.coe_injective.CommMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance cancelMonoidWithZero {α : Type _} [OrderedRing α] [NoZeroDivisors α] : CancelMonoidWithZero (Icc (0 : α) 1) :=
  @Function.Injective.cancelMonoidWithZero α _ NoZeroDivisors.toCancelMonoidWithZero _ _ _ _ coe Subtype.coe_injective
    coe_zero coe_one coe_mul coe_pow

instance cancelCommMonoidWithZero {α : Type _} [OrderedCommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero (Icc (0 : α) 1) :=
  @Function.Injective.cancelCommMonoidWithZero α _ NoZeroDivisors.toCancelCommMonoidWithZero _ _ _ _ coe
    Subtype.coe_injective coe_zero coe_one coe_mul coe_pow

variable {β : Type _} [OrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Icc (0 : β) 1) : 1 - t ∈ Icc (0 : β) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

theorem mem_iff_one_sub_mem {t : β} : t ∈ Icc (0 : β) 1 ↔ 1 - t ∈ Icc (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_sub_nonneg (x : Icc (0 : β) 1) : 0 ≤ 1 - (x : β) := by
  simpa using x.2.2

theorem one_sub_le_one (x : Icc (0 : β) 1) : 1 - (x : β) ≤ 1 := by
  simpa using x.2.1

end Set.Icc

/-! ### Instances for `↥(set.Ico 0 1)` -/


namespace Set.Ico

instance hasZero [Nontrivial α] : Zero (Ico (0 : α) 1) where zero := ⟨0, left_mem_Ico.2 zero_lt_one⟩

@[simp, norm_cast]
theorem coe_zero [Nontrivial α] : ↑(0 : Ico (0 : α) 1) = (0 : α) :=
  rfl

@[simp]
theorem mk_zero [Nontrivial α] (h : (0 : α) ∈ Ico (0 : α) 1) : (⟨0, h⟩ : Ico (0 : α) 1) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero [Nontrivial α] {x : Ico (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero [Nontrivial α] {x : Ico (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

theorem coe_nonneg (x : Ico (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1

theorem coe_lt_one (x : Ico (0 : α) 1) : (x : α) < 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Ico (0:α) 1`. -/
theorem nonneg [Nontrivial α] {t : Ico (0 : α) 1} : 0 ≤ t :=
  t.2.1

instance hasMul :
    Mul
      (Ico (0 : α)
        1) where mul := fun p q =>
    ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ico (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

instance semigroup : Semigroupₓ (Ico (0 : α) 1) :=
  Subtype.coe_injective.Semigroup _ coe_mul

instance commSemigroup {α : Type _} [OrderedCommSemiring α] : CommSemigroupₓ (Ico (0 : α) 1) :=
  Subtype.coe_injective.CommSemigroup _ coe_mul

end Set.Ico

/-! ### Instances for `↥(set.Ioc 0 1)` -/


namespace Set.Ioc

instance hasOne [Nontrivial α] : One (Ioc (0 : α) 1) where one := ⟨1, ⟨zero_lt_one, le_reflₓ 1⟩⟩

@[simp, norm_cast]
theorem coe_one [Nontrivial α] : ↑(1 : Ioc (0 : α) 1) = (1 : α) :=
  rfl

@[simp]
theorem mk_one [Nontrivial α] (h : (1 : α) ∈ Ioc (0 : α) 1) : (⟨1, h⟩ : Ioc (0 : α) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one [Nontrivial α] {x : Ioc (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one [Nontrivial α] {x : Ioc (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

theorem coe_pos (x : Ioc (0 : α) 1) : 0 < (x : α) :=
  x.2.1

theorem coe_le_one (x : Ioc (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2

/-- like `coe_le_one`, but with the inequality in `Ioc (0:α) 1`. -/
theorem le_one [Nontrivial α] {t : Ioc (0 : α) 1} : t ≤ 1 :=
  t.2.2

instance hasMul :
    Mul
      (Ioc (0 : α)
        1) where mul := fun p q => ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_ltₓ q.2.1) q.2.2⟩⟩

instance hasPow :
    Pow (Ioc (0 : α) 1) ℕ where pow := fun p n => ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_ltₓ p.2.1) p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ioc (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : Ioc (0 : α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) :=
  rfl

instance semigroup : Semigroupₓ (Ioc (0 : α) 1) :=
  Subtype.coe_injective.Semigroup _ coe_mul

instance monoid [Nontrivial α] : Monoidₓ (Ioc (0 : α) 1) :=
  Subtype.coe_injective.Monoid _ coe_one coe_mul coe_pow

instance cancelMonoid {α : Type _} [OrderedCommRing α] [IsDomain α] : CancelMonoid (Ioc (0 : α) 1) :=
  { Set.Ioc.monoid with
    mul_left_cancel := fun a b c h => Subtype.ext <| mul_left_cancel₀ a.Prop.1.ne' <| (congr_arg Subtype.val h : _),
    mul_right_cancel := fun a b c h => Subtype.ext <| mul_right_cancel₀ b.Prop.1.ne' <| (congr_arg Subtype.val h : _) }

instance commSemigroup {α : Type _} [OrderedCommSemiring α] : CommSemigroupₓ (Ioc (0 : α) 1) :=
  Subtype.coe_injective.CommSemigroup _ coe_mul

instance commMonoid {α : Type _} [OrderedCommSemiring α] [Nontrivial α] : CommMonoidₓ (Ioc (0 : α) 1) :=
  Subtype.coe_injective.CommMonoid _ coe_one coe_mul coe_pow

instance cancelCommMonoid {α : Type _} [OrderedCommRing α] [IsDomain α] : CancelCommMonoid (Ioc (0 : α) 1) :=
  { Set.Ioc.cancelMonoid, Set.Ioc.commMonoid with }

end Set.Ioc

/-! ### Instances for `↥(set.Ioo 0 1)` -/


namespace Set.Ioo

theorem pos (x : Ioo (0 : α) 1) : 0 < (x : α) :=
  x.2.1

theorem lt_one (x : Ioo (0 : α) 1) : (x : α) < 1 :=
  x.2.2

instance hasMul :
    Mul
      (Ioo (0 : α)
        1) where mul := fun p q =>
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : Ioo (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

instance semigroup : Semigroupₓ (Ioo (0 : α) 1) :=
  Subtype.coe_injective.Semigroup _ coe_mul

instance commSemigroup {α : Type _} [OrderedCommSemiring α] : CommSemigroupₓ (Ioo (0 : α) 1) :=
  Subtype.coe_injective.CommSemigroup _ coe_mul

variable {β : Type _} [OrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ Ioo (0 : β) 1) : 1 - t ∈ Ioo (0 : β) 1 := by
  rw [mem_Ioo] at *
  refine' ⟨sub_pos.2 ht.2, _⟩
  exact lt_of_le_of_neₓ ((sub_le_self_iff 1).2 ht.1.le) (mt sub_eq_self.mp ht.1.ne')

theorem mem_iff_one_sub_mem {t : β} : t ∈ Ioo (0 : β) 1 ↔ 1 - t ∈ Ioo (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_minus_pos (x : Ioo (0 : β) 1) : 0 < 1 - (x : β) := by
  simpa using x.2.2

theorem one_minus_lt_one (x : Ioo (0 : β) 1) : 1 - (x : β) < 1 := by
  simpa using x.2.1

end Set.Ioo

