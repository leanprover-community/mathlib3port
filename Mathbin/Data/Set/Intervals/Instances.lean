/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Eric Wieser, Yaël Dillies, Patrick Massot, Scott Morrison
-/
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Algebra.Ring.Regular
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


open Set

variable {α : Type _}

section OrderedSemiring

variable [OrderedSemiring α]

/-! ### Instances for `↥(set.Icc 0 1)` -/


namespace Set.IccCat

instance hasZero : Zero (IccCat (0 : α) 1) where zero := ⟨0, left_mem_Icc.2 zero_le_one⟩

instance hasOne : One (IccCat (0 : α) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩

@[simp, norm_cast]
theorem coe_zero : ↑(0 : IccCat (0 : α) 1) = (0 : α) :=
  rfl

@[simp, norm_cast]
theorem coe_one : ↑(1 : IccCat (0 : α) 1) = (1 : α) :=
  rfl

@[simp]
theorem mk_zero (h : (0 : α) ∈ IccCat (0 : α) 1) : (⟨0, h⟩ : IccCat (0 : α) 1) = 0 :=
  rfl

@[simp]
theorem mk_one (h : (1 : α) ∈ IccCat (0 : α) 1) : (⟨1, h⟩ : IccCat (0 : α) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero {x : IccCat (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero {x : IccCat (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

@[simp, norm_cast]
theorem coe_eq_one {x : IccCat (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one {x : IccCat (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

theorem coe_nonneg (x : IccCat (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1

theorem coe_le_one (x : IccCat (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Icc (0:α) 1`. -/
theorem nonneg {t : IccCat (0 : α) 1} : 0 ≤ t :=
  t.2.1

/-- like `coe_le_one`, but with the inequality in `Icc (0:α) 1`. -/
theorem le_one {t : IccCat (0 : α) 1} : t ≤ 1 :=
  t.2.2

instance hasMul :
    Mul (IccCat (0 : α) 1) where mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_le_one p.2.2 q.2.1 q.2.2⟩⟩

instance hasPow : Pow (IccCat (0 : α) 1) ℕ where pow p n := ⟨p.1 ^ n, ⟨pow_nonneg p.2.1 n, pow_le_one n p.2.1 p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : IccCat (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : IccCat (0 : α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) :=
  rfl

theorem mul_le_left {x y : IccCat (0 : α) 1} : x * y ≤ x :=
  (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq (mul_one x)

theorem mul_le_right {x y : IccCat (0 : α) 1} : x * y ≤ y :=
  (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq (one_mul y)

instance monoidWithZero : MonoidWithZero (IccCat (0 : α) 1) :=
  Subtype.coe_injective.MonoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance commMonoidWithZero {α : Type _} [OrderedCommSemiring α] : CommMonoidWithZero (IccCat (0 : α) 1) :=
  Subtype.coe_injective.CommMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

instance cancelMonoidWithZero {α : Type _} [OrderedRing α] [NoZeroDivisors α] :
    CancelMonoidWithZero (IccCat (0 : α) 1) :=
  @Function.Injective.cancelMonoidWithZero α _ NoZeroDivisors.toCancelMonoidWithZero _ _ _ _ coe Subtype.coe_injective
    coe_zero coe_one coe_mul coe_pow

instance cancelCommMonoidWithZero {α : Type _} [OrderedCommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero (IccCat (0 : α) 1) :=
  @Function.Injective.cancelCommMonoidWithZero α _ NoZeroDivisors.toCancelCommMonoidWithZero _ _ _ _ coe
    Subtype.coe_injective coe_zero coe_one coe_mul coe_pow

variable {β : Type _} [OrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ IccCat (0 : β) 1) : 1 - t ∈ IccCat (0 : β) 1 := by
  rw [mem_Icc] at *
  exact ⟨sub_nonneg.2 ht.2, (sub_le_self_iff _).2 ht.1⟩

theorem mem_iff_one_sub_mem {t : β} : t ∈ IccCat (0 : β) 1 ↔ 1 - t ∈ IccCat (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_sub_nonneg (x : IccCat (0 : β) 1) : 0 ≤ 1 - (x : β) := by simpa using x.2.2

theorem one_sub_le_one (x : IccCat (0 : β) 1) : 1 - (x : β) ≤ 1 := by simpa using x.2.1

end Set.IccCat

/-! ### Instances for `↥(set.Ico 0 1)` -/


namespace Set.IcoCat

instance hasZero [Nontrivial α] : Zero (IcoCat (0 : α) 1) where zero := ⟨0, left_mem_Ico.2 zero_lt_one⟩

@[simp, norm_cast]
theorem coe_zero [Nontrivial α] : ↑(0 : IcoCat (0 : α) 1) = (0 : α) :=
  rfl

@[simp]
theorem mk_zero [Nontrivial α] (h : (0 : α) ∈ IcoCat (0 : α) 1) : (⟨0, h⟩ : IcoCat (0 : α) 1) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_zero [Nontrivial α] {x : IcoCat (0 : α) 1} : (x : α) = 0 ↔ x = 0 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_zero [Nontrivial α] {x : IcoCat (0 : α) 1} : (x : α) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero

theorem coe_nonneg (x : IcoCat (0 : α) 1) : 0 ≤ (x : α) :=
  x.2.1

theorem coe_lt_one (x : IcoCat (0 : α) 1) : (x : α) < 1 :=
  x.2.2

/-- like `coe_nonneg`, but with the inequality in `Ico (0:α) 1`. -/
theorem nonneg [Nontrivial α] {t : IcoCat (0 : α) 1} : 0 ≤ t :=
  t.2.1

instance hasMul :
    Mul
      (IcoCat (0 : α)
        1) where mul p q := ⟨p * q, ⟨mul_nonneg p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1 q.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : IcoCat (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

instance semigroup : Semigroup (IcoCat (0 : α) 1) :=
  Subtype.coe_injective.Semigroup _ coe_mul

instance commSemigroup {α : Type _} [OrderedCommSemiring α] : CommSemigroup (IcoCat (0 : α) 1) :=
  Subtype.coe_injective.CommSemigroup _ coe_mul

end Set.IcoCat

end OrderedSemiring

variable [StrictOrderedSemiring α]

/-! ### Instances for `↥(set.Ioc 0 1)` -/


namespace Set.IocCat

instance hasOne [Nontrivial α] : One (IocCat (0 : α) 1) where one := ⟨1, ⟨zero_lt_one, le_refl 1⟩⟩

@[simp, norm_cast]
theorem coe_one [Nontrivial α] : ↑(1 : IocCat (0 : α) 1) = (1 : α) :=
  rfl

@[simp]
theorem mk_one [Nontrivial α] (h : (1 : α) ∈ IocCat (0 : α) 1) : (⟨1, h⟩ : IocCat (0 : α) 1) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_eq_one [Nontrivial α] {x : IocCat (0 : α) 1} : (x : α) = 1 ↔ x = 1 := by
  symm
  exact Subtype.ext_iff

theorem coe_ne_one [Nontrivial α] {x : IocCat (0 : α) 1} : (x : α) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one

theorem coe_pos (x : IocCat (0 : α) 1) : 0 < (x : α) :=
  x.2.1

theorem coe_le_one (x : IocCat (0 : α) 1) : (x : α) ≤ 1 :=
  x.2.2

/-- like `coe_le_one`, but with the inequality in `Ioc (0:α) 1`. -/
theorem le_one [Nontrivial α] {t : IocCat (0 : α) 1} : t ≤ 1 :=
  t.2.2

instance hasMul :
    Mul (IocCat (0 : α) 1) where mul p q := ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_le_one p.2.2 (le_of_lt q.2.1) q.2.2⟩⟩

instance hasPow :
    Pow (IocCat (0 : α) 1) ℕ where pow p n := ⟨p.1 ^ n, ⟨pow_pos p.2.1 n, pow_le_one n (le_of_lt p.2.1) p.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : IocCat (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

@[simp, norm_cast]
theorem coe_pow (x : IocCat (0 : α) 1) (n : ℕ) : ↑(x ^ n) = (x ^ n : α) :=
  rfl

instance semigroup : Semigroup (IocCat (0 : α) 1) :=
  Subtype.coe_injective.Semigroup _ coe_mul

instance monoid [Nontrivial α] : Monoid (IocCat (0 : α) 1) :=
  Subtype.coe_injective.Monoid _ coe_one coe_mul coe_pow

instance commSemigroup {α : Type _} [StrictOrderedCommSemiring α] : CommSemigroup (IocCat (0 : α) 1) :=
  Subtype.coe_injective.CommSemigroup _ coe_mul

instance commMonoid {α : Type _} [StrictOrderedCommSemiring α] [Nontrivial α] : CommMonoid (IocCat (0 : α) 1) :=
  Subtype.coe_injective.CommMonoid _ coe_one coe_mul coe_pow

instance cancelMonoid {α : Type _} [StrictOrderedRing α] [IsDomain α] : CancelMonoid (IocCat (0 : α) 1) :=
  { Set.IocCat.monoid with
    mul_left_cancel := fun a b c h => Subtype.ext <| mul_left_cancel₀ a.Prop.1.ne' <| (congr_arg Subtype.val h : _),
    mul_right_cancel := fun a b c h => Subtype.ext <| mul_right_cancel₀ b.Prop.1.ne' <| (congr_arg Subtype.val h : _) }

instance cancelCommMonoid {α : Type _} [StrictOrderedCommRing α] [IsDomain α] : CancelCommMonoid (IocCat (0 : α) 1) :=
  { Set.IocCat.cancelMonoid, Set.IocCat.commMonoid with }

end Set.IocCat

/-! ### Instances for `↥(set.Ioo 0 1)` -/


namespace Set.IooCat

theorem pos (x : IooCat (0 : α) 1) : 0 < (x : α) :=
  x.2.1

theorem lt_one (x : IooCat (0 : α) 1) : (x : α) < 1 :=
  x.2.2

instance hasMul :
    Mul
      (IooCat (0 : α)
        1) where mul p q :=
    ⟨p.1 * q.1, ⟨mul_pos p.2.1 q.2.1, mul_lt_one_of_nonneg_of_lt_one_right p.2.2.le q.2.1.le q.2.2⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : IooCat (0 : α) 1) : ↑(x * y) = (x * y : α) :=
  rfl

instance semigroup : Semigroup (IooCat (0 : α) 1) :=
  Subtype.coe_injective.Semigroup _ coe_mul

instance commSemigroup {α : Type _} [StrictOrderedCommSemiring α] : CommSemigroup (IooCat (0 : α) 1) :=
  Subtype.coe_injective.CommSemigroup _ coe_mul

variable {β : Type _} [OrderedRing β]

theorem one_sub_mem {t : β} (ht : t ∈ IooCat (0 : β) 1) : 1 - t ∈ IooCat (0 : β) 1 := by
  rw [mem_Ioo] at *
  refine' ⟨sub_pos.2 ht.2, _⟩
  exact lt_of_le_of_ne ((sub_le_self_iff 1).2 ht.1.le) (mt sub_eq_self.mp ht.1.ne')

theorem mem_iff_one_sub_mem {t : β} : t ∈ IooCat (0 : β) 1 ↔ 1 - t ∈ IooCat (0 : β) 1 :=
  ⟨one_sub_mem, fun h => sub_sub_cancel 1 t ▸ one_sub_mem h⟩

theorem one_minus_pos (x : IooCat (0 : β) 1) : 0 < 1 - (x : β) := by simpa using x.2.2

theorem one_minus_lt_one (x : IooCat (0 : β) 1) : 1 - (x : β) < 1 := by simpa using x.2.1

end Set.IooCat

