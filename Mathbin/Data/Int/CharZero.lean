import Mathbin.Data.Int.Cast 
import Mathbin.Algebra.CharZero

/-!
# Injectivity of `int.cast` into characteristic zero rings.

-/


variable {α : Type _}

open Nat

namespace Int

@[simp]
theorem cast_eq_zero [AddGroupₓ α] [HasOne α] [CharZero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
  ⟨fun h =>
      by 
        cases n
        ·
          exact congr_argₓ coeₓ (Nat.cast_eq_zero.1 h)
        ·
          rw [cast_neg_succ_of_nat, neg_eq_zero, ←cast_succ, Nat.cast_eq_zero] at h 
          contradiction,
    fun h =>
      by 
        rw [h, cast_zero]⟩

@[simp, normCast]
theorem cast_inj [AddGroupₓ α] [HasOne α] [CharZero α] {m n : ℤ} : (m : α) = n ↔ m = n :=
  by 
    rw [←sub_eq_zero, ←cast_sub, cast_eq_zero, sub_eq_zero]

theorem cast_injective [AddGroupₓ α] [HasOne α] [CharZero α] : Function.Injective (coeₓ : ℤ → α)
| m, n => cast_inj.1

theorem cast_ne_zero [AddGroupₓ α] [HasOne α] [CharZero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

end Int

