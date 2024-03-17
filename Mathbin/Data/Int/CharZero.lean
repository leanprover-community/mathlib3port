/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Int.Cast.Field

#align_import data.int.char_zero from "leanprover-community/mathlib"@"29cb56a7b35f72758b05a30490e1f10bd62c35c1"

/-!
# Injectivity of `int.cast` into characteristic zero rings and fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

open Nat

namespace Int

#print Int.cast_eq_zero /-
@[simp]
theorem cast_eq_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
  ⟨fun h => by
    cases n
    · rw [Int.cast_ofNat] at h; exact congr_arg coe (Nat.cast_eq_zero.1 h)
    · rw [cast_neg_succ_of_nat, neg_eq_zero, Nat.cast_eq_zero] at h
      contradiction, fun h => by rw [h, cast_zero]⟩
#align int.cast_eq_zero Int.cast_eq_zero
-/

#print Int.cast_inj /-
@[simp, norm_cast]
theorem cast_inj [AddGroupWithOne α] [CharZero α] {m n : ℤ} : (m : α) = n ↔ m = n := by
  rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]
#align int.cast_inj Int.cast_inj
-/

#print Int.cast_injective /-
theorem cast_injective [AddGroupWithOne α] [CharZero α] : Function.Injective (coe : ℤ → α)
  | m, n => cast_inj.1
#align int.cast_injective Int.cast_injective
-/

#print Int.cast_ne_zero /-
theorem cast_ne_zero [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero
#align int.cast_ne_zero Int.cast_ne_zero
-/

#print Int.cast_eq_one /-
@[simp]
theorem cast_eq_one [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) = 1 ↔ n = 1 := by
  rw [← cast_one, cast_inj]
#align int.cast_eq_one Int.cast_eq_one
-/

#print Int.cast_ne_one /-
theorem cast_ne_one [AddGroupWithOne α] [CharZero α] {n : ℤ} : (n : α) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.Not
#align int.cast_ne_one Int.cast_ne_one
-/

#print Int.cast_div_charZero /-
@[simp, norm_cast]
theorem cast_div_charZero {k : Type _} [DivisionRing k] [CharZero k] {m n : ℤ} (n_dvd : n ∣ m) :
    ((m / n : ℤ) : k) = m / n :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.div_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)
#align int.cast_div_char_zero Int.cast_div_charZero
-/

end Int

#print RingHom.injective_int /-
theorem RingHom.injective_int {α : Type _} [NonAssocRing α] (f : ℤ →+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective
#align ring_hom.injective_int RingHom.injective_int
-/

