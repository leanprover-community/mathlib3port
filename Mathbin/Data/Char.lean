/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.char
! leanprover-community/mathlib commit a59dad53320b73ef180174aae867addd707ef00e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# More `char` instances

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/609
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a `linear_order` instance on `char`. `char` is the type of Unicode scalar values.
-/


instance : LinearOrder Char :=
  { Char.hasLe, Char.hasLt with 
    le_refl := fun a => @le_refl ℕ _ _
    le_trans := fun a b c => @le_trans ℕ _ _ _ _
    le_antisymm := fun a b h₁ h₂ => Char.eq_of_veq <| le_antisymm h₁ h₂
    le_total := fun a b => @le_total ℕ _ _ _
    lt_iff_le_not_le := fun a b => @lt_iff_le_not_le ℕ _ _ _
    decidableLe := Char.decidableLe
    DecidableEq := Char.decidableEq
    decidableLt := Char.decidableLt }

#print Char.ofNat_toNat /-
theorem Char.ofNat_toNat {c : Char} (h : IsValidChar c.toNat) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos h]
  cases c
  simp [Char.toNat]
#align char.of_nat_to_nat Char.ofNat_toNat
-/

