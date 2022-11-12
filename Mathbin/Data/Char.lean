/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-!
# More `char` instances

This file provides a `linear_order` instance on `char`. `char` is the type of Unicode scalar values.
-/


instance : LinearOrder Char :=
  { Char.hasLe, Char.hasLt with le_refl := fun a => @le_refl ℕ _ _, le_trans := fun a b c => @le_trans ℕ _ _ _ _,
    le_antisymm := fun a b h₁ h₂ => Char.eq_of_veq <| le_antisymm h₁ h₂, le_total := fun a b => @le_total ℕ _ _ _,
    lt_iff_le_not_le := fun a b => @lt_iff_le_not_le ℕ _ _ _, decidableLe := Char.decidableLe,
    DecidableEq := Char.decidableEq, decidableLt := Char.decidableLt }

theorem Char.of_nat_to_nat {c : Char} (h : IsValidChar c.toNat) : Char.ofNat c.toNat = c := by
  rw [Char.ofNat, dif_pos h]
  cases c
  simp [Char.toNat]
#align char.of_nat_to_nat Char.of_nat_to_nat

