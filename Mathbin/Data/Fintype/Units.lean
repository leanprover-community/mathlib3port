/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.units
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Prod
import Mathbin.Data.Fintype.Sum
import Mathbin.Data.Int.Units

/-!
# fintype instances relating to units
-/


variable {α : Type _}

instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x => by cases Int.units_eq_one_or x <;> simp [*]⟩
#align units_int.fintype UnitsInt.fintype

@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} :=
  rfl
#align units_int.univ UnitsInt.univ

@[simp]
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 :=
  rfl
#align fintype.card_units_int Fintype.card_units_int

instance [Monoid α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

instance [Monoid α] [Finite α] : Finite αˣ :=
  Finite.of_injective _ Units.ext

theorem Fintype.card_units [GroupWithZero α] [Fintype α] [Fintype αˣ] :
    Fintype.card αˣ = Fintype.card α - 1 := by
  classical
    rw [eq_comm, Nat.sub_eq_iff_eq_add (Fintype.card_pos_iff.2 ⟨(0 : α)⟩),
      Fintype.card_congr (unitsEquivNeZero α)]
    have := Fintype.card_congr (Equiv.sumCompl (· = (0 : α))).symm
    rwa [Fintype.card_sum, add_comm, Fintype.card_subtype_eq] at this
#align fintype.card_units Fintype.card_units

