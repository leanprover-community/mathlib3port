/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fintype.Prod
import Data.Fintype.Sum
import Data.Int.Units

#align_import data.fintype.units from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# fintype instances relating to units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

#print UnitsInt.fintype /-
instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x => by cases Int.units_eq_one_or x <;> simp [*]⟩
#align units_int.fintype UnitsInt.fintype
-/

#print UnitsInt.univ /-
@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} :=
  rfl
#align units_int.univ UnitsInt.univ
-/

#print Fintype.card_units_int /-
@[simp]
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 :=
  rfl
#align fintype.card_units_int Fintype.card_units_int
-/

instance [Monoid α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

instance [Monoid α] [Finite α] : Finite αˣ :=
  Finite.of_injective _ Units.ext

#print Fintype.card_units /-
theorem Fintype.card_units [GroupWithZero α] [Fintype α] [Fintype αˣ] :
    Fintype.card αˣ = Fintype.card α - 1 := by classical
#align fintype.card_units Fintype.card_units
-/

