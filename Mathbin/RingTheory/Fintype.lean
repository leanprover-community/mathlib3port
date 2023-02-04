/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module ring_theory.fintype
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Units

/-!
# Some facts about finite rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Classical

/- warning: card_units_lt -> card_units_lt is a dubious translation:
lean 3 declaration is
  forall (M₀ : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : Fintype.{u1} M₀], LT.lt.{0} Nat Nat.hasLt (Fintype.card.{u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) (Units.fintype.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) _inst_3 (fun (a : M₀) (b : M₀) => Classical.propDecidable (Eq.{succ u1} M₀ a b)))) (Fintype.card.{u1} M₀ _inst_3)
but is expected to have type
  forall (M₀ : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] [_inst_3 : Fintype.{u1} M₀], LT.lt.{0} Nat instLTNat (Fintype.card.{u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) (instFintypeUnits.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) _inst_3 (fun (a : M₀) (b : M₀) => Classical.propDecidable (Eq.{succ u1} M₀ a b)))) (Fintype.card.{u1} M₀ _inst_3)
Case conversion may be inaccurate. Consider using '#align card_units_lt card_units_ltₓ'. -/
theorem card_units_lt (M₀ : Type _) [MonoidWithZero M₀] [Nontrivial M₀] [Fintype M₀] :
    Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_not_mem (coe : M₀ˣ → M₀) Units.ext not_isUnit_zero
#align card_units_lt card_units_lt

