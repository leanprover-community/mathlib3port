/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Group.Ulift
import Mathbin.Data.Equiv.Ring

/-!
# `ulift` instances for ring

This file defines instances for ring, semiring and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.ring_equiv : ulift R ≃+* R`.
-/


universe u v

variable {α : Type u} {x y : Ulift.{v} α}

namespace Ulift

instance mulZeroClass [MulZeroClassₓ α] : MulZeroClassₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), mul := (· * ·), .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance distrib [Distribₓ α] : Distribₓ (Ulift α) := by
  refine_struct { add := (· + ·), mul := (· * ·), .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiringₓ α] : NonUnitalNonAssocSemiringₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonAssocSemiring [NonAssocSemiringₓ α] : NonAssocSemiringₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), one := 1, add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalSemiring [NonUnitalSemiringₓ α] : NonUnitalSemiringₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance semiring [Semiringₓ α] : Semiringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

/-- The ring equivalence between `ulift α` and `α`.
-/
def ringEquiv [NonUnitalNonAssocSemiringₓ α] : Ulift α ≃+* α where
  toFun := Ulift.down
  invFun := Ulift.up
  map_mul' := fun x y => rfl
  map_add' := fun x y => rfl
  left_inv := by
    tidy
  right_inv := by
    tidy

instance commSemiring [CommSemiringₓ α] : CommSemiringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := (· + ·), mul := (· * ·), nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance ring [Ringₓ α] : Ringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance commRing [CommRingₓ α] : CommRingₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance field [Field α] : Field (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul, inv := Inv.inv, div := Div.div,
        zpow := fun n a => Ulift.up (a.down ^ n), exists_pair_ne := Ulift.nontrivial.1 } <;>
    run_tac
      tactic.pi_instance_derive_field
  -- `mul_inv_cancel` requires special attention: it leaves the goal `∀ {a}, a ≠ 0 → a * a⁻¹ = 1`.
  cases a
  tauto

end Ulift

