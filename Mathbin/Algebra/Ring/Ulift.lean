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

instance MulZeroClassₓ [MulZeroClassₓ α] : MulZeroClassₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Distribₓ [Distribₓ α] : Distribₓ (Ulift α) := by
  refine_struct { add := · + ·, mul := · * ·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalNonAssocSemiringₓ [NonUnitalNonAssocSemiringₓ α] : NonUnitalNonAssocSemiringₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonAssocSemiringₓ [NonAssocSemiringₓ α] : NonAssocSemiringₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), one := 1, add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalSemiringₓ [NonUnitalSemiringₓ α] : NonUnitalSemiringₓ (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Semiringₓ [Semiringₓ α] : Semiringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

/-- The ring equivalence between `ulift α` and `α`.
-/
def RingEquiv [NonUnitalNonAssocSemiringₓ α] : Ulift α ≃+* α where
  toFun := Ulift.down
  invFun := Ulift.up
  map_mul' := fun x y => rfl
  map_add' := fun x y => rfl
  left_inv := by
    tidy
  right_inv := by
    tidy

instance CommSemiringₓ [CommSemiringₓ α] : CommSemiringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := · + ·, mul := · * ·, nsmul := AddMonoidₓ.nsmul,
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), add := · + ·, mul := · * ·, sub := Sub.sub, neg := Neg.neg, nsmul := AddMonoidₓ.nsmul,
        zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Ringₓ [Ringₓ α] : Ringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := · + ·, mul := · * ·, sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance CommRingₓ [CommRingₓ α] : CommRingₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := · + ·, mul := · * ·, sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

end Ulift

