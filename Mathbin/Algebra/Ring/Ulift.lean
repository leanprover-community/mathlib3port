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

instance MulZeroClass [MulZeroClass α] : MulZeroClass (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), mul := ·*·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Distrib [Distrib α] : Distrib (Ulift α) := by
  refine_struct { add := ·+·, mul := ·*·, .. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), add := ·+·, mul := ·*·, nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), one := 1, add := ·+·, mul := ·*·, nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance NonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring (Ulift α) := by
  refine_struct { zero := (0 : Ulift α), add := ·+·, mul := ·*·, nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Semiringₓ [Semiringₓ α] : Semiringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := ·+·, mul := ·*·, nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

/-- 
The ring equivalence between `ulift α` and `α`.
-/
def RingEquiv [NonUnitalNonAssocSemiring α] : Ulift α ≃+* α :=
  { toFun := Ulift.down, invFun := Ulift.up, map_mul' := fun x y => rfl, map_add' := fun x y => rfl,
    left_inv := by
      tidy,
    right_inv := by
      tidy }

instance CommSemiringₓ [CommSemiringₓ α] : CommSemiringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := ·+·, mul := ·*·, nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance Ringₓ [Ringₓ α] : Ringₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := ·+·, mul := ·*·, sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance CommRingₓ [CommRingₓ α] : CommRingₓ (Ulift α) := by
  refine_struct
      { zero := (0 : Ulift α), one := 1, add := ·+·, mul := ·*·, sub := Sub.sub, neg := Neg.neg,
        nsmul := AddMonoidₓ.nsmul, npow := Monoidₓ.npow, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

end Ulift

