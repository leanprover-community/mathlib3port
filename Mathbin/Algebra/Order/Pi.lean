/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Order.Group
import Mathbin.Tactic.PiInstances

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      "The product of a family of ordered additive commutative monoids is\n  an ordered additive commutative monoid."]
instance orderedCommMonoid {ι : Type _} {Z : ι → Type _} [∀ i, OrderedCommMonoid (Z i)] :
    OrderedCommMonoid (∀ i, Z i) :=
  { Pi.partialOrder, Pi.commMonoid with mul_le_mul_left := fun f g w h i => mul_le_mul_left' (w i) _ }

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      "The product of a family of canonically ordered additive monoids is\n  a canonically ordered additive monoid."]
instance {ι : Type _} {Z : ι → Type _} [∀ i, CanonicallyOrderedMonoid (Z i)] : CanonicallyOrderedMonoid (∀ i, Z i) :=
  { Pi.orderBot, Pi.orderedCommMonoid with
    le_iff_exists_mul := fun f g => by
      fconstructor
      · intro w
        fconstructor
        · exact fun i => (le_iff_exists_mul.mp (w i)).some
          
        · ext i
          exact (le_iff_exists_mul.mp (w i)).some_spec
          
        
      · rintro ⟨h, rfl⟩
        exact fun i => le_mul_right le_rfl
         }

@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid <| f i] : OrderedCancelCommMonoid (∀ i : I, f i) := by
  refine_struct
      { Pi.partialOrder, Pi.monoid with mul := (· * ·), one := (1 : ∀ i, f i), le := (· ≤ ·), lt := (· < ·),
        npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup <| f i] : OrderedCommGroup (∀ i : I, f i) :=
  { Pi.commGroup, Pi.orderedCommMonoid with mul := (· * ·), one := (1 : ∀ i, f i), le := (· ≤ ·), lt := (· < ·),
    npow := Monoidₓ.npow }

end Pi

