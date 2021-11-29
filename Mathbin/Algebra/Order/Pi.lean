import Mathbin.Algebra.Group.Pi 
import Mathbin.Algebra.Order.Group 
import Mathbin.Tactic.PiInstances

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/


universe u v w

variable {I : Type u}

variable {f : I → Type v}

variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[toAdditive
      "The product of a family of ordered additive commutative monoids is\n  an ordered additive commutative monoid."]
instance OrderedCommMonoid {ι : Type _} {Z : ι → Type _} [∀ i, OrderedCommMonoid (Z i)] :
  OrderedCommMonoid (∀ i, Z i) :=
  { Pi.partialOrder, Pi.commMonoid with mul_le_mul_left := fun f g w h i => mul_le_mul_left' (w i) _ }

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[toAdditive
      "The product of a family of canonically ordered additive monoids is\n  a canonically ordered additive monoid."]
instance {ι : Type _} {Z : ι → Type _} [∀ i, CanonicallyOrderedMonoid (Z i)] : CanonicallyOrderedMonoid (∀ i, Z i) :=
  { Pi.orderBot, Pi.orderedCommMonoid with
    le_iff_exists_mul :=
      fun f g =>
        by 
          fsplit
          ·
            intro w 
            fsplit
            ·
              exact fun i => (le_iff_exists_mul.mp (w i)).some
            ·
              ext i 
              exact (le_iff_exists_mul.mp (w i)).some_spec
          ·
            rintro ⟨h, rfl⟩
            exact fun i => le_mul_right (le_reflₓ _) }

@[toAdditive]
instance OrderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid$ f i] : OrderedCancelCommMonoid (∀ i : I, f i) :=
  by 
    refineStruct
        { Pi.partialOrder, Pi.monoid with mul := ·*·, one := (1 : ∀ i, f i), le := · ≤ ·, lt := · < ·,
          npow := Monoidₓ.npow } <;>
      runTac 
        tactic.pi_instance_derive_field

@[toAdditive]
instance OrderedCommGroup [∀ i, OrderedCommGroup$ f i] : OrderedCommGroup (∀ i : I, f i) :=
  { Pi.commGroup, Pi.orderedCommMonoid with mul := ·*·, one := (1 : ∀ i, f i), le := · ≤ ·, lt := · < ·,
    npow := Monoidₓ.npow }

end Pi

