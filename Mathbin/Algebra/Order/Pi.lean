/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Algebra.Order.Ring
import Mathbin.Algebra.Ring.Pi

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

@[to_additive]
instance {ι : Type _} {α : ι → Type _} [∀ i, LE (α i)] [∀ i, Mul (α i)] [∀ i, HasExistsMulOfLe (α i)] :
    HasExistsMulOfLe (∀ i, α i) :=
  ⟨fun a b h => ⟨fun i => (exists_mul_of_le <| h i).some, funext fun i => (exists_mul_of_le <| h i).some_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      "The product of a family of canonically ordered additive monoids is\n  a canonically ordered additive monoid."]
instance {ι : Type _} {Z : ι → Type _} [∀ i, CanonicallyOrderedMonoid (Z i)] : CanonicallyOrderedMonoid (∀ i, Z i) :=
  { Pi.orderBot, Pi.orderedCommMonoid, Pi.has_exists_mul_of_le with le_self_mul := fun f g i => le_self_mul }

@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid <| f i] : OrderedCancelCommMonoid (∀ i : I, f i) := by
  refine_struct
      { Pi.partialOrder, Pi.monoid with mul := (· * ·), one := (1 : ∀ i, f i), le := (· ≤ ·), lt := (· < ·),
        npow := Monoid.npow } <;>
    pi_instance_derive_field

@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup <| f i] : OrderedCommGroup (∀ i : I, f i) :=
  { Pi.commGroup, Pi.orderedCommMonoid with mul := (· * ·), one := (1 : ∀ i, f i), le := (· ≤ ·), lt := (· < ·),
    npow := Monoid.npow }

instance [∀ i, OrderedSemiring (f i)] : OrderedSemiring (∀ i, f i) :=
  { Pi.semiring, Pi.partialOrder with add_le_add_left := fun a b hab c i => add_le_add_left (hab _) _,
    zero_le_one := fun _ => zero_le_one,
    mul_le_mul_of_nonneg_left := fun a b c hab hc i => mul_le_mul_of_nonneg_left (hab _) <| hc _,
    mul_le_mul_of_nonneg_right := fun a b c hab hc i => mul_le_mul_of_nonneg_right (hab _) <| hc _ }

instance [∀ i, OrderedCommSemiring (f i)] : OrderedCommSemiring (∀ i, f i) :=
  { Pi.commSemiring, Pi.orderedSemiring with }

instance [∀ i, OrderedRing (f i)] : OrderedRing (∀ i, f i) :=
  { Pi.ring, Pi.orderedSemiring with mul_nonneg := fun a b ha hb i => mul_nonneg (ha _) (hb _) }

instance [∀ i, OrderedCommRing (f i)] : OrderedCommRing (∀ i, f i) :=
  { Pi.commRing, Pi.orderedRing with }

end Pi

