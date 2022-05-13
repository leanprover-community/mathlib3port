/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.GroupTheory.Subsemigroup.Center
import Mathbin.Data.Fintype.Basic

/-!
# Centers of monoids

## Main definitions

* `submonoid.center`: the center of a monoid
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/


namespace Submonoid

section

variable (M : Type _) [Monoidₓ M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive "The center of a monoid `M` is the set of elements that commute with everything in\n`M`"]
def center : Submonoid M where
  Carrier := Set.Center M
  one_mem' := Set.one_mem_center M
  mul_mem' := fun a b => Set.mul_mem_center

@[to_additive]
theorem coe_center : ↑(center M) = Set.Center M :=
  rfl

@[simp]
theorem center_to_subsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl

theorem _root_.add_submonoid.center_to_add_subsemigroup M [AddMonoidₓ M] :
    (AddSubmonoid.center M).toAddSubsemigroup = AddSubsemigroup.center M :=
  rfl

attribute [to_additive AddSubmonoid.center_to_add_subsemigroup] Submonoid.center_to_subsemigroup

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl

instance decidableMemCenter [DecidableEq M] [Fintype M] : DecidablePred (· ∈ center M) := fun _ =>
  decidableOfIff' _ mem_center_iff

/-- The center of a monoid is commutative. -/
instance : CommMonoidₓ (center M) :=
  { (center M).toMonoid with mul_comm := fun a b => Subtype.ext <| b.Prop _ }

end

section

variable (M : Type _) [CommMonoidₓ M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end

end Submonoid

