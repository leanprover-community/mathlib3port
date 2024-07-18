/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Algebra.Ring.Equiv
import Algebra.Field.Defs
import Algebra.Group.Action.Basic

#align_import algebra.group_ring_action.basic from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Group action on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/


universe u v

#print MulSemiringAction /-
/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `distrib_mul_action` with `mul_distrib_mul_action`. -/
class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
    DistribMulAction M R where
  smul_one : ∀ g : M, (g • 1 : R) = 1
  smul_hMul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y
#align mul_semiring_action MulSemiringAction
-/

section Semiring

variable (M N G : Type _) [Monoid M] [Monoid N] [Group G]

variable (A R S F : Type v) [AddMonoid A] [Semiring R] [CommSemiring S] [DivisionRing F]

#print MulSemiringAction.toMulDistribMulAction /-
-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
instance (priority := 100) MulSemiringAction.toMulDistribMulAction [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }
#align mul_semiring_action.to_mul_distrib_mul_action MulSemiringAction.toMulDistribMulAction
-/

#print MulSemiringAction.toRingHom /-
/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps]
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with }
#align mul_semiring_action.to_ring_hom MulSemiringAction.toRingHom
-/

#print toRingHom_injective /-
theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r
#align to_ring_hom_injective toRingHom_injective
-/

#print MulSemiringAction.toRingEquiv /-
/-- Each element of the group defines a semiring isomorphism. -/
@[simps]
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] (x : G) : R ≃+* R :=
  { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
#align mul_semiring_action.to_ring_equiv MulSemiringAction.toRingEquiv
-/

section

variable {M N}

#print MulSemiringAction.compHom /-
/-- Compose a `mul_semiring_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def MulSemiringAction.compHom (f : N →* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with smul := SMul.comp.smul f }
#align mul_semiring_action.comp_hom MulSemiringAction.compHom
-/

end

section SimpLemmas

variable {M G A R F}

attribute [simp] smul_one smul_mul' smul_zero smul_add

#print smul_inv'' /-
/-- Note that `smul_inv'` refers to the group case, and `smul_inv` has an additional inverse
on `x`. -/
@[simp]
theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
  map_inv₀ (MulSemiringAction.toRingHom M F x) _
#align smul_inv'' smul_inv''
-/

end SimpLemmas

end Semiring

