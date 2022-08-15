/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import Mathbin.GroupTheory.Subgroup.Basic

/-!

# (Right) Ore sets

This defines right Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/


namespace OreLocalization

section Monoidₓ

/-- A submonoid `S` of a monoid `R` is (right) Ore if common factors on the left can be turned
into common factors on the right, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `r * u = s * v`. -/
class OreSet {R : Type _} [Monoidₓ R] (S : Submonoid R) where
  ore_left_cancel : ∀ (r₁ r₂ : R) (s : S), ↑s * r₁ = s * r₂ → ∃ s' : S, r₁ * s' = r₂ * s'
  oreNum : R → S → R
  oreDenom : R → S → S
  ore_eq : ∀ (r : R) (s : S), r * ore_denom r s = s * ore_num r s

variable {R : Type _} [Monoidₓ R] {S : Submonoid R} [OreSet S]

/-- Common factors on the left can be turned into common factors on the right, a weak form of
cancellability. -/
theorem ore_left_cancel (r₁ r₂ : R) (s : S) (h : ↑s * r₁ = s * r₂) : ∃ s' : S, r₁ * s' = r₂ * s' :=
  OreSet.ore_left_cancel r₁ r₂ s h

/-- The Ore numerator of a fraction. -/
def oreNum (r : R) (s : S) : R :=
  OreSet.oreNum r s

/-- The Ore denominator of a fraction. -/
def oreDenom (r : R) (s : S) : S :=
  OreSet.oreDenom r s

/-- The Ore condition of a fraction, expressed in terms of `ore_num` and `ore_denom`. -/
theorem ore_eq (r : R) (s : S) : r * oreDenom r s = s * oreNum r s :=
  OreSet.ore_eq r s

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
def oreCondition (r : R) (s : S) : Σ'r' : R, Σ's' : S, r * s' = s * r' :=
  ⟨oreNum r s, oreDenom r s, ore_eq r s⟩

/-- The trivial submonoid is an Ore set. -/
instance oreSetBot : OreSet (⊥ : Submonoid R) where
  ore_left_cancel := fun _ _ s h =>
    ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [SetLike.coe_mk, one_mulₓ, one_mulₓ] at h
      subst h⟩
  oreNum := fun r _ => r
  oreDenom := fun _ s => s
  ore_eq := fun _ s => by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [← hs]

/-- Every submonoid of a commutative monoid is an Ore set. -/
instance (priority := 100) oreSetComm {R} [CommMonoidₓ R] (S : Submonoid R) : OreSet S where
  ore_left_cancel := fun m n s h =>
    ⟨s, by
      rw [mul_comm n s, mul_comm m s, h]⟩
  oreNum := fun r _ => r
  oreDenom := fun _ s => s
  ore_eq := fun r s => by
    rw [mul_comm]

end Monoidₓ

/-- Cancellability in monoids with zeros can act as a replacement for the `ore_left_cancel`
condition of an ore set. -/
def oreSetOfCancelMonoidWithZero {R : Type _} [CancelMonoidWithZero R] {S : Submonoid R} (ore_num : R → S → R)
    (ore_denom : R → S → S) (ore_eq : ∀ (r : R) (s : S), r * ore_denom r s = s * ore_num r s) : OreSet S :=
  { ore_left_cancel := fun r₁ r₂ s h => ⟨s, mul_eq_mul_right_iff.mpr (mul_eq_mul_left_iff.mp h)⟩, oreNum, oreDenom,
    ore_eq }

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a proof for the Ore condition itself. -/
def oreSetOfNoZeroDivisors {R : Type _} [Ringₓ R] [NoZeroDivisors R] {S : Submonoid R} (ore_num : R → S → R)
    (ore_denom : R → S → S) (ore_eq : ∀ (r : R) (s : S), r * ore_denom r s = s * ore_num r s) : OreSet S := by
  letI : CancelMonoidWithZero R := NoZeroDivisors.toCancelMonoidWithZero
  exact ore_set_of_cancel_monoid_with_zero ore_num ore_denom ore_eq

end OreLocalization

