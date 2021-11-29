import Mathbin.GroupTheory.Submonoid.Operations 
import Mathbin.Data.Fintype.Basic

/-!
# Centers of magmas and monoids

## Main definitions

* `set.center`: the center of a magma
* `submonoid.center`: the center of a monoid
* `set.add_center`: the center of an additive magma
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/


variable {M : Type _}

namespace Set

variable (M)

/-- The center of a magma. -/
@[toAdditive add_center " The center of an additive magma. "]
def center [Mul M] : Set M :=
  { z | ∀ m, (m*z) = z*m }

@[toAdditive mem_add_center]
theorem mem_center_iff [Mul M] {z : M} : z ∈ center M ↔ ∀ g, (g*z) = z*g :=
  Iff.rfl

instance decidable_mem_center [Mul M] [DecidableEq M] [Fintype M] : DecidablePred (· ∈ center M) :=
  fun _ => decidableOfIff' _ (mem_center_iff M)

@[simp, toAdditive zero_mem_add_center]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.Center M :=
  by 
    simp [mem_center_iff]

@[simp]
theorem zero_mem_center [MulZeroClass M] : (0 : M) ∈ Set.Center M :=
  by 
    simp [mem_center_iff]

variable {M}

@[simp, toAdditive add_mem_add_center]
theorem mul_mem_center [Semigroupₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) :
  (a*b) ∈ Set.Center M :=
  fun g =>
    by 
      rw [mul_assocₓ, ←hb g, ←mul_assocₓ, ha g, mul_assocₓ]

@[simp, toAdditive neg_mem_add_center]
theorem inv_mem_center [Groupₓ M] {a : M} (ha : a ∈ Set.Center M) : a⁻¹ ∈ Set.Center M :=
  fun g =>
    by 
      rw [←inv_inj, mul_inv_rev, inv_invₓ, ←ha, mul_inv_rev, inv_invₓ]

@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) : (a+b) ∈ Set.Center M :=
  fun c =>
    by 
      rw [add_mulₓ, mul_addₓ, ha c, hb c]

@[simp]
theorem neg_mem_center [Ringₓ M] {a : M} (ha : a ∈ Set.Center M) : -a ∈ Set.Center M :=
  fun c =>
    by 
      rw [←neg_mul_comm, ha (-c), neg_mul_comm]

@[toAdditive subset_add_center_add_units]
theorem subset_center_units [Monoidₓ M] : (coeₓ : Units M → M) ⁻¹' center M ⊆ Set.Center (Units M) :=
  fun a ha b => Units.ext$ ha _

theorem center_units_subset [GroupWithZeroₓ M] : Set.Center (Units M) ⊆ (coeₓ : Units M → M) ⁻¹' center M :=
  fun a ha b =>
    by 
      obtain rfl | hb := eq_or_ne b 0
      ·
        rw [zero_mul, mul_zero]
      ·
        exact units.ext_iff.mp (ha (Units.mk0 _ hb))

/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZeroₓ M] : Set.Center (Units M) = (coeₓ : Units M → M) ⁻¹' center M :=
  subset.antisymm center_units_subset subset_center_units

@[simp]
theorem inv_mem_center₀ [GroupWithZeroₓ M] {a : M} (ha : a ∈ Set.Center M) : a⁻¹ ∈ Set.Center M :=
  by 
    obtain rfl | ha0 := eq_or_ne a 0
    ·
      rw [inv_zero]
      exact zero_mem_center M 
    lift a to Units M using ha0 
    rw [←Units.coe_inv']
    exact center_units_subset (inv_mem_center (subset_center_units ha))

@[simp, toAdditive sub_mem_add_center]
theorem div_mem_center [Groupₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) : a / b ∈ Set.Center M :=
  by 
    rw [div_eq_mul_inv]
    exact mul_mem_center ha (inv_mem_center hb)

@[simp]
theorem div_mem_center₀ [GroupWithZeroₓ M] {a b : M} (ha : a ∈ Set.Center M) (hb : b ∈ Set.Center M) :
  a / b ∈ Set.Center M :=
  by 
    rw [div_eq_mul_inv]
    exact mul_mem_center ha (inv_mem_center₀ hb)

variable (M)

@[simp, toAdditive add_center_eq_univ]
theorem center_eq_univ [CommSemigroupₓ M] : center M = Set.Univ :=
  subset.antisymm (subset_univ _)$ fun x _ y => mul_commₓ y x

end Set

namespace Submonoid

section 

variable (M) [Monoidₓ M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[toAdditive "The center of a monoid `M` is the set of elements that commute with everything in\n`M`"]
def center : Submonoid M :=
  { Carrier := Set.Center M, one_mem' := Set.one_mem_center M, mul_mem' := fun a b => Set.mul_mem_center }

@[toAdditive]
theorem coe_center : «expr↑ » (center M) = Set.Center M :=
  rfl

variable {M}

@[toAdditive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, (g*z) = z*g :=
  Iff.rfl

instance decidable_mem_center [DecidableEq M] [Fintype M] : DecidablePred (· ∈ center M) :=
  fun _ => decidableOfIff' _ mem_center_iff

/-- The center of a monoid is commutative. -/
instance : CommMonoidₓ (center M) :=
  { (center M).toMonoid with mul_comm := fun a b => Subtype.ext$ b.prop _ }

end 

section 

variable (M) [CommMonoidₓ M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end 

end Submonoid

