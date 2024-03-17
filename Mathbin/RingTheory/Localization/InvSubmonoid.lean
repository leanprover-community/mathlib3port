/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import GroupTheory.Submonoid.Inverses
import RingTheory.FiniteType
import RingTheory.Localization.Basic
import Tactic.RingExp

#align_import ring_theory.localization.inv_submonoid from "leanprover-community/mathlib"@"fe8d0ff42c3c24d789f491dc2622b6cac3d61564"

/-!
# Submonoid of inverses

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

 * `is_localization.inv_submonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
   each element `x ∈ M`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRing R] (M : Submonoid R) (S : Type _) [CommRing S]

variable [Algebra R S] {P : Type _} [CommRing P]

open Function

open scoped BigOperators

namespace IsLocalization

section InvSubmonoid

variable (M S)

#print IsLocalization.invSubmonoid /-
/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).left_inv
#align is_localization.inv_submonoid IsLocalization.invSubmonoid
-/

variable [IsLocalization M S]

#print IsLocalization.submonoid_map_le_is_unit /-
theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩; exact IsLocalization.map_units S ⟨_, ha⟩
#align is_localization.submonoid_map_le_is_unit IsLocalization.submonoid_map_le_is_unit
-/

#print IsLocalization.equivInvSubmonoid /-
/-- There is an equivalence of monoids between the image of `M` and `inv_submonoid`. -/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm
#align is_localization.equiv_inv_submonoid IsLocalization.equivInvSubmonoid
-/

#print IsLocalization.toInvSubmonoid /-
/-- There is a canonical map from `M` to `inv_submonoid` sending `x` to `1 / x`. -/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)
#align is_localization.to_inv_submonoid IsLocalization.toInvSubmonoid
-/

#print IsLocalization.toInvSubmonoid_surjective /-
theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (Equiv.surjective _) (MonoidHom.submonoidMap_surjective _ _)
#align is_localization.to_inv_submonoid_surjective IsLocalization.toInvSubmonoid_surjective
-/

#print IsLocalization.toInvSubmonoid_mul /-
@[simp]
theorem toInvSubmonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.leftInvEquiv_symm_mul _ _ _
#align is_localization.to_inv_submonoid_mul IsLocalization.toInvSubmonoid_mul
-/

#print IsLocalization.mul_toInvSubmonoid /-
@[simp]
theorem mul_toInvSubmonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_leftInvEquiv_symm _ _ ⟨_, _⟩
#align is_localization.mul_to_inv_submonoid IsLocalization.mul_toInvSubmonoid
-/

#print IsLocalization.smul_toInvSubmonoid /-
@[simp]
theorem smul_toInvSubmonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert mul_to_inv_submonoid M S m; rw [← Algebra.smul_def]; rfl
#align is_localization.smul_to_inv_submonoid IsLocalization.smul_toInvSubmonoid
-/

variable {S}

#print IsLocalization.surj'' /-
theorem surj'' (z : S) : ∃ (r : R) (m : M), z = r • toInvSubmonoid M S m :=
  by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine' ⟨r, m, _⟩
  rw [Algebra.smul_def, ← e, mul_assoc]
  simp
#align is_localization.surj' IsLocalization.surj''
-/

#print IsLocalization.toInvSubmonoid_eq_mk' /-
theorem toInvSubmonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]; simp
#align is_localization.to_inv_submonoid_eq_mk' IsLocalization.toInvSubmonoid_eq_mk'
-/

#print IsLocalization.mem_invSubmonoid_iff_exists_mk' /-
theorem mem_invSubmonoid_iff_exists_mk' (x : S) : x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x :=
  by
  simp_rw [← to_inv_submonoid_eq_mk']
  exact
    ⟨fun h => ⟨_, congr_arg Subtype.val (to_inv_submonoid_surjective M S ⟨x, h⟩).choose_spec⟩,
      fun h => h.choose_spec ▸ (to_inv_submonoid M S h.some).Prop⟩
#align is_localization.mem_inv_submonoid_iff_exists_mk' IsLocalization.mem_invSubmonoid_iff_exists_mk'
-/

variable (S)

#print IsLocalization.span_invSubmonoid /-
theorem span_invSubmonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ :=
  by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj'' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (to_inv_submonoid M S m).Prop)
#align is_localization.span_inv_submonoid IsLocalization.span_invSubmonoid
-/

#print IsLocalization.finiteType_of_monoid_fg /-
theorem finiteType_of_monoid_fg [Monoid.FG M] : Algebra.FiniteType R S :=
  by
  have := Monoid.fg_of_surjective _ (to_inv_submonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine' ⟨⟨s, _⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x ∈ ((Algebra.adjoin R _ : Subalgebra R S).toSubmodule : Set S)
  rw [Algebra.adjoin_eq_span, hs, span_inv_submonoid]
  trivial
#align is_localization.finite_type_of_monoid_fg IsLocalization.finiteType_of_monoid_fg
-/

end InvSubmonoid

end IsLocalization

