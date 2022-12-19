/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.inv_submonoid
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Inverses
import Mathbin.RingTheory.FiniteType
import Mathbin.RingTheory.Localization.Basic
import Mathbin.Tactic.RingExp

/-!
# Submonoid of inverses

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

open BigOperators

namespace IsLocalization

section InvSubmonoid

variable (M S)

/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).left_inv
#align is_localization.inv_submonoid IsLocalization.invSubmonoid

variable [IsLocalization M S]

theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩
#align is_localization.submonoid_map_le_is_unit IsLocalization.submonoid_map_le_is_unit

/-- There is an equivalence of monoids between the image of `M` and `inv_submonoid`. -/
noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm
#align is_localization.equiv_inv_submonoid IsLocalization.equivInvSubmonoid

/-- There is a canonical map from `M` to `inv_submonoid` sending `x` to `1 / x`. -/
noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)
#align is_localization.to_inv_submonoid IsLocalization.toInvSubmonoid

theorem to_inv_submonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (Equiv.surjective _) (MonoidHom.submonoid_map_surjective _ _)
#align is_localization.to_inv_submonoid_surjective IsLocalization.to_inv_submonoid_surjective

@[simp]
theorem to_inv_submonoid_mul (m : M) : (toInvSubmonoid M S m : S) * algebraMap R S m = 1 :=
  Submonoid.left_inv_equiv_symm_mul _ _ _
#align is_localization.to_inv_submonoid_mul IsLocalization.to_inv_submonoid_mul

@[simp]
theorem mul_to_inv_submonoid (m : M) : algebraMap R S m * (toInvSubmonoid M S m : S) = 1 :=
  Submonoid.mul_left_inv_equiv_symm _ _ ⟨_, _⟩
#align is_localization.mul_to_inv_submonoid IsLocalization.mul_to_inv_submonoid

@[simp]
theorem smul_to_inv_submonoid (m : M) : m • (toInvSubmonoid M S m : S) = 1 := by
  convert mul_to_inv_submonoid M S m
  rw [← Algebra.smul_def]
  rfl
#align is_localization.smul_to_inv_submonoid IsLocalization.smul_to_inv_submonoid

variable {S}

theorem surj' (z : S) : ∃ (r : R)(m : M), z = r • toInvSubmonoid M S m := by
  rcases IsLocalization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebraMap R S r⟩
  refine' ⟨r, m, _⟩
  rw [Algebra.smul_def, ← e, mul_assoc]
  simp
#align is_localization.surj' IsLocalization.surj'

theorem to_inv_submonoid_eq_mk' (x : M) : (toInvSubmonoid M S x : S) = mk' S 1 x := by
  rw [← (IsLocalization.map_units S x).mul_left_inj]
  simp
#align is_localization.to_inv_submonoid_eq_mk' IsLocalization.to_inv_submonoid_eq_mk'

theorem mem_inv_submonoid_iff_exists_mk' (x : S) : x ∈ invSubmonoid M S ↔ ∃ m : M, mk' S 1 m = x :=
  by 
  simp_rw [← to_inv_submonoid_eq_mk']
  exact
    ⟨fun h => ⟨_, congr_arg Subtype.val (to_inv_submonoid_surjective M S ⟨x, h⟩).some_spec⟩,
      fun h => h.some_spec ▸ (to_inv_submonoid M S h.some).Prop⟩
#align
  is_localization.mem_inv_submonoid_iff_exists_mk' IsLocalization.mem_inv_submonoid_iff_exists_mk'

variable (S)

theorem span_inv_submonoid : Submodule.span R (invSubmonoid M S : Set S) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rcases IsLocalization.surj' M x with ⟨r, m, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span (to_inv_submonoid M S m).Prop)
#align is_localization.span_inv_submonoid IsLocalization.span_inv_submonoid

theorem finiteTypeOfMonoidFg [Monoid.Fg M] : Algebra.FiniteType R S := by
  have := Monoid.fg_of_surjective _ (to_inv_submonoid_surjective M S)
  rw [Monoid.fg_iff_submonoid_fg] at this
  rcases this with ⟨s, hs⟩
  refine' ⟨⟨s, _⟩⟩
  rw [eq_top_iff]
  rintro x -
  change x ∈ ((Algebra.adjoin R _ : Subalgebra R S).toSubmodule : Set S)
  rw [Algebra.adjoin_eq_span, hs, span_inv_submonoid]
  trivial
#align is_localization.finite_type_of_monoid_fg IsLocalization.finiteTypeOfMonoidFg

end InvSubmonoid

end IsLocalization

