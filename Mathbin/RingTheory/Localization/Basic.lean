/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.basic
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Algebra.Ring.Equiv
import Mathbin.GroupTheory.MonoidLocalization
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.RingTheory.NonZeroDivisors
import Mathbin.Tactic.RingExp

/-!
# Localizations of commutative rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variables (R S P Q : Type*) [comm_ring R] [comm_ring S] [comm_ring P] [comm_ring Q]
variables [algebra R S] [algebra P Q] (M : submonoid R) (T : submonoid P)
```

## Main definitions

 * `is_localization (M : submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
   localization of `R` at `M`, i.e. the canonical map `algebra_map R S : R →+* S` is a
   localization map (satisfying the above properties).
 * `is_localization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
 * `is_localization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
   which maps elements of `M` to invertible elements of the codomain.
 * `is_localization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
   of `M` to elements of `T`
 * `is_localization.ring_equiv_of_ring_equiv`: if `R` and `P` are isomorphic by an isomorphism
   sending `M` to `T`, then `S` and `Q` are isomorphic
 * `is_localization.alg_equiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras

## Main results

 * `localization M S`, a construction of the localization as a quotient type, defined in
   `group_theory.monoid_localization`, has `comm_ring`, `algebra R` and `is_localization M`
   instances if `R` is a ring. `localization.away`, `localization.at_prime` and `fraction_ring`
   are abbreviations for `localization`s and have their corresponding `is_localization` instances

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : localization_map M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `is_localization` a predicate on the `algebra_map R S`,
we can ensure the localization map commutes nicely with other `algebra_map`s.

To prove most lemmas about a localization map `algebra_map R S` in this file we invoke the
corresponding proof for the underlying `comm_monoid` localization map
`is_localization.to_localization_map M S`, which can be found in `group_theory.monoid_localization`
and the namespace `submonoid.localization_map`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → localization M` equals the surjection
`localization_map.mk'` induced by the map `algebra_map : R →+* localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `localization_map.mk'` induced by any localization map.

The proof that "a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[field K]` instead of just `[comm_ring K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


open Function

open BigOperators

section CommSemiring

variable {R : Type _} [CommSemiring R] (M : Submonoid R) (S : Type _) [CommSemiring S]

variable [Algebra R S] {P : Type _} [CommSemiring P]

#print IsLocalization /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`map_units] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`surj] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`eq_iff_exists] [] -/
/-- The typeclass `is_localization (M : submodule R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
class IsLocalization : Prop where
  map_units : ∀ y : M, IsUnit (algebraMap R S y)
  surj : ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1
  eq_iff_exists : ∀ {x y}, algebraMap R S x = algebraMap R S y ↔ ∃ c : M, ↑c * x = ↑c * y
#align is_localization IsLocalization
-/

variable {M S}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

section

variable (M)

/- warning: is_localization.of_le -> IsLocalization.of_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (N : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))), (LE.le.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Preorder.toHasLe.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Submonoid.completeLattice.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) M N) -> (forall (r : R), (Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) r N) -> (IsUnit.{u2} S (MonoidWithZero.toMonoid.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) r))) -> (IsLocalization.{u1, u2} R _inst_1 N S _inst_2 _inst_3)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] (N : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))), (LE.le.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Preorder.toLE.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))))))) M N) -> (forall (r : R), (Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) r N) -> (IsUnit.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) r) (MonoidWithZero.toMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) r) (Semiring.toMonoidWithZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) r) (CommSemiring.toSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) r) _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) (algebraMap.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) r))) -> (IsLocalization.{u2, u1} R _inst_1 N S _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align is_localization.of_le IsLocalization.of_leₓ'. -/
theorem of_le (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ r ∈ N, IsUnit (algebraMap R S r)) :
    IsLocalization N S :=
  { map_units := fun r => h₂ r r.2
    surj := fun s => by
      obtain ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
      exact ⟨⟨x, y, h₁ hy⟩, H⟩
    eq_iff_exists := fun x y => by
      constructor
      · rw [IsLocalization.eq_iff_exists M]
        rintro ⟨c, hc⟩
        exact ⟨⟨c, h₁ c.2⟩, hc⟩
      · rintro ⟨c, h⟩
        simpa only [[anonymous], map_mul, (h₂ c c.2).mul_right_inj] using
          congr_arg (algebraMap R S) h }
#align is_localization.of_le IsLocalization.of_le

variable (S)

#print IsLocalization.toLocalizationWithZeroMap /-
/-- `is_localization.to_localization_with_zero_map M S` shows `S` is the monoid localization of
`R` at `M`. -/
@[simps]
def toLocalizationWithZeroMap : Submonoid.LocalizationWithZeroMap M S :=
  { algebraMap R S with
    toFun := algebraMap R S
    map_units' := IsLocalization.map_units _
    surj' := IsLocalization.surj _
    eq_iff_exists' := fun _ _ => IsLocalization.eq_iff_exists _ _ }
#align is_localization.to_localization_with_zero_map IsLocalization.toLocalizationWithZeroMap
-/

#print IsLocalization.toLocalizationMap /-
/-- `is_localization.to_localization_map M S` shows `S` is the monoid localization of `R` at `M`. -/
abbrev toLocalizationMap : Submonoid.LocalizationMap M S :=
  (toLocalizationWithZeroMap M S).toLocalizationMap
#align is_localization.to_localization_map IsLocalization.toLocalizationMap
-/

/- warning: is_localization.to_localization_map_to_map -> IsLocalization.toLocalizationMap_toMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.to_localization_map_to_map IsLocalization.toLocalizationMap_toMapₓ'. -/
@[simp]
theorem toLocalizationMap_toMap : (toLocalizationMap M S).toMap = (algebraMap R S : R →*₀ S) :=
  rfl
#align is_localization.to_localization_map_to_map IsLocalization.toLocalizationMap_toMap

/- warning: is_localization.to_localization_map_to_map_apply -> IsLocalization.toLocalizationMap_toMap_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : R), Eq.{succ u2} S (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) (fun (_x : MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) => R -> S) (MonoidHom.hasCoeToFun.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) (Submonoid.LocalizationMap.toMap.{u1, u2} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M S (CommSemiring.toCommMonoid.{u2} S _inst_2) (IsLocalization.toLocalizationMap.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5)) x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : R), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) R S (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) (MulOneClass.toMul.{u2} S (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))) R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} R S (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))) (Monoid.toMulOneClass.{u2} S (CommMonoid.toMonoid.{u2} S (CommSemiring.toCommMonoid.{u2} S _inst_2)))))) (Submonoid.LocalizationMap.toMap.{u1, u2} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M S (CommSemiring.toCommMonoid.{u2} S _inst_2) (IsLocalization.toLocalizationMap.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5)) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x)
Case conversion may be inaccurate. Consider using '#align is_localization.to_localization_map_to_map_apply IsLocalization.toLocalizationMap_toMap_applyₓ'. -/
theorem toLocalizationMap_toMap_apply (x) : (toLocalizationMap M S).toMap x = algebraMap R S x :=
  rfl
#align is_localization.to_localization_map_to_map_apply IsLocalization.toLocalizationMap_toMap_apply

end

variable (M)

/- warning: is_localization.sec -> IsLocalization.sec is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], S -> (Prod.{u1, u1} R (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], S -> (Prod.{u1, u1} R (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)))
Case conversion may be inaccurate. Consider using '#align is_localization.sec IsLocalization.secₓ'. -/
/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
noncomputable def sec (z : S) : R × M :=
  Classical.choose <| IsLocalization.surj _ z
#align is_localization.sec IsLocalization.sec

/- warning: is_localization.to_localization_map_sec -> IsLocalization.toLocalizationMap_sec is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], Eq.{max (succ u2) (succ u1)} (S -> (Prod.{u1, u1} R (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M))) (Submonoid.LocalizationMap.sec.{u1, u2} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M S (CommSemiring.toCommMonoid.{u2} S _inst_2) (IsLocalization.toLocalizationMap.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5)) (IsLocalization.sec.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3], Eq.{max (succ u2) (succ u1)} (S -> (Prod.{u2, u2} R (Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (Monoid.toMulOneClass.{u2} R (CommMonoid.toMonoid.{u2} R (CommSemiring.toCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (Monoid.toMulOneClass.{u2} R (CommMonoid.toMonoid.{u2} R (CommSemiring.toCommMonoid.{u2} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u2} R (Monoid.toMulOneClass.{u2} R (CommMonoid.toMonoid.{u2} R (CommSemiring.toCommMonoid.{u2} R _inst_1))))) x M)))) (Submonoid.LocalizationMap.sec.{u2, u1} R (CommSemiring.toCommMonoid.{u2} R _inst_1) M S (CommSemiring.toCommMonoid.{u1} S _inst_2) (IsLocalization.toLocalizationMap.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5)) (IsLocalization.sec.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_localization.to_localization_map_sec IsLocalization.toLocalizationMap_secₓ'. -/
@[simp]
theorem toLocalizationMap_sec : (toLocalizationMap M S).sec = sec M :=
  rfl
#align is_localization.to_localization_map_sec IsLocalization.toLocalizationMap_sec

/- warning: is_localization.sec_spec -> IsLocalization.sec_spec is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.sec_spec IsLocalization.sec_specₓ'. -/
/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
theorem sec_spec (z : S) :
    z * algebraMap R S (IsLocalization.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1 :=
  Classical.choose_spec <| IsLocalization.surj _ z
#align is_localization.sec_spec IsLocalization.sec_spec

/- warning: is_localization.sec_spec' -> IsLocalization.sec_spec' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.sec_spec' IsLocalization.sec_spec'ₓ'. -/
/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
theorem sec_spec' (z : S) :
    algebraMap R S (IsLocalization.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2 * z := by
  rw [mul_comm, sec_spec]
#align is_localization.sec_spec' IsLocalization.sec_spec'

variable {R M}

/- warning: is_localization.map_right_cancel -> IsLocalization.map_right_cancel is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_right_cancel IsLocalization.map_right_cancelₓ'. -/
theorem map_right_cancel {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_right_cancel h
#align is_localization.map_right_cancel IsLocalization.map_right_cancel

/- warning: is_localization.map_left_cancel -> IsLocalization.map_left_cancel is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_left_cancel IsLocalization.map_left_cancelₓ'. -/
theorem map_left_cancel {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_left_cancel h
#align is_localization.map_left_cancel IsLocalization.map_left_cancel

/- warning: is_localization.eq_zero_of_fst_eq_zero -> IsLocalization.eq_zero_of_fst_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.eq_zero_of_fst_eq_zero IsLocalization.eq_zero_of_fst_eq_zeroₓ'. -/
theorem eq_zero_of_fst_eq_zero {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
    (hx : x = 0) : z = 0 := by
  rw [hx, (algebraMap R S).map_zero] at h
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h
#align is_localization.eq_zero_of_fst_eq_zero IsLocalization.eq_zero_of_fst_eq_zero

variable (M S)

/- warning: is_localization.map_eq_zero_iff -> IsLocalization.map_eq_zero_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_eq_zero_iff IsLocalization.map_eq_zero_iffₓ'. -/
theorem map_eq_zero_iff (r : R) : algebraMap R S r = 0 ↔ ∃ m : M, ↑m * r = 0 :=
  by
  constructor
  intro h
  · obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).mp ((algebraMap R S).map_zero.trans h.symm)
    exact ⟨m, by simpa using hm.symm⟩
  · rintro ⟨m, hm⟩
    rw [← (IsLocalization.map_units S m).mul_right_inj, MulZeroClass.mul_zero, ← RingHom.map_mul,
      hm, RingHom.map_zero]
#align is_localization.map_eq_zero_iff IsLocalization.map_eq_zero_iff

variable {M}

/- warning: is_localization.mk' -> IsLocalization.mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], R -> (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) -> S
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], R -> (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)) -> S
Case conversion may be inaccurate. Consider using '#align is_localization.mk' IsLocalization.mk'ₓ'. -/
/-- `is_localization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (x : R) (y : M) : S :=
  (toLocalizationMap M S).mk' x y
#align is_localization.mk' IsLocalization.mk'

#print IsLocalization.mk'_sec /-
@[simp]
theorem mk'_sec (z : S) : mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z :=
  (toLocalizationMap M S).mk'_sec _
#align is_localization.mk'_sec IsLocalization.mk'_sec
-/

/- warning: is_localization.mk'_mul -> IsLocalization.mk'_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_mul IsLocalization.mk'_mulₓ'. -/
theorem mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) : mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
  (toLocalizationMap M S).mk'_mul _ _ _ _
#align is_localization.mk'_mul IsLocalization.mk'_mul

/- warning: is_localization.mk'_one -> IsLocalization.mk'_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : R), Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) 1 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) 1 (One.one.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : R), Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M)))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x)
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_one IsLocalization.mk'_oneₓ'. -/
theorem mk'_one (x) : mk' S x (1 : M) = algebraMap R S x :=
  (toLocalizationMap M S).mk'_one _
#align is_localization.mk'_one IsLocalization.mk'_one

/- warning: is_localization.mk'_spec -> IsLocalization.mk'_spec is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_spec IsLocalization.mk'_specₓ'. -/
@[simp]
theorem mk'_spec (x) (y : M) : mk' S x y * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec _ _
#align is_localization.mk'_spec IsLocalization.mk'_spec

/- warning: is_localization.mk'_spec' -> IsLocalization.mk'_spec' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_spec' IsLocalization.mk'_spec'ₓ'. -/
@[simp]
theorem mk'_spec' (x) (y : M) : algebraMap R S y * mk' S x y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec' _ _
#align is_localization.mk'_spec' IsLocalization.mk'_spec'

/- warning: is_localization.mk'_spec_mk -> IsLocalization.mk'_spec_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_spec_mk IsLocalization.mk'_spec_mkₓ'. -/
@[simp]
theorem mk'_spec_mk (x) (y : R) (hy : y ∈ M) :
    mk' S x ⟨y, hy⟩ * algebraMap R S y = algebraMap R S x :=
  mk'_spec S x ⟨y, hy⟩
#align is_localization.mk'_spec_mk IsLocalization.mk'_spec_mk

/- warning: is_localization.mk'_spec'_mk -> IsLocalization.mk'_spec'_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_spec'_mk IsLocalization.mk'_spec'_mkₓ'. -/
@[simp]
theorem mk'_spec'_mk (x) (y : R) (hy : y ∈ M) :
    algebraMap R S y * mk' S x ⟨y, hy⟩ = algebraMap R S x :=
  mk'_spec' S x ⟨y, hy⟩
#align is_localization.mk'_spec'_mk IsLocalization.mk'_spec'_mk

variable {S}

/- warning: is_localization.eq_mk'_iff_mul_eq -> IsLocalization.eq_mk'_iff_mul_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.eq_mk'_iff_mul_eq IsLocalization.eq_mk'_iff_mul_eqₓ'. -/
theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
    z = mk' S x y ↔ z * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).eq_mk'_iff_mul_eq
#align is_localization.eq_mk'_iff_mul_eq IsLocalization.eq_mk'_iff_mul_eq

/- warning: is_localization.mk'_eq_iff_eq_mul -> IsLocalization.mk'_eq_iff_eq_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_iff_eq_mul IsLocalization.mk'_eq_iff_eq_mulₓ'. -/
theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
    mk' S x y = z ↔ algebraMap R S x = z * algebraMap R S y :=
  (toLocalizationMap M S).mk'_eq_iff_eq_mul
#align is_localization.mk'_eq_iff_eq_mul IsLocalization.mk'_eq_iff_eq_mul

/- warning: is_localization.mk'_add_eq_iff_add_mul_eq_mul -> IsLocalization.mk'_add_eq_iff_add_mul_eq_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_add_eq_iff_add_mul_eq_mul IsLocalization.mk'_add_eq_iff_add_mul_eq_mulₓ'. -/
theorem mk'_add_eq_iff_add_mul_eq_mul {x} {y : M} {z₁ z₂} :
    mk' S x y + z₁ = z₂ ↔ algebraMap R S x + z₁ * algebraMap R S y = z₂ * algebraMap R S y := by
  rw [← mk'_spec S x y, ← IsUnit.mul_left_inj (IsLocalization.map_units S y), right_distrib]
#align is_localization.mk'_add_eq_iff_add_mul_eq_mul IsLocalization.mk'_add_eq_iff_add_mul_eq_mul

variable (M)

/- warning: is_localization.mk'_surjective -> IsLocalization.mk'_surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (z : S), Exists.{succ u1} R (fun (x : R) => Exists.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) (fun (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) => Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) z))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] (z : S), Exists.{succ u2} R (fun (x : R) => Exists.{succ u2} (Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)) (fun (y : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)) => Eq.{succ u1} S (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) z))
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_surjective IsLocalization.mk'_surjectiveₓ'. -/
theorem mk'_surjective (z : S) : ∃ (x : _)(y : M), mk' S x y = z :=
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r.1, r.2, (eq_mk'_iff_mul_eq.2 hr).symm⟩
#align is_localization.mk'_surjective IsLocalization.mk'_surjective

variable (S)

include M

#print IsLocalization.fintype' /-
/-- The localization of a `fintype` is a `fintype`. Cannot be an instance. -/
noncomputable def fintype' [Fintype R] : Fintype S :=
  have := Classical.propDecidable
  Fintype.ofSurjective (Function.uncurry <| IsLocalization.mk' S) fun a =>
    prod.exists'.mpr <| IsLocalization.mk'_surjective M a
#align is_localization.fintype' IsLocalization.fintype'
-/

omit M

variable {M S}

/- warning: is_localization.unique_of_zero_mem -> IsLocalization.uniqueOfZeroMem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], (Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) M) -> (Unique.{succ u2} S)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], (Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)))) M) -> (Unique.{succ u2} S)
Case conversion may be inaccurate. Consider using '#align is_localization.unique_of_zero_mem IsLocalization.uniqueOfZeroMemₓ'. -/
/-- Localizing at a submonoid with 0 inside it leads to the trivial ring. -/
def uniqueOfZeroMem (h : (0 : R) ∈ M) : Unique S :=
  uniqueOfZeroEqOne <| by simpa using IsLocalization.map_units S ⟨0, h⟩
#align is_localization.unique_of_zero_mem IsLocalization.uniqueOfZeroMem

/- warning: is_localization.mk'_eq_iff_eq -> IsLocalization.mk'_eq_iff_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_iff_eq IsLocalization.mk'_eq_iff_eqₓ'. -/
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (y₂ * x₁) = algebraMap R S (y₁ * x₂) :=
  (toLocalizationMap M S).mk'_eq_iff_eq
#align is_localization.mk'_eq_iff_eq IsLocalization.mk'_eq_iff_eq

/- warning: is_localization.mk'_eq_iff_eq' -> IsLocalization.mk'_eq_iff_eq' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_iff_eq' IsLocalization.mk'_eq_iff_eq'ₓ'. -/
theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (x₁ * y₂) = algebraMap R S (x₂ * y₁) :=
  (toLocalizationMap M S).mk'_eq_iff_eq'
#align is_localization.mk'_eq_iff_eq' IsLocalization.mk'_eq_iff_eq'

/- warning: is_localization.mk'_mem_iff -> IsLocalization.mk'_mem_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {x : R} {y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M} {I : Ideal.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)}, Iff (Membership.Mem.{u2, u2} S (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (SetLike.hasMem.{u2, u2} (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) S (Submodule.setLike.{u2, u2} S S (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (Semiring.toModule.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) I) (Membership.Mem.{u2, u2} S (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (SetLike.hasMem.{u2, u2} (Ideal.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) S (Submodule.setLike.{u2, u2} S S (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (Semiring.toModule.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x) I)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] {x : R} {y : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)} {I : Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)}, Iff (Membership.mem.{u1, u1} S (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) I) (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) (algebraMap.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) x) I)
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_mem_iff IsLocalization.mk'_mem_iffₓ'. -/
theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y ∈ I ↔ algebraMap R S x ∈ I :=
  by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this
#align is_localization.mk'_mem_iff IsLocalization.mk'_mem_iff

/- warning: is_localization.eq -> IsLocalization.eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.eq IsLocalization.eqₓ'. -/
protected theorem eq {a₁ b₁} {a₂ b₂ : M} :
    mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  (toLocalizationMap M S).Eq
#align is_localization.eq IsLocalization.eq

/- warning: is_localization.mk'_eq_zero_iff -> IsLocalization.mk'_eq_zero_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_zero_iff IsLocalization.mk'_eq_zero_iffₓ'. -/
theorem mk'_eq_zero_iff (x : R) (s : M) : mk' S x s = 0 ↔ ∃ m : M, ↑m * x = 0 := by
  rw [← (map_units S s).mul_left_inj, mk'_spec, MulZeroClass.zero_mul, map_eq_zero_iff M]
#align is_localization.mk'_eq_zero_iff IsLocalization.mk'_eq_zero_iff

/- warning: is_localization.mk'_zero -> IsLocalization.mk'_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (s : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M), Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) s) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] (s : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)), Eq.{succ u1} S (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)))) s) (OfNat.ofNat.{u1} S 0 (Zero.toOfNat0.{u1} S (CommMonoidWithZero.toZero.{u1} S (CommSemiring.toCommMonoidWithZero.{u1} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_zero IsLocalization.mk'_zeroₓ'. -/
@[simp]
theorem mk'_zero (s : M) : IsLocalization.mk' S 0 s = 0 := by
  rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, MulZeroClass.zero_mul, map_zero]
#align is_localization.mk'_zero IsLocalization.mk'_zero

/- warning: is_localization.ne_zero_of_mk'_ne_zero -> IsLocalization.ne_zero_of_mk'_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {x : R} {y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M}, (Ne.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))))) -> (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] {x : R} {y : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)}, (Ne.{succ u1} S (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) (OfNat.ofNat.{u1} S 0 (Zero.toOfNat0.{u1} S (CommMonoidWithZero.toZero.{u1} S (CommSemiring.toCommMonoidWithZero.{u1} S _inst_2))))) -> (Ne.{succ u2} R x (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_localization.ne_zero_of_mk'_ne_zero IsLocalization.ne_zero_of_mk'_ne_zeroₓ'. -/
theorem ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : IsLocalization.mk' S x y ≠ 0) : x ≠ 0 :=
  by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)
#align is_localization.ne_zero_of_mk'_ne_zero IsLocalization.ne_zero_of_mk'_ne_zero

section Ext

variable [Algebra R P] [IsLocalization M P]

/- warning: is_localization.eq_iff_eq -> IsLocalization.eq_iff_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.eq_iff_eq IsLocalization.eq_iff_eqₓ'. -/
theorem eq_iff_eq {x y} :
    algebraMap R S x = algebraMap R S y ↔ algebraMap R P x = algebraMap R P y :=
  (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)
#align is_localization.eq_iff_eq IsLocalization.eq_iff_eq

/- warning: is_localization.mk'_eq_iff_mk'_eq -> IsLocalization.mk'_eq_iff_mk'_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] [_inst_6 : Algebra.{u1, u3} R P _inst_1 (CommSemiring.toSemiring.{u3} P _inst_4)] [_inst_7 : IsLocalization.{u1, u3} R _inst_1 M P _inst_4 _inst_6] {x₁ : R} {x₂ : R} {y₁ : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M} {y₂ : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M}, Iff (Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x₁ y₁) (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x₂ y₂)) (Eq.{succ u3} P (IsLocalization.mk'.{u1, u3} R _inst_1 M P _inst_4 _inst_6 _inst_7 x₁ y₁) (IsLocalization.mk'.{u1, u3} R _inst_1 M P _inst_4 _inst_6 _inst_7 x₂ y₂))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] {M : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u1}} [_inst_4 : CommSemiring.{u1} P] [_inst_5 : IsLocalization.{u3, u2} R _inst_1 M S _inst_2 _inst_3] [_inst_6 : Algebra.{u3, u1} R P _inst_1 (CommSemiring.toSemiring.{u1} P _inst_4)] [_inst_7 : IsLocalization.{u3, u1} R _inst_1 M P _inst_4 _inst_6] {x₁ : R} {x₂ : R} {y₁ : Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))))) x M)} {y₂ : Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (SetLike.instMembership.{u3, u3} (Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))))) x M)}, Iff (Eq.{succ u2} S (IsLocalization.mk'.{u3, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x₁ y₁) (IsLocalization.mk'.{u3, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x₂ y₂)) (Eq.{succ u1} P (IsLocalization.mk'.{u3, u1} R _inst_1 M P _inst_4 _inst_6 _inst_7 x₁ y₁) (IsLocalization.mk'.{u3, u1} R _inst_1 M P _inst_4 _inst_6 _inst_7 x₂ y₂))
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_iff_mk'_eq IsLocalization.mk'_eq_iff_mk'_eqₓ'. -/
theorem mk'_eq_iff_mk'_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
  (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)
#align is_localization.mk'_eq_iff_mk'_eq IsLocalization.mk'_eq_iff_mk'_eq

/- warning: is_localization.mk'_eq_of_eq -> IsLocalization.mk'_eq_of_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_of_eq IsLocalization.mk'_eq_of_eqₓ'. -/
theorem mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq H
#align is_localization.mk'_eq_of_eq IsLocalization.mk'_eq_of_eq

/- warning: is_localization.mk'_eq_of_eq' -> IsLocalization.mk'_eq_of_eq' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_of_eq' IsLocalization.mk'_eq_of_eq'ₓ'. -/
theorem mk'_eq_of_eq' {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq' H
#align is_localization.mk'_eq_of_eq' IsLocalization.mk'_eq_of_eq'

variable (S)

/- warning: is_localization.mk'_self -> IsLocalization.mk'_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {x : R} (hx : Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M), Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x (Subtype.mk.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M) x hx)) (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S (AddMonoidWithOne.toOne.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} (S : Type.{u1}) [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] {x : R} (hx : Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M), Eq.{succ u1} S (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 x (Subtype.mk.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M) x hx)) (OfNat.ofNat.{u1} S 1 (One.toOfNat1.{u1} S (Semiring.toOne.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_self IsLocalization.mk'_selfₓ'. -/
@[simp]
theorem mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
  (toLocalizationMap M S).mk'_self _ hx
#align is_localization.mk'_self IsLocalization.mk'_self

/- warning: is_localization.mk'_self' -> IsLocalization.mk'_self' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_self' IsLocalization.mk'_self'ₓ'. -/
@[simp]
theorem mk'_self' {x : M} : mk' S (x : R) x = 1 :=
  (toLocalizationMap M S).mk'_self' _
#align is_localization.mk'_self' IsLocalization.mk'_self'

/- warning: is_localization.mk'_self'' -> IsLocalization.mk'_self'' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M}, Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 (Subtype.val.{succ u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M) x) x) (OfNat.ofNat.{u2} S 1 (OfNat.mk.{u2} S 1 (One.one.{u2} S (AddMonoidWithOne.toOne.{u2} S (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} S (NonAssocSemiring.toAddCommMonoidWithOne.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} (S : Type.{u1}) [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] {x : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)}, Eq.{succ u1} S (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 (Subtype.val.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M) x) x) (OfNat.ofNat.{u1} S 1 (One.toOfNat1.{u1} S (Semiring.toOne.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_self'' IsLocalization.mk'_self''ₓ'. -/
theorem mk'_self'' {x : M} : mk' S x.1 x = 1 :=
  mk'_self' _
#align is_localization.mk'_self'' IsLocalization.mk'_self''

end Ext

/- warning: is_localization.mul_mk'_eq_mk'_of_mul -> IsLocalization.mul_mk'_eq_mk'_of_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : R) (y : R) (z : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M), Eq.{succ u2} S (HMul.hMul.{u2, u2, u2} S S S (instHMul.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x) (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 y z)) (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) z)
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] (x : R) (y : R) (z : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) S ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (NonUnitalNonAssocSemiring.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (Semiring.toNonAssocSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (CommSemiring.toSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) _inst_2))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) (algebraMap.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) x) (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 y z)) (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) x y) z)
Case conversion may be inaccurate. Consider using '#align is_localization.mul_mk'_eq_mk'_of_mul IsLocalization.mul_mk'_eq_mk'_of_mulₓ'. -/
theorem mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
    (algebraMap R S) x * mk' S y z = mk' S (x * y) z :=
  (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _
#align is_localization.mul_mk'_eq_mk'_of_mul IsLocalization.mul_mk'_eq_mk'_of_mul

/- warning: is_localization.mk'_eq_mul_mk'_one -> IsLocalization.mk'_eq_mul_mk'_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : R) (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M), Eq.{succ u2} S (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) (HMul.hMul.{u2, u2, u2} S S S (instHMul.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) x) (IsLocalization.mk'.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) y))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))} {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3] (x : R) (y : Subtype.{succ u2} R (fun (x : R) => Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))) x M)), Eq.{succ u1} S (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 x y) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) S ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (NonUnitalNonAssocSemiring.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (Semiring.toNonAssocSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (CommSemiring.toSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) _inst_2))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) (algebraMap.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) x) (IsLocalization.mk'.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5 (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Semiring.toOne.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) y))
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_eq_mul_mk'_one IsLocalization.mk'_eq_mul_mk'_oneₓ'. -/
theorem mk'_eq_mul_mk'_one (x : R) (y : M) : mk' S x y = (algebraMap R S) x * mk' S 1 y :=
  ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm
#align is_localization.mk'_eq_mul_mk'_one IsLocalization.mk'_eq_mul_mk'_one

/- warning: is_localization.mk'_mul_cancel_left -> IsLocalization.mk'_mul_cancel_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_mul_cancel_left IsLocalization.mk'_mul_cancel_leftₓ'. -/
@[simp]
theorem mk'_mul_cancel_left (x : R) (y : M) : mk' S (y * x : R) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_left _ _
#align is_localization.mk'_mul_cancel_left IsLocalization.mk'_mul_cancel_left

/- warning: is_localization.mk'_mul_cancel_right -> IsLocalization.mk'_mul_cancel_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_mul_cancel_right IsLocalization.mk'_mul_cancel_rightₓ'. -/
theorem mk'_mul_cancel_right (x : R) (y : M) : mk' S (x * y) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_right _ _
#align is_localization.mk'_mul_cancel_right IsLocalization.mk'_mul_cancel_right

/- warning: is_localization.mk'_mul_mk'_eq_one -> IsLocalization.mk'_mul_mk'_eq_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_mul_mk'_eq_one IsLocalization.mk'_mul_mk'_eq_oneₓ'. -/
@[simp]
theorem mk'_mul_mk'_eq_one (x y : M) : mk' S (x : R) y * mk' S (y : R) x = 1 := by
  rw [← mk'_mul, mul_comm] <;> exact mk'_self _ _
#align is_localization.mk'_mul_mk'_eq_one IsLocalization.mk'_mul_mk'_eq_one

/- warning: is_localization.mk'_mul_mk'_eq_one' -> IsLocalization.mk'_mul_mk'_eq_one' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_mul_mk'_eq_one' IsLocalization.mk'_mul_mk'_eq_one'ₓ'. -/
theorem mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) : mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
  mk'_mul_mk'_eq_one ⟨x, h⟩ _
#align is_localization.mk'_mul_mk'_eq_one' IsLocalization.mk'_mul_mk'_eq_one'

section

variable (M)

/- warning: is_localization.is_unit_comp -> IsLocalization.isUnit_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.is_unit_comp IsLocalization.isUnit_compₓ'. -/
theorem isUnit_comp (j : S →+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y) :=
  (toLocalizationMap M S).isUnit_comp j.toMonoidHom _
#align is_localization.is_unit_comp IsLocalization.isUnit_comp

end

/- warning: is_localization.eq_of_eq -> IsLocalization.eq_of_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.eq_of_eq IsLocalization.eq_of_eqₓ'. -/
/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_semiring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
theorem eq_of_eq {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) {x y}
    (h : (algebraMap R S) x = (algebraMap R S) y) : g x = g y :=
  @Submonoid.LocalizationMap.eq_of_eq _ _ _ _ _ _ _ (toLocalizationMap M S) g.toMonoidHom hg _ _ h
#align is_localization.eq_of_eq IsLocalization.eq_of_eq

/- warning: is_localization.mk'_add -> IsLocalization.mk'_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mk'_add IsLocalization.mk'_addₓ'. -/
theorem mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
  mk'_eq_iff_eq_mul.2 <|
    Eq.symm
      (by
        rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, mk'_add_eq_iff_add_mul_eq_mul,
          mul_comm (_ * _), ← mul_assoc, add_comm, ← map_mul, mul_mk'_eq_mk'_of_mul,
          mk'_add_eq_iff_add_mul_eq_mul]
        simp only [map_add, Submonoid.coe_mul, map_mul]
        ring)
#align is_localization.mk'_add IsLocalization.mk'_add

/- warning: is_localization.mul_add_inv_left -> IsLocalization.mul_add_inv_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.mul_add_inv_left IsLocalization.mul_add_inv_leftₓ'. -/
theorem mul_add_inv_left {g : R →+* P} (h : ∀ y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P) :
    w * ↑(IsUnit.liftRight (g.toMonoidHom.restrict M) h y)⁻¹ + z₁ = z₂ ↔ w + g y * z₁ = g y * z₂ :=
  by
  rw [mul_comm, ← one_mul z₁, ← Units.inv_mul (IsUnit.liftRight (g.to_monoid_hom.restrict M) h y),
    mul_assoc, ← mul_add, Units.inv_mul_eq_iff_eq_mul, Units.inv_mul_cancel_left,
    IsUnit.coe_liftRight]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.restrict_apply, [anonymous]]
#align is_localization.mul_add_inv_left IsLocalization.mul_add_inv_left

/- warning: is_localization.lift_spec_mul_add -> IsLocalization.lift_spec_mul_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_spec_mul_add IsLocalization.lift_spec_mul_addₓ'. -/
theorem lift_spec_mul_add {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) (z w w' v) :
    ((toLocalizationWithZeroMap M S).lift g.toMonoidWithZeroHom hg) z * w + w' = v ↔
      g ((toLocalizationMap M S).sec z).1 * w + g ((toLocalizationMap M S).sec z).2 * w' =
        g ((toLocalizationMap M S).sec z).2 * v :=
  by
  show _ * _ * _ + _ = _ ↔ _ = _
  erw [mul_comm, ← mul_assoc, mul_add_inv_left hg, mul_comm]
  rfl
#align is_localization.lift_spec_mul_add IsLocalization.lift_spec_mul_add

/- warning: is_localization.lift -> IsLocalization.lift is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift IsLocalization.liftₓ'. -/
/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_semiring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) : S →+* P :=
  {
    @Submonoid.LocalizationWithZeroMap.lift _ _ _ _ _ _ _ (toLocalizationWithZeroMap M S)
      g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      erw [(to_localization_map M S).lift_spec, mul_add, mul_comm, eq_comm, lift_spec_mul_add,
        add_comm, mul_comm, mul_assoc, mul_comm, mul_assoc, lift_spec_mul_add]
      simp_rw [← mul_assoc]
      show g _ * g _ * g _ + g _ * g _ * g _ = g _ * g _ * g _
      simp_rw [← map_mul g, ← map_add g]
      apply @eq_of_eq _ _ _ S _ _ _ _ _ g hg
      simp only [sec_spec', to_localization_map_sec, map_add, map_mul]
      ring }
#align is_localization.lift IsLocalization.lift

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

/- warning: is_localization.lift_mk' -> IsLocalization.lift_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_mk' IsLocalization.lift_mk'ₓ'. -/
/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_semiring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
theorem lift_mk' (x y) :
    lift hg (mk' S x y) = g x * ↑(IsUnit.liftRight (g.toMonoidHom.restrict M) hg y)⁻¹ :=
  (toLocalizationMap M S).lift_mk' _ _ _
#align is_localization.lift_mk' IsLocalization.lift_mk'

/- warning: is_localization.lift_mk'_spec -> IsLocalization.lift_mk'_spec is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_mk'_spec IsLocalization.lift_mk'_specₓ'. -/
theorem lift_mk'_spec (x v) (y : M) : lift hg (mk' S x y) = v ↔ g x = g y * v :=
  (toLocalizationMap M S).lift_mk'_spec _ _ _ _
#align is_localization.lift_mk'_spec IsLocalization.lift_mk'_spec

/- warning: is_localization.lift_eq -> IsLocalization.lift_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_eq IsLocalization.lift_eqₓ'. -/
@[simp]
theorem lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x :=
  (toLocalizationMap M S).liftEq _ _
#align is_localization.lift_eq IsLocalization.lift_eq

/- warning: is_localization.lift_eq_iff -> IsLocalization.lift_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_eq_iff IsLocalization.lift_eq_iffₓ'. -/
theorem lift_eq_iff {x y : R × M} :
    lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
  (toLocalizationMap M S).lift_eq_iff _
#align is_localization.lift_eq_iff IsLocalization.lift_eq_iff

/- warning: is_localization.lift_comp -> IsLocalization.lift_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_comp IsLocalization.lift_compₓ'. -/
@[simp]
theorem lift_comp : (lift hg).comp (algebraMap R S) = g :=
  RingHom.ext <| MonoidHom.ext_iff.1 <| (toLocalizationMap M S).lift_comp _
#align is_localization.lift_comp IsLocalization.lift_comp

/- warning: is_localization.lift_of_comp -> IsLocalization.lift_of_comp is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (j : RingHom.{u2, u3} S P (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))), Eq.{max (succ u2) (succ u3)} (RingHom.{u2, u3} S P (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))) (IsLocalization.lift.{u1, u2, u3} R _inst_1 M S _inst_2 _inst_3 P _inst_4 _inst_5 (RingHom.comp.{u1, u2, u3} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) j (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3)) (IsLocalization.isUnit_comp.{u1, u2, u3} R _inst_1 M S _inst_2 _inst_3 P _inst_4 _inst_5 j)) j
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u3}} [_inst_2 : CommSemiring.{u3} S] [_inst_3 : Algebra.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] [_inst_5 : IsLocalization.{u1, u3} R _inst_1 M S _inst_2 _inst_3] (j : RingHom.{u3, u2} S P (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))), Eq.{max (succ u3) (succ u2)} (RingHom.{u3, u2} S P (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))) (IsLocalization.lift.{u1, u3, u2} R _inst_1 M S _inst_2 _inst_3 P _inst_4 _inst_5 (RingHom.comp.{u1, u3, u2} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) j (algebraMap.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2) _inst_3)) (IsLocalization.isUnit_comp.{u1, u2, u3} R _inst_1 M S _inst_2 _inst_3 P _inst_4 _inst_5 j)) j
Case conversion may be inaccurate. Consider using '#align is_localization.lift_of_comp IsLocalization.lift_of_compₓ'. -/
@[simp]
theorem lift_of_comp (j : S →+* P) : lift (isUnit_comp M j) = j :=
  RingHom.ext <| MonoidHom.ext_iff.1 <| (toLocalizationMap M S).lift_of_comp j.toMonoidHom
#align is_localization.lift_of_comp IsLocalization.lift_of_comp

variable (M)

/- warning: is_localization.monoid_hom_ext -> IsLocalization.monoidHom_ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.monoid_hom_ext IsLocalization.monoidHom_extₓ'. -/
/-- See note [partially-applied ext lemmas] -/
theorem monoidHom_ext ⦃j k : S →* P⦄
    (h : j.comp (algebraMap R S : R →* S) = k.comp (algebraMap R S)) : j = k :=
  Submonoid.LocalizationMap.epic_of_localizationMap (toLocalizationMap M S) <| MonoidHom.congr_fun h
#align is_localization.monoid_hom_ext IsLocalization.monoidHom_ext

/- warning: is_localization.ring_hom_ext -> IsLocalization.ringHom_ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {{j : RingHom.{u2, u3} S P (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))}} {{k : RingHom.{u2, u3} S P (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))}}, (Eq.{max (succ u1) (succ u3)} (RingHom.{u1, u3} R P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))) (RingHom.comp.{u1, u2, u3} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) j (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3)) (RingHom.comp.{u1, u2, u3} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) k (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3))) -> (Eq.{max (succ u2) (succ u3)} (RingHom.{u2, u3} S P (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))) j k)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u3}} [_inst_2 : CommSemiring.{u3} S] [_inst_3 : Algebra.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] [_inst_5 : IsLocalization.{u1, u3} R _inst_1 M S _inst_2 _inst_3] {{j : RingHom.{u3, u2} S P (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))}} {{k : RingHom.{u3, u2} S P (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))}}, (Eq.{max (succ u1) (succ u2)} (RingHom.{u1, u2} R P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))) (RingHom.comp.{u1, u3, u2} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) j (algebraMap.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2) _inst_3)) (RingHom.comp.{u1, u3, u2} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) k (algebraMap.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2) _inst_3))) -> (Eq.{max (succ u3) (succ u2)} (RingHom.{u3, u2} S P (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))) j k)
Case conversion may be inaccurate. Consider using '#align is_localization.ring_hom_ext IsLocalization.ringHom_extₓ'. -/
/-- See note [partially-applied ext lemmas] -/
theorem ringHom_ext ⦃j k : S →+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) :
    j = k :=
  RingHom.coe_monoidHom_injective <| monoidHom_ext M <| MonoidHom.ext <| RingHom.congr_fun h
#align is_localization.ring_hom_ext IsLocalization.ringHom_ext

/- warning: is_localization.alg_hom_subsingleton -> IsLocalization.algHom_subsingleton is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] [_inst_6 : Algebra.{u1, u3} R P _inst_1 (CommSemiring.toSemiring.{u3} P _inst_4)], Subsingleton.{max (succ u2) (succ u3)} (AlgHom.{u1, u2, u3} R S P _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) (CommSemiring.toSemiring.{u3} P _inst_4) _inst_3 _inst_6)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] (M : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u3, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] [_inst_5 : IsLocalization.{u3, u1} R _inst_1 M S _inst_2 _inst_3] [_inst_6 : Algebra.{u3, u2} R P _inst_1 (CommSemiring.toSemiring.{u2} P _inst_4)], Subsingleton.{max (succ u2) (succ u1)} (AlgHom.{u3, u1, u2} R S P _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) (CommSemiring.toSemiring.{u2} P _inst_4) _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align is_localization.alg_hom_subsingleton IsLocalization.algHom_subsingletonₓ'. -/
/- This is not an instance because the submonoid `M` would become a metavariable
  in typeclass search. -/
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebra_map, g.comp_algebra_map]⟩
#align is_localization.alg_hom_subsingleton IsLocalization.algHom_subsingleton

/- warning: is_localization.ext -> IsLocalization.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.ext IsLocalization.extₓ'. -/
/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected theorem ext (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
    (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
    (h : ∀ a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  MonoidHom.mk.inj (monoidHom_ext M <| MonoidHom.ext h : (⟨j, hj1, hjm⟩ : S →* P) = ⟨k, hk1, hkm⟩)
#align is_localization.ext IsLocalization.ext

variable {M}

/- warning: is_localization.lift_unique -> IsLocalization.lift_unique is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_unique IsLocalization.lift_uniqueₓ'. -/
theorem lift_unique {j : S →+* P} (hj : ∀ x, j ((algebraMap R S) x) = g x) : lift hg = j :=
  RingHom.ext <|
    MonoidHom.ext_iff.1 <|
      @Submonoid.LocalizationMap.lift_unique _ _ _ _ _ _ _ (toLocalizationMap M S) g.toMonoidHom hg
        j.toMonoidHom hj
#align is_localization.lift_unique IsLocalization.lift_unique

/- warning: is_localization.lift_id -> IsLocalization.lift_id is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : S), Eq.{succ u2} S (coeFn.{succ u2, succ u2} (RingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (fun (_x : RingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) => S -> S) (RingHom.hasCoeToFun.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (IsLocalization.lift.{u1, u2, u2} R _inst_1 M S _inst_2 _inst_3 S _inst_2 _inst_5 (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (IsLocalization.map_units.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5)) x) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (x : S), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : S) => S) x) (FunLike.coe.{succ u2, succ u2, succ u2} (RingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) S (fun (_x : S) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : S) => S) _x) (MulHomClass.toFunLike.{u2, u2, u2} (RingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) S S (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{u2, u2, u2} (RingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) S S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{u2, u2, u2} (RingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u2} S S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))))) (IsLocalization.lift.{u1, u2, u2} R _inst_1 M S _inst_2 _inst_3 S _inst_2 _inst_5 (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (IsLocalization.map_units.{u2, u1} R _inst_1 M S _inst_2 _inst_3 _inst_5)) x) x
Case conversion may be inaccurate. Consider using '#align is_localization.lift_id IsLocalization.lift_idₓ'. -/
@[simp]
theorem lift_id (x) : lift (map_units S : ∀ y : M, IsUnit _) x = x :=
  (toLocalizationMap M S).lift_id _
#align is_localization.lift_id IsLocalization.lift_id

/- warning: is_localization.lift_surjective_iff -> IsLocalization.lift_surjective_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_surjective_iff IsLocalization.lift_surjective_iffₓ'. -/
theorem lift_surjective_iff :
    Surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
  (toLocalizationMap M S).lift_surjective_iff hg
#align is_localization.lift_surjective_iff IsLocalization.lift_surjective_iff

/- warning: is_localization.lift_injective_iff -> IsLocalization.lift_injective_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_injective_iff IsLocalization.lift_injective_iffₓ'. -/
theorem lift_injective_iff :
    Injective (lift hg : S → P) ↔ ∀ x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (toLocalizationMap M S).lift_injective_iff hg
#align is_localization.lift_injective_iff IsLocalization.lift_injective_iff

section Map

variable {T : Submonoid P} {Q : Type _} [CommSemiring Q] (hy : M ≤ T.comap g)

variable [Algebra P Q] [IsLocalization T Q]

section

variable (Q)

/- warning: is_localization.map -> IsLocalization.map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map IsLocalization.mapₓ'. -/
/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebra_map P Q (g x) * (algebra_map P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  @lift R _ M _ _ _ _ _ _ ((algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩
#align is_localization.map IsLocalization.map

end

/- warning: is_localization.map_eq -> IsLocalization.map_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_eq IsLocalization.map_eqₓ'. -/
theorem map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x
#align is_localization.map_eq IsLocalization.map_eq

/- warning: is_localization.map_comp -> IsLocalization.map_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_comp IsLocalization.map_compₓ'. -/
@[simp]
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp fun y => map_units _ ⟨g y, hy y.2⟩
#align is_localization.map_comp IsLocalization.map_comp

/- warning: is_localization.map_mk' -> IsLocalization.map_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_mk' IsLocalization.map_mk'ₓ'. -/
theorem map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  @Submonoid.LocalizationMap.map_mk' _ _ _ _ _ _ _ (toLocalizationMap M S) g.toMonoidHom _
    (fun y => hy y.2) _ _ (toLocalizationMap T Q) _ _
#align is_localization.map_mk' IsLocalization.map_mk'

/- warning: is_localization.map_id -> IsLocalization.map_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_id IsLocalization.map_idₓ'. -/
@[simp]
theorem map_id (z : S) (h : M ≤ M.comap (RingHom.id R) := le_refl M) :
    map S (RingHom.id _) h z = z :=
  lift_id _
#align is_localization.map_id IsLocalization.map_id

/- warning: is_localization.map_unique -> IsLocalization.map_unique is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_unique IsLocalization.map_uniqueₓ'. -/
theorem map_unique (j : S →+* Q) (hj : ∀ x : R, j (algebraMap R S x) = algebraMap P Q (g x)) :
    map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj
#align is_localization.map_unique IsLocalization.map_unique

/- warning: is_localization.map_comp_map -> IsLocalization.map_comp_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_comp_map IsLocalization.map_comp_mapₓ'. -/
/-- If `comm_semiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {A : Type _} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
    [Algebra A W] [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
    (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) fun x hx => hl (hy hx) :=
  RingHom.ext fun x =>
    @Submonoid.LocalizationMap.map_map _ _ _ _ _ P _ (toLocalizationMap M S) g _ _ _ _ _ _ _ _ _ _
      (toLocalizationMap U W) l _ x
#align is_localization.map_comp_map IsLocalization.map_comp_map

/- warning: is_localization.map_map -> IsLocalization.map_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_map IsLocalization.map_mapₓ'. -/
/-- If `comm_semiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_map {A : Type _} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
    [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
    map W l hl (map Q g hy x) = map W (l.comp g) (fun x hx => hl (hy hx)) x := by
  rw [← map_comp_map hy hl] <;> rfl
#align is_localization.map_map IsLocalization.map_map

/- warning: is_localization.map_smul -> IsLocalization.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_smul IsLocalization.map_smulₓ'. -/
theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, map_eq]
#align is_localization.map_smul IsLocalization.map_smul

section

variable (S Q)

/- warning: is_localization.ring_equiv_of_ring_equiv -> IsLocalization.ringEquivOfRingEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {T : Submonoid.{u3} P (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))} (Q : Type.{u4}) [_inst_6 : CommSemiring.{u4} Q] [_inst_7 : Algebra.{u3, u4} P Q _inst_4 (CommSemiring.toSemiring.{u4} Q _inst_6)] [_inst_8 : IsLocalization.{u3, u4} P _inst_4 T Q _inst_6 _inst_7] (h : RingEquiv.{u1, u3} R P (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasMul.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Distrib.toHasAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))))), (Eq.{succ u3} (Submonoid.{u3} P (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Submonoid.map.{u1, u3, max u3 u1} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))) (MonoidHom.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (MonoidHom.monoidHomClass.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (RingEquiv.toMonoidHom.{u1, u3} R P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) h) M) T) -> (RingEquiv.{u2, u4} S Q (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Distrib.toHasAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Distrib.toHasMul.{u4} Q (NonUnitalNonAssocSemiring.toDistrib.{u4} Q (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} Q (Semiring.toNonAssocSemiring.{u4} Q (CommSemiring.toSemiring.{u4} Q _inst_6))))) (Distrib.toHasAdd.{u4} Q (NonUnitalNonAssocSemiring.toDistrib.{u4} Q (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} Q (Semiring.toNonAssocSemiring.{u4} Q (CommSemiring.toSemiring.{u4} Q _inst_6))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] {T : Submonoid.{u3} P (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))} (Q : Type.{u4}) [_inst_6 : CommSemiring.{u4} Q] [_inst_7 : Algebra.{u3, u4} P Q _inst_4 (CommSemiring.toSemiring.{u4} Q _inst_6)] [_inst_8 : IsLocalization.{u3, u4} P _inst_4 T Q _inst_6 _inst_7] (h : RingEquiv.{u1, u3} R P (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))))), (Eq.{succ u3} (Submonoid.{u3} P (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Submonoid.map.{u1, u3, max u1 u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))) (MonoidHom.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (MonoidHom.monoidHomClass.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (RingEquiv.toMonoidHom.{u1, u3} R P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) h) M) T) -> (RingEquiv.{u2, u4} S Q (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u4} Q (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} Q (Semiring.toNonAssocSemiring.{u4} Q (CommSemiring.toSemiring.{u4} Q _inst_6)))) (Distrib.toAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Distrib.toAdd.{u4} Q (NonUnitalNonAssocSemiring.toDistrib.{u4} Q (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} Q (Semiring.toNonAssocSemiring.{u4} Q (CommSemiring.toSemiring.{u4} Q _inst_6))))))
Case conversion may be inaccurate. Consider using '#align is_localization.ring_equiv_of_ring_equiv IsLocalization.ringEquivOfRingEquivₓ'. -/
/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M :=
    by
    rw [← M.map_id, ← H, Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  {
    map Q (h : R →+* P)
      _ with
    toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x =>
      by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      intro x
      convert congr_arg (algebraMap R S) (h.symm_apply_apply x).symm
    right_inv := fun x =>
      by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      intro x
      convert congr_arg (algebraMap P Q) (h.apply_symm_apply x).symm }
#align is_localization.ring_equiv_of_ring_equiv IsLocalization.ringEquivOfRingEquiv

end

/- warning: is_localization.ring_equiv_of_ring_equiv_eq_map -> IsLocalization.ringEquivOfRingEquiv_eq_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.ring_equiv_of_ring_equiv_eq_map IsLocalization.ringEquivOfRingEquiv_eq_mapₓ'. -/
theorem ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) :
    (ringEquivOfRingEquiv S Q j H : S →+* Q) =
      map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl
#align is_localization.ring_equiv_of_ring_equiv_eq_map IsLocalization.ringEquivOfRingEquiv_eq_map

/- warning: is_localization.ring_equiv_of_ring_equiv_eq -> IsLocalization.ringEquivOfRingEquiv_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.ring_equiv_of_ring_equiv_eq IsLocalization.ringEquivOfRingEquiv_eqₓ'. -/
@[simp]
theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
    ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) :=
  map_eq _ _
#align is_localization.ring_equiv_of_ring_equiv_eq IsLocalization.ringEquivOfRingEquiv_eq

/- warning: is_localization.ring_equiv_of_ring_equiv_mk' -> IsLocalization.ringEquivOfRingEquiv_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.ring_equiv_of_ring_equiv_mk' IsLocalization.ringEquivOfRingEquiv_mk'ₓ'. -/
theorem ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M) :
    ringEquivOfRingEquiv S Q j H (mk' S x y) =
      mk' Q (j x) ⟨j y, show j y ∈ T from H ▸ Set.mem_image_of_mem j y.2⟩ :=
  map_mk' _ _ _
#align is_localization.ring_equiv_of_ring_equiv_mk' IsLocalization.ringEquivOfRingEquiv_mk'

end Map

section AlgEquiv

variable {Q : Type _} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

section

variable (M S Q)

#print IsLocalization.algEquiv /-
/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps]
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }
#align is_localization.alg_equiv IsLocalization.algEquiv
-/

end

/- warning: is_localization.alg_equiv_mk' -> IsLocalization.algEquiv_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.alg_equiv_mk' IsLocalization.algEquiv_mk'ₓ'. -/
@[simp]
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y :=
  map_mk' _ _ _
#align is_localization.alg_equiv_mk' IsLocalization.algEquiv_mk'

/- warning: is_localization.alg_equiv_symm_mk' -> IsLocalization.algEquiv_symm_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.alg_equiv_symm_mk' IsLocalization.algEquiv_symm_mk'ₓ'. -/
@[simp]
theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y :=
  map_mk' _ _ _
#align is_localization.alg_equiv_symm_mk' IsLocalization.algEquiv_symm_mk'

end AlgEquiv

end IsLocalization

section

variable (M)

/- warning: is_localization.is_localization_of_alg_equiv -> IsLocalization.isLocalization_of_algEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : Algebra.{u1, u3} R P _inst_1 (CommSemiring.toSemiring.{u3} P _inst_4)] [_inst_6 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], (AlgEquiv.{u1, u2, u3} R S P _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) (CommSemiring.toSemiring.{u3} P _inst_4) _inst_3 _inst_5) -> (IsLocalization.{u1, u3} R _inst_1 M P _inst_4 _inst_5)
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] (M : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u3, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] [_inst_5 : Algebra.{u3, u2} R P _inst_1 (CommSemiring.toSemiring.{u2} P _inst_4)] [_inst_6 : IsLocalization.{u3, u1} R _inst_1 M S _inst_2 _inst_3], (AlgEquiv.{u3, u1, u2} R S P _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) (CommSemiring.toSemiring.{u2} P _inst_4) _inst_3 _inst_5) -> (IsLocalization.{u3, u2} R _inst_1 M P _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align is_localization.is_localization_of_alg_equiv IsLocalization.isLocalization_of_algEquivₓ'. -/
theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor
  · intro y
    convert(IsLocalization.map_units S y).map h.to_alg_hom.to_ring_hom.to_monoid_hom
    exact (h.commutes y).symm
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    apply_fun h  at e
    simp only [h.map_mul, h.apply_symm_apply, h.commutes] at e
    exact ⟨⟨x, s⟩, e⟩
  · intro x y
    rw [← h.symm.to_equiv.injective.eq_iff, ← IsLocalization.eq_iff_exists M S, ← h.symm.commutes, ←
      h.symm.commutes]
    rfl
#align is_localization.is_localization_of_alg_equiv IsLocalization.isLocalization_of_algEquiv

/- warning: is_localization.is_localization_iff_of_alg_equiv -> IsLocalization.isLocalization_iff_of_algEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : Algebra.{u1, u3} R P _inst_1 (CommSemiring.toSemiring.{u3} P _inst_4)], (AlgEquiv.{u1, u2, u3} R S P _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) (CommSemiring.toSemiring.{u3} P _inst_4) _inst_3 _inst_5) -> (Iff (IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3) (IsLocalization.{u1, u3} R _inst_1 M P _inst_4 _inst_5))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] (M : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u3, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] [_inst_5 : Algebra.{u3, u2} R P _inst_1 (CommSemiring.toSemiring.{u2} P _inst_4)], (AlgEquiv.{u3, u1, u2} R S P _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) (CommSemiring.toSemiring.{u2} P _inst_4) _inst_3 _inst_5) -> (Iff (IsLocalization.{u3, u1} R _inst_1 M S _inst_2 _inst_3) (IsLocalization.{u3, u2} R _inst_1 M P _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align is_localization.is_localization_iff_of_alg_equiv IsLocalization.isLocalization_iff_of_algEquivₓ'. -/
theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => is_localization_of_alg_equiv M h, fun _ => is_localization_of_alg_equiv M h.symm⟩
#align is_localization.is_localization_iff_of_alg_equiv IsLocalization.isLocalization_iff_of_algEquiv

/- warning: is_localization.is_localization_iff_of_ring_equiv -> IsLocalization.isLocalization_iff_of_ringEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u2}} [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] (h : RingEquiv.{u2, u3} S P (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Distrib.toHasAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Distrib.toHasMul.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Distrib.toHasAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))))), Iff (IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3) (IsLocalization.{u1, u3} R _inst_1 M P _inst_4 (RingHom.toAlgebra.{u1, u3} R P _inst_1 _inst_4 (RingHom.comp.{u1, u2, u3} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) (RingEquiv.toRingHom.{u2, u3} S P (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) h) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) {S : Type.{u3}} [_inst_2 : CommSemiring.{u3} S] [_inst_3 : Algebra.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] (h : RingEquiv.{u3, u2} S P (NonUnitalNonAssocSemiring.toMul.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u2} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)))) (Distrib.toAdd.{u3} S (NonUnitalNonAssocSemiring.toDistrib.{u3} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} S (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2))))) (Distrib.toAdd.{u2} P (NonUnitalNonAssocSemiring.toDistrib.{u2} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)))))), Iff (IsLocalization.{u1, u3} R _inst_1 M S _inst_2 _inst_3) (IsLocalization.{u1, u2} R _inst_1 M P _inst_4 (RingHom.toAlgebra.{u1, u2} R P _inst_1 _inst_4 (RingHom.comp.{u1, u3, u2} R S P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) (RingEquiv.toRingHom.{u3, u2} S P (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S _inst_2)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) h) (algebraMap.{u1, u3} R S _inst_1 (CommSemiring.toSemiring.{u3} S _inst_2) _inst_3))))
Case conversion may be inaccurate. Consider using '#align is_localization.is_localization_iff_of_ring_equiv IsLocalization.isLocalization_iff_of_ringEquivₓ'. -/
theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔ @IsLocalization _ M P _ (h.toRingHom.comp <| algebraMap R S).toAlgebra :=
  letI := (h.to_ring_hom.comp <| algebraMap R S).toAlgebra
  is_localization_iff_of_alg_equiv M { h with commutes' := fun _ => rfl }
#align is_localization.is_localization_iff_of_ring_equiv IsLocalization.isLocalization_iff_of_ringEquiv

variable (S)

/- warning: is_localization.is_localization_of_base_ring_equiv -> IsLocalization.isLocalization_of_base_ringEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3] (h : RingEquiv.{u1, u3} R P (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasMul.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Distrib.toHasAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))))), IsLocalization.{u3, u2} P _inst_4 (Submonoid.map.{u1, u3, max u3 u1} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))) (MonoidHom.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (MonoidHom.monoidHomClass.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (RingEquiv.toMonoidHom.{u1, u3} R P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) h) M) S _inst_2 (RingHom.toAlgebra.{u3, u2} P S _inst_4 _inst_2 (RingHom.comp.{u3, u1, u2} P R S (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (RingEquiv.toRingHom.{u3, u1} P R (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingEquiv.symm.{u1, u3} R P (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasMul.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Distrib.toHasAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) h))))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] (M : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u1}} [_inst_4 : CommSemiring.{u1} P] [_inst_5 : IsLocalization.{u3, u2} R _inst_1 M S _inst_2 _inst_3] (h : RingEquiv.{u3, u1} R P (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)))) (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (Distrib.toAdd.{u1} P (NonUnitalNonAssocSemiring.toDistrib.{u1} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)))))), IsLocalization.{u1, u2} P _inst_4 (Submonoid.map.{u3, u1, max u3 u1} R P (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} P (NonAssocSemiring.toMulZeroOneClass.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)))) (MonoidHom.{u3, u1} R P (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} P (NonAssocSemiring.toMulZeroOneClass.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4))))) (MonoidHom.monoidHomClass.{u3, u1} R P (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} P (NonAssocSemiring.toMulZeroOneClass.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4))))) (RingEquiv.toMonoidHom.{u3, u1} R P (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)) h) M) S _inst_2 (RingHom.toAlgebra.{u1, u2} P S _inst_4 _inst_2 (RingHom.comp.{u1, u3, u2} P R S (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (algebraMap.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (RingEquiv.toRingHom.{u1, u3} P R (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (RingEquiv.symm.{u3, u1} R P (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4)))) (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (Distrib.toAdd.{u1} P (NonUnitalNonAssocSemiring.toDistrib.{u1} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} P (Semiring.toNonAssocSemiring.{u1} P (CommSemiring.toSemiring.{u1} P _inst_4))))) h))))
Case conversion may be inaccurate. Consider using '#align is_localization.is_localization_of_base_ring_equiv IsLocalization.isLocalization_of_base_ringEquivₓ'. -/
theorem isLocalization_of_base_ringEquiv [IsLocalization M S] (h : R ≃+* P) :
    @IsLocalization _ (M.map h.toMonoidHom) S _
      ((algebraMap R S).comp h.symm.toRingHom).toAlgebra :=
  by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert IsLocalization.map_units S ⟨y, hy⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    exact congr_arg _ (h.symm_apply_apply _)
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M y
    refine' ⟨⟨h x, _, _, s.prop, rfl⟩, _⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at e⊢
    convert e <;> exact h.symm_apply_apply _
  · intro x y
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply,
      IsLocalization.eq_iff_exists M S]
    simp_rw [← h.to_equiv.apply_eq_iff_eq]
    change (∃ c : M, h (c * h.symm x) = h (c * h.symm y)) ↔ _
    simp only [RingEquiv.apply_symm_apply, RingEquiv.map_mul]
    exact
      ⟨fun ⟨c, e⟩ => ⟨⟨_, _, c.Prop, rfl⟩, e⟩, fun ⟨⟨_, c, h, e₁⟩, e₂⟩ => ⟨⟨_, h⟩, e₁.symm ▸ e₂⟩⟩
#align is_localization.is_localization_of_base_ring_equiv IsLocalization.isLocalization_of_base_ringEquiv

/- warning: is_localization.is_localization_iff_of_base_ring_equiv -> IsLocalization.isLocalization_iff_of_base_ringEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] {P : Type.{u3}} [_inst_4 : CommSemiring.{u3} P] (h : RingEquiv.{u1, u3} R P (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasMul.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Distrib.toHasAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))))), Iff (IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3) (IsLocalization.{u3, u2} P _inst_4 (Submonoid.map.{u1, u3, max u3 u1} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)))) (MonoidHom.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (MonoidHom.monoidHomClass.{u1, u3} R P (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u3} P (NonAssocSemiring.toMulZeroOneClass.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (RingEquiv.toMonoidHom.{u1, u3} R P (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) h) M) S _inst_2 (RingHom.toAlgebra.{u3, u2} P S _inst_4 _inst_2 (RingHom.comp.{u3, u1, u2} P R S (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (RingEquiv.toRingHom.{u3, u1} P R (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4)) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (RingEquiv.symm.{u1, u3} R P (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Distrib.toHasMul.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) (Distrib.toHasAdd.{u3} P (NonUnitalNonAssocSemiring.toDistrib.{u3} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} P (Semiring.toNonAssocSemiring.{u3} P (CommSemiring.toSemiring.{u3} P _inst_4))))) h)))))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] (M : Submonoid.{u3} R (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (S : Type.{u1}) [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u3, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] {P : Type.{u2}} [_inst_4 : CommSemiring.{u2} P] (h : RingEquiv.{u3, u2} R P (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)))) (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (Distrib.toAdd.{u2} P (NonUnitalNonAssocSemiring.toDistrib.{u2} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)))))), Iff (IsLocalization.{u3, u1} R _inst_1 M S _inst_2 _inst_3) (IsLocalization.{u2, u1} P _inst_4 (Submonoid.map.{u3, u2, max u3 u2} R P (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} P (NonAssocSemiring.toMulZeroOneClass.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)))) (MonoidHom.{u3, u2} R P (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} P (NonAssocSemiring.toMulZeroOneClass.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))))) (MonoidHom.monoidHomClass.{u3, u2} R P (MulZeroOneClass.toMulOneClass.{u3} R (NonAssocSemiring.toMulZeroOneClass.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} P (NonAssocSemiring.toMulZeroOneClass.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))))) (RingEquiv.toMonoidHom.{u3, u2} R P (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) h) M) S _inst_2 (RingHom.toAlgebra.{u2, u1} P S _inst_4 _inst_2 (RingHom.comp.{u2, u3, u1} P R S (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (algebraMap.{u3, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) (RingEquiv.toRingHom.{u2, u3} P R (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)) (RingEquiv.symm.{u3, u2} R P (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4)))) (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (Distrib.toAdd.{u2} P (NonUnitalNonAssocSemiring.toDistrib.{u2} P (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} P (Semiring.toNonAssocSemiring.{u2} P (CommSemiring.toSemiring.{u2} P _inst_4))))) h)))))
Case conversion may be inaccurate. Consider using '#align is_localization.is_localization_iff_of_base_ring_equiv IsLocalization.isLocalization_iff_of_base_ringEquivₓ'. -/
theorem isLocalization_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsLocalization M S ↔
      @IsLocalization _ (M.map h.toMonoidHom) S _
        ((algebraMap R S).comp h.symm.toRingHom).toAlgebra :=
  by
  refine' ⟨fun _ => is_localization_of_base_ring_equiv _ _ h, _⟩
  letI := ((algebraMap R S).comp h.symm.to_ring_hom).toAlgebra
  intro H
  convert@is_localization_of_base_ring_equiv _ _ _ _ _ _ H h.symm
  · erw [Submonoid.map_equiv_eq_comap_symm, Submonoid.comap_map_eq_of_injective]
    exact h.to_equiv.injective
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc]
  simp only [RingHom.comp_id, RingEquiv.symm_symm, RingEquiv.symm_toRingHom_comp_toRingHom]
  apply Algebra.algebra_ext
  intro r
  rw [RingHom.algebraMap_toAlgebra]
#align is_localization.is_localization_iff_of_base_ring_equiv IsLocalization.isLocalization_iff_of_base_ringEquiv

end

variable (M S)

include M

/- warning: is_localization.non_zero_divisors_le_comap -> IsLocalization.nonZeroDivisors_le_comap is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], LE.le.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Preorder.toHasLe.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Submonoid.completeLattice.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) (nonZeroDivisors.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Submonoid.comap.{u1, u2, max u1 u2} R S (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toMonoidHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (nonZeroDivisors.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (S : Type.{u1}) [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3], LE.le.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Preorder.toLE.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))))))) (nonZeroDivisors.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Submonoid.comap.{u2, u1, max u2 u1} R S (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} S (MonoidWithZero.toMulZeroOneClass.{u1} S (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (RingHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (algebraMap.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) (nonZeroDivisors.{u1} S (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_localization.non_zero_divisors_le_comap IsLocalization.nonZeroDivisors_le_comapₓ'. -/
theorem nonZeroDivisors_le_comap [IsLocalization M S] :
    nonZeroDivisors R ≤ (nonZeroDivisors S).comap (algebraMap R S) :=
  by
  rintro a ha b (e : b * algebraMap R S a = 0)
  obtain ⟨x, s, rfl⟩ := mk'_surjective M b
  rw [← @mk'_one R _ M, ← mk'_mul, ← (algebraMap R S).map_zero, ← @mk'_one R _ M,
    IsLocalization.eq] at e
  obtain ⟨c, e⟩ := e
  rw [MulZeroClass.mul_zero, MulZeroClass.mul_zero, Submonoid.coe_one, one_mul, ← mul_assoc] at e
  rw [mk'_eq_zero_iff]
  exact ⟨c, ha _ e⟩
#align is_localization.non_zero_divisors_le_comap IsLocalization.nonZeroDivisors_le_comap

/- warning: is_localization.map_non_zero_divisors_le -> IsLocalization.map_nonZeroDivisors_le is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], LE.le.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Preorder.toHasLe.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (Submonoid.completeLattice.{u2} S (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))))) (Submonoid.map.{u1, u2, max u1 u2} R S (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (RingHomClass.toMonoidHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (RingHom.ringHomClass.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (algebraMap.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_3) (nonZeroDivisors.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (nonZeroDivisors.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (S : Type.{u1}) [_inst_2 : CommSemiring.{u1} S] [_inst_3 : Algebra.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2)] [_inst_5 : IsLocalization.{u2, u1} R _inst_1 M S _inst_2 _inst_3], LE.le.{u1} (Submonoid.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (Preorder.toLE.{u1} (Submonoid.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submonoid.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submonoid.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) (Submonoid.instCompleteLatticeSubmonoid.{u1} S (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))))))) (Submonoid.map.{u2, u1, max u2 u1} R S (MulZeroOneClass.toMulOneClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} S (NonAssocSemiring.toMulZeroOneClass.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) (RingHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (algebraMap.{u2, u1} R S _inst_1 (CommSemiring.toSemiring.{u1} S _inst_2) _inst_3) (nonZeroDivisors.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (nonZeroDivisors.{u1} S (Semiring.toMonoidWithZero.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_localization.map_non_zero_divisors_le IsLocalization.map_nonZeroDivisors_leₓ'. -/
theorem map_nonZeroDivisors_le [IsLocalization M S] :
    (nonZeroDivisors R).map (algebraMap R S) ≤ nonZeroDivisors S :=
  Submonoid.map_le_iff_le_comap.mpr (nonZeroDivisors_le_comap M S)
#align is_localization.map_non_zero_divisors_le IsLocalization.map_nonZeroDivisors_le

end IsLocalization

namespace Localization

open IsLocalization

/-! ### Constructing a localization at a given submonoid -/


variable {M}

section

instance [Subsingleton R] : Unique (Localization M) :=
  ⟨⟨1⟩, by intro a; induction a; induction default; congr ; rfl; rfl⟩

#print Localization.add /-
/-- Addition in a ring localization is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨b * c + d * a, b * d⟩`.

Should not be confused with `add_localization.add`, which is defined as
`⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.
-/
protected irreducible_def add (z w : Localization M) : Localization M :=
  Localization.liftOn₂ z w (fun a b c d => mk ((b : R) * c + d * a) (b * d))
    fun a a' b b' c c' d d' h1 h2 =>
    mk_eq_mk_iff.2
      (by
        rw [r_eq_r'] at h1 h2⊢
        cases' h1 with t₅ ht₅
        cases' h2 with t₆ ht₆
        use t₅ * t₆
        dsimp only
        calc
          ↑t₅ * ↑t₆ * (↑b' * ↑d' * ((b : R) * c + d * a)) =
              t₆ * (d' * c) * (t₅ * (b' * b)) + t₅ * (b' * a) * (t₆ * (d' * d)) :=
            by ring
          _ = t₅ * t₆ * (b * d * (b' * c' + d' * a')) := by rw [ht₆, ht₅] <;> ring
          )
#align localization.add Localization.add
-/

instance : Add (Localization M) :=
  ⟨Localization.add⟩

/- warning: localization.add_mk -> Localization.add_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.add_mk Localization.add_mkₓ'. -/
theorem add_mk (a b c d) : (mk a b : Localization M) + mk c d = mk (b * c + d * a) (b * d) :=
  by
  unfold Add.add Localization.add
  apply lift_on₂_mk
#align localization.add_mk Localization.add_mk

/- warning: localization.add_mk_self -> Localization.add_mk_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (a : R) (b : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M) (c : R), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (HAdd.hAdd.{u1, u1, u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (instHAdd.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.hasAdd.{u1} R _inst_1 M)) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M a b) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M c b)) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) a c) b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (a : R) (b : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) x M)) (c : R), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (HAdd.hAdd.{u1, u1, u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (instHAdd.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instAddLocalizationToCommMonoid.{u1} R _inst_1 M)) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M a b) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M c b)) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) a c) b)
Case conversion may be inaccurate. Consider using '#align localization.add_mk_self Localization.add_mk_selfₓ'. -/
theorem add_mk_self (a b c) : (mk a b : Localization M) + mk c b = mk (a + c) b :=
  by
  rw [add_mk, mk_eq_mk_iff, r_eq_r']
  refine' (r' M).symm ⟨1, _⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  ring
#align localization.add_mk_self Localization.add_mk_self

/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def tac :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2028012893.tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2028012893.tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2028012893.tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2028012893.tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2028012893.tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.2028012893.tac -/
instance : CommSemiring (Localization M) :=
  { Localization.commMonoidWithZero M with
    zero := 0
    one := 1
    add := (· + ·)
    mul := (· * ·)
    npow := Localization.npow _
    nsmul := (· • ·)
    nsmul_zero := fun x =>
      Localization.induction_on x fun x => by simp only [smul_mk, zero_nsmul, mk_zero]
    nsmul_succ := fun n x =>
      Localization.induction_on x fun x => by simp only [smul_mk, succ_nsmul, add_mk_self]
    add_assoc := fun m n k =>
      Localization.induction_on₃ m n k
        (by
          run_tac
            tac)
    zero_add := fun y =>
      Localization.induction_on y
        (by
          run_tac
            tac)
    add_zero := fun y =>
      Localization.induction_on y
        (by
          run_tac
            tac)
    add_comm := fun y z =>
      Localization.induction_on₂ z y
        (by
          run_tac
            tac)
    left_distrib := fun m n k =>
      Localization.induction_on₃ m n k
        (by
          run_tac
            tac)
    right_distrib := fun m n k =>
      Localization.induction_on₃ m n k
        (by
          run_tac
            tac) }

/- warning: localization.mk_add_monoid_hom -> Localization.mkAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))}, (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M) -> (AddMonoidHom.{u1, u1} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddMonoidWithOne.toAddMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toAddCommMonoidWithOne.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))}, (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)) -> (AddMonoidHom.{u1, u1} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddMonoidWithOne.toAddMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toAddCommMonoidWithOne.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M))))))))
Case conversion may be inaccurate. Consider using '#align localization.mk_add_monoid_hom Localization.mkAddMonoidHomₓ'. -/
/-- For any given denominator `b : M`, the map `a ↦ a / b` is an `add_monoid_hom` from `R` to
  `localization M`-/
@[simps]
def mkAddMonoidHom (b : M) : R →+ Localization M
    where
  toFun a := mk a b
  map_zero' := mk_zero _
  map_add' x y := (add_mk_self _ _ _).symm
#align localization.mk_add_monoid_hom Localization.mkAddMonoidHom

/- warning: localization.mk_sum -> Localization.mk_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {ι : Type.{u2}} (f : ι -> R) (s : Finset.{u2} ι) (b : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => f i)) b) (Finset.sum.{u1, u2} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M))))) s (fun (i : ι) => Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (f i) b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} {ι : Type.{u2}} (f : ι -> R) (s : Finset.{u2} ι) (b : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Finset.sum.{u1, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) s (fun (i : ι) => f i)) b) (Finset.sum.{u1, u2} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M))))) s (fun (i : ι) => Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (f i) b))
Case conversion may be inaccurate. Consider using '#align localization.mk_sum Localization.mk_sumₓ'. -/
theorem mk_sum {ι : Type _} (f : ι → R) (s : Finset ι) (b : M) :
    mk (∑ i in s, f i) b = ∑ i in s, mk (f i) b :=
  (mkAddMonoidHom b).map_sum f s
#align localization.mk_sum Localization.mk_sum

/- warning: localization.mk_list_sum -> Localization.mk_list_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (l : List.{u1} R) (b : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) l) b) (List.sum.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.hasAdd.{u1} R _inst_1 M) (Localization.hasZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1) M) (List.map.{u1, u1} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (fun (a : R) => Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M a b) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (l : List.{u1} R) (b : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1)) l) b) (List.sum.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instAddLocalizationToCommMonoid.{u1} R _inst_1 M) (Localization.instZeroLocalizationToCommMonoid.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1) M) (List.map.{u1, u1} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (fun (a : R) => Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M a b) l))
Case conversion may be inaccurate. Consider using '#align localization.mk_list_sum Localization.mk_list_sumₓ'. -/
theorem mk_list_sum (l : List R) (b : M) : mk l.Sum b = (l.map fun a => mk a b).Sum :=
  (mkAddMonoidHom b).map_list_sum l
#align localization.mk_list_sum Localization.mk_list_sum

/- warning: localization.mk_multiset_sum -> Localization.mk_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (l : Multiset.{u1} R) (b : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) M), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) l) b) (Multiset.sum.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M))))) (Multiset.map.{u1, u1} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (fun (a : R) => Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M a b) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (l : Multiset.{u1} R) (b : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) R (Submonoid.instSetLikeSubmonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x M)), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Multiset.sum.{u1} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) l) b) (Multiset.sum.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M))))) (Multiset.map.{u1, u1} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (fun (a : R) => Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M a b) l))
Case conversion may be inaccurate. Consider using '#align localization.mk_multiset_sum Localization.mk_multiset_sumₓ'. -/
theorem mk_multiset_sum (l : Multiset R) (b : M) : mk l.Sum b = (l.map fun a => mk a b).Sum :=
  (mkAddMonoidHom b).map_multiset_sum l
#align localization.mk_multiset_sum Localization.mk_multiset_sum

instance {S : Type _} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] :
    DistribMulAction S (Localization M)
    where
  smul_zero s := by simp only [← Localization.mk_zero 1, Localization.smul_mk, smul_zero]
  smul_add s x y :=
    Localization.induction_on₂ x y <|
      Prod.rec fun r₁ x₁ =>
        Prod.rec fun r₂ x₂ => by
          simp only [Localization.smul_mk, Localization.add_mk, smul_add, mul_comm _ (s • _),
            mul_comm _ r₁, mul_comm _ r₂, smul_mul_assoc]

instance {S : Type _} [Semiring S] [MulSemiringAction S R] [IsScalarTower S R R] :
    MulSemiringAction S (Localization M) :=
  { Localization.mulDistribMulAction with }

instance {S : Type _} [Semiring S] [Module S R] [IsScalarTower S R R] : Module S (Localization M) :=
  {
    Localization.distribMulAction with
    zero_smul :=
      Localization.ind <|
        Prod.rec <| by
          intros
          simp only [Localization.smul_mk, zero_smul, mk_zero]
    add_smul := fun s₁ s₂ =>
      Localization.ind <|
        Prod.rec <| by
          intros
          simp only [Localization.smul_mk, add_smul, add_mk_self] }

instance {S : Type _} [CommSemiring S] [Algebra S R] : Algebra S (Localization M)
    where
  toRingHom :=
    RingHom.comp
      { Localization.monoidOf M with
        toFun := (monoidOf M).toMap
        map_zero' := by rw [← mk_zero (1 : M), mk_one_eq_monoid_of_mk]
        map_add' := fun x y => by
          simp only [← mk_one_eq_monoid_of_mk, add_mk, Submonoid.coe_one, one_mul, add_comm] }
      (algebraMap S R)
  smul_def' s :=
    Localization.ind <|
      Prod.rec <| by
        intro r x
        dsimp
        simp only [← mk_one_eq_monoid_of_mk, mk_mul, Localization.smul_mk, one_mul,
          Algebra.smul_def]
  commutes' s :=
    Localization.ind <|
      Prod.rec <| by
        intro r x
        dsimp
        simp only [← mk_one_eq_monoid_of_mk, mk_mul, Localization.smul_mk, one_mul, mul_one,
          Algebra.commutes]

instance : IsLocalization M (Localization M)
    where
  map_units := (Localization.monoidOf M).map_units
  surj := (Localization.monoidOf M).surj
  eq_iff_exists _ _ := (Localization.monoidOf M).eq_iff_exists

end

/- warning: localization.to_localization_map_eq_monoid_of -> Localization.toLocalizationMap_eq_monoidOf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))}, Eq.{succ u1} (Submonoid.LocalizationMap.{u1, u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toCommMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M))) (IsLocalization.toLocalizationMap.{u1, u1} R _inst_1 M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M) (Localization.algebra.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) (Localization.isLocalization.{u1} R _inst_1 M)) (Localization.monoidOf.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))}, Eq.{succ u1} (Submonoid.LocalizationMap.{u1, u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toCommMonoid.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M))) (IsLocalization.toLocalizationMap.{u1, u1} R _inst_1 M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M) (Localization.instAlgebraLocalizationToCommMonoidToSemiringInstCommSemiringLocalizationToCommMonoid.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) (Localization.isLocalization.{u1} R _inst_1 M)) (Localization.monoidOf.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M)
Case conversion may be inaccurate. Consider using '#align localization.to_localization_map_eq_monoid_of Localization.toLocalizationMap_eq_monoidOfₓ'. -/
@[simp]
theorem toLocalizationMap_eq_monoidOf : toLocalizationMap M (Localization M) = monoidOf M :=
  rfl
#align localization.to_localization_map_eq_monoid_of Localization.toLocalizationMap_eq_monoidOf

/- warning: localization.monoid_of_eq_algebra_map -> Localization.monoidOf_eq_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.monoid_of_eq_algebra_map Localization.monoidOf_eq_algebraMapₓ'. -/
theorem monoidOf_eq_algebraMap (x) : (monoidOf M).toMap x = algebraMap R (Localization M) x :=
  rfl
#align localization.monoid_of_eq_algebra_map Localization.monoidOf_eq_algebraMap

/- warning: localization.mk_one_eq_algebra_map -> Localization.mk_one_eq_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.mk_one_eq_algebra_map Localization.mk_one_eq_algebraMapₓ'. -/
theorem mk_one_eq_algebraMap (x) : mk x 1 = algebraMap R (Localization M) x :=
  rfl
#align localization.mk_one_eq_algebra_map Localization.mk_one_eq_algebraMap

/- warning: localization.mk_eq_mk'_apply -> Localization.mk_eq_mk'_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (x : R) (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M x y) (IsLocalization.mk'.{u1, u1} R _inst_1 M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M) (Localization.algebra.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) (Localization.isLocalization.{u1} R _inst_1 M) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (x : R) (y : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) x M)), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M x y) (IsLocalization.mk'.{u1, u1} R _inst_1 M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M) (Localization.instAlgebraLocalizationToCommMonoidToSemiringInstCommSemiringLocalizationToCommMonoid.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) (Localization.isLocalization.{u1} R _inst_1 M) x y)
Case conversion may be inaccurate. Consider using '#align localization.mk_eq_mk'_apply Localization.mk_eq_mk'_applyₓ'. -/
theorem mk_eq_mk'_apply (x y) : mk x y = IsLocalization.mk' (Localization M) x y := by
  rw [mk_eq_monoid_of_mk'_apply, mk', to_localization_map_eq_monoid_of]
#align localization.mk_eq_mk'_apply Localization.mk_eq_mk'_apply

/- warning: localization.mk_eq_mk' -> Localization.mk_eq_mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))}, Eq.{succ u1} (R -> (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M) -> (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M)) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (IsLocalization.mk'.{u1, u1} R _inst_1 M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M) (Localization.algebra.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) (Localization.isLocalization.{u1} R _inst_1 M))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))}, Eq.{succ u1} (R -> (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) x M)) -> (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M)) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (IsLocalization.mk'.{u1, u1} R _inst_1 M (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M) (Localization.instAlgebraLocalizationToCommMonoidToSemiringInstCommSemiringLocalizationToCommMonoid.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) (Localization.isLocalization.{u1} R _inst_1 M))
Case conversion may be inaccurate. Consider using '#align localization.mk_eq_mk' Localization.mk_eq_mk'ₓ'. -/
@[simp]
theorem mk_eq_mk' : (mk : R → M → Localization M) = IsLocalization.mk' (Localization M) :=
  mk_eq_monoidOf_mk'
#align localization.mk_eq_mk' Localization.mk_eq_mk'

/- warning: localization.mk_algebra_map -> Localization.mk_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.mk_algebra_map Localization.mk_algebraMapₓ'. -/
theorem mk_algebraMap {A : Type _} [CommSemiring A] [Algebra A R] (m : A) :
    mk (algebraMap A R m) 1 = algebraMap A (Localization M) m := by
  rw [mk_eq_mk', mk'_eq_iff_eq_mul, Submonoid.coe_one, map_one, mul_one] <;> rfl
#align localization.mk_algebra_map Localization.mk_algebraMap

/- warning: localization.mk_nat_cast -> Localization.mk_nat_cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (m : Nat), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) m) (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M) 1 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M) 1 (One.one.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) M) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (HasLiftT.mk.{1, succ u1} Nat (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CoeTCₓ.coe.{1, succ u1} Nat (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Nat.castCoe.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddMonoidWithOne.toNatCast.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (NonAssocSemiring.toAddCommMonoidWithOne.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNonAssocSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M))))))))) m)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))} (m : Nat), Eq.{succ u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) m) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) x M)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1))))) x M)) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) M)))) (Nat.cast.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Semiring.toNatCast.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M))) m)
Case conversion may be inaccurate. Consider using '#align localization.mk_nat_cast Localization.mk_nat_castₓ'. -/
theorem mk_nat_cast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using @mk_algebra_map R _ M ℕ _ _ m
#align localization.mk_nat_cast Localization.mk_nat_cast

variable [IsLocalization M S]

section

variable (M S)

/- warning: localization.alg_equiv -> Localization.algEquiv is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], AlgEquiv.{u1, u1, u2} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) S _inst_1 (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.commSemiring.{u1} R _inst_1 M)) (CommSemiring.toSemiring.{u2} S _inst_2) (Localization.algebra.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) _inst_3
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (S : Type.{u2}) [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : IsLocalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3], AlgEquiv.{u1, u1, u2} R (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) S _inst_1 (CommSemiring.toSemiring.{u1} (Localization.{u1} R (CommSemiring.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} R _inst_1 M)) (CommSemiring.toSemiring.{u2} S _inst_2) (Localization.instAlgebraLocalizationToCommMonoidToSemiringInstCommSemiringLocalizationToCommMonoid.{u1, u1} R _inst_1 M R _inst_1 (Algebra.id.{u1} R _inst_1)) _inst_3
Case conversion may be inaccurate. Consider using '#align localization.alg_equiv Localization.algEquivₓ'. -/
/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps]
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _
#align localization.alg_equiv Localization.algEquiv

#print IsLocalization.unique /-
/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
noncomputable def IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ] (M : Submonoid R)
    [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (AlgEquiv M Rₘ).symm.Injective.unique
#align is_localization.unique IsLocalization.unique
-/

end

/- warning: localization.alg_equiv_mk' -> Localization.algEquiv_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.alg_equiv_mk' Localization.algEquiv_mk'ₓ'. -/
@[simp]
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _
#align localization.alg_equiv_mk' Localization.algEquiv_mk'

/- warning: localization.alg_equiv_symm_mk' -> Localization.algEquiv_symm_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.alg_equiv_symm_mk' Localization.algEquiv_symm_mk'ₓ'. -/
@[simp]
theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _
#align localization.alg_equiv_symm_mk' Localization.algEquiv_symm_mk'

/- warning: localization.alg_equiv_mk -> Localization.algEquiv_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.alg_equiv_mk Localization.algEquiv_mkₓ'. -/
theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', alg_equiv_mk']
#align localization.alg_equiv_mk Localization.algEquiv_mk

/- warning: localization.alg_equiv_symm_mk -> Localization.algEquiv_symm_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.alg_equiv_symm_mk Localization.algEquiv_symm_mkₓ'. -/
theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk', alg_equiv_symm_mk']
#align localization.alg_equiv_symm_mk Localization.algEquiv_symm_mk

end Localization

end CommSemiring

section CommRing

variable {R : Type _} [CommRing R] {M : Submonoid R} (S : Type _) [CommRing S]

variable [Algebra R S] {P : Type _} [CommRing P]

namespace Localization

#print Localization.neg /-
/-- Negation in a ring localization is defined as `-⟨a, b⟩ = ⟨-a, b⟩`. -/
protected irreducible_def neg (z : Localization M) : Localization M :=
  Localization.liftOn z (fun a b => mk (-a) b) fun a b c d h =>
    mk_eq_mk_iff.2
      (by
        rw [r_eq_r'] at h⊢
        cases' h with t ht
        use t
        rw [mul_neg, mul_neg, ht]
        ring_nf)
#align localization.neg Localization.neg
-/

instance : Neg (Localization M) :=
  ⟨Localization.neg⟩

/- warning: localization.neg_mk -> Localization.neg_mk is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))} (a : R) (b : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) M), Eq.{succ u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Neg.neg.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.hasNeg.{u1} R _inst_1 M) (Localization.mk.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M a b)) (Localization.mk.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) a) b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))} (a : R) (b : Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) x M)), Eq.{succ u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Neg.neg.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.instNegLocalizationToCommMonoid.{u1} R _inst_1 M) (Localization.mk.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M a b)) (Localization.mk.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) a) b)
Case conversion may be inaccurate. Consider using '#align localization.neg_mk Localization.neg_mkₓ'. -/
theorem neg_mk (a b) : -(mk a b : Localization M) = mk (-a) b :=
  by
  unfold Neg.neg Localization.neg
  apply lift_on_mk
#align localization.neg_mk Localization.neg_mk

instance : CommRing (Localization M) :=
  { Localization.commSemiring with
    zsmul := (· • ·)
    zsmul_zero' := fun x =>
      Localization.induction_on x fun x => by simp only [smul_mk, zero_zsmul, mk_zero]
    zsmul_succ' := fun n x =>
      Localization.induction_on x fun x => by
        simp [smul_mk, add_mk_self, -mk_eq_monoid_of_mk', add_comm (n : ℤ) 1, add_smul]
    zsmul_neg' := fun n x =>
      Localization.induction_on x fun x =>
        by
        rw [smul_mk, smul_mk, neg_mk, ← neg_smul]
        rfl
    neg := Neg.neg
    sub := fun x y => x + -y
    sub_eq_add_neg := fun x y => rfl
    add_left_neg := fun y =>
      Localization.induction_on y
        (by
          intros
          simp only [add_mk, Localization.mk_mul, neg_mk, ← mk_zero 1]
          refine' mk_eq_mk_iff.mpr (r_of_eq _)
          simp only [Submonoid.coe_mul]
          ring) }

/- warning: localization.sub_mk -> Localization.sub_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization.sub_mk Localization.sub_mkₓ'. -/
theorem sub_mk (a c) (b d) : (mk a b : Localization M) - mk c d = mk (d * a - b * c) (b * d) :=
  calc
    mk a b - mk c d = mk a b + -mk c d := sub_eq_add_neg _ _
    _ = mk a b + mk (-c) d := by rw [neg_mk]
    _ = mk (b * -c + d * a) (b * d) := (add_mk _ _ _ _)
    _ = mk (d * a - b * c) (b * d) := by congr <;> ring
    
#align localization.sub_mk Localization.sub_mk

/- warning: localization.mk_int_cast -> Localization.mk_int_cast is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))} (m : Int), Eq.{succ u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) m) (OfNat.ofNat.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) M) 1 (OfNat.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) M) 1 (One.one.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.setLike.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) M) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) M))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (HasLiftT.mk.{1, succ u1} Int (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (CoeTCₓ.coe.{1, succ u1} Int (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Int.castCoe.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (AddGroupWithOne.toHasIntCast.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (AddCommGroupWithOne.toAddGroupWithOne.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Ring.toAddCommGroupWithOne.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (CommRing.toRing.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.commRing.{u1} R _inst_1 M)))))))) m)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))} (m : Int), Eq.{succ u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.mk.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M (Int.cast.{u1} R (Ring.toIntCast.{u1} R (CommRing.toRing.{u1} R _inst_1)) m) (OfNat.ofNat.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) x M)) 1 (One.toOfNat1.{u1} (Subtype.{succ u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1)))) R (Submonoid.instSetLikeSubmonoid.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1))))) x M)) (Submonoid.one.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) M)))) (Int.cast.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Ring.toIntCast.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (CommRing.toRing.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommRingLocalizationToCommMonoid.{u1} R _inst_1 M))) m)
Case conversion may be inaccurate. Consider using '#align localization.mk_int_cast Localization.mk_int_castₓ'. -/
theorem mk_int_cast (m : ℤ) : (mk m 1 : Localization M) = m := by
  simpa using @mk_algebra_map R _ M ℤ _ _ m
#align localization.mk_int_cast Localization.mk_int_cast

end Localization

namespace IsLocalization

variable {R M} (S) {K : Type _} [IsLocalization M S]

/- warning: is_localization.to_map_eq_zero_iff -> IsLocalization.to_map_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))} (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] {x : R}, (LE.le.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Preorder.toHasLe.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Submonoid.completeLattice.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))))) M (nonZeroDivisors.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) -> (Iff (Eq.{succ u2} S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (algebraMap.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3) x) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))} (S : Type.{u1}) [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] [_inst_5 : IsLocalization.{u2, u1} R (CommRing.toCommSemiring.{u2} R _inst_1) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_3] {x : R}, (LE.le.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (Preorder.toLE.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))))))) M (nonZeroDivisors.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) -> (Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))))) (algebraMap.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)) _inst_3) x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (CommMonoidWithZero.toZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (CommSemiring.toCommMonoidWithZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) (CommRing.toCommSemiring.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) x) _inst_2)))))) (Eq.{succ u2} R x (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align is_localization.to_map_eq_zero_iff IsLocalization.to_map_eq_zero_iffₓ'. -/
theorem to_map_eq_zero_iff {x : R} (hM : M ≤ nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0 :=
  by
  rw [← (algebraMap R S).map_zero]
  constructor <;> intro h
  · cases' (eq_iff_exists M S).mp h with c hc
    rw [MulZeroClass.mul_zero, mul_comm] at hc
    exact hM c.2 x hc
  · rw [h]
#align is_localization.to_map_eq_zero_iff IsLocalization.to_map_eq_zero_iff

/- warning: is_localization.injective -> IsLocalization.injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))} (S : Type.{u2}) [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3], (LE.le.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Preorder.toHasLe.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (Submonoid.completeLattice.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))))) M (nonZeroDivisors.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) -> (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)))) (algebraMap.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))} (S : Type.{u1}) [_inst_2 : CommRing.{u1} S] [_inst_3 : Algebra.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] [_inst_5 : IsLocalization.{u2, u1} R (CommRing.toCommSemiring.{u2} R _inst_1) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_3], (LE.le.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (Preorder.toLE.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))))))) M (nonZeroDivisors.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) -> (Function.Injective.{succ u2, succ u1} R S (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))) R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))) (RingHom.instRingHomClassRingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))))) (algebraMap.{u2, u1} R S (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align is_localization.injective IsLocalization.injectiveₓ'. -/
protected theorem injective (hM : M ≤ nonZeroDivisors R) : Injective (algebraMap R S) :=
  by
  rw [injective_iff_map_eq_zero (algebraMap R S)]
  intro a ha
  rwa [to_map_eq_zero_iff S hM] at ha
#align is_localization.injective IsLocalization.injective

/- warning: is_localization.to_map_ne_zero_of_mem_non_zero_divisors -> IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.to_map_ne_zero_of_mem_non_zero_divisors IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisorsₓ'. -/
protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] (hM : M ≤ nonZeroDivisors R)
    {x : R} (hx : x ∈ nonZeroDivisors R) : algebraMap R S x ≠ 0 :=
  show (algebraMap R S).toMonoidWithZeroHom x ≠ 0 from
    map_ne_zero_of_mem_nonZeroDivisors (algebraMap R S) (IsLocalization.injective S hM) hx
#align is_localization.to_map_ne_zero_of_mem_non_zero_divisors IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors

variable {S}

/- warning: is_localization.sec_snd_ne_zero -> IsLocalization.sec_snd_ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.sec_snd_ne_zero IsLocalization.sec_snd_ne_zeroₓ'. -/
theorem sec_snd_ne_zero [Nontrivial R] (hM : M ≤ nonZeroDivisors R) (x : S) :
    ((sec M x).snd : R) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩
#align is_localization.sec_snd_ne_zero IsLocalization.sec_snd_ne_zero

/- warning: is_localization.sec_fst_ne_zero -> IsLocalization.sec_fst_ne_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.sec_fst_ne_zero IsLocalization.sec_fst_ne_zeroₓ'. -/
theorem sec_fst_ne_zero [Nontrivial R] [NoZeroDivisors S] (hM : M ≤ nonZeroDivisors R) {x : S}
    (hx : x ≠ 0) : (sec M x).fst ≠ 0 :=
  by
  have hsec := sec_spec M x
  intro hfst
  rw [hfst, map_zero, mul_eq_zero, _root_.map_eq_zero_iff] at hsec
  · exact Or.elim hsec hx (sec_snd_ne_zero hM x)
  · exact IsLocalization.injective S hM
#align is_localization.sec_fst_ne_zero IsLocalization.sec_fst_ne_zero

variable (S M) (Q : Type _) [CommRing Q] {g : R →+* P} [Algebra P Q]

/- warning: is_localization.map_injective_of_injective -> IsLocalization.map_injective_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_injective_of_injective IsLocalization.map_injective_of_injectiveₓ'. -/
/-- Injectivity of a map descends to the map induced on localizations. -/
theorem map_injective_of_injective (hg : Function.Injective g)
    [IsLocalization (M.map g : Submonoid P) Q] :
    Function.Injective (map Q g M.le_comap_map : S → Q) :=
  by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, b, rfl⟩ := mk'_surjective M z
  rw [map_mk', mk'_eq_zero_iff] at hz
  obtain ⟨⟨m', hm'⟩, hm⟩ := hz
  rw [Submonoid.mem_map] at hm'
  obtain ⟨n, hn, hnm⟩ := hm'
  rw [Subtype.coe_mk, ← hnm, ← map_mul, ← map_zero g] at hm
  rw [mk'_eq_zero_iff]
  exact ⟨⟨n, hn⟩, hg hm⟩
#align is_localization.map_injective_of_injective IsLocalization.map_injective_of_injective

variable {S Q M}

variable (A : Type _) [CommRing A] [IsDomain A]

/- warning: is_localization.no_zero_divisors_of_le_non_zero_divisors -> IsLocalization.noZeroDivisors_of_le_nonZeroDivisors is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] (A : Type.{u2}) [_inst_8 : CommRing.{u2} A] [_inst_9 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_8))] [_inst_10 : Algebra.{u2, u1} A S (CommRing.toCommSemiring.{u2} A _inst_8) (Ring.toSemiring.{u1} S (CommRing.toRing.{u1} S _inst_2))] {M : Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))} [_inst_11 : IsLocalization.{u2, u1} A (CommRing.toCommSemiring.{u2} A _inst_8) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_10], (LE.le.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (Preorder.toHasLe.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (Submonoid.completeLattice.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))))))) M (nonZeroDivisors.{u2} A (Semiring.toMonoidWithZero.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_8))))) -> (NoZeroDivisors.{u1} S (Distrib.toHasMul.{u1} S (Ring.toDistrib.{u1} S (CommRing.toRing.{u1} S _inst_2))) (MulZeroClass.toHasZero.{u1} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S (CommRing.toRing.{u1} S _inst_2)))))))
but is expected to have type
  forall {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] (A : Type.{u2}) [_inst_8 : CommRing.{u2} A] [_inst_9 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8))] [_inst_10 : Algebra.{u2, u1} A S (CommRing.toCommSemiring.{u2} A _inst_8) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] {M : Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))} [_inst_11 : IsLocalization.{u2, u1} A (CommRing.toCommSemiring.{u2} A _inst_8) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_10], (LE.le.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (Preorder.toLE.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))))))) M (nonZeroDivisors.{u2} A (Semiring.toMonoidWithZero.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8))))) -> (NoZeroDivisors.{u1} S (NonUnitalNonAssocRing.toMul.{u1} S (NonAssocRing.toNonUnitalNonAssocRing.{u1} S (Ring.toNonAssocRing.{u1} S (CommRing.toRing.{u1} S _inst_2)))) (CommMonoidWithZero.toZero.{u1} S (CommSemiring.toCommMonoidWithZero.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))))
Case conversion may be inaccurate. Consider using '#align is_localization.no_zero_divisors_of_le_non_zero_divisors IsLocalization.noZeroDivisors_of_le_nonZeroDivisorsₓ'. -/
/-- A `comm_ring` `S` which is the localization of a ring `R` without zero divisors at a subset of
non-zero elements does not have zero divisors.
See note [reducible non-instances]. -/
@[reducible]
theorem noZeroDivisors_of_le_nonZeroDivisors [Algebra A S] {M : Submonoid A} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors A) : NoZeroDivisors S :=
  {
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro z w h
      cases' surj M z with x hx
      cases' surj M w with y hy
      have :
        z * w * algebraMap A S y.2 * algebraMap A S x.2 = algebraMap A S x.1 * algebraMap A S y.1 :=
        by rw [mul_assoc z, hy, ← hx] <;> ring
      rw [h, MulZeroClass.zero_mul, MulZeroClass.zero_mul, ← (algebraMap A S).map_mul] at this
      cases' eq_zero_or_eq_zero_of_mul_eq_zero ((to_map_eq_zero_iff S hM).mp this.symm) with H H
      · exact Or.inl (eq_zero_of_fst_eq_zero hx H)
      · exact Or.inr (eq_zero_of_fst_eq_zero hy H) }
#align is_localization.no_zero_divisors_of_le_non_zero_divisors IsLocalization.noZeroDivisors_of_le_nonZeroDivisors

/- warning: is_localization.is_domain_of_le_non_zero_divisors -> IsLocalization.isDomain_of_le_nonZeroDivisors is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] (A : Type.{u2}) [_inst_8 : CommRing.{u2} A] [_inst_9 : IsDomain.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_8))] [_inst_10 : Algebra.{u2, u1} A S (CommRing.toCommSemiring.{u2} A _inst_8) (Ring.toSemiring.{u1} S (CommRing.toRing.{u1} S _inst_2))] {M : Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))} [_inst_11 : IsLocalization.{u2, u1} A (CommRing.toCommSemiring.{u2} A _inst_8) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_10], (LE.le.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (Preorder.toHasLe.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (CompleteSemilatticeInf.toPartialOrder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))) (Submonoid.completeLattice.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (NonAssocRing.toNonAssocSemiring.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_8)))))))))) M (nonZeroDivisors.{u2} A (Semiring.toMonoidWithZero.{u2} A (Ring.toSemiring.{u2} A (CommRing.toRing.{u2} A _inst_8))))) -> (IsDomain.{u1} S (Ring.toSemiring.{u1} S (CommRing.toRing.{u1} S _inst_2)))
but is expected to have type
  forall {S : Type.{u1}} [_inst_2 : CommRing.{u1} S] (A : Type.{u2}) [_inst_8 : CommRing.{u2} A] [_inst_9 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8))] [_inst_10 : Algebra.{u2, u1} A S (CommRing.toCommSemiring.{u2} A _inst_8) (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2))] {M : Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))} [_inst_11 : IsLocalization.{u2, u1} A (CommRing.toCommSemiring.{u2} A _inst_8) M S (CommRing.toCommSemiring.{u1} S _inst_2) _inst_10], (LE.le.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (Preorder.toLE.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (PartialOrder.toPreorder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))) (Submonoid.instCompleteLatticeSubmonoid.{u2} A (MulZeroOneClass.toMulOneClass.{u2} A (NonAssocSemiring.toMulZeroOneClass.{u2} A (Semiring.toNonAssocSemiring.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8)))))))))) M (nonZeroDivisors.{u2} A (Semiring.toMonoidWithZero.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_8))))) -> (IsDomain.{u1} S (CommSemiring.toSemiring.{u1} S (CommRing.toCommSemiring.{u1} S _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_localization.is_domain_of_le_non_zero_divisors IsLocalization.isDomain_of_le_nonZeroDivisorsₓ'. -/
/-- A `comm_ring` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem isDomain_of_le_nonZeroDivisors [Algebra A S] {M : Submonoid A} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors A) : IsDomain S :=
  by
  apply NoZeroDivisors.to_isDomain _
  ·
    exact
      ⟨⟨(algebraMap A S) 0, (algebraMap A S) 1, fun h =>
          zero_ne_one (IsLocalization.injective S hM h)⟩⟩
  · exact no_zero_divisors_of_le_non_zero_divisors _ hM
#align is_localization.is_domain_of_le_non_zero_divisors IsLocalization.isDomain_of_le_nonZeroDivisors

variable {A}

/- warning: is_localization.is_domain_localization -> IsLocalization.isDomain_localization is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_8 : CommRing.{u1} A] [_inst_9 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_8))] {M : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))}, (LE.le.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))) (Preorder.toHasLe.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))) (Submonoid.completeLattice.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (NonAssocRing.toNonAssocSemiring.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_8)))))))))) M (nonZeroDivisors.{u1} A (Semiring.toMonoidWithZero.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_8))))) -> (IsDomain.{u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_8) M) (Ring.toSemiring.{u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_8) M) (CommRing.toRing.{u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_8) M) (Localization.commRing.{u1} A _inst_8 M))))
but is expected to have type
  forall {A : Type.{u1}} [_inst_8 : CommRing.{u1} A] [_inst_9 : IsDomain.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8))] {M : Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))}, (LE.le.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))) (Preorder.toLE.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))) (Submonoid.instCompleteLatticeSubmonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (NonAssocSemiring.toMulZeroOneClass.{u1} A (Semiring.toNonAssocSemiring.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8)))))))))) M (nonZeroDivisors.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8))))) -> (IsDomain.{u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_8) M) (CommSemiring.toSemiring.{u1} (Localization.{u1} A (CommRing.toCommMonoid.{u1} A _inst_8) M) (Localization.instCommSemiringLocalizationToCommMonoid.{u1} A (CommRing.toCommSemiring.{u1} A _inst_8) M)))
Case conversion may be inaccurate. Consider using '#align is_localization.is_domain_localization IsLocalization.isDomain_localizationₓ'. -/
/-- The localization at of an integral domain to a set of non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem isDomain_localization {M : Submonoid A} (hM : M ≤ nonZeroDivisors A) :
    IsDomain (Localization M) :=
  isDomain_of_le_nonZeroDivisors _ hM
#align is_localization.is_domain_localization IsLocalization.isDomain_localization

end IsLocalization

open IsLocalization

/- warning: is_field.localization_map_bijective -> IsField.localization_map_bijective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {Rₘ : Type.{u2}} [_inst_5 : CommRing.{u1} R] [_inst_6 : CommRing.{u2} Rₘ] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_5)))))}, (Not (Membership.Mem.{u1, u1} R (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_5)))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_5)))))) R (Submonoid.setLike.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_5))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_5))))))))) M)) -> (IsField.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_5))) -> (forall [_inst_7 : Algebra.{u1, u2} R Rₘ (CommRing.toCommSemiring.{u1} R _inst_5) (Ring.toSemiring.{u2} Rₘ (CommRing.toRing.{u2} Rₘ _inst_6))] [_inst_8 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_5) M Rₘ (CommRing.toCommSemiring.{u2} Rₘ _inst_6) _inst_7], Function.Bijective.{succ u1, succ u2} R Rₘ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R Rₘ (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_5))) (Semiring.toNonAssocSemiring.{u2} Rₘ (Ring.toSemiring.{u2} Rₘ (CommRing.toRing.{u2} Rₘ _inst_6)))) (fun (_x : RingHom.{u1, u2} R Rₘ (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_5))) (Semiring.toNonAssocSemiring.{u2} Rₘ (Ring.toSemiring.{u2} Rₘ (CommRing.toRing.{u2} Rₘ _inst_6)))) => R -> Rₘ) (RingHom.hasCoeToFun.{u1, u2} R Rₘ (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_5))) (Semiring.toNonAssocSemiring.{u2} Rₘ (Ring.toSemiring.{u2} Rₘ (CommRing.toRing.{u2} Rₘ _inst_6)))) (algebraMap.{u1, u2} R Rₘ (CommRing.toCommSemiring.{u1} R _inst_5) (Ring.toSemiring.{u2} Rₘ (CommRing.toRing.{u2} Rₘ _inst_6)) _inst_7)))
but is expected to have type
  forall {R : Type.{u2}} {Rₘ : Type.{u1}} [_inst_5 : CommRing.{u2} R] [_inst_6 : CommRing.{u1} Rₘ] {M : Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))))}, (Not (Membership.mem.{u2, u2} R (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))))) R (Submonoid.instSetLikeSubmonoid.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))))))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))))) M)) -> (IsField.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) -> (forall [_inst_7 : Algebra.{u2, u1} R Rₘ (CommRing.toCommSemiring.{u2} R _inst_5) (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6))] [_inst_8 : IsLocalization.{u2, u1} R (CommRing.toCommSemiring.{u2} R _inst_5) M Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6) _inst_7], Function.Bijective.{succ u2, succ u1} R Rₘ (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R Rₘ (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Rₘ) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R Rₘ (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6)))) R Rₘ (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))))) (NonUnitalNonAssocSemiring.toMul.{u1} Rₘ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} Rₘ (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R Rₘ (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6)))) R Rₘ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} Rₘ (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R Rₘ (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6)))) R Rₘ (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6))) (RingHom.instRingHomClassRingHom.{u2, u1} R Rₘ (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))) (Semiring.toNonAssocSemiring.{u1} Rₘ (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6))))))) (algebraMap.{u2, u1} R Rₘ (CommRing.toCommSemiring.{u2} R _inst_5) (CommSemiring.toSemiring.{u1} Rₘ (CommRing.toCommSemiring.{u1} Rₘ _inst_6)) _inst_7)))
Case conversion may be inaccurate. Consider using '#align is_field.localization_map_bijective IsField.localization_map_bijectiveₓ'. -/
/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem IsField.localization_map_bijective {R Rₘ : Type _} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) :=
  by
  letI := hR.to_field
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  refine' ⟨IsLocalization.injective _ hM, fun x => _⟩
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  exact ⟨r * n, by erw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, mul_comm n, hn, mul_one]⟩
#align is_field.localization_map_bijective IsField.localization_map_bijective

/- warning: field.localization_map_bijective -> Field.localization_map_bijective is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {Kₘ : Type.{u2}} [_inst_5 : Field.{u1} K] [_inst_6 : CommRing.{u2} Kₘ] {M : Submonoid.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (NonAssocSemiring.toMulZeroOneClass.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_5))))))}, (Not (Membership.Mem.{u1, u1} K (Submonoid.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (NonAssocSemiring.toMulZeroOneClass.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_5))))))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (NonAssocSemiring.toMulZeroOneClass.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_5))))))) K (Submonoid.setLike.{u1} K (MulZeroOneClass.toMulOneClass.{u1} K (NonAssocSemiring.toMulZeroOneClass.{u1} K (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_5)))))))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_5)))))))))) M)) -> (forall [_inst_7 : Algebra.{u1, u2} K Kₘ (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_5)) (Ring.toSemiring.{u2} Kₘ (CommRing.toRing.{u2} Kₘ _inst_6))] [_inst_8 : IsLocalization.{u1, u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_5)) M Kₘ (CommRing.toCommSemiring.{u2} Kₘ _inst_6) _inst_7], Function.Bijective.{succ u1, succ u2} K Kₘ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} K Kₘ (Semiring.toNonAssocSemiring.{u1} K (CommSemiring.toSemiring.{u1} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_5)))) (Semiring.toNonAssocSemiring.{u2} Kₘ (Ring.toSemiring.{u2} Kₘ (CommRing.toRing.{u2} Kₘ _inst_6)))) (fun (_x : RingHom.{u1, u2} K Kₘ (Semiring.toNonAssocSemiring.{u1} K (CommSemiring.toSemiring.{u1} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_5)))) (Semiring.toNonAssocSemiring.{u2} Kₘ (Ring.toSemiring.{u2} Kₘ (CommRing.toRing.{u2} Kₘ _inst_6)))) => K -> Kₘ) (RingHom.hasCoeToFun.{u1, u2} K Kₘ (Semiring.toNonAssocSemiring.{u1} K (CommSemiring.toSemiring.{u1} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_5)))) (Semiring.toNonAssocSemiring.{u2} Kₘ (Ring.toSemiring.{u2} Kₘ (CommRing.toRing.{u2} Kₘ _inst_6)))) (algebraMap.{u1, u2} K Kₘ (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_5)) (Ring.toSemiring.{u2} Kₘ (CommRing.toRing.{u2} Kₘ _inst_6)) _inst_7)))
but is expected to have type
  forall {K : Type.{u2}} {Kₘ : Type.{u1}} [_inst_5 : Field.{u2} K] [_inst_6 : CommRing.{u1} Kₘ] {M : Submonoid.{u2} K (MulZeroOneClass.toMulOneClass.{u2} K (NonAssocSemiring.toMulZeroOneClass.{u2} K (Semiring.toNonAssocSemiring.{u2} K (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5))))))}, (Not (Membership.mem.{u2, u2} K (Submonoid.{u2} K (MulZeroOneClass.toMulOneClass.{u2} K (NonAssocSemiring.toMulZeroOneClass.{u2} K (Semiring.toNonAssocSemiring.{u2} K (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5))))))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} K (MulZeroOneClass.toMulOneClass.{u2} K (NonAssocSemiring.toMulZeroOneClass.{u2} K (Semiring.toNonAssocSemiring.{u2} K (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5))))))) K (Submonoid.instSetLikeSubmonoid.{u2} K (MulZeroOneClass.toMulOneClass.{u2} K (NonAssocSemiring.toMulZeroOneClass.{u2} K (Semiring.toNonAssocSemiring.{u2} K (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))))))) (OfNat.ofNat.{u2} K 0 (Zero.toOfNat0.{u2} K (CommMonoidWithZero.toZero.{u2} K (CommGroupWithZero.toCommMonoidWithZero.{u2} K (Semifield.toCommGroupWithZero.{u2} K (Field.toSemifield.{u2} K _inst_5)))))) M)) -> (forall [_inst_7 : Algebra.{u2, u1} K Kₘ (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)) (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6))] [_inst_8 : IsLocalization.{u2, u1} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)) M Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6) _inst_7], Function.Bijective.{succ u2, succ u1} K Kₘ (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} K Kₘ (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))) (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6)))) K (fun (_x : K) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : K) => Kₘ) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} K Kₘ (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))) (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6)))) K Kₘ (NonUnitalNonAssocSemiring.toMul.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))))) (NonUnitalNonAssocSemiring.toMul.{u1} Kₘ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} Kₘ (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} K Kₘ (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))) (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6)))) K Kₘ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} Kₘ (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} K Kₘ (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))) (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6)))) K Kₘ (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))) (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6))) (RingHom.instRingHomClassRingHom.{u2, u1} K Kₘ (Semiring.toNonAssocSemiring.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)))) (Semiring.toNonAssocSemiring.{u1} Kₘ (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6))))))) (algebraMap.{u2, u1} K Kₘ (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_5)) (CommSemiring.toSemiring.{u1} Kₘ (CommRing.toCommSemiring.{u1} Kₘ _inst_6)) _inst_7)))
Case conversion may be inaccurate. Consider using '#align field.localization_map_bijective Field.localization_map_bijectiveₓ'. -/
/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem Field.localization_map_bijective {K Kₘ : Type _} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM
#align field.localization_map_bijective Field.localization_map_bijective

-- this looks weird due to the `letI` inside the above lemma, but trying to do it the other
-- way round causes issues with defeq of instances, so this is actually easier.
section Algebra

variable {R S} {Rₘ Sₘ : Type _} [CommRing Rₘ] [CommRing Sₘ]

variable [Algebra R Rₘ] [IsLocalization M Rₘ]

variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

section

variable (S M)

#print localizationAlgebra /-
/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebra_map R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := localization (algebra.algebra_map_submonoid S M)`,
however we will instead use the hypotheses `[algebra Rₘ Sₘ] [is_scalar_tower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra
#align localization_algebra localizationAlgebra
-/

end

section

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

variable (S Rₘ Sₘ)

include S

/- warning: is_localization.map_units_map_submonoid -> IsLocalization.map_units_map_submonoid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.map_units_map_submonoid IsLocalization.map_units_map_submonoidₓ'. -/
theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) :=
  by
  rw [IsScalarTower.algebraMap_apply _ S]
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩
#align is_localization.map_units_map_submonoid IsLocalization.map_units_map_submonoid

/- warning: is_localization.algebra_map_mk' -> IsLocalization.algebraMap_mk' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.algebra_map_mk' IsLocalization.algebraMap_mk'ₓ'. -/
@[simp]
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ :=
  by
  rw [IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, ←
    IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ Sₘ,
    IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← _root_.map_mul, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)
#align is_localization.algebra_map_mk' IsLocalization.algebraMap_mk'

variable (M)

/- warning: is_localization.algebra_map_eq_map_map_submonoid -> IsLocalization.algebraMap_eq_map_map_submonoid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.algebra_map_eq_map_map_submonoid IsLocalization.algebraMap_eq_map_map_submonoidₓ'. -/
/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  Eq.symm <|
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ, ← IsScalarTower.algebraMap_apply R Rₘ Sₘ]
#align is_localization.algebra_map_eq_map_map_submonoid IsLocalization.algebraMap_eq_map_map_submonoid

/- warning: is_localization.algebra_map_apply_eq_map_map_submonoid -> IsLocalization.algebraMap_apply_eq_map_map_submonoid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.algebra_map_apply_eq_map_map_submonoid IsLocalization.algebraMap_apply_eq_map_map_submonoidₓ'. -/
/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  FunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x
#align is_localization.algebra_map_apply_eq_map_map_submonoid IsLocalization.algebraMap_apply_eq_map_map_submonoid

variable {R}

/- warning: is_localization.lift_algebra_map_eq_algebra_map -> IsLocalization.lift_algebraMap_eq_algebraMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.lift_algebra_map_eq_algebra_map IsLocalization.lift_algebraMap_eq_algebraMapₓ'. -/
theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    @IsLocalization.lift R _ M Rₘ _ _ Sₘ _ _ (algebraMap R Sₘ)
        (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun x => (IsScalarTower.algebraMap_apply _ _ _ _).symm
#align is_localization.lift_algebra_map_eq_algebra_map IsLocalization.lift_algebraMap_eq_algebraMap

end

variable (Rₘ Sₘ)

/- warning: localization_algebra_injective -> localizationAlgebra_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align localization_algebra_injective localizationAlgebra_injectiveₓ'. -/
/-- Injectivity of the underlying `algebra_map` descends to the algebra induced by localization. -/
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  IsLocalization.map_injective_of_injective M Rₘ Sₘ hRS
#align localization_algebra_injective localizationAlgebra_injective

end Algebra

end CommRing

