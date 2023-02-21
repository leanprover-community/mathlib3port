/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module deprecated.subring
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Deprecated.Subgroup
import Mathbin.Deprecated.Group
import Mathbin.RingTheory.Subring.Basic

/-!
# Unbundled subrings (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subrings. Instead of using this file, please use
`subring`, defined in `ring_theory.subring.basic`, for subrings of rings.

## Main definitions

`is_subring (S : set R) : Prop` : the predicate that `S` is the underlying set of a subring
of the ring `R`. The bundled variant `subring R` should be used in preference to this.

## Tags

is_subring
-/


universe u v

open Group

variable {R : Type u} [Ring R]

#print IsSubring /-
/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and additive
inverse. -/
structure IsSubring (S : Set R) extends IsAddSubgroup S, IsSubmonoid S : Prop
#align is_subring IsSubring
-/

#print IsSubring.subring /-
/-- Construct a `subring` from a set satisfying `is_subring`. -/
def IsSubring.subring {S : Set R} (hs : IsSubring S) : Subring R
    where
  carrier := S
  one_mem' := hs.one_mem
  mul_mem' _ _ := hs.mul_mem
  zero_mem' := hs.zero_mem
  add_mem' _ _ := hs.add_mem
  neg_mem' _ := hs.neg_mem
#align is_subring.subring IsSubring.subring
-/

namespace RingHom

/- warning: ring_hom.is_subring_preimage -> RingHom.isSubring_preimage is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : Ring.{u1} R] [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) {s : Set.{u2} S}, (IsSubring.{u2} S _inst_3 s) -> (IsSubring.{u1} R _inst_2 (Set.preimage.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) f) s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : Ring.{u1} R] [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) {s : Set.{u2} S}, (IsSubring.{u2} S _inst_3 s) -> (IsSubring.{u1} R _inst_2 (Set.preimage.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)))))) f) s))
Case conversion may be inaccurate. Consider using '#align ring_hom.is_subring_preimage RingHom.isSubring_preimageₓ'. -/
theorem isSubring_preimage {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {s : Set S}
    (hs : IsSubring s) : IsSubring (f ⁻¹' s) :=
  { IsAddGroupHom.preimage f.to_isAddGroupHom hs.to_isAddSubgroup,
    IsSubmonoid.preimage f.to_isMonoidHom hs.to_isSubmonoid with }
#align ring_hom.is_subring_preimage RingHom.isSubring_preimage

/- warning: ring_hom.is_subring_image -> RingHom.isSubring_image is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : Ring.{u1} R] [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) {s : Set.{u1} R}, (IsSubring.{u1} R _inst_2 s) -> (IsSubring.{u2} S _inst_3 (Set.image.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) f) s))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : Ring.{u1} R] [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) {s : Set.{u1} R}, (IsSubring.{u1} R _inst_2 s) -> (IsSubring.{u2} S _inst_3 (Set.image.{u1, u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)))))) f) s))
Case conversion may be inaccurate. Consider using '#align ring_hom.is_subring_image RingHom.isSubring_imageₓ'. -/
theorem isSubring_image {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) {s : Set R}
    (hs : IsSubring s) : IsSubring (f '' s) :=
  { IsAddGroupHom.image_addSubgroup f.to_isAddGroupHom hs.to_isAddSubgroup,
    IsSubmonoid.image f.to_isMonoidHom hs.to_isSubmonoid with }
#align ring_hom.is_subring_image RingHom.isSubring_image

/- warning: ring_hom.is_subring_set_range -> RingHom.isSubring_set_range is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : Ring.{u1} R] [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))), IsSubring.{u2} S _inst_3 (Set.range.{u2, succ u1} S R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) f))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_2 : Ring.{u1} R] [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))), IsSubring.{u2} S _inst_3 (Set.range.{u2, succ u1} S R (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)) (RingHom.instRingHomClassRingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_2)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3)))))) f))
Case conversion may be inaccurate. Consider using '#align ring_hom.is_subring_set_range RingHom.isSubring_set_rangeₓ'. -/
theorem isSubring_set_range {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) :
    IsSubring (Set.range f) :=
  { IsAddGroupHom.range_addSubgroup f.to_isAddGroupHom, Range.isSubmonoid f.to_isMonoidHom with }
#align ring_hom.is_subring_set_range RingHom.isSubring_set_range

end RingHom

variable {cR : Type u} [CommRing cR]

/- warning: is_subring.inter -> IsSubring.inter is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S₁ : Set.{u1} R} {S₂ : Set.{u1} R}, (IsSubring.{u1} R _inst_1 S₁) -> (IsSubring.{u1} R _inst_1 S₂) -> (IsSubring.{u1} R _inst_1 (Inter.inter.{u1} (Set.{u1} R) (Set.hasInter.{u1} R) S₁ S₂))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S₁ : Set.{u1} R} {S₂ : Set.{u1} R}, (IsSubring.{u1} R _inst_1 S₁) -> (IsSubring.{u1} R _inst_1 S₂) -> (IsSubring.{u1} R _inst_1 (Inter.inter.{u1} (Set.{u1} R) (Set.instInterSet.{u1} R) S₁ S₂))
Case conversion may be inaccurate. Consider using '#align is_subring.inter IsSubring.interₓ'. -/
theorem IsSubring.inter {S₁ S₂ : Set R} (hS₁ : IsSubring S₁) (hS₂ : IsSubring S₂) :
    IsSubring (S₁ ∩ S₂) :=
  { IsAddSubgroup.inter hS₁.to_isAddSubgroup hS₂.to_isAddSubgroup,
    IsSubmonoid.inter hS₁.to_isSubmonoid hS₂.to_isSubmonoid with }
#align is_subring.inter IsSubring.inter

/- warning: is_subring.Inter -> IsSubring.interᵢ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Sort.{u2}} {S : ι -> (Set.{u1} R)}, (forall (y : ι), IsSubring.{u1} R _inst_1 (S y)) -> (IsSubring.{u1} R _inst_1 (Set.interᵢ.{u1, u2} R ι S))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Sort.{u1}} {S : ι -> (Set.{u2} R)}, (forall (y : ι), IsSubring.{u2} R _inst_1 (S y)) -> (IsSubring.{u2} R _inst_1 (Set.interᵢ.{u2, u1} R ι S))
Case conversion may be inaccurate. Consider using '#align is_subring.Inter IsSubring.interᵢₓ'. -/
theorem IsSubring.interᵢ {ι : Sort _} {S : ι → Set R} (h : ∀ y : ι, IsSubring (S y)) :
    IsSubring (Set.interᵢ S) :=
  { IsAddSubgroup.interᵢ fun i => (h i).to_isAddSubgroup,
    IsSubmonoid.interᵢ fun i => (h i).to_isSubmonoid with }
#align is_subring.Inter IsSubring.interᵢ

/- warning: is_subring_Union_of_directed -> isSubring_unionᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {ι : Type.{u2}} [hι : Nonempty.{succ u2} ι] {s : ι -> (Set.{u1} R)}, (forall (i : ι), IsSubring.{u1} R _inst_1 (s i)) -> (forall (i : ι) (j : ι), Exists.{succ u2} ι (fun (k : ι) => And (HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) (s i) (s k)) (HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) (s j) (s k)))) -> (IsSubring.{u1} R _inst_1 (Set.unionᵢ.{u1, succ u2} R ι (fun (i : ι) => s i)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {ι : Type.{u1}} [hι : Nonempty.{succ u1} ι] {s : ι -> (Set.{u2} R)}, (forall (i : ι), IsSubring.{u2} R _inst_1 (s i)) -> (forall (i : ι) (j : ι), Exists.{succ u1} ι (fun (k : ι) => And (HasSubset.Subset.{u2} (Set.{u2} R) (Set.instHasSubsetSet.{u2} R) (s i) (s k)) (HasSubset.Subset.{u2} (Set.{u2} R) (Set.instHasSubsetSet.{u2} R) (s j) (s k)))) -> (IsSubring.{u2} R _inst_1 (Set.unionᵢ.{u2, succ u1} R ι (fun (i : ι) => s i)))
Case conversion may be inaccurate. Consider using '#align is_subring_Union_of_directed isSubring_unionᵢ_of_directedₓ'. -/
theorem isSubring_unionᵢ_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set R}
    (h : ∀ i, IsSubring (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubring (⋃ i, s i) :=
  { to_isAddSubgroup := isAddSubgroup_unionᵢ_of_directed (fun i => (h i).to_isAddSubgroup) Directed
    to_isSubmonoid := isSubmonoid_unionᵢ_of_directed (fun i => (h i).to_isSubmonoid) Directed }
#align is_subring_Union_of_directed isSubring_unionᵢ_of_directed

namespace Ring

#print Ring.closure /-
/-- The smallest subring containing a given subset of a ring, considered as a set. This function
is deprecated; use `subring.closure`. -/
def closure (s : Set R) :=
  AddGroup.closure (Monoid.Closure s)
#align ring.closure Ring.closure
-/

variable {s : Set R}

attribute [local reducible] closure

/- warning: ring.exists_list_of_mem_closure -> Ring.exists_list_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {a : R}, (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) a (Ring.closure.{u1} R _inst_1 s)) -> (Exists.{succ u1} (List.{u1} (List.{u1} R)) (fun (L : List.{u1} (List.{u1} R)) => And (forall (l : List.{u1} R), (Membership.Mem.{u1, u1} (List.{u1} R) (List.{u1} (List.{u1} R)) (List.hasMem.{u1} (List.{u1} R)) l L) -> (forall (x : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) x l) -> (Or (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x s) (Eq.{succ u1} R x (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))))))) (Eq.{succ u1} R (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (List.map.{u1, u1} (List.{u1} R) R (List.prod.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) L)) a)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {a : R}, (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) a (Ring.closure.{u1} R _inst_1 s)) -> (Exists.{succ u1} (List.{u1} (List.{u1} R)) (fun (L : List.{u1} (List.{u1} R)) => And (forall (l : List.{u1} R), (Membership.mem.{u1, u1} (List.{u1} R) (List.{u1} (List.{u1} R)) (List.instMembershipList.{u1} (List.{u1} R)) l L) -> (forall (x : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) x l) -> (Or (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x s) (Eq.{succ u1} R x (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) (Eq.{succ u1} R (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (List.map.{u1, u1} (List.{u1} R) R (List.prod.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) L)) a)))
Case conversion may be inaccurate. Consider using '#align ring.exists_list_of_mem_closure Ring.exists_list_of_mem_closureₓ'. -/
theorem exists_list_of_mem_closure {a : R} (h : a ∈ closure s) :
    ∃ L : List (List R), (∀ l ∈ L, ∀ x ∈ l, x ∈ s ∨ x = (-1 : R)) ∧ (L.map List.prod).Sum = a :=
  AddGroup.InClosure.rec_on h
    (fun x hx =>
      match x, Monoid.exists_list_of_mem_closure hx with
      | _, ⟨L, h1, rfl⟩ =>
        ⟨[L], List.forall_mem_singleton.2 fun r hr => Or.inl (h1 r hr), zero_add _⟩)
    ⟨[], List.forall_mem_nil _, rfl⟩
    (fun b _ ih =>
      match b, ih with
      | _, ⟨L1, h1, rfl⟩ =>
        ⟨L1.map (List.cons (-1)), fun L2 h2 =>
          match L2, List.mem_map'.1 h2 with
          | _, ⟨L3, h3, rfl⟩ => List.forall_mem_cons.2 ⟨Or.inr rfl, h1 L3 h3⟩,
          by
          simp only [List.map_map, (· ∘ ·), List.prod_cons, neg_one_mul] <;>
            exact
              List.recOn L1 neg_zero.symm fun hd tl ih => by
                rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]⟩)
    fun r1 r2 hr1 hr2 ih1 ih2 =>
    match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ =>
      ⟨L1 ++ L2, List.forall_mem_append.2 ⟨h1, h2⟩, by rw [List.map_append, List.sum_append]⟩
#align ring.exists_list_of_mem_closure Ring.exists_list_of_mem_closure

/- warning: ring.in_closure.rec_on -> Ring.InClosure.recOn is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {C : R -> Prop} {x : R}, (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x (Ring.closure.{u1} R _inst_1 s)) -> (C (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))))) -> (C (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) -> (forall (z : R), (Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) z s) -> (forall (n : R), (C n) -> (C (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1))) z n)))) -> (forall {x : R} {y : R}, (C x) -> (C y) -> (C (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R _inst_1))) x y))) -> (C x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {s : Set.{u1} R} {C : R -> Prop} {x : R}, (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x (Ring.closure.{u1} R _inst_1 s)) -> (C (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) -> (C (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) -> (forall (z : R), (Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) z s) -> (forall (n : R), (C n) -> (C (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) z n)))) -> (forall {x : R} {y : R}, (C x) -> (C y) -> (C (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) x y))) -> (C x)
Case conversion may be inaccurate. Consider using '#align ring.in_closure.rec_on Ring.InClosure.recOnₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[elab_as_elim]
protected theorem InClosure.recOn {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_self (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction' L with hd tl ih
  · exact h0
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    ∃ L : List R, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact h1
    rw [List.forall_mem_cons] at HL'
    rw [List.prod_cons]
    exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact hneg1
    rw [List.prod_cons, neg_mul_eq_mul_neg]
    rw [List.forall_mem_cons] at HL'
    exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  ·
    exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  ·
    exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩
#align ring.in_closure.rec_on Ring.InClosure.recOn

#print Ring.closure.isSubring /-
theorem closure.isSubring : IsSubring (closure s) :=
  {
    AddGroup.closure.isAddSubgroup
      _ with
    one_mem := AddGroup.mem_closure <| IsSubmonoid.one_mem <| Monoid.closure.isSubmonoid _
    mul_mem := fun a b ha hb =>
      AddGroup.InClosure.rec_on hb
        (fun c hc =>
          AddGroup.InClosure.rec_on ha
            (fun d hd => AddGroup.subset_closure ((Monoid.closure.isSubmonoid _).mul_mem hd hc))
            ((zero_mul c).symm ▸ (AddGroup.closure.isAddSubgroup _).zero_mem)
            (fun d hd hdc =>
              neg_mul_eq_neg_mul d c ▸ (AddGroup.closure.isAddSubgroup _).neg_mem hdc)
            fun d e hd he hdc hec =>
            (add_mul d e c).symm ▸ (AddGroup.closure.isAddSubgroup _).add_mem hdc hec)
        ((mul_zero a).symm ▸ (AddGroup.closure.isAddSubgroup _).zero_mem)
        (fun c hc hac => neg_mul_eq_mul_neg a c ▸ (AddGroup.closure.isAddSubgroup _).neg_mem hac)
        fun c d hc hd hac had =>
        (mul_add a c d).symm ▸ (AddGroup.closure.isAddSubgroup _).add_mem hac had }
#align ring.closure.is_subring Ring.closure.isSubring
-/

#print Ring.mem_closure /-
theorem mem_closure {a : R} : a ∈ s → a ∈ closure s :=
  AddGroup.mem_closure ∘ @Monoid.subset_closure _ _ _ _
#align ring.mem_closure Ring.mem_closure
-/

#print Ring.subset_closure /-
theorem subset_closure : s ⊆ closure s := fun _ => mem_closure
#align ring.subset_closure Ring.subset_closure
-/

#print Ring.closure_subset /-
theorem closure_subset {t : Set R} (ht : IsSubring t) : s ⊆ t → closure s ⊆ t :=
  AddGroup.closure_subset ht.to_isAddSubgroup ∘ Monoid.closure_subset ht.to_isSubmonoid
#align ring.closure_subset Ring.closure_subset
-/

#print Ring.closure_subset_iff /-
theorem closure_subset_iff {s t : Set R} (ht : IsSubring t) : closure s ⊆ t ↔ s ⊆ t :=
  (AddGroup.closure_subset_iff ht.to_isAddSubgroup).trans
    ⟨Set.Subset.trans Monoid.subset_closure, Monoid.closure_subset ht.to_isSubmonoid⟩
#align ring.closure_subset_iff Ring.closure_subset_iff
-/

#print Ring.closure_mono /-
theorem closure_mono {s t : Set R} (H : s ⊆ t) : closure s ⊆ closure t :=
  closure_subset closure.isSubring <| Set.Subset.trans H subset_closure
#align ring.closure_mono Ring.closure_mono
-/

/- warning: ring.image_closure -> Ring.image_closure is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {S : Type.{u2}} [_inst_3 : Ring.{u2} S] (f : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (s : Set.{u1} R), Eq.{succ u2} (Set.{u2} S) (Set.image.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) f) (Ring.closure.{u1} R _inst_1 s)) (Ring.closure.{u2} S _inst_3 (Set.image.{u1, u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) (fun (_x : RingHom.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S _inst_3))) f) s))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Ring.{u2} R] {S : Type.{u1}} [_inst_3 : Ring.{u1} S] (f : RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) (s : Set.{u2} R), Eq.{succ u1} (Set.{u1} S) (Set.image.{u2, u1} R S (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3)))))) f) (Ring.closure.{u2} R _inst_1 s)) (Ring.closure.{u1} S _inst_3 (Set.image.{u2, u1} R S (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => S) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R S (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3))) R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3)) (RingHom.instRingHomClassRingHom.{u2, u1} R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u1} S (Ring.toNonAssocRing.{u1} S _inst_3)))))) f) s))
Case conversion may be inaccurate. Consider using '#align ring.image_closure Ring.image_closureₓ'. -/
theorem image_closure {S : Type _} [Ring S] (f : R →+* S) (s : Set R) :
    f '' closure s = closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      apply in_closure.rec_on hx <;> intros
      · rw [f.map_one]
        apply closure.is_subring.to_is_submonoid.one_mem
      · rw [f.map_neg, f.map_one]
        apply closure.is_subring.to_is_add_subgroup.neg_mem
        apply closure.is_subring.to_is_submonoid.one_mem
      · rw [f.map_mul]
        apply closure.is_subring.to_is_submonoid.mul_mem <;>
          solve_by_elim [subset_closure, Set.mem_image_of_mem]
      · rw [f.map_add]
        apply closure.is_subring.to_is_add_submonoid.add_mem
        assumption')
    (closure_subset (RingHom.isSubring_image _ closure.isSubring) <|
      Set.image_subset _ subset_closure)
#align ring.image_closure Ring.image_closure

end Ring

