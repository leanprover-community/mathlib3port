/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module linear_algebra.orientation
! leanprover-community/mathlib commit 7d34004e19699895c13c86b78ae62bbaea0bc893
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Ray
import Mathbin.LinearAlgebra.Determinant

/-!
# Orientations of modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines orientations of modules.

## Main definitions

* `orientation` is a type synonym for `module.ray` for the case where the module is that of
alternating maps from a module to its underlying ring.  An orientation may be associated with an
alternating map or with a basis.

* `module.oriented` is a type class for a choice of orientation of a module that is considered
the positive orientation.

## Implementation notes

`orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/


noncomputable section

open BigOperators

section OrderedCommSemiring

variable (R : Type _) [StrictOrderedCommSemiring R]

variable (M : Type _) [AddCommMonoid M] [Module R M]

variable {N : Type _} [AddCommMonoid N] [Module R N]

variable (ι : Type _)

#print Orientation /-
/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
abbrev Orientation :=
  Module.Ray R (AlternatingMap R M R ι)
#align orientation Orientation
-/

#print Module.Oriented /-
/-- A type class fixing an orientation of a module. -/
class Module.Oriented where
  positiveOrientation : Orientation R M ι
#align module.oriented Module.Oriented
-/

export Module.Oriented (positiveOrientation)

variable {R M}

#print Orientation.map /-
/-- An equivalence between modules implies an equivalence between orientations. -/
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLCongr R R ι R e
#align orientation.map Orientation.map
-/

/- warning: orientation.map_apply -> Orientation.map_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.map_apply Orientation.map_applyₓ'. -/
@[simp]
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : AlternatingMap R M R ι) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.comp_linearEquiv_eq_zero_iff e.symm).mp hv) :=
  rfl
#align orientation.map_apply Orientation.map_apply

/- warning: orientation.map_refl -> Orientation.map_refl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedCommSemiring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_2] (ι : Type.{u3}), Eq.{succ (max u2 u1 u3)} (Equiv.{succ (max u2 u1 u3), succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι)) (Orientation.map.{u1, u2, u2, u3} R _inst_1 M _inst_2 _inst_3 M _inst_2 _inst_3 ι (LinearEquiv.refl.{u1, u2} R M (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_2 _inst_3)) (Equiv.refl.{succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : StrictOrderedCommSemiring.{u3} R] {M : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R _inst_1)) _inst_2] (ι : Type.{u1}), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Orientation.{u3, u2, u1} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u3, u2, u1} R _inst_1 M _inst_2 _inst_3 ι)) (Orientation.map.{u3, u2, u2, u1} R _inst_1 M _inst_2 _inst_3 M _inst_2 _inst_3 ι (LinearEquiv.refl.{u3, u2} R M (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R _inst_1)) _inst_2 _inst_3)) (Equiv.refl.{max (max (succ u3) (succ u2)) (succ u1)} (Orientation.{u3, u2, u1} R _inst_1 M _inst_2 _inst_3 ι))
Case conversion may be inaccurate. Consider using '#align orientation.map_refl Orientation.map_reflₓ'. -/
@[simp]
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _ := by
  rw [Orientation.map, AlternatingMap.domLCongr_refl, Module.Ray.map_refl]
#align orientation.map_refl Orientation.map_refl

/- warning: orientation.map_symm -> Orientation.map_symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedCommSemiring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_2] {N : Type.{u3}} [_inst_4 : AddCommMonoid.{u3} N] [_inst_5 : Module.{u1, u3} R N (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_4] (ι : Type.{u4}) (e : LinearEquiv.{u1, u1, u2, u3} R R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) M N _inst_2 _inst_4 _inst_3 _inst_5), Eq.{max 1 (max (succ (max u3 u1 u4)) (succ (max u2 u1 u4))) (succ (max u2 u1 u4)) (succ (max u3 u1 u4))} (Equiv.{succ (max u3 u1 u4), succ (max u2 u1 u4)} (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι) (Orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι)) (Equiv.symm.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι) (Orientation.map.{u1, u2, u3, u4} R _inst_1 M _inst_2 _inst_3 N _inst_4 _inst_5 ι e)) (Orientation.map.{u1, u3, u2, u4} R _inst_1 N _inst_4 _inst_5 M _inst_2 _inst_3 ι (LinearEquiv.symm.{u1, u1, u2, u3} R R M N (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_2 _inst_4 _inst_3 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) e))
but is expected to have type
  forall {R : Type.{u4}} [_inst_1 : StrictOrderedCommSemiring.{u4} R] {M : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u4, u3} R M (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) _inst_2] {N : Type.{u2}} [_inst_4 : AddCommMonoid.{u2} N] [_inst_5 : Module.{u4, u2} R N (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) _inst_4] (ι : Type.{u1}) (e : LinearEquiv.{u4, u4, u3, u2} R R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)))) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1))) M N _inst_2 _inst_4 _inst_3 _inst_5), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Equiv.{max (max (succ u4) (succ u2)) (succ u1), max (max (succ u4) (succ u3)) (succ u1)} (Orientation.{u4, u2, u1} R _inst_1 N _inst_4 _inst_5 ι) (Orientation.{u4, u3, u1} R _inst_1 M _inst_2 _inst_3 ι)) (Equiv.symm.{max (max (succ u4) (succ u3)) (succ u1), max (max (succ u4) (succ u2)) (succ u1)} (Orientation.{u4, u3, u1} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u4, u2, u1} R _inst_1 N _inst_4 _inst_5 ι) (Orientation.map.{u4, u3, u2, u1} R _inst_1 M _inst_2 _inst_3 N _inst_4 _inst_5 ι e)) (Orientation.map.{u4, u2, u3, u1} R _inst_1 N _inst_4 _inst_5 M _inst_2 _inst_3 ι (LinearEquiv.symm.{u4, u4, u3, u2} R R M N (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) _inst_2 _inst_4 _inst_3 _inst_5 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)))) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1))) e))
Case conversion may be inaccurate. Consider using '#align orientation.map_symm Orientation.map_symmₓ'. -/
@[simp]
theorem Orientation.map_symm (e : M ≃ₗ[R] N) :
    (Orientation.map ι e).symm = Orientation.map ι e.symm :=
  rfl
#align orientation.map_symm Orientation.map_symm

#print IsEmpty.oriented /-
/-- A module is canonically oriented with respect to an empty index type. -/
instance (priority := 100) IsEmpty.oriented [Nontrivial R] [IsEmpty ι] : Module.Oriented R M ι
    where positiveOrientation :=
    rayOfNeZero R (AlternatingMap.constLinearEquivOfIsEmpty 1) <|
      AlternatingMap.constLinearEquivOfIsEmpty.Injective.Ne (by simp)
#align is_empty.oriented IsEmpty.oriented
-/

/- warning: orientation.map_positive_orientation_of_is_empty -> Orientation.map_positiveOrientation_of_isEmpty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedCommSemiring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_2] {N : Type.{u3}} [_inst_4 : AddCommMonoid.{u3} N] [_inst_5 : Module.{u1, u3} R N (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_4] (ι : Type.{u4}) [_inst_6 : Nontrivial.{u1} R] [_inst_7 : IsEmpty.{succ u4} ι] (f : LinearEquiv.{u1, u1, u2, u3} R R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) M N _inst_2 _inst_4 _inst_3 _inst_5), Eq.{succ (max u3 u1 u4)} (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι) (coeFn.{max 1 (max (succ (max u2 u1 u4)) (succ (max u3 u1 u4))) (succ (max u3 u1 u4)) (succ (max u2 u1 u4)), max (succ (max u2 u1 u4)) (succ (max u3 u1 u4))} (Equiv.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι)) (fun (_x : Equiv.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι)) => (Orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι) -> (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι)) (Equiv.hasCoeToFun.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι)) (Orientation.map.{u1, u2, u3, u4} R _inst_1 M _inst_2 _inst_3 N _inst_4 _inst_5 ι f) (Module.Oriented.positiveOrientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι (IsEmpty.oriented.{u1, u2, u4} R _inst_1 M _inst_2 _inst_3 ι _inst_6 _inst_7))) (Module.Oriented.positiveOrientation.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι (IsEmpty.oriented.{u1, u3, u4} R _inst_1 N _inst_4 _inst_5 ι _inst_6 _inst_7))
but is expected to have type
  forall {R : Type.{u4}} [_inst_1 : StrictOrderedCommSemiring.{u4} R] {M : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u4, u2} R M (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) _inst_2] {N : Type.{u1}} [_inst_4 : AddCommMonoid.{u1} N] [_inst_5 : Module.{u4, u1} R N (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) _inst_4] (ι : Type.{u3}) [_inst_6 : Nontrivial.{u4} R] [_inst_7 : IsEmpty.{succ u3} ι] (f : LinearEquiv.{u4, u4, u2, u1} R R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)))) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1)))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R _inst_1))) M N _inst_2 _inst_4 _inst_3 _inst_5), Eq.{max (max (succ u4) (succ u1)) (succ u3)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) => Orientation.{u4, u1, u3} R _inst_1 N _inst_4 _inst_5 ι) (Module.Oriented.positiveOrientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι (IsEmpty.oriented.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι _inst_6 _inst_7))) (FunLike.coe.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3), max (max (succ u4) (succ u2)) (succ u3), max (max (succ u4) (succ u1)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u4), max (max (succ u3) (succ u1)) (succ u4)} (Orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u4, u1, u3} R _inst_1 N _inst_4 _inst_5 ι)) (Orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (fun (_x : Orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) => Orientation.{u4, u1, u3} R _inst_1 N _inst_4 _inst_5 ι) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u3), max (max (succ u4) (succ u1)) (succ u3)} (Orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u4, u1, u3} R _inst_1 N _inst_4 _inst_5 ι)) (Orientation.map.{u4, u2, u1, u3} R _inst_1 M _inst_2 _inst_3 N _inst_4 _inst_5 ι f) (Module.Oriented.positiveOrientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι (IsEmpty.oriented.{u4, u2, u3} R _inst_1 M _inst_2 _inst_3 ι _inst_6 _inst_7))) (Module.Oriented.positiveOrientation.{u4, u1, u3} R _inst_1 N _inst_4 _inst_5 ι (IsEmpty.oriented.{u4, u1, u3} R _inst_1 N _inst_4 _inst_5 ι _inst_6 _inst_7))
Case conversion may be inaccurate. Consider using '#align orientation.map_positive_orientation_of_is_empty Orientation.map_positiveOrientation_of_isEmptyₓ'. -/
@[simp]
theorem Orientation.map_positiveOrientation_of_isEmpty [Nontrivial R] [IsEmpty ι] (f : M ≃ₗ[R] N) :
    Orientation.map ι f positiveOrientation = positiveOrientation :=
  rfl
#align orientation.map_positive_orientation_of_is_empty Orientation.map_positiveOrientation_of_isEmpty

/- warning: orientation.map_of_is_empty -> Orientation.map_of_isEmpty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedCommSemiring.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) _inst_2] (ι : Type.{u3}) [_inst_6 : IsEmpty.{succ u3} ι] (x : Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (f : LinearEquiv.{u1, u1, u2, u2} R R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) (RingHomInvPair.ids.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1))) M M _inst_2 _inst_2 _inst_3 _inst_3), Eq.{succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (coeFn.{succ (max u2 u1 u3), succ (max u2 u1 u3)} (Equiv.{succ (max u2 u1 u3), succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι)) (fun (_x : Equiv.{succ (max u2 u1 u3), succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι)) => (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) -> (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι)) (Equiv.hasCoeToFun.{succ (max u2 u1 u3), succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι)) (Orientation.map.{u1, u2, u2, u3} R _inst_1 M _inst_2 _inst_3 M _inst_2 _inst_3 ι f) x) x
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : StrictOrderedCommSemiring.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1)) _inst_2] (ι : Type.{u3}) [_inst_6 : IsEmpty.{succ u3} ι] (x : Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) (f : LinearEquiv.{u2, u2, u1, u1} R R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1)) (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1)))) (RingHomInvPair.ids.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1))) (RingHomInvPair.ids.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1))) M M _inst_2 _inst_2 _inst_3 _inst_3), Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) => Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) x) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Equiv.{max (max (succ u3) (succ u1)) (succ u2), max (max (succ u3) (succ u1)) (succ u2)} (Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι)) (Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) (fun (_x : Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) => Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) _x) (Equiv.instFunLikeEquiv.{max (max (succ u2) (succ u1)) (succ u3), max (max (succ u2) (succ u1)) (succ u3)} (Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι) (Orientation.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι)) (Orientation.map.{u2, u1, u1, u3} R _inst_1 M _inst_2 _inst_3 M _inst_2 _inst_3 ι f) x) x
Case conversion may be inaccurate. Consider using '#align orientation.map_of_is_empty Orientation.map_of_isEmptyₓ'. -/
@[simp]
theorem Orientation.map_of_isEmpty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = x :=
  by
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.compLinearMap_apply]
  congr
#align orientation.map_of_is_empty Orientation.map_of_isEmpty

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type _} [StrictOrderedCommRing R]

variable {M N : Type _} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/- warning: orientation.map_neg -> Orientation.map_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.map_neg Orientation.map_negₓ'. -/
@[simp]
protected theorem Orientation.map_neg {ι : Type _} (f : M ≃ₗ[R] N) (x : Orientation R M ι) :
    Orientation.map ι f (-x) = -Orientation.map ι f x :=
  Module.Ray.map_neg _ x
#align orientation.map_neg Orientation.map_neg

namespace Basis

variable {ι : Type _}

/- warning: basis.map_orientation_eq_det_inv_smul -> Basis.map_orientation_eq_det_inv_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.map_orientation_eq_det_inv_smul Basis.map_orientation_eq_det_inv_smulₓ'. -/
/-- The value of `orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
theorem map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = f.det⁻¹ • x :=
  by
  cases nonempty_fintype ι
  letI := Classical.decEq ι
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply, smul_rayOfNeZero, ray_eq_iff, Units.smul_def,
    (g.comp_linear_map ↑f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e,
    AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Basis.det_comp, Basis.det_self,
    mul_one, smul_eq_mul, mul_comm, mul_smul, LinearEquiv.coe_inv_det]
#align basis.map_orientation_eq_det_inv_smul Basis.map_orientation_eq_det_inv_smul

variable [Fintype ι] [DecidableEq ι]

#print Basis.orientation /-
/-- The orientation given by a basis. -/
protected def orientation [Nontrivial R] (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero
#align basis.orientation Basis.orientation
-/

/- warning: basis.orientation_map -> Basis.orientation_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u1} R] {M : Type.{u2}} {N : Type.{u3}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : AddCommGroup.{u3} N] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_5 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u3} N _inst_3)] {ι : Type.{u4}} [_inst_6 : Fintype.{u4} ι] [_inst_7 : DecidableEq.{succ u4} ι] [_inst_8 : Nontrivial.{u1} R] (e : Basis.{u4, u1, u2} ι R M (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4) (f : LinearEquiv.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))))) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)))) (RingHomInvPair.ids.{u1} R (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)))) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_4 _inst_5), Eq.{succ (max u3 u1 u4)} (Orientation.{u1, u3, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 ι) (Basis.orientation.{u1, u3, u4} R _inst_1 N _inst_3 _inst_5 ι _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b) _inst_8 (Basis.map.{u4, u1, u2, u3} ι R M N (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 e f)) (coeFn.{max 1 (max (succ (max u2 u1 u4)) (succ (max u3 u1 u4))) (succ (max u3 u1 u4)) (succ (max u2 u1 u4)), max (succ (max u2 u1 u4)) (succ (max u3 u1 u4))} (Equiv.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (Orientation.{u1, u3, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 ι)) (fun (_x : Equiv.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (Orientation.{u1, u3, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 ι)) => (Orientation.{u1, u2, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) -> (Orientation.{u1, u3, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 ι)) (Equiv.hasCoeToFun.{succ (max u2 u1 u4), succ (max u3 u1 u4)} (Orientation.{u1, u2, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (Orientation.{u1, u3, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 ι)) (Orientation.map.{u1, u2, u3, u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 N (AddCommGroup.toAddCommMonoid.{u3} N _inst_3) _inst_5 ι f) (Basis.orientation.{u1, u2, u4} R _inst_1 M _inst_2 _inst_4 ι _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b) _inst_8 e))
but is expected to have type
  forall {R : Type.{u4}} [_inst_1 : StrictOrderedCommRing.{u4} R] {M : Type.{u2}} {N : Type.{u1}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : AddCommGroup.{u1} N] [_inst_4 : Module.{u4, u2} R M (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_5 : Module.{u4, u1} R N (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} N _inst_3)] {ι : Type.{u3}} [_inst_6 : Fintype.{u3} ι] [_inst_7 : DecidableEq.{succ u3} ι] [_inst_8 : Nontrivial.{u4} R] (e : Basis.{u3, u4, u2} ι R M (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4) (f : LinearEquiv.{u4, u4, u2, u1} R R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))) (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))))) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1)))) (RingHomInvPair.ids.{u4} R (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1)))) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_4 _inst_5), Eq.{max (max (succ u4) (succ u1)) (succ u3)} (Orientation.{u4, u1, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_5 ι) (Basis.orientation.{u4, u1, u3} R _inst_1 N _inst_3 _inst_5 ι _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b) _inst_8 (Basis.map.{u3, u4, u2, u1} ι R M N (StrictOrderedSemiring.toSemiring.{u4} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u4} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_5 e f)) (FunLike.coe.{max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3), max (max (succ u4) (succ u2)) (succ u3), max (max (succ u4) (succ u1)) (succ u3)} (Equiv.{max (max (succ u3) (succ u2)) (succ u4), max (max (succ u3) (succ u1)) (succ u4)} (Orientation.{u4, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (Orientation.{u4, u1, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_5 ι)) (Orientation.{u4, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (fun (_x : Orientation.{u4, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Orientation.{u4, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) => Orientation.{u4, u1, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_5 ι) _x) (Equiv.instFunLikeEquiv.{max (max (succ u4) (succ u2)) (succ u3), max (max (succ u4) (succ u1)) (succ u3)} (Orientation.{u4, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (Orientation.{u4, u1, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) N (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_5 ι)) (Orientation.map.{u4, u2, u1, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u4} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 N (AddCommGroup.toAddCommMonoid.{u1} N _inst_3) _inst_5 ι f) (Basis.orientation.{u4, u2, u3} R _inst_1 M _inst_2 _inst_4 ι _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b) _inst_8 e))
Case conversion may be inaccurate. Consider using '#align basis.orientation_map Basis.orientation_mapₓ'. -/
theorem orientation_map [Nontrivial R] (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).Orientation = Orientation.map ι f e.Orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']
#align basis.orientation_map Basis.orientation_map

/- warning: basis.orientation_units_smul -> Basis.orientation_unitsSMul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_units_smul Basis.orientation_unitsSMulₓ'. -/
/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
theorem orientation_unitsSMul [Nontrivial R] (e : Basis ι R M) (w : ι → Units R) :
    (e.units_smul w).Orientation = (∏ i, w i)⁻¹ • e.Orientation :=
  by
  rw [Basis.orientation, Basis.orientation, smul_rayOfNeZero, ray_eq_iff,
    e.det.eq_smul_basis_det (e.units_smul w), det_units_smul_self, Units.smul_def, smul_smul]
  norm_cast
  simp
#align basis.orientation_units_smul Basis.orientation_unitsSMul

/- warning: basis.orientation_is_empty -> Basis.orientation_isEmpty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {ι : Type.{u3}} [_inst_6 : Fintype.{u3} ι] [_inst_7 : DecidableEq.{succ u3} ι] [_inst_8 : Nontrivial.{u1} R] [_inst_9 : IsEmpty.{succ u3} ι] (b : Basis.{u3, u1, u2} ι R M (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4), Eq.{succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι) (Basis.orientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_4 ι _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b) _inst_8 b) (Module.Oriented.positiveOrientation.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι (IsEmpty.oriented.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_4 ι _inst_8 _inst_9))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u3} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_4 : Module.{u3, u1} R M (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {ι : Type.{u2}} [_inst_6 : Fintype.{u2} ι] [_inst_7 : DecidableEq.{succ u2} ι] [_inst_8 : Nontrivial.{u3} R] [_inst_9 : IsEmpty.{succ u2} ι] (b : Basis.{u2, u3, u1} ι R M (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Orientation.{u3, u1, u2} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4 ι) (Basis.orientation.{u3, u1, u2} R _inst_1 M _inst_2 _inst_4 ι _inst_6 (fun (a : ι) (b : ι) => _inst_7 a b) _inst_8 b) (Module.Oriented.positiveOrientation.{u3, u1, u2} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4 ι (IsEmpty.oriented.{u3, u1, u2} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_4 ι _inst_8 _inst_9))
Case conversion may be inaccurate. Consider using '#align basis.orientation_is_empty Basis.orientation_isEmptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ray_of_ne_zero _ _ _]] -/
@[simp]
theorem orientation_isEmpty [Nontrivial R] [IsEmpty ι] (b : Basis ι R M) :
    b.Orientation = positiveOrientation :=
  by
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ray_of_ne_zero _ _ _]]"
  convert b.det_is_empty
#align basis.orientation_is_empty Basis.orientation_isEmpty

end Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type _} [LinearOrderedCommRing R]

variable {M : Type _} [AddCommGroup M] [Module R M]

variable {ι : Type _}

namespace Orientation

/- warning: orientation.eq_or_eq_neg_of_is_empty -> Orientation.eq_or_eq_neg_of_isEmpty is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.eq_or_eq_neg_of_is_empty Orientation.eq_or_eq_neg_of_isEmptyₓ'. -/
/-- A module `M` over a linearly ordered commutative ring has precisely two "orientations" with
respect to an empty index type. (Note that these are only orientations of `M` of in the conventional
mathematical sense if `M` is zero-dimensional.) -/
theorem eq_or_eq_neg_of_isEmpty [Nontrivial R] [IsEmpty ι] (o : Orientation R M ι) :
    o = positiveOrientation ∨ o = -positiveOrientation :=
  by
  induction' o using Module.Ray.ind with x hx
  dsimp [positive_orientation]
  simp only [ray_eq_iff, sameRay_neg_swap]
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  intro h
  let a : R := alternating_map.const_linear_equiv_of_is_empty.symm x
  have H : LinearIndependent R ![a, 1] :=
    by
    convert h.map' (↑alternating_map.const_linear_equiv_of_is_empty.symm) (LinearEquiv.ker _)
    ext i
    fin_cases i <;> simp [a]
  rw [linearIndependent_iff'] at H
  simpa using H Finset.univ ![1, -a] (by simp [Fin.sum_univ_succ]) 0 (by simp)
#align orientation.eq_or_eq_neg_of_is_empty Orientation.eq_or_eq_neg_of_isEmpty

end Orientation

namespace Basis

variable [Fintype ι] [DecidableEq ι]

/- warning: basis.orientation_eq_iff_det_pos -> Basis.orientation_eq_iff_det_pos is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_eq_iff_det_pos Basis.orientation_eq_iff_det_posₓ'. -/
/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) :
    e₁.Orientation = e₂.Orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.Orientation = e₂.Orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).NeZero
    
#align basis.orientation_eq_iff_det_pos Basis.orientation_eq_iff_det_pos

/- warning: basis.orientation_eq_or_eq_neg -> Basis.orientation_eq_or_eq_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_eq_or_eq_neg Basis.orientation_eq_or_eq_negₓ'. -/
/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x = e.Orientation ∨ x = -e.Orientation :=
  by
  induction' x using Module.Ray.ind with x hx
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_iff_ne, ne_comm]
#align basis.orientation_eq_or_eq_neg Basis.orientation_eq_or_eq_neg

/- warning: basis.orientation_ne_iff_eq_neg -> Basis.orientation_ne_iff_eq_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_ne_iff_eq_neg Basis.orientation_ne_iff_eq_negₓ'. -/
/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x ≠ e.Orientation ↔ x = -e.Orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.Orientation).symm⟩
#align basis.orientation_ne_iff_eq_neg Basis.orientation_ne_iff_eq_neg

/- warning: basis.orientation_comp_linear_equiv_eq_iff_det_pos -> Basis.orientation_comp_linearEquiv_eq_iff_det_pos is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_comp_linear_equiv_eq_iff_det_pos Basis.orientation_comp_linearEquiv_eq_iff_det_posₓ'. -/
/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
theorem orientation_comp_linearEquiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = e.Orientation ↔ 0 < (f : M →ₗ[R] M).det := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff,
    LinearEquiv.coe_det]
#align basis.orientation_comp_linear_equiv_eq_iff_det_pos Basis.orientation_comp_linearEquiv_eq_iff_det_pos

/- warning: basis.orientation_comp_linear_equiv_eq_neg_iff_det_neg -> Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_comp_linear_equiv_eq_neg_iff_det_neg Basis.orientation_comp_linearEquiv_eq_neg_iff_det_negₓ'. -/
/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
theorem orientation_comp_linearEquiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = -e.Orientation ↔ (f : M →ₗ[R] M).det < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff,
    LinearEquiv.coe_det]
#align basis.orientation_comp_linear_equiv_eq_neg_iff_det_neg Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg

/- warning: basis.orientation_neg_single -> Basis.orientation_neg_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.orientation_neg_single Basis.orientation_neg_singleₓ'. -/
/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
theorem orientation_neg_single [Nontrivial R] (e : Basis ι R M) (i : ι) :
    (e.units_smul (Function.update 1 i (-1))).Orientation = -e.Orientation :=
  by
  rw [orientation_units_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp
#align basis.orientation_neg_single Basis.orientation_neg_single

#print Basis.adjustToOrientation /-
/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
def adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.units_smul (Function.update 1 (Classical.arbitrary ι) (-1))
#align basis.adjust_to_orientation Basis.adjustToOrientation
-/

/- warning: basis.orientation_adjust_to_orientation -> Basis.orientation_adjustToOrientation is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedCommRing.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {ι : Type.{u3}} [_inst_4 : Fintype.{u3} ι] [_inst_5 : DecidableEq.{succ u3} ι] [_inst_6 : Nontrivial.{u1} R] [_inst_7 : Nonempty.{succ u3} ι] (e : Basis.{u3, u1, u2} ι R M (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) (x : Orientation.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R _inst_1)) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 ι), Eq.{succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R _inst_1)) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 ι) (Basis.orientation.{u1, u2, u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R _inst_1) M _inst_2 _inst_3 ι _inst_4 (fun (a : ι) (b : ι) => _inst_5 a b) _inst_6 (Basis.adjustToOrientation.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι _inst_4 (fun (a : ι) (b : ι) => _inst_5 a b) _inst_6 _inst_7 e x)) x
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : LinearOrderedCommRing.{u3} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u3, u1} R M (StrictOrderedSemiring.toSemiring.{u3} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} R (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u3} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {ι : Type.{u2}} [_inst_4 : Fintype.{u2} ι] [_inst_5 : DecidableEq.{succ u2} ι] [_inst_6 : Nontrivial.{u3} R] [_inst_7 : Nonempty.{succ u2} ι] (e : Basis.{u2, u3, u1} ι R M (StrictOrderedSemiring.toSemiring.{u3} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} R (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u3} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3) (x : Orientation.{u3, u1, u2} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u3} R (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u3} R _inst_1)) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 ι), Eq.{max (max (succ u3) (succ u1)) (succ u2)} (Orientation.{u3, u1, u2} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R _inst_1)) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 ι) (Basis.orientation.{u3, u1, u2} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R _inst_1) M _inst_2 _inst_3 ι _inst_4 (fun (a : ι) (b : ι) => _inst_5 a b) _inst_6 (Basis.adjustToOrientation.{u3, u1, u2} R _inst_1 M _inst_2 _inst_3 ι _inst_4 (fun (a : ι) (b : ι) => _inst_5 a b) _inst_6 _inst_7 e x)) x
Case conversion may be inaccurate. Consider using '#align basis.orientation_adjust_to_orientation Basis.orientation_adjustToOrientationₓ'. -/
/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
theorem orientation_adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) : (e.adjustToOrientation x).Orientation = x :=
  by
  rw [adjust_to_orientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h
#align basis.orientation_adjust_to_orientation Basis.orientation_adjustToOrientation

/- warning: basis.adjust_to_orientation_apply_eq_or_eq_neg -> Basis.adjustToOrientation_apply_eq_or_eq_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.adjust_to_orientation_apply_eq_or_eq_neg Basis.adjustToOrientation_apply_eq_or_eq_negₓ'. -/
/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
theorem adjustToOrientation_apply_eq_or_eq_neg [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i :=
  by
  rw [adjust_to_orientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [units_smul_apply, hi]
#align basis.adjust_to_orientation_apply_eq_or_eq_neg Basis.adjustToOrientation_apply_eq_or_eq_neg

/- warning: basis.det_adjust_to_orientation -> Basis.det_adjustToOrientation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.det_adjust_to_orientation Basis.det_adjustToOrientationₓ'. -/
theorem det_adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) :
    (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -e.det :=
  by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp [e.det_units_smul, ← Units.coe_prod, Finset.prod_update_of_mem]
#align basis.det_adjust_to_orientation Basis.det_adjustToOrientation

/- warning: basis.abs_det_adjust_to_orientation -> Basis.abs_det_adjustToOrientation is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.abs_det_adjust_to_orientation Basis.abs_det_adjustToOrientationₓ'. -/
@[simp]
theorem abs_det_adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (v : ι → M) : |(e.adjustToOrientation x).det v| = |e.det v| := by
  cases' e.det_adjust_to_orientation x with h h <;> simp [h]
#align basis.abs_det_adjust_to_orientation Basis.abs_det_adjustToOrientation

end Basis

end LinearOrderedCommRing

section LinearOrderedField

variable {R : Type _} [LinearOrderedField R]

variable {M : Type _} [AddCommGroup M] [Module R M]

variable {ι : Type _}

namespace Orientation

variable [Fintype ι] [_i : FiniteDimensional R M]

open FiniteDimensional

include _i

/- warning: orientation.eq_or_eq_neg -> Orientation.eq_or_eq_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.eq_or_eq_neg Orientation.eq_or_eq_negₓ'. -/
/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
theorem eq_or_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    x₁ = x₂ ∨ x₁ = -x₂ :=
  by
  have e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  letI := Classical.decEq ι
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
      rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;>
    simp [h₁, h₂]
#align orientation.eq_or_eq_neg Orientation.eq_or_eq_neg

/- warning: orientation.ne_iff_eq_neg -> Orientation.ne_iff_eq_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.ne_iff_eq_neg Orientation.ne_iff_eq_negₓ'. -/
/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
theorem ne_iff_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩
#align orientation.ne_iff_eq_neg Orientation.ne_iff_eq_neg

/- warning: orientation.map_eq_det_inv_smul -> Orientation.map_eq_det_inv_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.map_eq_det_inv_smul Orientation.map_eq_det_inv_smulₓ'. -/
/-- The value of `orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
theorem map_eq_det_inv_smul (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = f.det⁻¹ • x :=
  haveI e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f
#align orientation.map_eq_det_inv_smul Orientation.map_eq_det_inv_smul

omit _i

/- warning: orientation.map_eq_iff_det_pos -> Orientation.map_eq_iff_det_pos is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.map_eq_iff_det_pos Orientation.map_eq_iff_det_posₓ'. -/
/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
theorem map_eq_iff_det_pos (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = x ↔ 0 < (f : M →ₗ[R] M).det :=
  by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := by
      refine' h.symm.trans _
      convert Fintype.card_of_isEmpty
      infer_instance
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  haveI : FiniteDimensional R M := finite_dimensional_of_finrank H
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]
#align orientation.map_eq_iff_det_pos Orientation.map_eq_iff_det_pos

/- warning: orientation.map_eq_neg_iff_det_neg -> Orientation.map_eq_neg_iff_det_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orientation.map_eq_neg_iff_det_neg Orientation.map_eq_neg_iff_det_negₓ'. -/
/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = -x ↔ (f : M →ₗ[R] M).det < 0 :=
  by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := by
      refine' h.symm.trans _
      convert Fintype.card_of_isEmpty
      infer_instance
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  haveI : FiniteDimensional R M := finite_dimensional_of_finrank H
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]
#align orientation.map_eq_neg_iff_det_neg Orientation.map_eq_neg_iff_det_neg

include _i

#print Orientation.someBasis /-
/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
def someBasis [Nonempty ι] [DecidableEq ι] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x
#align orientation.some_basis Orientation.someBasis
-/

/- warning: orientation.some_basis_orientation -> Orientation.someBasis_orientation is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] {M : Type.{u2}} [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {ι : Type.{u3}} [_inst_4 : Fintype.{u3} ι] [_i : FiniteDimensional.{u1, u2} R M (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)) _inst_2 _inst_3] [_inst_5 : Nonempty.{succ u3} ι] [_inst_6 : DecidableEq.{succ u3} ι] (x : Orientation.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 ι) (h : Eq.{1} Nat (Fintype.card.{u3} ι _inst_4) (FiniteDimensional.finrank.{u1, u2} R M (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) _inst_2 _inst_3)), Eq.{succ (max u2 u1 u3)} (Orientation.{u1, u2, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u1} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))) M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3 ι) (Basis.orientation.{u1, u2, u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) M _inst_2 _inst_3 ι _inst_4 (fun (a : ι) (b : ι) => _inst_6 a b) (EuclideanDomain.to_nontrivial.{u1} R (Field.toEuclideanDomain.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) (Orientation.someBasis.{u1, u2, u3} R _inst_1 M _inst_2 _inst_3 ι _inst_4 _i _inst_5 (fun (a : ι) (b : ι) => _inst_6 a b) x h)) x
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} R] {M : Type.{u1}} [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : Module.{u2, u1} R M (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (LinearOrderedSemifield.toSemifield.{u2} R (LinearOrderedField.toLinearOrderedSemifield.{u2} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {ι : Type.{u3}} [_inst_4 : Fintype.{u3} ι] [_i : FiniteDimensional.{u2, u1} R M (Field.toDivisionRing.{u2} R (LinearOrderedField.toField.{u2} R _inst_1)) _inst_2 _inst_3] [_inst_5 : Nonempty.{succ u3} ι] [_inst_6 : DecidableEq.{succ u3} ι] (x : Orientation.{u2, u1, u3} R (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} R (LinearOrderedField.toLinearOrderedSemifield.{u2} R _inst_1))) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 ι) (h : Eq.{1} Nat (Fintype.card.{u3} ι _inst_4) (FiniteDimensional.finrank.{u2, u1} R M (DivisionSemiring.toSemiring.{u2} R (Semifield.toDivisionSemiring.{u2} R (LinearOrderedSemifield.toSemifield.{u2} R (LinearOrderedField.toLinearOrderedSemifield.{u2} R _inst_1)))) _inst_2 _inst_3)), Eq.{max (max (succ u2) (succ u1)) (succ u3)} (Orientation.{u2, u1, u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u2} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1))) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_3 ι) (Basis.orientation.{u2, u1, u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u2} R (LinearOrderedField.toLinearOrderedCommRing.{u2} R _inst_1)) M _inst_2 _inst_3 ι _inst_4 (fun (a : ι) (b : ι) => _inst_6 a b) (EuclideanDomain.toNontrivial.{u2} R (Field.toEuclideanDomain.{u2} R (LinearOrderedField.toField.{u2} R _inst_1))) (Orientation.someBasis.{u2, u1, u3} R _inst_1 M _inst_2 _inst_3 ι _inst_4 _i _inst_5 (fun (a : ι) (b : ι) => _inst_6 a b) x h)) x
Case conversion may be inaccurate. Consider using '#align orientation.some_basis_orientation Orientation.someBasis_orientationₓ'. -/
/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
theorem someBasis_orientation [Nonempty ι] [DecidableEq ι] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : (x.someBasis h).Orientation = x :=
  Basis.orientation_adjustToOrientation _ _
#align orientation.some_basis_orientation Orientation.someBasis_orientation

end Orientation

end LinearOrderedField

