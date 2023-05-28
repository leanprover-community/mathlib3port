/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.category.Ring.adjunctions
! leanprover-community/mathlib commit 79ffb5563b56fefdea3d60b5736dad168a9494ab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Data.MvPolynomial.CommRing

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/


noncomputable section

universe u

open MvPolynomial

open CategoryTheory

namespace CommRingCat

open Classical

#print CommRingCat.free /-
/-- The free functor `Type u ⥤ CommRing` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRingCat.{u}
    where
  obj α := of (MvPolynomial α ℤ)
  map X Y f := (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
  -- TODO these next two fields can be done by `tidy`, but the calls in `dsimp` and `simp` it
  -- generates are too slow.
  map_id' X := RingHom.ext <| rename_id
  map_comp' X Y Z f g := RingHom.ext fun p => (rename_rename f g p).symm
#align CommRing.free CommRingCat.free
-/

/- warning: CommRing.free_obj_coe -> CommRingCat.free_obj_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Type.{u1} (coeSort.{succ (succ u1), succ (succ u1)} CommRingCat.{u1} Type.{u1} CommRingCat.hasCoeToSort.{u1} (CategoryTheory.Functor.obj.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} CommRingCat.{u1} CommRingCat.largeCategory.{u1} CommRingCat.free.{u1} α)) (MvPolynomial.{u1, 0} α Int Int.commSemiring)
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Type.{u1} (CategoryTheory.Bundled.α.{u1, u1} CommRing.{u1} (Prefunctor.obj.{succ u1, succ u1, succ u1, succ u1} Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) CommRingCat.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} CommRingCat.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} CommRingCat.{u1} instCommRingCatLargeCategory.{u1} CommRingCat.free.{u1}) α)) (MvPolynomial.{u1, 0} α Int Int.instCommSemiringInt)
Case conversion may be inaccurate. Consider using '#align CommRing.free_obj_coe CommRingCat.free_obj_coeₓ'. -/
@[simp]
theorem free_obj_coe {α : Type u} : (free.obj α : Type u) = MvPolynomial α ℤ :=
  rfl
#align CommRing.free_obj_coe CommRingCat.free_obj_coe

/- warning: CommRing.free_map_coe -> CommRingCat.free_map_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align CommRing.free_map_coe CommRingCat.free_map_coeₓ'. -/
@[simp]
theorem free_map_coe {α β : Type u} {f : α → β} : ⇑(free.map f) = rename f :=
  rfl
#align CommRing.free_map_coe CommRingCat.free_map_coe

#print CommRingCat.adj /-
/-- The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ forget CommRingCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X R => homEquiv
      homEquiv_naturality_left_symm := fun _ _ Y f g =>
        RingHom.ext fun x => eval₂_cast_comp f (Int.castRingHom Y) g x }
#align CommRing.adj CommRingCat.adj
-/

instance : IsRightAdjoint (forget CommRingCat.{u}) :=
  ⟨_, adj⟩

end CommRingCat

