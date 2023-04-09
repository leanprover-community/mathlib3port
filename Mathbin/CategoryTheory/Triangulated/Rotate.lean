/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw, Joël Riou

! This file was ported from Lean 3 source module category_theory.triangulated.rotate
! leanprover-community/mathlib commit 94d4e70e97c36c896cb70fb42821acfed040de60
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Triangulated.Basic

/-!
# Rotate

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [HasShift C ℤ]

variable (X : C)

/- warning: category_theory.pretriangulated.triangle.rotate -> CategoryTheory.Pretriangulated.Triangle.rotate is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid], (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) -> (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt], (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) -> (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.triangle.rotate CategoryTheory.Pretriangulated.Triangle.rotateₓ'. -/
/-- If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `rotate` gives a triangle of the form:
```
      g       h        -f⟦1⟧'
  Y  ───> Z  ───>  X⟦1⟧ ───> Y⟦1⟧
```
-/
@[simps]
def Triangle.rotate (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')
#align category_theory.pretriangulated.triangle.rotate CategoryTheory.Pretriangulated.Triangle.rotate

section

/- warning: category_theory.pretriangulated.triangle.inv_rotate -> CategoryTheory.Pretriangulated.Triangle.invRotate is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid], (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) -> (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt], (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) -> (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.triangle.inv_rotate CategoryTheory.Pretriangulated.Triangle.invRotateₓ'. -/
/-- Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `inv_rotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧'     f       g
  Z⟦-1⟧  ───>  X  ───> Y  ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counit_iso` of `shift C`)
-/
@[simps]
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg _ _).Hom) T.mor₁
    (T.mor₂ ≫ (shiftNegShift _ _).inv)
#align category_theory.pretriangulated.triangle.inv_rotate CategoryTheory.Pretriangulated.Triangle.invRotate

end

variable (C)

/- warning: category_theory.pretriangulated.rotate -> CategoryTheory.Pretriangulated.rotate is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid], CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt], CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.rotate CategoryTheory.Pretriangulated.rotateₓ'. -/
/-- Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def rotate : Triangle C ⥤ Triangle C
    where
  obj := Triangle.rotate
  map T₁ T₂ f :=
    { hom₁ := f.hom₂
      hom₂ := f.hom₃
      hom₃ := f.hom₁⟦1⟧'
      comm₃' := by
        dsimp
        simp only [comp_neg, neg_comp, ← functor.map_comp, f.comm₁] }
#align category_theory.pretriangulated.rotate CategoryTheory.Pretriangulated.rotate

/- warning: category_theory.pretriangulated.inv_rotate -> CategoryTheory.Pretriangulated.invRotate is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid], CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt], CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.inv_rotate CategoryTheory.Pretriangulated.invRotateₓ'. -/
/-- The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def invRotate : Triangle C ⥤ Triangle C
    where
  obj := Triangle.invRotate
  map T₁ T₂ f :=
    { hom₁ := f.hom₃⟦-1⟧'
      hom₂ := f.hom₁
      hom₃ := f.hom₂
      comm₁' := by
        dsimp
        rw [neg_comp, assoc, comp_neg, neg_inj, ← functor.map_comp_assoc, ← f.comm₃,
          functor.map_comp, assoc]
        erw [← nat_trans.naturality]
        rfl
      comm₃' := by
        dsimp
        erw [← f.comm₂_assoc, assoc, ← nat_trans.naturality]
        rfl }
#align category_theory.pretriangulated.inv_rotate CategoryTheory.Pretriangulated.invRotate

variable {C}

variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]

attribute [local simp]
  shift_shift_neg' shift_neg_shift' shift_shift_functor_comp_iso_id_add_neg_self_inv_app shift_shift_functor_comp_iso_id_add_neg_self_hom_app

/- warning: category_theory.pretriangulated.rot_comp_inv_rot -> CategoryTheory.Pretriangulated.rotCompInvRot is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid] [_inst_4 : forall (n : Int), CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C C _inst_1 _inst_1 _inst_2 _inst_2 (CategoryTheory.shiftFunctor.{u1, u2, 0} C Int _inst_1 Int.addMonoid _inst_3 n)], CategoryTheory.Iso.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.id.{u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.rotate.{u1, u2} C _inst_1 _inst_2 _inst_3) (CategoryTheory.Pretriangulated.invRotate.{u1, u2} C _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt] [_inst_4 : forall (n : Int), CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C C _inst_1 _inst_1 _inst_2 _inst_2 (CategoryTheory.shiftFunctor.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt _inst_3 n)], CategoryTheory.Iso.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.id.{u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.rotate.{u1, u2} C _inst_1 _inst_2 _inst_3) (CategoryTheory.Pretriangulated.invRotate.{u1, u2} C _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.rot_comp_inv_rot CategoryTheory.Pretriangulated.rotCompInvRotₓ'. -/
/-- The unit isomorphism of the auto-equivalence of categories `triangle_rotation C` of
`triangle C` given by the rotation of triangles. -/
@[simps]
def rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C :=
  NatIso.ofComponents
    (fun T =>
      Triangle.isoMk _ _ ((shiftEquiv C (1 : ℤ)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)
        (by tidy) (by tidy) (by tidy))
    (by tidy)
#align category_theory.pretriangulated.rot_comp_inv_rot CategoryTheory.Pretriangulated.rotCompInvRot

/- warning: category_theory.pretriangulated.inv_rot_comp_rot -> CategoryTheory.Pretriangulated.invRotCompRot is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid] [_inst_4 : forall (n : Int), CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C C _inst_1 _inst_1 _inst_2 _inst_2 (CategoryTheory.shiftFunctor.{u1, u2, 0} C Int _inst_1 Int.addMonoid _inst_3 n)], CategoryTheory.Iso.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.invRotate.{u1, u2} C _inst_1 _inst_2 _inst_3) (CategoryTheory.Pretriangulated.rotate.{u1, u2} C _inst_1 _inst_2 _inst_3)) (CategoryTheory.Functor.id.{u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt] [_inst_4 : forall (n : Int), CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C C _inst_1 _inst_1 _inst_2 _inst_2 (CategoryTheory.shiftFunctor.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt _inst_3 n)], CategoryTheory.Iso.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.category.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)) (CategoryTheory.Functor.comp.{u1, u1, u1, max u2 u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.invRotate.{u1, u2} C _inst_1 _inst_2 _inst_3) (CategoryTheory.Pretriangulated.rotate.{u1, u2} C _inst_1 _inst_2 _inst_3)) (CategoryTheory.Functor.id.{u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.inv_rot_comp_rot CategoryTheory.Pretriangulated.invRotCompRotₓ'. -/
/-- The counit isomorphism of the auto-equivalence of categories `triangle_rotation C` of
`triangle C` given by the rotation of triangles. -/
@[simps]
def invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C) :=
  NatIso.ofComponents
    (fun T =>
      Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((shiftEquiv C (1 : ℤ)).counitIso.app T.obj₃)
        (by tidy) (by tidy) (by tidy))
    (by tidy)
#align category_theory.pretriangulated.inv_rot_comp_rot CategoryTheory.Pretriangulated.invRotCompRot

variable (C)

/- warning: category_theory.pretriangulated.triangle_rotation -> CategoryTheory.Pretriangulated.triangleRotation is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.addMonoid] [_inst_4 : forall (n : Int), CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C C _inst_1 _inst_1 _inst_2 _inst_2 (CategoryTheory.shiftFunctor.{u1, u2, 0} C Int _inst_1 Int.addMonoid _inst_3 n)], CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} C _inst_1] [_inst_3 : CategoryTheory.HasShift.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt] [_inst_4 : forall (n : Int), CategoryTheory.Functor.Additive.{u2, u2, u1, u1} C C _inst_1 _inst_1 _inst_2 _inst_2 (CategoryTheory.shiftFunctor.{u1, u2, 0} C Int _inst_1 Int.instAddMonoidInt _inst_3 n)], CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.Triangle.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3) (CategoryTheory.Pretriangulated.triangleCategory.{u1, u2} C _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align category_theory.pretriangulated.triangle_rotation CategoryTheory.Pretriangulated.triangleRotationₓ'. -/
/-- Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
def triangleRotation : Equivalence (Triangle C) (Triangle C)
    where
  Functor := rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot
#align category_theory.pretriangulated.triangle_rotation CategoryTheory.Pretriangulated.triangleRotation

variable {C}

instance : IsEquivalence (rotate C) :=
  by
  change is_equivalence (triangle_rotation C).Functor
  infer_instance

instance : IsEquivalence (invRotate C) :=
  by
  change is_equivalence (triangle_rotation C).inverse
  infer_instance

end CategoryTheory.Pretriangulated

