/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module category_theory.conj
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Units.Basic
import Mathbin.CategoryTheory.Endomorphism

/-!
# Conjugate morphisms by isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism `conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `conj_Aut : Aut X ≃* Aut Y` by `α.conj_Aut f = α.symm ≪≫ f ≪≫ α`.

For completeness, we also define `hom_congr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`,
cf. `equiv.arrow_congr`.
-/


universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

#print CategoryTheory.Iso.homCongr /-
/-- If `X` is isomorphic to `X₁` and `Y` is isomorphic to `Y₁`, then
there is a natural bijection between `X ⟶ Y` and `X₁ ⟶ Y₁`. See also `equiv.arrow_congr`. -/
def homCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) : (X ⟶ Y) ≃ (X₁ ⟶ Y₁)
    where
  toFun f := α.inv ≫ f ≫ β.Hom
  invFun f := α.Hom ≫ f ≫ β.inv
  left_inv f :=
    show α.Hom ≫ (α.inv ≫ f ≫ β.Hom) ≫ β.inv = f by
      rw [category.assoc, category.assoc, β.hom_inv_id, α.hom_inv_id_assoc, category.comp_id]
  right_inv f :=
    show α.inv ≫ (α.Hom ≫ f ≫ β.inv) ≫ β.Hom = f by
      rw [category.assoc, category.assoc, β.inv_hom_id, α.inv_hom_id_assoc, category.comp_id]
#align category_theory.iso.hom_congr CategoryTheory.Iso.homCongr
-/

#print CategoryTheory.Iso.homCongr_apply /-
@[simp]
theorem homCongr_apply {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) :
    α.homCongr β f = α.inv ≫ f ≫ β.Hom :=
  rfl
#align category_theory.iso.hom_congr_apply CategoryTheory.Iso.homCongr_apply
-/

#print CategoryTheory.Iso.homCongr_comp /-
theorem homCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y)
    (g : Y ⟶ Z) : α.homCongr γ (f ≫ g) = α.homCongr β f ≫ β.homCongr γ g := by simp
#align category_theory.iso.hom_congr_comp CategoryTheory.Iso.homCongr_comp
-/

#print CategoryTheory.Iso.homCongr_refl /-
@[simp]
theorem homCongr_refl {X Y : C} (f : X ⟶ Y) : (Iso.refl X).homCongr (Iso.refl Y) f = f := by simp
#align category_theory.iso.hom_congr_refl CategoryTheory.Iso.homCongr_refl
-/

#print CategoryTheory.Iso.homCongr_trans /-
@[simp]
theorem homCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃)
    (β₂ : Y₂ ≅ Y₃) (f : X₁ ⟶ Y₁) :
    (α₁ ≪≫ α₂).homCongr (β₁ ≪≫ β₂) f = (α₁.homCongr β₁).trans (α₂.homCongr β₂) f := by simp
#align category_theory.iso.hom_congr_trans CategoryTheory.Iso.homCongr_trans
-/

#print CategoryTheory.Iso.homCongr_symm /-
@[simp]
theorem homCongr_symm {X₁ Y₁ X₂ Y₂ : C} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂) :
    (α.homCongr β).symm = α.symm.homCongr β.symm :=
  rfl
#align category_theory.iso.hom_congr_symm CategoryTheory.Iso.homCongr_symm
-/

variable {X Y : C} (α : X ≅ Y)

#print CategoryTheory.Iso.conj /-
/-- An isomorphism between two objects defines a monoid isomorphism between their
monoid of endomorphisms. -/
def conj : End X ≃* End Y :=
  { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }
#align category_theory.iso.conj CategoryTheory.Iso.conj
-/

/- warning: category_theory.iso.conj_apply -> CategoryTheory.Iso.conj_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (α : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) (f : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X), Eq.{succ u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (fun (_x : MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) => (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) -> (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (MulEquiv.hasCoeToFun.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.Iso.conj.{u1, u2} C _inst_1 X Y α) f) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y X Y (CategoryTheory.Iso.inv.{u1, u2} C _inst_1 X Y α) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X X Y f (CategoryTheory.Iso.hom.{u1, u2} C _inst_1 X Y α)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (α : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) (f : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) f) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (fun (_x : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y))))) (CategoryTheory.Iso.conj.{u1, u2} C _inst_1 X Y α) f) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y X Y (CategoryTheory.Iso.inv.{u1, u2} C _inst_1 X Y α) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X X Y f (CategoryTheory.Iso.hom.{u1, u2} C _inst_1 X Y α)))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_apply CategoryTheory.Iso.conj_applyₓ'. -/
theorem conj_apply (f : End X) : α.conj f = α.inv ≫ f ≫ α.Hom :=
  rfl
#align category_theory.iso.conj_apply CategoryTheory.Iso.conj_apply

/- warning: category_theory.iso.conj_comp -> CategoryTheory.Iso.conj_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_comp CategoryTheory.Iso.conj_compₓ'. -/
@[simp]
theorem conj_comp (f g : End X) : α.conj (f ≫ g) = α.conj f ≫ α.conj g :=
  α.conj.map_mul g f
#align category_theory.iso.conj_comp CategoryTheory.Iso.conj_comp

/- warning: category_theory.iso.conj_id -> CategoryTheory.Iso.conj_id is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (α : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y), Eq.{succ u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (fun (_x : MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) => (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) -> (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (MulEquiv.hasCoeToFun.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.Iso.conj.{u1, u2} C _inst_1 X Y α) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (α : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (fun (_x : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y))))) (CategoryTheory.Iso.conj.{u1, u2} C _inst_1 X Y α) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) Y)
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_id CategoryTheory.Iso.conj_idₓ'. -/
@[simp]
theorem conj_id : α.conj (𝟙 X) = 𝟙 Y :=
  α.conj.map_one
#align category_theory.iso.conj_id CategoryTheory.Iso.conj_id

/- warning: category_theory.iso.refl_conj -> CategoryTheory.Iso.refl_conj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X), Eq.{succ u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (fun (_x : MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) => (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) -> (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (MulEquiv.hasCoeToFun.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.Iso.conj.{u1, u2} C _inst_1 X X (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 X)) f) f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} (f : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) f) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (fun (_x : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) => CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X)) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X) (CategoryTheory.End.mul.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X))))) (CategoryTheory.Iso.conj.{u1, u2} C _inst_1 X X (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 X)) f) f
Case conversion may be inaccurate. Consider using '#align category_theory.iso.refl_conj CategoryTheory.Iso.refl_conjₓ'. -/
@[simp]
theorem refl_conj (f : End X) : (Iso.refl X).conj f = f := by
  rw [conj_apply, iso.refl_inv, iso.refl_hom, category.id_comp, category.comp_id]
#align category_theory.iso.refl_conj CategoryTheory.Iso.refl_conj

/- warning: category_theory.iso.trans_conj -> CategoryTheory.Iso.trans_conj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.trans_conj CategoryTheory.Iso.trans_conjₓ'. -/
@[simp]
theorem trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.conj f) :=
  homCongr_trans α α β β f
#align category_theory.iso.trans_conj CategoryTheory.Iso.trans_conj

/- warning: category_theory.iso.symm_self_conj -> CategoryTheory.Iso.symm_self_conj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.symm_self_conj CategoryTheory.Iso.symm_self_conjₓ'. -/
@[simp]
theorem symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f := by
  rw [← trans_conj, α.self_symm_id, refl_conj]
#align category_theory.iso.symm_self_conj CategoryTheory.Iso.symm_self_conj

/- warning: category_theory.iso.self_symm_conj -> CategoryTheory.Iso.self_symm_conj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.self_symm_conj CategoryTheory.Iso.self_symm_conjₓ'. -/
@[simp]
theorem self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f :=
  α.symm.symm_self_conj f
#align category_theory.iso.self_symm_conj CategoryTheory.Iso.self_symm_conj

/- warning: category_theory.iso.conj_pow -> CategoryTheory.Iso.conj_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_pow CategoryTheory.Iso.conj_powₓ'. -/
@[simp]
theorem conj_pow (f : End X) (n : ℕ) : α.conj (f ^ n) = α.conj f ^ n :=
  α.conj.toMonoidHom.map_pow f n
#align category_theory.iso.conj_pow CategoryTheory.Iso.conj_pow

/- warning: category_theory.iso.conj_Aut -> CategoryTheory.Iso.conjAut is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C}, (CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) -> (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 X))))) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 Y))))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C}, (CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) -> (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y))))))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut CategoryTheory.Iso.conjAutₓ'. -/
/-- `conj` defines a group isomorphisms between groups of automorphisms -/
def conjAut : Aut X ≃* Aut Y :=
  (Aut.unitsEndEquivAut X).symm.trans <| (Units.mapEquiv α.conj).trans <| Aut.unitsEndEquivAut Y
#align category_theory.iso.conj_Aut CategoryTheory.Iso.conjAut

/- warning: category_theory.iso.conj_Aut_apply -> CategoryTheory.Iso.conjAut_apply is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (α : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) (f : CategoryTheory.Aut.{u1, u2} C _inst_1 X), Eq.{succ u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 X))))) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 Y)))))) (fun (_x : MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 X))))) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 Y)))))) => (CategoryTheory.Aut.{u1, u2} C _inst_1 X) -> (CategoryTheory.Aut.{u1, u2} C _inst_1 Y)) (MulEquiv.hasCoeToFun.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 X))))) (MulOneClass.toHasMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.group.{u1, u2} C _inst_1 Y)))))) (CategoryTheory.Iso.conjAut.{u1, u2} C _inst_1 X Y α) f) (CategoryTheory.Iso.trans.{u1, u2} C _inst_1 Y X Y (CategoryTheory.Iso.symm.{u1, u2} C _inst_1 X Y α) (CategoryTheory.Iso.trans.{u1, u2} C _inst_1 X X Y f α))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (α : CategoryTheory.Iso.{u1, u2} C _inst_1 X Y) (f : CategoryTheory.Aut.{u1, u2} C _inst_1 X), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.Aut.{u1, u2} C _inst_1 X) => CategoryTheory.Aut.{u1, u2} C _inst_1 Y) f) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y)))))) (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (fun (_x : CategoryTheory.Aut.{u1, u2} C _inst_1 X) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : CategoryTheory.Aut.{u1, u2} C _inst_1 X) => CategoryTheory.Aut.{u1, u2} C _inst_1 Y) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y)))))) (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y)))))) (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y)))))) (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y))))) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 X) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 X))))) (MulOneClass.toMul.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Monoid.toMulOneClass.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (DivInvMonoid.toMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (Group.toDivInvMonoid.{u1} (CategoryTheory.Aut.{u1, u2} C _inst_1 Y) (CategoryTheory.Aut.instGroupAut.{u1, u2} C _inst_1 Y))))))))) (CategoryTheory.Iso.conjAut.{u1, u2} C _inst_1 X Y α) f) (CategoryTheory.Iso.trans.{u1, u2} C _inst_1 Y X Y (CategoryTheory.Iso.symm.{u1, u2} C _inst_1 X Y α) (CategoryTheory.Iso.trans.{u1, u2} C _inst_1 X X Y f α))
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut_apply CategoryTheory.Iso.conjAut_applyₓ'. -/
theorem conjAut_apply (f : Aut X) : α.conjAut f = α.symm ≪≫ f ≪≫ α := by
  cases f <;> cases α <;> ext <;> rfl
#align category_theory.iso.conj_Aut_apply CategoryTheory.Iso.conjAut_apply

/- warning: category_theory.iso.conj_Aut_hom -> CategoryTheory.Iso.conjAut_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut_hom CategoryTheory.Iso.conjAut_homₓ'. -/
@[simp]
theorem conjAut_hom (f : Aut X) : (α.conjAut f).Hom = α.conj f.Hom :=
  rfl
#align category_theory.iso.conj_Aut_hom CategoryTheory.Iso.conjAut_hom

/- warning: category_theory.iso.trans_conj_Aut -> CategoryTheory.Iso.trans_conjAut is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.trans_conj_Aut CategoryTheory.Iso.trans_conjAutₓ'. -/
@[simp]
theorem trans_conjAut {Z : C} (β : Y ≅ Z) (f : Aut X) :
    (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f) := by
  simp only [conj_Aut_apply, iso.trans_symm, iso.trans_assoc]
#align category_theory.iso.trans_conj_Aut CategoryTheory.Iso.trans_conjAut

/- warning: category_theory.iso.conj_Aut_mul -> CategoryTheory.Iso.conjAut_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut_mul CategoryTheory.Iso.conjAut_mulₓ'. -/
@[simp]
theorem conjAut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g :=
  α.conjAut.map_mul f g
#align category_theory.iso.conj_Aut_mul CategoryTheory.Iso.conjAut_mul

/- warning: category_theory.iso.conj_Aut_trans -> CategoryTheory.Iso.conjAut_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut_trans CategoryTheory.Iso.conjAut_transₓ'. -/
@[simp]
theorem conjAut_trans (f g : Aut X) : α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g :=
  conjAut_mul α g f
#align category_theory.iso.conj_Aut_trans CategoryTheory.Iso.conjAut_trans

/- warning: category_theory.iso.conj_Aut_pow -> CategoryTheory.Iso.conjAut_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut_pow CategoryTheory.Iso.conjAut_powₓ'. -/
@[simp]
theorem conjAut_pow (f : Aut X) (n : ℕ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  α.conjAut.toMonoidHom.map_pow f n
#align category_theory.iso.conj_Aut_pow CategoryTheory.Iso.conjAut_pow

/- warning: category_theory.iso.conj_Aut_zpow -> CategoryTheory.Iso.conjAut_zpow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.iso.conj_Aut_zpow CategoryTheory.Iso.conjAut_zpowₓ'. -/
@[simp]
theorem conjAut_zpow (f : Aut X) (n : ℤ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  α.conjAut.toMonoidHom.map_zpow f n
#align category_theory.iso.conj_Aut_zpow CategoryTheory.Iso.conjAut_zpow

end Iso

namespace Functor

universe v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

/- warning: category_theory.functor.map_hom_congr -> CategoryTheory.Functor.map_homCongr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_hom_congr CategoryTheory.Functor.map_homCongrₓ'. -/
theorem map_homCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) :
    F.map (Iso.homCongr α β f) = Iso.homCongr (F.mapIso α) (F.mapIso β) (F.map f) := by simp
#align category_theory.functor.map_hom_congr CategoryTheory.Functor.map_homCongr

/- warning: category_theory.functor.map_conj -> CategoryTheory.Functor.map_conj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_conj CategoryTheory.Functor.map_conjₓ'. -/
theorem map_conj {X Y : C} (α : X ≅ Y) (f : End X) :
    F.map (α.conj f) = (F.mapIso α).conj (F.map f) :=
  map_homCongr F α α f
#align category_theory.functor.map_conj CategoryTheory.Functor.map_conj

/- warning: category_theory.functor.map_conj_Aut -> CategoryTheory.Functor.map_conjAut is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_conj_Aut CategoryTheory.Functor.map_conjAutₓ'. -/
theorem map_conjAut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) :
    F.mapIso (α.conjAut f) = (F.mapIso α).conjAut (F.mapIso f) := by
  ext <;> simp only [map_iso_hom, iso.conj_Aut_hom, F.map_conj]
#align category_theory.functor.map_conj_Aut CategoryTheory.Functor.map_conjAut

-- alternative proof: by simp only [iso.conj_Aut_apply, F.map_iso_trans, F.map_iso_symm]
end Functor

end CategoryTheory

