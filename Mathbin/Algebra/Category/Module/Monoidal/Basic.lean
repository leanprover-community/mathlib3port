/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer

! This file was ported from Lean 3 source module algebra.category.Module.monoidal.basic
! leanprover-community/mathlib commit 74403a3b2551b0970855e14ef5e8fd0d6af1bfc2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Basic
import Mathbin.LinearAlgebra.TensorProduct
import Mathbin.CategoryTheory.Linear.Yoneda
import Mathbin.CategoryTheory.Monoidal.Linear

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `linear_algebra.tensor_product`.
We just need to provide a few small missing pieces to build the
`monoidal_category` instance.
The `symmetric_category` instance is in `algebra.category.Module.monoidal.symmetric`
to reduce imports.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We construct the monoidal closed structure on `Module R` in
`algebra.category.Module.monoidal.closed`.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/


universe v w x u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `monoidal_category (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

#print ModuleCat.MonoidalCategory.tensorObj /-
/-- (implementation) tensor product of R-modules -/
def tensorObj (M N : ModuleCat R) : ModuleCat R :=
  ModuleCat.of R (M ⊗[R] N)
#align Module.monoidal_category.tensor_obj ModuleCat.MonoidalCategory.tensorObj
-/

#print ModuleCat.MonoidalCategory.tensorHom /-
/-- (implementation) tensor product of morphisms R-modules -/
def tensorHom {M N M' N' : ModuleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  TensorProduct.map f g
#align Module.monoidal_category.tensor_hom ModuleCat.MonoidalCategory.tensorHom
-/

/- warning: Module.monoidal_category.tensor_id -> ModuleCat.MonoidalCategory.tensor_id is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (N : ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)), Eq.{succ (max u2 u3)} (Quiver.Hom.{succ (max u2 u3), max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)))) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 M N) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 M N)) (ModuleCat.MonoidalCategory.tensorHom.{u1, u2, u3} R _inst_1 M M N N (CategoryTheory.CategoryStruct.id.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u2, u1} R (CommRing.toRing.{u1} R _inst_1))) M) (CategoryTheory.CategoryStruct.id.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u3, u1} R (CommRing.toRing.{u1} R _inst_1))) N)) (CategoryTheory.CategoryStruct.id.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1))) (ModuleCat.of.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1) (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) (coeSort.{max (succ u1) (succ (succ u2)), succ (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u2} (ModuleCat.hasCoeToSort.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (coeSort.{max (succ u1) (succ (succ u3)), succ (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u3} (ModuleCat.hasCoeToSort.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) N) (AddCommGroup.toAddCommMonoid.{u2} (coeSort.{max (succ u1) (succ (succ u2)), succ (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u2} (ModuleCat.hasCoeToSort.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (ModuleCat.isAddCommGroup.{u2, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (AddCommGroup.toAddCommMonoid.{u3} (coeSort.{max (succ u1) (succ (succ u3)), succ (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u3} (ModuleCat.hasCoeToSort.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) N) (ModuleCat.isAddCommGroup.{u3, u1} R (CommRing.toRing.{u1} R _inst_1) N)) (ModuleCat.isModule.{u2, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isModule.{u3, u1} R (CommRing.toRing.{u1} R _inst_1) N)) (TensorProduct.addCommGroup.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) (coeSort.{max (succ u1) (succ (succ u2)), succ (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u2} (ModuleCat.hasCoeToSort.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (coeSort.{max (succ u1) (succ (succ u3)), succ (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u3} (ModuleCat.hasCoeToSort.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) N) (ModuleCat.isAddCommGroup.{u2, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isAddCommGroup.{u3, u1} R (CommRing.toRing.{u1} R _inst_1) N) (ModuleCat.isModule.{u2, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isModule.{u3, u1} R (CommRing.toRing.{u1} R _inst_1) N)) (TensorProduct.module.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) (coeSort.{max (succ u1) (succ (succ u2)), succ (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u2} (ModuleCat.hasCoeToSort.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (coeSort.{max (succ u1) (succ (succ u3)), succ (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u3} (ModuleCat.hasCoeToSort.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) N) (AddCommGroup.toAddCommMonoid.{u2} (coeSort.{max (succ u1) (succ (succ u2)), succ (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u2} (ModuleCat.hasCoeToSort.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (ModuleCat.isAddCommGroup.{u2, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (AddCommGroup.toAddCommMonoid.{u3} (coeSort.{max (succ u1) (succ (succ u3)), succ (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u3} (ModuleCat.hasCoeToSort.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) N) (ModuleCat.isAddCommGroup.{u3, u1} R (CommRing.toRing.{u1} R _inst_1) N)) (ModuleCat.isModule.{u2, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isModule.{u3, u1} R (CommRing.toRing.{u1} R _inst_1) N))))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommRing.{u3} R] (M : ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (N : ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)), Eq.{max (succ u2) (succ u1)} (Quiver.Hom.{max (succ u2) (succ u1), max (max (succ u1) (succ u2)) u3} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 (succ u2)) (succ u1)} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 (succ u2)) (succ u1)} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u1, u3} R (CommRing.toRing.{u3} R _inst_1)))) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 M N) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 M N)) (ModuleCat.MonoidalCategory.tensorHom.{u3, u2, u1} R _inst_1 M M N N (CategoryTheory.CategoryStruct.id.{u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u2, u3} R (CommRing.toRing.{u3} R _inst_1))) M) (CategoryTheory.CategoryStruct.id.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u1, u3} R (CommRing.toRing.{u3} R _inst_1))) N)) (CategoryTheory.CategoryStruct.id.{max u2 u1, max u3 (succ (max u1 u2))} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 (succ u2)) (succ u1)} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u1, u3} R (CommRing.toRing.{u3} R _inst_1))) (ModuleCat.of.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1) (TensorProduct.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) (ModuleCat.carrier.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.carrier.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N) (AddCommGroup.toAddCommMonoid.{u2} (ModuleCat.carrier.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.isAddCommGroup.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M)) (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N) (ModuleCat.isAddCommGroup.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N)) (ModuleCat.isModule.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.isModule.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N)) (TensorProduct.addCommGroup.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) (ModuleCat.carrier.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.carrier.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N) (ModuleCat.isAddCommGroup.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.isAddCommGroup.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N) (ModuleCat.isModule.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.isModule.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N)) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u3, u2, u1} R (CommRing.toCommSemiring.{u3} R _inst_1) (ModuleCat.carrier.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.carrier.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N) (AddCommGroup.toAddCommMonoid.{u2} (ModuleCat.carrier.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.isAddCommGroup.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M)) (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N) (ModuleCat.isAddCommGroup.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N)) (ModuleCat.isModule.{u2, u3} R (CommRing.toRing.{u3} R _inst_1) M) (ModuleCat.isModule.{u1, u3} R (CommRing.toRing.{u3} R _inst_1) N))))
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.tensor_id ModuleCat.MonoidalCategory.tensor_idₓ'. -/
theorem tensor_id (M N : ModuleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (ModuleCat.of R (M ⊗ N)) := by
  ext1; rfl
#align Module.monoidal_category.tensor_id ModuleCat.MonoidalCategory.tensor_id

/- warning: Module.monoidal_category.tensor_comp -> ModuleCat.MonoidalCategory.tensor_comp is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {X₁ : ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)} {Y₁ : ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)} {Z₁ : ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)} {X₂ : ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)} {Y₂ : ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)} {Z₂ : ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)} (f₁ : Quiver.Hom.{succ u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)))) X₁ Y₁) (f₂ : Quiver.Hom.{succ u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)))) X₂ Y₂) (g₁ : Quiver.Hom.{succ u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)))) Y₁ Z₁) (g₂ : Quiver.Hom.{succ u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)))) Y₂ Z₂), Eq.{succ (max u2 u3)} (Quiver.Hom.{succ (max u2 u3), max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)))) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 X₁ X₂) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 Z₁ Z₂)) (ModuleCat.MonoidalCategory.tensorHom.{u1, u2, u3} R _inst_1 X₁ Z₁ X₂ Z₂ (CategoryTheory.CategoryStruct.comp.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 (succ u2)} (ModuleCat.{u2, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u2, u1} R (CommRing.toRing.{u1} R _inst_1))) X₁ Y₁ Z₁ f₁ g₁) (CategoryTheory.CategoryStruct.comp.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u3, max u1 (succ u3)} (ModuleCat.{u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u3, u1} R (CommRing.toRing.{u1} R _inst_1))) X₂ Y₂ Z₂ f₂ g₂)) (CategoryTheory.CategoryStruct.comp.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 (succ (max u2 u3))} (ModuleCat.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u3, u1} R (CommRing.toRing.{u1} R _inst_1))) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 X₁ X₂) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 Y₁ Y₂) (ModuleCat.MonoidalCategory.tensorObj.{u1, u2, u3} R _inst_1 Z₁ Z₂) (ModuleCat.MonoidalCategory.tensorHom.{u1, u2, u3} R _inst_1 X₁ Y₁ X₂ Y₂ f₁ f₂) (ModuleCat.MonoidalCategory.tensorHom.{u1, u2, u3} R _inst_1 Y₁ Z₁ Y₂ Z₂ g₁ g₂))
but is expected to have type
  forall {R : Type.{u3}} [_inst_1 : CommRing.{u3} R] {X₁ : ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)} {Y₁ : ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)} {Z₁ : ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)} {X₂ : ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)} {Y₂ : ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)} {Z₂ : ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)} (f₁ : Quiver.Hom.{succ u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)))) X₁ Y₁) (f₂ : Quiver.Hom.{succ u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)))) X₂ Y₂) (g₁ : Quiver.Hom.{succ u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max u3 (succ u2)} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)))) Y₁ Z₁) (g₂ : Quiver.Hom.{succ u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)))) Y₂ Z₂), Eq.{max (succ u2) (succ u1)} (Quiver.Hom.{max (succ u2) (succ u1), max (max (succ u1) (succ u2)) u3} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 (succ u2)) (succ u1)} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 (succ u2)) (succ u1)} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{max u2 u1, u3} R (CommRing.toRing.{u3} R _inst_1)))) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 X₁ X₂) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 Z₁ Z₂)) (ModuleCat.MonoidalCategory.tensorHom.{u3, u2, u1} R _inst_1 X₁ Z₁ X₂ Z₂ (CategoryTheory.CategoryStruct.comp.{u2, max (succ u2) u3} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u2, max (succ u2) u3} (ModuleCat.{u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u2, u3} R (CommRing.toRing.{u3} R _inst_1))) X₁ Y₁ Z₁ f₁ g₁) (CategoryTheory.CategoryStruct.comp.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{u1, max u3 (succ u1)} (ModuleCat.{u1, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{u1, u3} R (CommRing.toRing.{u3} R _inst_1))) X₂ Y₂ Z₂ f₂ g₂)) (CategoryTheory.CategoryStruct.comp.{max u1 u2, max (max (succ u1) (succ u2)) u3} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max (max (succ u1) (succ u2)) u3} (ModuleCat.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1)) (ModuleCat.moduleCategory.{max u1 u2, u3} R (CommRing.toRing.{u3} R _inst_1))) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 X₁ X₂) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 Y₁ Y₂) (ModuleCat.MonoidalCategory.tensorObj.{u3, u2, u1} R _inst_1 Z₁ Z₂) (ModuleCat.MonoidalCategory.tensorHom.{u3, u2, u1} R _inst_1 X₁ Y₁ X₂ Y₂ f₁ f₂) (ModuleCat.MonoidalCategory.tensorHom.{u3, u2, u1} R _inst_1 Y₁ Z₁ Y₂ Z₂ g₁ g₂))
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.tensor_comp ModuleCat.MonoidalCategory.tensor_compₓ'. -/
theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by ext1;
  rfl
#align Module.monoidal_category.tensor_comp ModuleCat.MonoidalCategory.tensor_comp

#print ModuleCat.MonoidalCategory.associator /-
/-- (implementation) the associator for R-modules -/
def associator (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (K : ModuleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIso
#align Module.monoidal_category.associator ModuleCat.MonoidalCategory.associator
-/

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/


open TensorProduct (and_assoc map)

private theorem associator_naturality_aux {X₁ X₂ X₃ : Type _} [AddCommMonoid X₁] [AddCommMonoid X₂]
    [AddCommMonoid X₃] [Module R X₁] [Module R X₂] [Module R X₃] {Y₁ Y₂ Y₃ : Type _}
    [AddCommMonoid Y₁] [AddCommMonoid Y₂] [AddCommMonoid Y₃] [Module R Y₁] [Module R Y₂]
    [Module R Y₃] (f₁ : X₁ →ₗ[R] Y₁) (f₂ : X₂ →ₗ[R] Y₂) (f₃ : X₃ →ₗ[R] Y₃) :
    ↑(assoc R Y₁ Y₂ Y₃) ∘ₗ map (map f₁ f₂) f₃ = map f₁ (map f₂ f₃) ∘ₗ ↑(assoc R X₁ X₂ X₃) :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

variable (R)

private theorem pentagon_aux (W X Y Z : Type _) [AddCommMonoid W] [AddCommMonoid X]
    [AddCommMonoid Y] [AddCommMonoid Z] [Module R W] [Module R X] [Module R Y] [Module R Z] :
    ((map (1 : W →ₗ[R] W) (assoc R X Y Z).toLinearMap).comp
            (assoc R W (X ⊗[R] Y) Z).toLinearMap).comp
        (map ↑(assoc R W X Y) (1 : Z →ₗ[R] Z)) =
      (assoc R W X (Y ⊗[R] Z)).toLinearMap.comp (assoc R (W ⊗[R] X) Y Z).toLinearMap :=
  by
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

end

/- warning: Module.monoidal_category.associator_naturality -> ModuleCat.MonoidalCategory.associator_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.associator_naturality ModuleCat.MonoidalCategory.associator_naturalityₓ'. -/
theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).Hom =
      (associator X₁ X₂ X₃).Hom ≫ tensorHom f₁ (tensorHom f₂ f₃) :=
  by convert associator_naturality_aux f₁ f₂ f₃ using 1
#align Module.monoidal_category.associator_naturality ModuleCat.MonoidalCategory.associator_naturality

/- warning: Module.monoidal_category.pentagon -> ModuleCat.MonoidalCategory.pentagon is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.pentagon ModuleCat.MonoidalCategory.pentagonₓ'. -/
theorem pentagon (W X Y Z : ModuleCat R) :
    tensorHom (associator W X Y).Hom (𝟙 Z) ≫
        (associator W (tensorObj X Y) Z).Hom ≫ tensorHom (𝟙 W) (associator X Y Z).Hom =
      (associator (tensorObj W X) Y Z).Hom ≫ (associator W X (tensorObj Y Z)).Hom :=
  by convert pentagon_aux R W X Y Z using 1
#align Module.monoidal_category.pentagon ModuleCat.MonoidalCategory.pentagon

/- warning: Module.monoidal_category.left_unitor -> ModuleCat.MonoidalCategory.leftUnitor is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)), CategoryTheory.Iso.{u1, succ u1} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.of.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) (TensorProduct.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (TensorProduct.addCommGroup.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (TensorProduct.module.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M))) M
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)), CategoryTheory.Iso.{u1, succ u1} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.of.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) (TensorProduct.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (TensorProduct.addCommGroup.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Ring.toAddCommGroup.{u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) R (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M))) M
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.left_unitor ModuleCat.MonoidalCategory.leftUnitorₓ'. -/
/-- (implementation) the left unitor for R-modules -/
def leftUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (R ⊗[R] M) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.lid R M) : of R (R ⊗ M) ≅ of R M).trans (ofSelfIso M)
#align Module.monoidal_category.left_unitor ModuleCat.MonoidalCategory.leftUnitor

#print ModuleCat.MonoidalCategory.leftUnitor_naturality /-
theorem leftUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (ModuleCat.of R R)) f ≫ (leftUnitor N).Hom = (leftUnitor M).Hom ≫ f :=
  by
  ext (x y); dsimp
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  rw [LinearMap.map_smul]
  rfl
#align Module.monoidal_category.left_unitor_naturality ModuleCat.MonoidalCategory.leftUnitor_naturality
-/

/- warning: Module.monoidal_category.right_unitor -> ModuleCat.MonoidalCategory.rightUnitor is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)), CategoryTheory.Iso.{u1, succ u1} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.of.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) (TensorProduct.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) R (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (TensorProduct.addCommGroup.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) R (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (TensorProduct.module.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) R (AddCommGroup.toAddCommMonoid.{u1} (coeSort.{succ (succ u1), succ (succ u1)} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) Type.{u1} (ModuleCat.hasCoeToSort.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (AddCommGroup.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) M
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)), CategoryTheory.Iso.{u1, succ u1} (ModuleCat.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.moduleCategory.{u1, u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.of.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) (TensorProduct.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) R (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (TensorProduct.addCommGroup.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) R (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Ring.toAddCommGroup.{u1} R (CommRing.toRing.{u1} R _inst_1)) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u1, u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) R (AddCommGroup.toAddCommMonoid.{u1} (ModuleCat.carrier.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (ModuleCat.isAddCommGroup.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (ModuleCat.isModule.{u1, u1} R (CommRing.toRing.{u1} R _inst_1) M) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) M
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.right_unitor ModuleCat.MonoidalCategory.rightUnitorₓ'. -/
/-- (implementation) the right unitor for R-modules -/
def rightUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (M ⊗[R] R) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.rid R M) : of R (M ⊗ R) ≅ of R M).trans (ofSelfIso M)
#align Module.monoidal_category.right_unitor ModuleCat.MonoidalCategory.rightUnitor

#print ModuleCat.MonoidalCategory.rightUnitor_naturality /-
theorem rightUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (ModuleCat.of R R)) ≫ (rightUnitor N).Hom = (rightUnitor M).Hom ≫ f :=
  by
  ext (x y); dsimp
  erw [TensorProduct.rid_tmul, TensorProduct.rid_tmul]
  rw [LinearMap.map_smul]
  rfl
#align Module.monoidal_category.right_unitor_naturality ModuleCat.MonoidalCategory.rightUnitor_naturality
-/

#print ModuleCat.MonoidalCategory.triangle /-
theorem triangle (M N : ModuleCat.{u} R) :
    (associator M (ModuleCat.of R R) N).Hom ≫ tensorHom (𝟙 M) (leftUnitor N).Hom =
      tensorHom (rightUnitor M).Hom (𝟙 N) :=
  by
  apply TensorProduct.ext_threefold
  intro x y z
  change R at y
  dsimp [tensor_hom, associator]
  erw [TensorProduct.lid_tmul, TensorProduct.rid_tmul]
  exact (TensorProduct.smul_tmul _ _ _).symm
#align Module.monoidal_category.triangle ModuleCat.MonoidalCategory.triangle
-/

end MonoidalCategory

open MonoidalCategory

#print ModuleCat.monoidalCategory /-
instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R)
    where
  -- data
  tensorObj := tensorObj
  tensorHom := @tensorHom _ _
  tensorUnit := ModuleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  -- properties
  tensor_id' M N := tensor_id M N
  tensor_comp' M N K M' N' K' f g h := tensor_comp f g h
  associator_naturality' M N K M' N' K' f g h := associator_naturality f g h
  leftUnitor_naturality' M N f := leftUnitor_naturality f
  rightUnitor_naturality' M N f := rightUnitor_naturality f
  pentagon M N K L := pentagon M N K L
  triangle M N := triangle M N
#align Module.monoidal_category ModuleCat.monoidalCategory
-/

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  (by infer_instance : CommRing R)

namespace MonoidalCategory

/- warning: Module.monoidal_category.hom_apply -> ModuleCat.MonoidalCategory.hom_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.hom_apply ModuleCat.MonoidalCategory.hom_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem hom_apply {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl
#align Module.monoidal_category.hom_apply ModuleCat.MonoidalCategory.hom_apply

/- warning: Module.monoidal_category.left_unitor_hom_apply -> ModuleCat.MonoidalCategory.leftUnitor_hom_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.left_unitor_hom_apply ModuleCat.MonoidalCategory.leftUnitor_hom_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).Hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r
#align Module.monoidal_category.left_unitor_hom_apply ModuleCat.MonoidalCategory.leftUnitor_hom_apply

/- warning: Module.monoidal_category.left_unitor_inv_apply -> ModuleCat.MonoidalCategory.leftUnitor_inv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.left_unitor_inv_apply ModuleCat.MonoidalCategory.leftUnitor_inv_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m
#align Module.monoidal_category.left_unitor_inv_apply ModuleCat.MonoidalCategory.leftUnitor_inv_apply

/- warning: Module.monoidal_category.right_unitor_hom_apply -> ModuleCat.MonoidalCategory.rightUnitor_hom_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.right_unitor_hom_apply ModuleCat.MonoidalCategory.rightUnitor_hom_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).Hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r
#align Module.monoidal_category.right_unitor_hom_apply ModuleCat.MonoidalCategory.rightUnitor_hom_apply

/- warning: Module.monoidal_category.right_unitor_inv_apply -> ModuleCat.MonoidalCategory.rightUnitor_inv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.right_unitor_inv_apply ModuleCat.MonoidalCategory.rightUnitor_inv_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m
#align Module.monoidal_category.right_unitor_inv_apply ModuleCat.MonoidalCategory.rightUnitor_inv_apply

/- warning: Module.monoidal_category.associator_hom_apply -> ModuleCat.MonoidalCategory.associator_hom_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.associator_hom_apply ModuleCat.MonoidalCategory.associator_hom_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).Hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl
#align Module.monoidal_category.associator_hom_apply ModuleCat.MonoidalCategory.associator_hom_apply

/- warning: Module.monoidal_category.associator_inv_apply -> ModuleCat.MonoidalCategory.associator_inv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align Module.monoidal_category.associator_inv_apply ModuleCat.MonoidalCategory.associator_inv_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl
#align Module.monoidal_category.associator_inv_apply ModuleCat.MonoidalCategory.associator_inv_apply

end MonoidalCategory

open Opposite

instance : MonoidalPreadditive (ModuleCat.{u} R) := by
  refine' ⟨_, _, _, _⟩ <;> dsimp only [autoParam] <;> intros <;>
      refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _) <;>
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, monoidal_category.hom_apply,
      LinearMap.zero_apply, TensorProduct.tmul_zero, TensorProduct.zero_tmul, LinearMap.add_apply,
      TensorProduct.tmul_add, TensorProduct.add_tmul]

instance : MonoidalLinear R (ModuleCat.{u} R) := by
  refine' ⟨_, _⟩ <;> dsimp only [autoParam] <;> intros <;>
      refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _) <;>
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, monoidal_category.hom_apply,
      LinearMap.smul_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul]

end ModuleCat

