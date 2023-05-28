/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.yoneda
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Hom
import Mathbin.CategoryTheory.Functor.Currying
import Mathbin.CategoryTheory.Products.Basic

/-!
# The Yoneda embedding

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `fully_faithful`.

Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/


namespace CategoryTheory

open Opposite

universe v₁ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C]

#print CategoryTheory.yoneda /-
/-- The Yoneda embedding, as a functor from `C` into presheaves on `C`.

See <https://stacks.math.columbia.edu/tag/001O>.
-/
@[simps]
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁
    where
  obj X :=
    { obj := fun Y => unop Y ⟶ X
      map := fun Y Y' f g => f.unop ≫ g
      map_comp' := fun _ _ _ f g => by ext; dsimp; erw [category.assoc]
      map_id' := fun Y => by ext; dsimp; erw [category.id_comp] }
  map X X' f := { app := fun Y g => g ≫ f }
#align category_theory.yoneda CategoryTheory.yoneda
-/

#print CategoryTheory.coyoneda /-
/-- The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
@[simps]
def coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁
    where
  obj X :=
    { obj := fun Y => unop X ⟶ Y
      map := fun Y Y' f g => g ≫ f }
  map X X' f := { app := fun Y g => f.unop ≫ g }
#align category_theory.coyoneda CategoryTheory.coyoneda
-/

namespace Yoneda

/- warning: category_theory.yoneda.obj_map_id -> CategoryTheory.Yoneda.obj_map_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda.obj_map_id CategoryTheory.Yoneda.obj_map_idₓ'. -/
theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) :
    (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) :=
  by
  dsimp
  simp
#align category_theory.yoneda.obj_map_id CategoryTheory.Yoneda.obj_map_id

/- warning: category_theory.yoneda.naturality -> CategoryTheory.Yoneda.naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda.naturality CategoryTheory.Yoneda.naturalityₓ'. -/
@[simp]
theorem naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y) {Z Z' : C} (f : Z ⟶ Z')
    (h : Z' ⟶ X) : f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
  (FunctorToTypes.naturality _ _ α f.op h).symm
#align category_theory.yoneda.naturality CategoryTheory.Yoneda.naturality

#print CategoryTheory.Yoneda.yonedaFull /-
/-- The Yoneda embedding is full.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
instance yonedaFull : Full (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁) where preimage X Y f := f.app (op X) (𝟙 X)
#align category_theory.yoneda.yoneda_full CategoryTheory.Yoneda.yonedaFull
-/

#print CategoryTheory.Yoneda.yoneda_faithful /-
/-- The Yoneda embedding is faithful.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
instance yoneda_faithful : Faithful (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁)
    where map_injective' X Y f g p := by
    convert congr_fun (congr_app p (op X)) (𝟙 X) <;> dsimp <;> simp
#align category_theory.yoneda.yoneda_faithful CategoryTheory.Yoneda.yoneda_faithful
-/

#print CategoryTheory.Yoneda.ext /-
/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y)) (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
    (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  yoneda.preimageIso
    (NatIso.ofComponents
      (fun Z =>
        { Hom := p
          inv := q })
      (by tidy))
#align category_theory.yoneda.ext CategoryTheory.Yoneda.ext
-/

/- warning: category_theory.yoneda.is_iso -> CategoryTheory.Yoneda.isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_2 : CategoryTheory.IsIso.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) Y) (CategoryTheory.Functor.map.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X Y f)], CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y) [_inst_2 : CategoryTheory.IsIso.{max u1 u2, max (succ u1) u2} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) Y) (Prefunctor.map.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X Y f)], CategoryTheory.IsIso.{u1, u2} C _inst_1 X Y f
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda.is_iso CategoryTheory.Yoneda.isIsoₓ'. -/
/-- If `yoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful yoneda f
#align category_theory.yoneda.is_iso CategoryTheory.Yoneda.isIso

end Yoneda

namespace Coyoneda

/- warning: category_theory.coyoneda.naturality -> CategoryTheory.Coyoneda.naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.naturality CategoryTheory.Coyoneda.naturalityₓ'. -/
@[simp]
theorem naturality {X Y : Cᵒᵖ} (α : coyoneda.obj X ⟶ coyoneda.obj Y) {Z Z' : C} (f : Z' ⟶ Z)
    (h : unop X ⟶ Z') : α.app Z' h ≫ f = α.app Z (h ≫ f) :=
  (FunctorToTypes.naturality _ _ α f h).symm
#align category_theory.coyoneda.naturality CategoryTheory.Coyoneda.naturality

#print CategoryTheory.Coyoneda.coyonedaFull /-
instance coyonedaFull : Full (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁)
    where preimage X Y f := (f.app _ (𝟙 X.unop)).op
#align category_theory.coyoneda.coyoneda_full CategoryTheory.Coyoneda.coyonedaFull
-/

#print CategoryTheory.Coyoneda.coyoneda_faithful /-
instance coyoneda_faithful : Faithful (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁)
    where map_injective' X Y f g p :=
    by
    have t := congr_fun (congr_app p X.unop) (𝟙 _)
    simpa using congr_arg Quiver.Hom.op t
#align category_theory.coyoneda.coyoneda_faithful CategoryTheory.Coyoneda.coyoneda_faithful
-/

/- warning: category_theory.coyoneda.is_iso -> CategoryTheory.Coyoneda.isIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} (f : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) X) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) Y) (CategoryTheory.Functor.map.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) X Y f)], CategoryTheory.IsIso.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) X Y f
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : Opposite.{succ u2} C} {Y : Opposite.{succ u2} C} (f : Quiver.Hom.{succ u1, u2} (Opposite.{succ u2} C) (Quiver.opposite.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1))) X Y) [_inst_2 : CategoryTheory.IsIso.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) X) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) Y) (Prefunctor.map.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) X Y f)], CategoryTheory.IsIso.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) X Y f
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.is_iso CategoryTheory.Coyoneda.isIsoₓ'. -/
/-- If `coyoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful coyoneda f
#align category_theory.coyoneda.is_iso CategoryTheory.Coyoneda.isIso

/- warning: category_theory.coyoneda.punit_iso -> CategoryTheory.Coyoneda.punitIso is a dubious translation:
lean 3 declaration is
  CategoryTheory.Iso.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, succ u1, succ u1, succ u1} (Opposite.{succ (succ u1)} Type.{u1}) (CategoryTheory.Category.opposite.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) (Opposite.op.{succ (succ u1)} Type.{u1} PUnit.{succ u1})) (CategoryTheory.Functor.id.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})
but is expected to have type
  CategoryTheory.Iso.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, succ (succ u1), succ u1, succ u1} (Opposite.{succ (succ u1)} Type.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (Opposite.{succ (succ u1)} Type.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (Opposite.{succ (succ u1)} Type.{u1}) (CategoryTheory.Category.opposite.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, succ u1, succ u1, succ u1} (Opposite.{succ (succ u1)} Type.{u1}) (CategoryTheory.Category.opposite.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, succ u1, succ u1} Type.{u1} CategoryTheory.types.{u1} Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (Opposite.op.{succ (succ u1)} Type.{u1} PUnit.{succ u1})) (CategoryTheory.Functor.id.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.punit_iso CategoryTheory.Coyoneda.punitIsoₓ'. -/
/-- The identity functor on `Type` is isomorphic to the coyoneda functor coming from `punit`. -/
def punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  NatIso.ofComponents
    (fun X =>
      { Hom := fun f => f ⟨⟩
        inv := fun x _ => x })
    (by tidy)
#align category_theory.coyoneda.punit_iso CategoryTheory.Coyoneda.punitIso

/- warning: category_theory.coyoneda.obj_op_op -> CategoryTheory.Coyoneda.objOpOp is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), CategoryTheory.Iso.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} (Opposite.{succ u2} C)) (CategoryTheory.Category.opposite.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} (Opposite.{succ u2} C) (Opposite.op.{succ u2} C X))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C), CategoryTheory.Iso.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} (Opposite.{succ u2} C)) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} (Opposite.{succ u2} C)) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} (Opposite.{succ u2} C)) (CategoryTheory.Category.opposite.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} (Opposite.{succ u2} C)) (CategoryTheory.Category.opposite.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (Opposite.op.{succ u2} (Opposite.{succ u2} C) (Opposite.op.{succ u2} C X))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X)
Case conversion may be inaccurate. Consider using '#align category_theory.coyoneda.obj_op_op CategoryTheory.Coyoneda.objOpOpₓ'. -/
/-- Taking the `unop` of morphisms is a natural isomorphism. -/
@[simps]
def objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X :=
  NatIso.ofComponents (fun Y => (opEquiv _ _).toIso) fun X Y f => rfl
#align category_theory.coyoneda.obj_op_op CategoryTheory.Coyoneda.objOpOp

end Coyoneda

namespace Functor

#print CategoryTheory.Functor.Representable /-
/-- A functor `F : Cᵒᵖ ⥤ Type v₁` is representable if there is object `X` so `F ≅ yoneda.obj X`.

See <https://stacks.math.columbia.edu/tag/001Q>.
-/
class Representable (F : Cᵒᵖ ⥤ Type v₁) : Prop where
  has_representation : ∃ (X : _)(f : yoneda.obj X ⟶ F), IsIso f
#align category_theory.functor.representable CategoryTheory.Functor.Representable
-/

instance {X : C} : Representable (yoneda.obj X) where has_representation := ⟨X, 𝟙 _, inferInstance⟩

#print CategoryTheory.Functor.Corepresentable /-
/-- A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.

See <https://stacks.math.columbia.edu/tag/001Q>.
-/
class Corepresentable (F : C ⥤ Type v₁) : Prop where
  has_corepresentation : ∃ (X : _)(f : coyoneda.obj X ⟶ F), IsIso f
#align category_theory.functor.corepresentable CategoryTheory.Functor.Corepresentable
-/

instance {X : Cᵒᵖ} : Corepresentable (coyoneda.obj X)
    where has_corepresentation := ⟨X, 𝟙 _, inferInstance⟩

-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso
section Representable

variable (F : Cᵒᵖ ⥤ Type v₁)

variable [F.Representable]

#print CategoryTheory.Functor.reprX /-
/-- The representing object for the representable functor `F`. -/
noncomputable def reprX : C :=
  (Representable.has_representation : ∃ (X : _)(f : _ ⟶ F), _).some
#align category_theory.functor.repr_X CategoryTheory.Functor.reprX
-/

/- warning: category_theory.functor.repr_f -> CategoryTheory.Functor.reprF is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], Quiver.Hom.{max (succ u2) (succ u1), max (succ u1) u2} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F
Case conversion may be inaccurate. Consider using '#align category_theory.functor.repr_f CategoryTheory.Functor.reprFₓ'. -/
/-- The (forward direction of the) isomorphism witnessing `F` is representable. -/
noncomputable def reprF : yoneda.obj F.reprX ⟶ F :=
  Representable.has_representation.choose_spec.some
#align category_theory.functor.repr_f CategoryTheory.Functor.reprF

/- warning: category_theory.functor.repr_x -> CategoryTheory.Functor.reprx is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F (Opposite.op.{succ u2} C (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], Prefunctor.obj.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) (Opposite.op.{succ u2} C (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.repr_x CategoryTheory.Functor.reprxₓ'. -/
/-- The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def reprx : F.obj (op F.reprX) :=
  F.reprF.app (op F.reprX) (𝟙 F.reprX)
#align category_theory.functor.repr_x CategoryTheory.Functor.reprx

instance : IsIso F.reprF :=
  Representable.has_representation.choose_spec.choose_spec

/- warning: category_theory.functor.repr_w -> CategoryTheory.Functor.reprW is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], CategoryTheory.Iso.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], CategoryTheory.Iso.{max u2 u1, max (succ u1) u2} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F
Case conversion may be inaccurate. Consider using '#align category_theory.functor.repr_w CategoryTheory.Functor.reprWₓ'. -/
/-- An isomorphism between `F` and a functor of the form `C(-, F.repr_X)`.  Note the components
`F.repr_w.app X` definitionally have type `(X.unop ⟶ F.repr_X) ≅ F.obj X`.
-/
noncomputable def reprW : yoneda.obj F.reprX ≅ F :=
  asIso F.reprF
#align category_theory.functor.repr_w CategoryTheory.Functor.reprW

/- warning: category_theory.functor.repr_w_hom -> CategoryTheory.Functor.reprW_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], Eq.{succ (max u2 u1)} (Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F) (CategoryTheory.Iso.hom.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F (CategoryTheory.Functor.reprW.{u1, u2} C _inst_1 F _inst_2)) (CategoryTheory.Functor.reprF.{u1, u2} C _inst_1 F _inst_2)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F], Eq.{max (succ u2) (succ u1)} (Quiver.Hom.{succ (max u2 u1), max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F) (CategoryTheory.Iso.hom.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F (CategoryTheory.Functor.reprW.{u1, u2} C _inst_1 F _inst_2)) (CategoryTheory.Functor.reprF.{u1, u2} C _inst_1 F _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.repr_w_hom CategoryTheory.Functor.reprW_homₓ'. -/
@[simp]
theorem reprW_hom : F.reprW.Hom = F.reprF :=
  rfl
#align category_theory.functor.repr_w_hom CategoryTheory.Functor.reprW_hom

/- warning: category_theory.functor.repr_w_app_hom -> CategoryTheory.Functor.reprW_app_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F] (X : Opposite.{succ u2} C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Opposite.unop.{succ u2} C X) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)), Eq.{succ u1} (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F X) (CategoryTheory.Iso.hom.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) X) (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F X) (CategoryTheory.Iso.app.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F (CategoryTheory.Functor.reprW.{u1, u2} C _inst_1 F _inst_2) X) f) (CategoryTheory.Functor.map.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F (Opposite.op.{succ u2} C (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) X (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Opposite.unop.{succ u2} C X) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2) f) (CategoryTheory.Functor.reprx.{u1, u2} C _inst_1 F _inst_2))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Representable.{u1, u2} C _inst_1 F] (X : Opposite.{succ u2} C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Opposite.unop.{succ u2} C X) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)), Eq.{succ u1} (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) X) (CategoryTheory.Iso.hom.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2))) X) (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) X) (CategoryTheory.Iso.app.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) F (CategoryTheory.Functor.reprW.{u1, u2} C _inst_1 F _inst_2) X) f) (Prefunctor.map.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) (Opposite.op.{succ u2} C (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2)) (Opposite.op.{succ u2} C (Opposite.unop.{succ u2} C X)) (Quiver.Hom.op.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Opposite.unop.{succ u2} C X) (CategoryTheory.Functor.reprX.{u1, u2} C _inst_1 F _inst_2) f) (CategoryTheory.Functor.reprx.{u1, u2} C _inst_1 F _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.repr_w_app_hom CategoryTheory.Functor.reprW_app_homₓ'. -/
theorem reprW_app_hom (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    (F.reprW.app X).Hom f = F.map f.op F.reprx :=
  by
  change F.repr_f.app X f = (F.repr_f.app (op F.repr_X) ≫ F.map f.op) (𝟙 F.repr_X)
  rw [← F.repr_f.naturality]
  dsimp
  simp
#align category_theory.functor.repr_w_app_hom CategoryTheory.Functor.reprW_app_hom

end Representable

section Corepresentable

variable (F : C ⥤ Type v₁)

variable [F.Corepresentable]

#print CategoryTheory.Functor.coreprX /-
/-- The representing object for the corepresentable functor `F`. -/
noncomputable def coreprX : C :=
  (Corepresentable.has_corepresentation : ∃ (X : _)(f : _ ⟶ F), _).some.unop
#align category_theory.functor.corepr_X CategoryTheory.Functor.coreprX
-/

/- warning: category_theory.functor.corepr_f -> CategoryTheory.Functor.coreprF is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F], Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) F
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F], Quiver.Hom.{max (succ u2) (succ u1), max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) F
Case conversion may be inaccurate. Consider using '#align category_theory.functor.corepr_f CategoryTheory.Functor.coreprFₓ'. -/
/-- The (forward direction of the) isomorphism witnessing `F` is corepresentable. -/
noncomputable def coreprF : coyoneda.obj (op F.coreprX) ⟶ F :=
  Corepresentable.has_corepresentation.choose_spec.some
#align category_theory.functor.corepr_f CategoryTheory.Functor.coreprF

/- warning: category_theory.functor.corepr_x -> CategoryTheory.Functor.coreprx is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F], CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F], Prefunctor.obj.{succ u1, succ u1, u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.corepr_x CategoryTheory.Functor.coreprxₓ'. -/
/-- The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def coreprx : F.obj F.coreprX :=
  F.coreprF.app F.coreprX (𝟙 F.coreprX)
#align category_theory.functor.corepr_x CategoryTheory.Functor.coreprx

instance : IsIso F.coreprF :=
  Corepresentable.has_corepresentation.choose_spec.choose_spec

/- warning: category_theory.functor.corepr_w -> CategoryTheory.Functor.coreprW is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F], CategoryTheory.Iso.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) F
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F], CategoryTheory.Iso.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) F
Case conversion may be inaccurate. Consider using '#align category_theory.functor.corepr_w CategoryTheory.Functor.coreprWₓ'. -/
/-- An isomorphism between `F` and a functor of the form `C(F.corepr X, -)`. Note the components
`F.corepr_w.app X` definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def coreprW : coyoneda.obj (op F.coreprX) ≅ F :=
  asIso F.coreprF
#align category_theory.functor.corepr_w CategoryTheory.Functor.coreprW

/- warning: category_theory.functor.corepr_w_app_hom -> CategoryTheory.Functor.coreprW_app_hom is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F] (X : C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2) X), Eq.{succ u1} (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F X) (CategoryTheory.Iso.hom.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) X) (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F X) (CategoryTheory.Iso.app.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) F (CategoryTheory.Functor.coreprW.{u1, u2} C _inst_1 F _inst_2) X) f) (CategoryTheory.Functor.map.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2) X f (CategoryTheory.Functor.coreprx.{u1, u2} C _inst_1 F _inst_2))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) [_inst_2 : CategoryTheory.Functor.Corepresentable.{u1, u2} C _inst_1 F] (X : C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2) X), Eq.{succ u1} (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) X) (CategoryTheory.Iso.hom.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2)))) X) (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) X) (CategoryTheory.Iso.app.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} (Prefunctor.obj.{succ u1, max (succ u2) (succ u1), u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) (CategoryTheory.Functor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.coyoneda.{u1, u2} C _inst_1)) (Opposite.op.{succ u2} C (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2))) F (CategoryTheory.Functor.coreprW.{u1, u2} C _inst_1 F _inst_2) X) f) (Prefunctor.map.{succ u1, succ u1, u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) (CategoryTheory.Functor.coreprX.{u1, u2} C _inst_1 F _inst_2) X f (CategoryTheory.Functor.coreprx.{u1, u2} C _inst_1 F _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.functor.corepr_w_app_hom CategoryTheory.Functor.coreprW_app_homₓ'. -/
theorem coreprW_app_hom (X : C) (f : F.coreprX ⟶ X) : (F.coreprW.app X).Hom f = F.map f F.coreprx :=
  by
  change F.corepr_f.app X f = (F.corepr_f.app F.corepr_X ≫ F.map f) (𝟙 F.corepr_X)
  rw [← F.corepr_f.naturality]
  dsimp
  simp
#align category_theory.functor.corepr_w_app_hom CategoryTheory.Functor.coreprW_app_hom

end Corepresentable

end Functor

#print CategoryTheory.representable_of_nat_iso /-
theorem representable_of_nat_iso (F : Cᵒᵖ ⥤ Type v₁) {G} (i : F ≅ G) [F.Representable] :
    G.Representable :=
  { has_representation := ⟨F.reprX, F.reprF ≫ i.Hom, inferInstance⟩ }
#align category_theory.representable_of_nat_iso CategoryTheory.representable_of_nat_iso
-/

#print CategoryTheory.corepresentable_of_nat_iso /-
theorem corepresentable_of_nat_iso (F : C ⥤ Type v₁) {G} (i : F ≅ G) [F.Corepresentable] :
    G.Corepresentable :=
  { has_corepresentation := ⟨op F.coreprX, F.coreprF ≫ i.Hom, inferInstance⟩ }
#align category_theory.corepresentable_of_nat_iso CategoryTheory.corepresentable_of_nat_iso
-/

instance : Functor.Corepresentable (𝟭 (Type v₁)) :=
  corepresentable_of_nat_iso (coyoneda.obj (op PUnit)) Coyoneda.punitIso

open Opposite

variable (C)

#print CategoryTheory.prodCategoryInstance1 /-
-- We need to help typeclass inference with some awkward universe levels here.
instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ
#align category_theory.prod_category_instance_1 CategoryTheory.prodCategoryInstance1
-/

#print CategoryTheory.prodCategoryInstance2 /-
instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)
#align category_theory.prod_category_instance_2 CategoryTheory.prodCategoryInstance2
-/

open Yoneda

#print CategoryTheory.yonedaEvaluation /-
/-- The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor.{u₁}
#align category_theory.yoneda_evaluation CategoryTheory.yonedaEvaluation
-/

/- warning: category_theory.yoneda_evaluation_map_down -> CategoryTheory.yonedaEvaluation_map_down is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_evaluation_map_down CategoryTheory.yonedaEvaluation_map_downₓ'. -/
@[simp]
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl
#align category_theory.yoneda_evaluation_map_down CategoryTheory.yonedaEvaluation_map_down

#print CategoryTheory.yonedaPairing /-
/-- The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)
#align category_theory.yoneda_pairing CategoryTheory.yonedaPairing
-/

/- warning: category_theory.yoneda_pairing_map -> CategoryTheory.yonedaPairing_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_pairing_map CategoryTheory.yonedaPairing_mapₓ'. -/
@[simp]
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yonedaPairing C).obj P) :
    (yonedaPairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl
#align category_theory.yoneda_pairing_map CategoryTheory.yonedaPairing_map

#print CategoryTheory.yonedaLemma /-
/-- The Yoneda lemma asserts that that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See <https://stacks.math.columbia.edu/tag/001P>.
-/
def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C
    where
  Hom :=
    { app := fun F x => ULift.up ((x.app F.1) (𝟙 (unop F.1)))
      naturality' := by
        intro X Y f; ext; dsimp
        erw [category.id_comp, ← functor_to_types.naturality]
        simp only [category.comp_id, yoneda_obj_map] }
  inv :=
    { app := fun F x =>
        { app := fun X a => (F.2.map a.op) x.down
          naturality' := by
            intro X Y f; ext; dsimp
            rw [functor_to_types.map_comp_apply] }
      naturality' := by
        intro X Y f; ext; dsimp
        rw [← functor_to_types.naturality, functor_to_types.map_comp_apply] }
  hom_inv_id' := by
    ext; dsimp
    erw [← functor_to_types.naturality, obj_map_id]
    simp only [yoneda_map_app, Quiver.Hom.unop_op]
    erw [category.id_comp]
  inv_hom_id' := by
    ext; dsimp
    rw [functor_to_types.map_id_apply]
#align category_theory.yoneda_lemma CategoryTheory.yonedaLemma
-/

variable {C}

/- warning: category_theory.yoneda_sections -> CategoryTheory.yonedaSections is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C) (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Iso.{max u2 u1, succ (max u1 u2)} Type.{max u1 u2} CategoryTheory.types.{max u2 u1} (Quiver.Hom.{succ (max u1 u2), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X) F) (ULift.{u2, u1} (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F (Opposite.op.{succ u2} C X)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : C) (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Iso.{max u2 u1, max (succ u2) (succ u1)} Sort.{max (succ u2) (succ u1)} CategoryTheory.types.{max u2 u1} (Quiver.Hom.{max (succ u2) (succ u1), max (succ u1) u2} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X) F) (ULift.{u2, u1} (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) (Opposite.op.{succ u2} C X)))
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_sections CategoryTheory.yonedaSectionsₓ'. -/
/-- The isomorphism between `yoneda.obj X ⟶ F` and `F.obj (op X)`
(we need to insert a `ulift` to get the universes right!)
given by the Yoneda lemma.
-/
@[simps]
def yonedaSections (X : C) (F : Cᵒᵖ ⥤ Type v₁) : (yoneda.obj X ⟶ F) ≅ ULift.{u₁} (F.obj (op X)) :=
  (yonedaLemma C).app (op X, F)
#align category_theory.yoneda_sections CategoryTheory.yonedaSections

/- warning: category_theory.yoneda_equiv -> CategoryTheory.yonedaEquiv is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, Equiv.{succ (max u2 u1), succ u1} (Quiver.Hom.{succ (max u2 u1), max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u1 u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.obj.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) X) F) (CategoryTheory.Functor.obj.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F (Opposite.op.{succ u2} C X))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X : C} {F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}}, Equiv.{max (succ u2) (succ u1), succ u1} (Quiver.Hom.{max (succ u2) (succ u1), max (succ u1) u2} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (Prefunctor.obj.{succ u1, max (succ u1) (succ u2), u2, max (succ u1) u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 (succ u1)} (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1)) X) F) (Prefunctor.obj.{succ u1, succ u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.toCategoryStruct.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1} F) (Opposite.op.{succ u2} C X))
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_equiv CategoryTheory.yonedaEquivₓ'. -/
/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) :=
  (yonedaSections X F).toEquiv.trans Equiv.ulift
#align category_theory.yoneda_equiv CategoryTheory.yonedaEquiv

/- warning: category_theory.yoneda_equiv_apply -> CategoryTheory.yonedaEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_equiv_apply CategoryTheory.yonedaEquiv_applyₓ'. -/
@[simp]
theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl
#align category_theory.yoneda_equiv_apply CategoryTheory.yonedaEquiv_apply

/- warning: category_theory.yoneda_equiv_symm_app_apply -> CategoryTheory.yonedaEquiv_symm_app_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_equiv_symm_app_apply CategoryTheory.yonedaEquiv_symm_app_applyₓ'. -/
@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl
#align category_theory.yoneda_equiv_symm_app_apply CategoryTheory.yonedaEquiv_symm_app_apply

/- warning: category_theory.yoneda_equiv_naturality -> CategoryTheory.yonedaEquiv_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_equiv_naturality CategoryTheory.yonedaEquiv_naturalityₓ'. -/
theorem yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) :=
  by
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g)
  rw [← f.naturality]
  dsimp
  simp
#align category_theory.yoneda_equiv_naturality CategoryTheory.yonedaEquiv_naturality

/- warning: category_theory.yoneda_sections_small -> CategoryTheory.yonedaSectionsSmall is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} C] (X : C) (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (Quiver.Hom.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} C _inst_2 (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u1} C _inst_2) X) F) (CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1} F (Opposite.op.{succ u1} C X))
but is expected to have type
  forall {C : Type.{u1}} [_inst_2 : CategoryTheory.SmallCategory.{u1} C] (X : C) (F : CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Iso.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} (Quiver.Hom.{succ u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}))) (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} C (CategoryTheory.Category.toCategoryStruct.{u1, u1} C _inst_2)) (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}))) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} C _inst_2 (CategoryTheory.Functor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u1} C _inst_2)) X) F) (Prefunctor.obj.{succ u1, succ u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} (Opposite.{succ u1} C) (CategoryTheory.Category.opposite.{u1, u1} C _inst_2) Type.{u1} CategoryTheory.types.{u1} F) (Opposite.op.{succ u1} C X))
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_sections_small CategoryTheory.yonedaSectionsSmallₓ'. -/
/-- When `C` is a small category, we can restate the isomorphism from `yoneda_sections`
without having to change universes.
-/
def yonedaSectionsSmall {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) :
    (yoneda.obj X ⟶ F) ≅ F.obj (op X) :=
  yonedaSections X F ≪≫ uliftTrivial _
#align category_theory.yoneda_sections_small CategoryTheory.yonedaSectionsSmall

/- warning: category_theory.yoneda_sections_small_hom -> CategoryTheory.yonedaSectionsSmall_hom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_sections_small_hom CategoryTheory.yonedaSectionsSmall_homₓ'. -/
@[simp]
theorem yonedaSectionsSmall_hom {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type u₁)
    (f : yoneda.obj X ⟶ F) : (yonedaSectionsSmall X F).Hom f = f.app _ (𝟙 _) :=
  rfl
#align category_theory.yoneda_sections_small_hom CategoryTheory.yonedaSectionsSmall_hom

/- warning: category_theory.yoneda_sections_small_inv_app_apply -> CategoryTheory.yonedaSectionsSmall_inv_app_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.yoneda_sections_small_inv_app_apply CategoryTheory.yonedaSectionsSmall_inv_app_applyₓ'. -/
@[simp]
theorem yonedaSectionsSmall_inv_app_apply {C : Type u₁} [SmallCategory C] (X : C)
    (F : Cᵒᵖ ⥤ Type u₁) (t : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    ((yonedaSectionsSmall X F).inv t).app Y f = F.map f.op t :=
  rfl
#align category_theory.yoneda_sections_small_inv_app_apply CategoryTheory.yonedaSectionsSmall_inv_app_apply

attribute [local ext] Functor.ext

#print CategoryTheory.curriedYonedaLemma /-
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁) :=
  eqToIso (by tidy) ≪≫
    curry.mapIso
        (yonedaLemma C ≪≫ isoWhiskerLeft (evaluationUncurried Cᵒᵖ (Type u₁)) uliftFunctorTrivial) ≪≫
      eqToIso (by tidy)
#align category_theory.curried_yoneda_lemma CategoryTheory.curriedYonedaLemma
-/

/- warning: category_theory.curried_yoneda_lemma' -> CategoryTheory.curriedYonedaLemma' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.curried_yoneda_lemma' CategoryTheory.curriedYonedaLemma'ₓ'. -/
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  eqToIso (by tidy) ≪≫
    curry.mapIso
        (isoWhiskerLeft (Prod.swap _ _)
          (yonedaLemma C ≪≫ isoWhiskerLeft (evaluationUncurried Cᵒᵖ (Type u₁)) uliftFunctorTrivial :
            _)) ≪≫
      eqToIso (by tidy)
#align category_theory.curried_yoneda_lemma' CategoryTheory.curriedYonedaLemma'

end CategoryTheory

