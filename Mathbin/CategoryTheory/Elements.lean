/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.elements
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.StructuredArrow
import Mathbin.CategoryTheory.Groupoid
import Mathbin.CategoryTheory.Punit

/-!
# The category of elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`category_theory.category_of_elements.structured_arrow_equivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/


namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

#print CategoryTheory.Functor.Elements /-
/-- The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
@[nolint has_nonempty_instance]
def Functor.Elements (F : C ⥤ Type w) :=
  Σc : C, F.obj c
#align category_theory.functor.elements CategoryTheory.Functor.Elements
-/

#print CategoryTheory.categoryOfElements /-
/-- The category structure on `F.elements`, for `F : C ⥤ Type`.
    A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.
 -/
instance categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements
    where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by obviously⟩
  comp p q r f g := ⟨f.val ≫ g.val, by obviously⟩
#align category_theory.category_of_elements CategoryTheory.categoryOfElements
-/

namespace CategoryOfElements

#print CategoryTheory.CategoryOfElements.ext /-
@[ext]
theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext_val w
#align category_theory.category_of_elements.ext CategoryTheory.CategoryOfElements.ext
-/

#print CategoryTheory.CategoryOfElements.comp_val /-
@[simp]
theorem comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl
#align category_theory.category_of_elements.comp_val CategoryTheory.CategoryOfElements.comp_val
-/

#print CategoryTheory.CategoryOfElements.id_val /-
@[simp]
theorem id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl
#align category_theory.category_of_elements.id_val CategoryTheory.CategoryOfElements.id_val
-/

end CategoryOfElements

#print CategoryTheory.groupoidOfElements /-
noncomputable instance groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) :
    Groupoid F.Elements
    where
  inv p q f :=
    ⟨inv f.val,
      calc
        F.map (inv f.val) q.2 = F.map (inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp' _ _ _ := by
    ext
    simp
  comp_inv' _ _ _ := by
    ext
    simp
#align category_theory.groupoid_of_elements CategoryTheory.groupoidOfElements
-/

namespace CategoryOfElements

variable (F : C ⥤ Type w)

#print CategoryTheory.CategoryOfElements.π /-
/-- The functor out of the category of elements which forgets the element. -/
@[simps]
def π : F.Elements ⥤ C where
  obj X := X.1
  map X Y f := f.val
#align category_theory.category_of_elements.π CategoryTheory.CategoryOfElements.π
-/

#print CategoryTheory.CategoryOfElements.map /-
/-- A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements
    where
  obj t := ⟨t.1, α.app t.1 t.2⟩
  map t₁ t₂ k := ⟨k.1, by simpa [← k.2] using (functor_to_types.naturality _ _ α k.1 t₁.2).symm⟩
#align category_theory.category_of_elements.map CategoryTheory.CategoryOfElements.map
-/

#print CategoryTheory.CategoryOfElements.map_π /-
@[simp]
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl
#align category_theory.category_of_elements.map_π CategoryTheory.CategoryOfElements.map_π
-/

#print CategoryTheory.CategoryOfElements.toStructuredArrow /-
/-- The forward direction of the equivalence `F.elements ≅ (*, F)`. -/
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F
    where
  obj X := StructuredArrow.mk fun _ => X.2
  map X Y f := StructuredArrow.homMk f.val (by tidy)
#align category_theory.category_of_elements.to_structured_arrow CategoryTheory.CategoryOfElements.toStructuredArrow
-/

/- warning: category_theory.category_of_elements.to_structured_arrow_obj -> CategoryTheory.CategoryOfElements.toStructuredArrow_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (X : CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F), Eq.{succ (max u3 u1)} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.Functor.obj.{u2, max u1 u2, max u3 u1, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.StructuredArrow.category.{u1, succ u1, u3, u2} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.CategoryOfElements.toStructuredArrow.{u1, u2, u3} C _inst_1 F) X) (CategoryTheory.Comma.mk.{u1, u2, u1, u1, u3, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) F (CategoryTheory.Discrete.mk.{u1} PUnit.{succ u1} PUnit.unit.{succ u1}) (Sigma.fst.{u3, u1} C (fun (c : C) => CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F c) X) (fun (_x : CategoryTheory.Functor.obj.{u1, u1, u1, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) (CategoryTheory.Discrete.mk.{u1} PUnit.{succ u1} PUnit.unit.{succ u1})) => Sigma.snd.{u3, u1} C (fun (c : C) => CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F c) X))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (X : CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F), Eq.{max (succ u3) (succ u1)} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (Prefunctor.obj.{succ u2, max (succ u2) (succ u1), max u3 u1, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.Category.toCategoryStruct.{u2, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F))) (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.instCategoryStructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F))) (CategoryTheory.Functor.toPrefunctor.{u2, max u2 u1, max u3 u1, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.instCategoryStructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.CategoryOfElements.toStructuredArrow.{u1, u2, u3} C _inst_1 F)) X) (CategoryTheory.Comma.mk.{u1, u2, u1, u1, u3, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) F (CategoryTheory.Discrete.mk.{u1} PUnit.{succ u1} PUnit.unit.{succ u1}) (Sigma.fst.{u3, u1} C (fun (c : C) => Prefunctor.obj.{succ u2, succ u1, u3, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) c) X) (fun (_x : Prefunctor.obj.{succ u1, succ u1, u1, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.CategoryStruct.toQuiver.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.Category.toCategoryStruct.{u1, u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}))) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u1, u1, u1, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1})) (CategoryTheory.Discrete.mk.{u1} PUnit.{succ u1} PUnit.unit.{succ u1})) => Sigma.snd.{u3, u1} C (fun (c : C) => Prefunctor.obj.{succ u2, succ u1, u3, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) c) X))
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.to_structured_arrow_obj CategoryTheory.CategoryOfElements.toStructuredArrow_objₓ'. -/
@[simp]
theorem toStructuredArrow_obj (X) :
    (toStructuredArrow F).obj X =
      { left := ⟨⟨⟩⟩
        right := X.1
        Hom := fun _ => X.2 } :=
  rfl
#align category_theory.category_of_elements.to_structured_arrow_obj CategoryTheory.CategoryOfElements.toStructuredArrow_obj

/- warning: category_theory.category_of_elements.to_comma_map_right -> CategoryTheory.CategoryOfElements.to_comma_map_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.to_comma_map_right CategoryTheory.CategoryOfElements.to_comma_map_rightₓ'. -/
@[simp]
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right = f.val :=
  rfl
#align category_theory.category_of_elements.to_comma_map_right CategoryTheory.CategoryOfElements.to_comma_map_right

#print CategoryTheory.CategoryOfElements.fromStructuredArrow /-
/-- The reverse direction of the equivalence `F.elements ≅ (*, F)`. -/
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements
    where
  obj X := ⟨X.right, X.Hom PUnit.unit⟩
  map X Y f := ⟨f.right, congr_fun f.w'.symm PUnit.unit⟩
#align category_theory.category_of_elements.from_structured_arrow CategoryTheory.CategoryOfElements.fromStructuredArrow
-/

/- warning: category_theory.category_of_elements.from_structured_arrow_obj -> CategoryTheory.CategoryOfElements.fromStructuredArrow_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (X : CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.Functor.obj.{max u1 u2, u2, max u3 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.StructuredArrow.category.{u1, succ u1, u3, u2} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.CategoryOfElements.fromStructuredArrow.{u1, u2, u3} C _inst_1 F) X) (Sigma.mk.{u3, u1} C (fun (c : C) => CategoryTheory.Functor.obj.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F c) (CategoryTheory.Comma.right.{u1, u2, u1, u1, u3, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) F X) (CategoryTheory.Comma.hom.{u1, u2, u1, u1, u3, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) F X PUnit.unit.{succ u1}))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}) (X : CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F), Eq.{max (succ u3) (succ u1)} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (Prefunctor.obj.{max (succ u2) (succ u1), succ u2, max u3 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.instCategoryStructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F))) (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.Category.toCategoryStruct.{u2, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F))) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, u2, max u3 u1, max u3 u1} (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.instCategoryStructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.CategoryOfElements.fromStructuredArrow.{u1, u2, u3} C _inst_1 F)) X) (Sigma.mk.{u3, u1} C (fun (c : C) => Prefunctor.obj.{succ u2, succ u1, u3, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u3} C (CategoryTheory.Category.toCategoryStruct.{u2, u3} C _inst_1)) Type.{u1} (CategoryTheory.CategoryStruct.toQuiver.{u1, succ u1} Type.{u1} (CategoryTheory.Category.toCategoryStruct.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1})) (CategoryTheory.Functor.toPrefunctor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} F) c) (CategoryTheory.Comma.right.{u1, u2, u1, u1, u3, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) F X) (CategoryTheory.Comma.hom.{u1, u2, u1, u1, u3, succ u1} (CategoryTheory.Discrete.{u1} PUnit.{succ u1}) (CategoryTheory.discreteCategory.{u1} PUnit.{succ u1}) C _inst_1 Type.{u1} CategoryTheory.types.{u1} (CategoryTheory.Functor.fromPUnit.{u1, succ u1} Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1}) F X PUnit.unit.{succ u1}))
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.from_structured_arrow_obj CategoryTheory.CategoryOfElements.fromStructuredArrow_objₓ'. -/
@[simp]
theorem fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.Hom PUnit.unit⟩ :=
  rfl
#align category_theory.category_of_elements.from_structured_arrow_obj CategoryTheory.CategoryOfElements.fromStructuredArrow_obj

/- warning: category_theory.category_of_elements.from_structured_arrow_map -> CategoryTheory.CategoryOfElements.fromStructuredArrow_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.from_structured_arrow_map CategoryTheory.CategoryOfElements.fromStructuredArrow_mapₓ'. -/
@[simp]
theorem fromStructuredArrow_map {X Y} (f : X ⟶ Y) :
    (fromStructuredArrow F).map f = ⟨f.right, congr_fun f.w'.symm PUnit.unit⟩ :=
  rfl
#align category_theory.category_of_elements.from_structured_arrow_map CategoryTheory.CategoryOfElements.fromStructuredArrow_map

/- warning: category_theory.category_of_elements.structured_arrow_equivalence -> CategoryTheory.CategoryOfElements.structuredArrowEquivalence is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Equivalence.{u2, max u1 u2, max u3 u1, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.StructuredArrow.category.{u1, succ u1, u3, u2} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} C] (F : CategoryTheory.Functor.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Equivalence.{u2, max u2 u1, max u3 u1, max u3 u1} (CategoryTheory.Functor.Elements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.StructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F) (CategoryTheory.categoryOfElements.{u1, u2, u3} C _inst_1 F) (CategoryTheory.instCategoryStructuredArrow.{u2, u1, u3, succ u1} C _inst_1 Type.{u1} CategoryTheory.types.{u1} PUnit.{succ u1} F)
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.structured_arrow_equivalence CategoryTheory.CategoryOfElements.structuredArrowEquivalenceₓ'. -/
/-- The equivalence between the category of elements `F.elements`
    and the comma category `(*, F)`. -/
@[simps]
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F :=
  Equivalence.mk (toStructuredArrow F) (fromStructuredArrow F)
    (NatIso.ofComponents (fun X => eqToIso (by tidy)) (by tidy))
    (NatIso.ofComponents (fun X => StructuredArrow.isoMk (Iso.refl _) (by tidy)) (by tidy))
#align category_theory.category_of_elements.structured_arrow_equivalence CategoryTheory.CategoryOfElements.structuredArrowEquivalence

open Opposite

#print CategoryTheory.CategoryOfElements.toCostructuredArrow /-
/-- The forward direction of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)`,
given by `category_theory.yoneda_sections`.
-/
@[simps]
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F
    where
  obj X := CostructuredArrow.mk ((yonedaSections (unop (unop X).fst) F).inv (ULift.up (unop X).2))
  map X Y f := by
    fapply costructured_arrow.hom_mk
    exact f.unop.val.unop
    ext y
    simp only [costructured_arrow.mk_hom_eq_self, yoneda_map_app, functor_to_types.comp, op_comp,
      yoneda_sections_inv_app, functor_to_types.map_comp_apply, Quiver.Hom.op_unop,
      Subtype.val_eq_coe]
    congr
    exact f.unop.2
#align category_theory.category_of_elements.to_costructured_arrow CategoryTheory.CategoryOfElements.toCostructuredArrow
-/

#print CategoryTheory.CategoryOfElements.fromCostructuredArrow /-
/-- The reverse direction of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)`,
given by `category_theory.yoneda_equiv`.
-/
@[simps]
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements
    where
  obj X := ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map X Y f :=
    ⟨f.unop.1.op,
      by
      convert(congr_fun ((unop X).Hom.naturality f.unop.left.op) (𝟙 _)).symm
      simp only [Equiv.toFun_as_coe, Quiver.Hom.unop_op, yoneda_equiv_apply, types_comp_apply,
        category.comp_id, yoneda_obj_map]
      have : yoneda.map f.unop.left ≫ (unop X).Hom = (unop Y).Hom :=
        by
        convert f.unop.3
        erw [category.comp_id]
      erw [← this]
      simp only [yoneda_map_app, functor_to_types.comp]
      erw [category.id_comp]⟩
#align category_theory.category_of_elements.from_costructured_arrow CategoryTheory.CategoryOfElements.fromCostructuredArrow
-/

/- warning: category_theory.category_of_elements.from_costructured_arrow_obj_mk -> CategoryTheory.CategoryOfElements.fromCostructuredArrow_obj_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.from_costructured_arrow_obj_mk CategoryTheory.CategoryOfElements.fromCostructuredArrow_obj_mkₓ'. -/
@[simp]
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaEquiv.1 f⟩ :=
  rfl
#align category_theory.category_of_elements.from_costructured_arrow_obj_mk CategoryTheory.CategoryOfElements.fromCostructuredArrow_obj_mk

#print CategoryTheory.CategoryOfElements.from_toCostructuredArrow_eq /-
/-- The unit of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem from_toCostructuredArrow_eq (F : Cᵒᵖ ⥤ Type v) :
    (toCostructuredArrow F).rightOp ⋙ fromCostructuredArrow F = 𝟭 _ :=
  by
  apply Functor.ext
  intro X Y f
  have :
    ∀ {a b : F.elements} (H : a = b),
      ↑(eq_to_hom H) =
        eq_to_hom
          (show a.fst = b.fst by
            cases H
            rfl) :=
    fun _ _ H => by
    cases H
    rfl
  ext; simp [this]
  tidy
#align category_theory.category_of_elements.from_to_costructured_arrow_eq CategoryTheory.CategoryOfElements.from_toCostructuredArrow_eq
-/

#print CategoryTheory.CategoryOfElements.to_fromCostructuredArrow_eq /-
/-- The counit of the equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem to_fromCostructuredArrow_eq (F : Cᵒᵖ ⥤ Type v) :
    (fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F = 𝟭 _ :=
  by
  apply functor.hext
  · intro X
    cases X
    cases X_right
    simp only [functor.id_obj, functor.right_op_obj, to_costructured_arrow_obj, functor.comp_obj,
      costructured_arrow.mk]
    congr
    ext (x f)
    convert congr_fun (X_hom.naturality f.op).symm (𝟙 X_left)
    simp only [Quiver.Hom.unop_op, yoneda_obj_map]
    erw [category.comp_id]
  intro X Y f
  rcases X with ⟨X_left, ⟨⟨⟩⟩⟩; rcases Y with ⟨Y_left, ⟨⟨⟩⟩⟩; cases f
  simp [costructured_arrow.hom_mk]
  delta costructured_arrow.mk
  congr
  · ext (x f)
    convert congr_fun (X_hom.naturality f.op).symm (𝟙 X_left)
    simp only [Quiver.Hom.unop_op, CategoryTheory.yoneda_obj_map]
    erw [category.comp_id]
  · ext (x f)
    convert congr_fun (Y_hom.naturality f.op).symm (𝟙 Y_left)
    simp only [Quiver.Hom.unop_op, CategoryTheory.yoneda_obj_map]
    erw [category.comp_id]
  simp
  exact proof_irrel_heq _ _
#align category_theory.category_of_elements.to_from_costructured_arrow_eq CategoryTheory.CategoryOfElements.to_fromCostructuredArrow_eq
-/

/- warning: category_theory.category_of_elements.costructured_arrow_yoneda_equivalence -> CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Equivalence.{u1, max u2 u1, max u2 u1, max u2 u1} (Opposite.{succ (max u2 u1)} (CategoryTheory.Functor.Elements.{u1, u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) F)) (CategoryTheory.Category.opposite.{u1, max u2 u1} (CategoryTheory.Functor.Elements.{u1, u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) F) (CategoryTheory.categoryOfElements.{u1, u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) F)) (CategoryTheory.CostructuredArrow.{u1, max u2 u1, u2, max u1 u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) F) (CategoryTheory.CostructuredArrow.category.{max u2 u1, max u1 u2 (succ u1), u2, u1} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) F)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (F : CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}), CategoryTheory.Equivalence.{u1, max u2 u1, max u2 u1, max u2 u1} (Opposite.{max (succ u2) (succ u1)} (CategoryTheory.Functor.Elements.{u1, u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) F)) (CategoryTheory.CostructuredArrow.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) F) (CategoryTheory.Category.opposite.{u1, max u2 u1} (CategoryTheory.Functor.Elements.{u1, u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) F) (CategoryTheory.categoryOfElements.{u1, u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) F)) (CategoryTheory.instCategoryCostructuredArrow.{u1, max u2 u1, u2, max u2 (succ u1)} C _inst_1 (CategoryTheory.Functor.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.Functor.category.{u1, u1, u2, succ u1} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1) Type.{u1} CategoryTheory.types.{u1}) (CategoryTheory.yoneda.{u1, u2} C _inst_1) F)
Case conversion may be inaccurate. Consider using '#align category_theory.category_of_elements.costructured_arrow_yoneda_equivalence CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalenceₓ'. -/
/-- The equivalence `F.elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps]
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F :=
  Equivalence.mk (toCostructuredArrow F) (fromCostructuredArrow F).rightOp
    (NatIso.op (eqToIso (from_toCostructuredArrow_eq F))) (eqToIso <| to_fromCostructuredArrow_eq F)
#align category_theory.category_of_elements.costructured_arrow_yoneda_equivalence CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence

#print CategoryTheory.CategoryOfElements.costructuredArrow_yoneda_equivalence_naturality /-
/-- The equivalence `(-.elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
theorem costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ CostructuredArrow.map α :=
  by
  fapply Functor.ext
  · intro X
    simp only [costructured_arrow.map_mk, to_costructured_arrow_obj, functor.op_obj,
      functor.comp_obj]
    congr
    ext (x f)
    simpa using congr_fun (α.naturality f.op).symm (unop X).snd
  · intro X Y f
    ext
    have :
      ∀ {F : Cᵒᵖ ⥤ Type v} {a b : costructured_arrow yoneda F} (H : a = b),
        comma_morphism.left (eq_to_hom H) =
          eq_to_hom
            (show a.left = b.left by
              cases H
              rfl) :=
      fun _ _ _ H => by
      cases H
      rfl
    simp [this]
#align category_theory.category_of_elements.costructured_arrow_yoneda_equivalence_naturality CategoryTheory.CategoryOfElements.costructuredArrow_yoneda_equivalence_naturality
-/

end CategoryOfElements

end CategoryTheory

