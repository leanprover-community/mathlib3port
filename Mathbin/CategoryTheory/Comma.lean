/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.comma
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Isomorphism
import Mathbin.CategoryTheory.Functor.Category
import Mathbin.CategoryTheory.EqToHom

/-!
# Comma categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left   ⟶   L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right  ⟶   R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `comma L R`: the comma category of the functors `L` and `R`.
* `over X`: the over category of the object `X` (developed in `over.lean`).
* `under X`: the under category of the object `X` (also developed in `over.lean`).
* `arrow T`: the arrow category of the category `T` (developed in `arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/


namespace CategoryTheory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]

variable {B : Type u₂} [Category.{v₂} B]

variable {T : Type u₃} [Category.{v₃} T]

#print CategoryTheory.Comma /-
/-- The objects of the comma category are triples of an object `left : A`, an object
   `right : B` and a morphism `hom : L.obj left ⟶ R.obj right`.  -/
structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  left : A := by obviously
  right : B := by obviously
  Hom : L.obj left ⟶ R.obj right
#align category_theory.comma CategoryTheory.Comma
-/

#print CategoryTheory.Comma.inhabited /-
-- Satisfying the inhabited linter
instance Comma.inhabited [Inhabited T] : Inhabited (Comma (𝟭 T) (𝟭 T))
    where default :=
    { left := default
      right := default
      Hom := 𝟙 default }
#align category_theory.comma.inhabited CategoryTheory.Comma.inhabited
-/

variable {L : A ⥤ T} {R : B ⥤ T}

#print CategoryTheory.CommaMorphism /-
/-- A morphism between two objects in the comma category is a commutative square connecting the
    morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
@[ext]
structure CommaMorphism (X Y : Comma L R) where
  left : X.left ⟶ Y.left := by obviously
  right : X.right ⟶ Y.right := by obviously
  w' : L.map left ≫ Y.Hom = X.Hom ≫ R.map right := by obviously
#align category_theory.comma_morphism CategoryTheory.CommaMorphism
-/

#print CategoryTheory.CommaMorphism.inhabited /-
-- Satisfying the inhabited linter
instance CommaMorphism.inhabited [Inhabited (Comma L R)] :
    Inhabited (CommaMorphism (default : Comma L R) default) :=
  ⟨⟨𝟙 _, 𝟙 _⟩⟩
#align category_theory.comma_morphism.inhabited CategoryTheory.CommaMorphism.inhabited
-/

restate_axiom comma_morphism.w'

attribute [simp, reassoc.1] comma_morphism.w

#print CategoryTheory.commaCategory /-
instance commaCategory : Category (Comma L R)
    where
  Hom := CommaMorphism
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp X Y Z f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }
#align category_theory.comma_category CategoryTheory.commaCategory
-/

namespace Comma

section

variable {X Y Z : Comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

#print CategoryTheory.Comma.id_left /-
@[simp]
theorem id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left :=
  rfl
#align category_theory.comma.id_left CategoryTheory.Comma.id_left
-/

#print CategoryTheory.Comma.id_right /-
@[simp]
theorem id_right : (𝟙 X : CommaMorphism X X).right = 𝟙 X.right :=
  rfl
#align category_theory.comma.id_right CategoryTheory.Comma.id_right
-/

#print CategoryTheory.Comma.comp_left /-
@[simp]
theorem comp_left : (f ≫ g).left = f.left ≫ g.left :=
  rfl
#align category_theory.comma.comp_left CategoryTheory.Comma.comp_left
-/

#print CategoryTheory.Comma.comp_right /-
@[simp]
theorem comp_right : (f ≫ g).right = f.right ≫ g.right :=
  rfl
#align category_theory.comma.comp_right CategoryTheory.Comma.comp_right
-/

end

variable (L) (R)

#print CategoryTheory.Comma.fst /-
/-- The functor sending an object `X` in the comma category to `X.left`. -/
@[simps]
def fst : Comma L R ⥤ A where
  obj X := X.left
  map _ _ f := f.left
#align category_theory.comma.fst CategoryTheory.Comma.fst
-/

#print CategoryTheory.Comma.snd /-
/-- The functor sending an object `X` in the comma category to `X.right`. -/
@[simps]
def snd : Comma L R ⥤ B where
  obj X := X.right
  map _ _ f := f.right
#align category_theory.comma.snd CategoryTheory.Comma.snd
-/

#print CategoryTheory.Comma.natTrans /-
/-- We can interpret the commutative square constituting a morphism in the comma category as a
    natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
    to `T`, where the components are given by the morphism that constitutes an object of the comma
    category. -/
@[simps]
def natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X := X.Hom
#align category_theory.comma.nat_trans CategoryTheory.Comma.natTrans
-/

#print CategoryTheory.Comma.eqToHom_left /-
@[simp]
theorem eqToHom_left (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.left (eqToHom H) =
      eqToHom
        (by
          cases H
          rfl) :=
  by
  cases H
  rfl
#align category_theory.comma.eq_to_hom_left CategoryTheory.Comma.eqToHom_left
-/

#print CategoryTheory.Comma.eqToHom_right /-
@[simp]
theorem eqToHom_right (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.right (eqToHom H) =
      eqToHom
        (by
          cases H
          rfl) :=
  by
  cases H
  rfl
#align category_theory.comma.eq_to_hom_right CategoryTheory.Comma.eqToHom_right
-/

section

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

/- warning: category_theory.comma.iso_mk -> CategoryTheory.Comma.isoMk is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} A] {B : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} B] {T : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} T] {L₁ : CategoryTheory.Functor.{u1, u3, u4, u6} A _inst_1 T _inst_3} {R₁ : CategoryTheory.Functor.{u2, u3, u5, u6} B _inst_2 T _inst_3} {X : CategoryTheory.Comma.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁} {Y : CategoryTheory.Comma.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁} (l : CategoryTheory.Iso.{u1, u4} (autoParamₓ.{succ u4} A (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 98 (OfNat.mk.{0} Nat 98 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)) _inst_1 (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (r : CategoryTheory.Iso.{u2, u5} (autoParamₓ.{succ u5} B (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 98 (OfNat.mk.{0} Nat 98 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)) _inst_2 (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)), (Eq.{succ u3} (Quiver.Hom.{succ u3, u6} T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁ (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁ (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y))) (CategoryTheory.CategoryStruct.comp.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁ (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁ (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁ (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (CategoryTheory.Functor.map.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁ (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) (CategoryTheory.Iso.hom.{u1, u4} (autoParamₓ.{succ u4} A (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 98 (OfNat.mk.{0} Nat 98 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)) _inst_1 (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) l)) (CategoryTheory.Comma.hom.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (CategoryTheory.CategoryStruct.comp.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3) (CategoryTheory.Functor.obj.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁ (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁ (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (CategoryTheory.Functor.obj.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁ (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (CategoryTheory.Comma.hom.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Functor.map.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁ (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) (CategoryTheory.Iso.hom.{u2, u5} (autoParamₓ.{succ u5} B (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 98 (OfNat.mk.{0} Nat 98 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)) _inst_2 (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) r)))) -> (CategoryTheory.Iso.{max u1 u2, max u4 u5 u3} (CategoryTheory.Comma.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁) (CategoryTheory.commaCategory.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁) X Y)
but is expected to have type
  forall {A : Type.{u4}} [_inst_1 : CategoryTheory.Category.{u1, u4} A] {B : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u2, u5} B] {T : Type.{u6}} [_inst_3 : CategoryTheory.Category.{u3, u6} T] {L₁ : CategoryTheory.Functor.{u1, u3, u4, u6} A _inst_1 T _inst_3} {R₁ : CategoryTheory.Functor.{u2, u3, u5, u6} B _inst_2 T _inst_3} {X : CategoryTheory.Comma.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁} {Y : CategoryTheory.Comma.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁} (l : CategoryTheory.Iso.{u1, u4} A _inst_1 (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (r : CategoryTheory.Iso.{u2, u5} B _inst_2 (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)), (Eq.{succ u3} (Quiver.Hom.{succ u3, u6} T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} A (CategoryTheory.Category.toCategoryStruct.{u1, u4} A _inst_1)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} B (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} B (CategoryTheory.Category.toCategoryStruct.{u2, u5} B _inst_2)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y))) (CategoryTheory.CategoryStruct.comp.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3) (Prefunctor.obj.{succ u1, succ u3, u4, u6} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} A (CategoryTheory.Category.toCategoryStruct.{u1, u4} A _inst_1)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (Prefunctor.obj.{succ u1, succ u3, u4, u6} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} A (CategoryTheory.Category.toCategoryStruct.{u1, u4} A _inst_1)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} B (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} B (CategoryTheory.Category.toCategoryStruct.{u2, u5} B _inst_2)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (Prefunctor.map.{succ u1, succ u3, u4, u6} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} A (CategoryTheory.Category.toCategoryStruct.{u1, u4} A _inst_1)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) (CategoryTheory.Iso.hom.{u1, u4} A _inst_1 (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) l)) (CategoryTheory.Comma.hom.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (CategoryTheory.CategoryStruct.comp.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3) (Prefunctor.obj.{succ u1, succ u3, u4, u6} A (CategoryTheory.CategoryStruct.toQuiver.{u1, u4} A (CategoryTheory.Category.toCategoryStruct.{u1, u4} A _inst_1)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u4, u6} A _inst_1 T _inst_3 L₁) (CategoryTheory.Comma.left.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} B (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} B (CategoryTheory.Category.toCategoryStruct.{u2, u5} B _inst_2)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X)) (Prefunctor.obj.{succ u2, succ u3, u5, u6} B (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} B (CategoryTheory.Category.toCategoryStruct.{u2, u5} B _inst_2)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y)) (CategoryTheory.Comma.hom.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (Prefunctor.map.{succ u2, succ u3, u5, u6} B (CategoryTheory.CategoryStruct.toQuiver.{u2, u5} B (CategoryTheory.Category.toCategoryStruct.{u2, u5} B _inst_2)) T (CategoryTheory.CategoryStruct.toQuiver.{u3, u6} T (CategoryTheory.Category.toCategoryStruct.{u3, u6} T _inst_3)) (CategoryTheory.Functor.toPrefunctor.{u2, u3, u5, u6} B _inst_2 T _inst_3 R₁) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) (CategoryTheory.Iso.hom.{u2, u5} B _inst_2 (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ X) (CategoryTheory.Comma.right.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁ Y) r)))) -> (CategoryTheory.Iso.{max u1 u2, max (max u4 u5) u3} (CategoryTheory.Comma.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁) (CategoryTheory.commaCategory.{u1, u2, u3, u4, u5, u6} A _inst_1 B _inst_2 T _inst_3 L₁ R₁) X Y)
Case conversion may be inaccurate. Consider using '#align category_theory.comma.iso_mk CategoryTheory.Comma.isoMkₓ'. -/
/-- Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[simps]
def isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
    (h : L₁.map l.Hom ≫ Y.Hom = X.Hom ≫ R₁.map r.Hom) : X ≅ Y
    where
  Hom :=
    { left := l.Hom
      right := r.Hom }
  inv :=
    { left := l.inv
      right := r.inv
      w' :=
        by
        rw [← L₁.map_iso_inv l, iso.inv_comp_eq, L₁.map_iso_hom, reassoc_of h, ← R₁.map_comp]
        simp }
#align category_theory.comma.iso_mk CategoryTheory.Comma.isoMk

#print CategoryTheory.Comma.mapLeft /-
/-- A natural transformation `L₁ ⟶ L₂` induces a functor `comma L₂ R ⥤ comma L₁ R`. -/
@[simps]
def mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R
    where
  obj X :=
    { left := X.left
      right := X.right
      Hom := l.app X.left ≫ X.Hom }
  map X Y f :=
    { left := f.left
      right := f.right }
#align category_theory.comma.map_left CategoryTheory.Comma.mapLeft
-/

#print CategoryTheory.Comma.mapLeftId /-
/-- The functor `comma L R ⥤ comma L R` induced by the identity natural transformation on `L` is
    naturally isomorphic to the identity functor. -/
@[simps]
def mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _
    where
  Hom :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_left_id CategoryTheory.Comma.mapLeftId
-/

#print CategoryTheory.Comma.mapLeftComp /-
/-- The functor `comma L₁ R ⥤ comma L₃ R` induced by the composition of two natural transformations
    `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
    induced by these natural transformations. -/
@[simps]
def mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) : mapLeft R (l ≫ l') ≅ mapLeft R l' ⋙ mapLeft R l
    where
  Hom :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_left_comp CategoryTheory.Comma.mapLeftComp
-/

#print CategoryTheory.Comma.mapRight /-
/-- A natural transformation `R₁ ⟶ R₂` induces a functor `comma L R₁ ⥤ comma L R₂`. -/
@[simps]
def mapRight (r : R₁ ⟶ R₂) : Comma L R₁ ⥤ Comma L R₂
    where
  obj X :=
    { left := X.left
      right := X.right
      Hom := X.Hom ≫ r.app X.right }
  map X Y f :=
    { left := f.left
      right := f.right }
#align category_theory.comma.map_right CategoryTheory.Comma.mapRight
-/

#print CategoryTheory.Comma.mapRightId /-
/-- The functor `comma L R ⥤ comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simps]
def mapRightId : mapRight L (𝟙 R) ≅ 𝟭 _
    where
  Hom :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_right_id CategoryTheory.Comma.mapRightId
-/

#print CategoryTheory.Comma.mapRightComp /-
/-- The functor `comma L R₁ ⥤ comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simps]
def mapRightComp (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) : mapRight L (r ≫ r') ≅ mapRight L r ⋙ mapRight L r'
    where
  Hom :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
  inv :=
    {
      app := fun X =>
        { left := 𝟙 _
          right := 𝟙 _ } }
#align category_theory.comma.map_right_comp CategoryTheory.Comma.mapRightComp
-/

end

section

variable {C : Type u₄} [Category.{v₄} C] {D : Type u₅} [Category.{v₅} D]

#print CategoryTheory.Comma.preLeft /-
/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps]
def preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R
    where
  obj X :=
    { left := F.obj X.left
      right := X.right
      Hom := X.Hom }
  map X Y f :=
    { left := F.map f.left
      right := f.right
      w' := by simpa using f.w }
#align category_theory.comma.pre_left CategoryTheory.Comma.preLeft
-/

#print CategoryTheory.Comma.preRight /-
/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[simps]
def preRight (L : A ⥤ T) (F : C ⥤ B) (R : B ⥤ T) : Comma L (F ⋙ R) ⥤ Comma L R
    where
  obj X :=
    { left := X.left
      right := F.obj X.right
      Hom := X.Hom }
  map X Y f :=
    { left := f.left
      right := F.map f.right
      w' := by simp }
#align category_theory.comma.pre_right CategoryTheory.Comma.preRight
-/

#print CategoryTheory.Comma.post /-
/-- The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)` -/
@[simps]
def post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F)
    where
  obj X :=
    { left := X.left
      right := X.right
      Hom := F.map X.Hom }
  map X Y f :=
    { left := f.left
      right := f.right
      w' := by simp only [functor.comp_map, ← F.map_comp, f.w] }
#align category_theory.comma.post CategoryTheory.Comma.post
-/

end

end Comma

end CategoryTheory

