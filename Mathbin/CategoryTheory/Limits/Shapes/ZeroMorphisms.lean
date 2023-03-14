/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.limits.shapes.zero_morphisms
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pi.Algebra
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.Images
import Mathbin.CategoryTheory.IsomorphismClasses
import Mathbin.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Zero morphisms and zero objects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v u

universe v' u'

open CategoryTheory

open CategoryTheory.Category

open Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

variable (D : Type u') [Category.{v'} D]

#print CategoryTheory.Limits.HasZeroMorphisms /-
/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class HasZeroMorphisms where
  [Zero : ∀ X Y : C, Zero (X ⟶ Y)]
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by obviously
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by obviously
#align category_theory.limits.has_zero_morphisms CategoryTheory.Limits.HasZeroMorphisms
-/

attribute [instance] has_zero_morphisms.has_zero

restate_axiom has_zero_morphisms.comp_zero'

restate_axiom has_zero_morphisms.zero_comp'

variable {C}

#print CategoryTheory.Limits.comp_zero /-
@[simp]
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z
#align category_theory.limits.comp_zero CategoryTheory.Limits.comp_zero
-/

#print CategoryTheory.Limits.zero_comp /-
@[simp]
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f
#align category_theory.limits.zero_comp CategoryTheory.Limits.zero_comp
-/

#print CategoryTheory.Limits.hasZeroMorphismsPempty /-
instance hasZeroMorphismsPempty : HasZeroMorphisms (Discrete PEmpty) where Zero := by tidy
#align category_theory.limits.has_zero_morphisms_pempty CategoryTheory.Limits.hasZeroMorphismsPempty
-/

#print CategoryTheory.Limits.hasZeroMorphismsPunit /-
instance hasZeroMorphismsPunit : HasZeroMorphisms (Discrete PUnit) where Zero := by tidy
#align category_theory.limits.has_zero_morphisms_punit CategoryTheory.Limits.hasZeroMorphismsPunit
-/

namespace HasZeroMorphisms

variable {C}

/-- This lemma will be immediately superseded by `ext`, below. -/
private theorem ext_aux (I J : HasZeroMorphisms C)
    (w :
      ∀ X Y : C,
        (@HasZeroMorphisms.hasZero _ _ I X Y).zero = (@HasZeroMorphisms.hasZero _ _ J X Y).zero) :
    I = J := by
  cases I; cases J
  congr
  · ext (X Y)
    exact w X Y
  · apply proof_irrel_heq
  · apply proof_irrel_heq
#align category_theory.limits.has_zero_morphisms.ext_aux category_theory.limits.has_zero_morphisms.ext_aux

#print CategoryTheory.Limits.HasZeroMorphisms.ext /-
/-- If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `has_zero_morphisms` to exist at all.

See, particularly, the note on `zero_morphisms_of_zero_object` below.
-/
theorem ext (I J : HasZeroMorphisms C) : I = J :=
  by
  apply ext_aux
  intro X Y
  rw [← @has_zero_morphisms.comp_zero _ _ I X X (@has_zero_morphisms.has_zero _ _ J X X).zero]
  rw [@has_zero_morphisms.zero_comp _ _ J]
#align category_theory.limits.has_zero_morphisms.ext CategoryTheory.Limits.HasZeroMorphisms.ext
-/

instance : Subsingleton (HasZeroMorphisms C) :=
  ⟨ext⟩

end HasZeroMorphisms

open Opposite HasZeroMorphisms

#print CategoryTheory.Limits.hasZeroMorphismsOpposite /-
instance hasZeroMorphismsOpposite [HasZeroMorphisms C] : HasZeroMorphisms Cᵒᵖ
    where
  Zero X Y := ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero X Y f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X Y Z f := congr_arg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))
#align category_theory.limits.has_zero_morphisms_opposite CategoryTheory.Limits.hasZeroMorphismsOpposite
-/

section

variable {C} [HasZeroMorphisms C]

#print CategoryTheory.Limits.zero_of_comp_mono /-
theorem zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0 :=
  by
  rw [← zero_comp, cancel_mono] at h
  exact h
#align category_theory.limits.zero_of_comp_mono CategoryTheory.Limits.zero_of_comp_mono
-/

#print CategoryTheory.Limits.zero_of_epi_comp /-
theorem zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0 :=
  by
  rw [← comp_zero, cancel_epi] at h
  exact h
#align category_theory.limits.zero_of_epi_comp CategoryTheory.Limits.zero_of_epi_comp
-/

#print CategoryTheory.Limits.eq_zero_of_image_eq_zero /-
theorem eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) : f = 0 :=
  by rw [← image.fac f, w, has_zero_morphisms.comp_zero]
#align category_theory.limits.eq_zero_of_image_eq_zero CategoryTheory.Limits.eq_zero_of_image_eq_zero
-/

#print CategoryTheory.Limits.nonzero_image_of_nonzero /-
theorem nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f ≠ 0) : image.ι f ≠ 0 :=
  fun h => w (eq_zero_of_image_eq_zero h)
#align category_theory.limits.nonzero_image_of_nonzero CategoryTheory.Limits.nonzero_image_of_nonzero
-/

end

section

variable [HasZeroMorphisms D]

instance : HasZeroMorphisms (C ⥤ D) where Zero F G := ⟨{ app := fun X => 0 }⟩

/- warning: category_theory.limits.zero_app -> CategoryTheory.Limits.zero_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u3, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (G : CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (j : C), Eq.{succ u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F j) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 G j)) (CategoryTheory.NatTrans.app.{u1, u3, u2, u4} C _inst_1 D _inst_2 F G (OfNat.ofNat.{max u2 u3} (Quiver.Hom.{succ (max u2 u3), max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2))) F G) 0 (OfNat.mk.{max u2 u3} (Quiver.Hom.{succ (max u2 u3), max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2))) F G) 0 (Zero.zero.{max u2 u3} (Quiver.Hom.{succ (max u2 u3), max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2))) F G) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.CategoryTheory.Functor.hasZeroMorphisms.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3) F G)))) j) (OfNat.ofNat.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F j) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 G j)) 0 (OfNat.mk.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F j) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 G j)) 0 (Zero.zero.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F j) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 G j)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u3, u4} D _inst_2 _inst_3 (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F j) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 G j)))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroMorphisms.{u3, u4} D _inst_2] (F : CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (G : CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (j : C), Eq.{succ u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) j) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 G) j)) (CategoryTheory.NatTrans.app.{u1, u3, u2, u4} C _inst_1 D _inst_2 F G (OfNat.ofNat.{max u2 u3} (Quiver.Hom.{max (succ u2) (succ u3), max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2))) F G) 0 (Zero.toOfNat0.{max u2 u3} (Quiver.Hom.{max (succ u2) (succ u3), max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2))) F G) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.instHasZeroMorphismsFunctorCategory.{u1, u2, u3, u4} C _inst_1 D _inst_2 _inst_3) F G))) j) (OfNat.ofNat.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) j) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 G) j)) 0 (Zero.toOfNat0.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) j) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 G) j)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u3, u4} D _inst_2 _inst_3 (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) j) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 G) j))))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.zero_app CategoryTheory.Limits.zero_appₓ'. -/
@[simp]
theorem zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 :=
  rfl
#align category_theory.limits.zero_app CategoryTheory.Limits.zero_app

end

namespace IsZero

variable [HasZeroMorphisms C]

#print CategoryTheory.Limits.IsZero.eq_zero_of_src /-
theorem eq_zero_of_src {X Y : C} (o : IsZero X) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_src _ _
#align category_theory.limits.is_zero.eq_zero_of_src CategoryTheory.Limits.IsZero.eq_zero_of_src
-/

#print CategoryTheory.Limits.IsZero.eq_zero_of_tgt /-
theorem eq_zero_of_tgt {X Y : C} (o : IsZero Y) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_tgt _ _
#align category_theory.limits.is_zero.eq_zero_of_tgt CategoryTheory.Limits.IsZero.eq_zero_of_tgt
-/

#print CategoryTheory.Limits.IsZero.iff_id_eq_zero /-
theorem iff_id_eq_zero (X : C) : IsZero X ↔ 𝟙 X = 0 :=
  ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by rw [← id_comp f, ← id_comp default, h, zero_comp, zero_comp]⟩⟩,
      fun Y => ⟨⟨⟨0⟩, fun f => by rw [← comp_id f, ← comp_id default, h, comp_zero, comp_zero]⟩⟩⟩⟩
#align category_theory.limits.is_zero.iff_id_eq_zero CategoryTheory.Limits.IsZero.iff_id_eq_zero
-/

#print CategoryTheory.Limits.IsZero.of_mono_zero /-
theorem of_mono_zero (X Y : C) [Mono (0 : X ⟶ Y)] : IsZero X :=
  (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))
#align category_theory.limits.is_zero.of_mono_zero CategoryTheory.Limits.IsZero.of_mono_zero
-/

#print CategoryTheory.Limits.IsZero.of_epi_zero /-
theorem of_epi_zero (X Y : C) [Epi (0 : X ⟶ Y)] : IsZero Y :=
  (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))
#align category_theory.limits.is_zero.of_epi_zero CategoryTheory.Limits.IsZero.of_epi_zero
-/

#print CategoryTheory.Limits.IsZero.of_mono_eq_zero /-
theorem of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0) : IsZero X :=
  by
  subst h
  apply of_mono_zero X Y
#align category_theory.limits.is_zero.of_mono_eq_zero CategoryTheory.Limits.IsZero.of_mono_eq_zero
-/

#print CategoryTheory.Limits.IsZero.of_epi_eq_zero /-
theorem of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y :=
  by
  subst h
  apply of_epi_zero X Y
#align category_theory.limits.is_zero.of_epi_eq_zero CategoryTheory.Limits.IsZero.of_epi_eq_zero
-/

#print CategoryTheory.Limits.IsZero.iff_isSplitMono_eq_zero /-
theorem iff_isSplitMono_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔ f = 0 :=
  by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← category.id_comp f, h, zero_comp]
  · intro h
    rw [← is_split_mono.id f]
    simp [h]
#align category_theory.limits.is_zero.iff_is_split_mono_eq_zero CategoryTheory.Limits.IsZero.iff_isSplitMono_eq_zero
-/

#print CategoryTheory.Limits.IsZero.iff_isSplitEpi_eq_zero /-
theorem iff_isSplitEpi_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f = 0 :=
  by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← category.comp_id f, h, comp_zero]
  · intro h
    rw [← is_split_epi.id f]
    simp [h]
#align category_theory.limits.is_zero.iff_is_split_epi_eq_zero CategoryTheory.Limits.IsZero.iff_isSplitEpi_eq_zero
-/

#print CategoryTheory.Limits.IsZero.of_mono /-
theorem of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y) : IsZero X :=
  by
  have hf := i.eq_zero_of_tgt f
  subst hf
  exact is_zero.of_mono_zero X Y
#align category_theory.limits.is_zero.of_mono CategoryTheory.Limits.IsZero.of_mono
-/

#print CategoryTheory.Limits.IsZero.of_epi /-
theorem of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X) : IsZero Y :=
  by
  have hf := i.eq_zero_of_src f
  subst hf
  exact is_zero.of_epi_zero X Y
#align category_theory.limits.is_zero.of_epi CategoryTheory.Limits.IsZero.of_epi
-/

end IsZero

#print CategoryTheory.Limits.IsZero.hasZeroMorphisms /-
/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def IsZero.hasZeroMorphisms {O : C} (hO : IsZero O) : HasZeroMorphisms C
    where
  Zero X Y := { zero := hO.from X ≫ hO.to Y }
  zero_comp X Y Z f := by
    rw [category.assoc]
    congr
    apply hO.eq_of_src
  comp_zero X Y Z f := by
    rw [← category.assoc]
    congr
    apply hO.eq_of_tgt
#align category_theory.limits.is_zero.has_zero_morphisms CategoryTheory.Limits.IsZero.hasZeroMorphisms
-/

namespace HasZeroObject

variable [HasZeroObject C]

open ZeroObject

#print CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject /-
/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def zeroMorphismsOfZeroObject : HasZeroMorphisms C
    where
  Zero X Y := { zero := (default : X ⟶ 0) ≫ default }
  zero_comp X Y Z f := by
    dsimp only [Zero.zero]
    rw [category.assoc]
    congr
  comp_zero X Y Z f := by
    dsimp only [Zero.zero]
    rw [← category.assoc]
    congr
#align category_theory.limits.has_zero_object.zero_morphisms_of_zero_object CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject
-/

section HasZeroMorphisms

variable [HasZeroMorphisms C]

#print CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_hom /-
@[simp]
theorem zeroIsoIsInitial_hom {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).Hom = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_initial_hom CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_hom
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_inv /-
@[simp]
theorem zeroIsoIsInitial_inv {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).inv = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_initial_inv CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_inv
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_hom /-
@[simp]
theorem zeroIsoIsTerminal_hom {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).Hom = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_terminal_hom CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_hom
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_inv /-
@[simp]
theorem zeroIsoIsTerminal_inv {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).inv = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_terminal_inv CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_inv
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_hom /-
@[simp]
theorem zeroIsoInitial_hom [HasInitial C] : zeroIsoInitial.Hom = (0 : 0 ⟶ ⊥_ C) := by ext
#align category_theory.limits.has_zero_object.zero_iso_initial_hom CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_hom
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_inv /-
@[simp]
theorem zeroIsoInitial_inv [HasInitial C] : zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0) := by ext
#align category_theory.limits.has_zero_object.zero_iso_initial_inv CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_inv
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_hom /-
@[simp]
theorem zeroIsoTerminal_hom [HasTerminal C] : zeroIsoTerminal.Hom = (0 : 0 ⟶ ⊤_ C) := by ext
#align category_theory.limits.has_zero_object.zero_iso_terminal_hom CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_hom
-/

#print CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_inv /-
@[simp]
theorem zeroIsoTerminal_inv [HasTerminal C] : zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0) := by ext
#align category_theory.limits.has_zero_object.zero_iso_terminal_inv CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_inv
-/

end HasZeroMorphisms

open ZeroObject

instance {B : Type _} [Category B] : HasZeroObject (B ⥤ C) :=
  (((CategoryTheory.Functor.const B).obj (0 : C)).IsZero fun X => isZero_zero _).HasZeroObject

end HasZeroObject

open ZeroObject

variable {D}

/- warning: category_theory.limits.is_zero.map -> CategoryTheory.Limits.IsZero.map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u3, u4} D _inst_2] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u3, u4} D _inst_2] {F : CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.Limits.IsZero.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) F) -> (forall {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), Eq.{succ u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Functor.map.{u1, u3, u2, u4} C _inst_1 D _inst_2 F X Y f) (OfNat.ofNat.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F Y)) 0 (OfNat.mk.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F Y)) 0 (Zero.zero.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F Y)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u3, u4} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 F Y))))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u3, u4} D _inst_2] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u3, u4} D _inst_2] {F : CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2}, (CategoryTheory.Limits.IsZero.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) F) -> (forall {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), Eq.{succ u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) Y)) (Prefunctor.map.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) X Y f) (OfNat.ofNat.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) Y)) 0 (Zero.toOfNat0.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) Y)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u3, u4} D _inst_2 _inst_4 (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 F) Y)))))
Case conversion may be inaccurate. Consider using '#align category_theory.limits.is_zero.map CategoryTheory.Limits.IsZero.mapₓ'. -/
@[simp]
theorem IsZero.map [HasZeroObject D] [HasZeroMorphisms D] {F : C ⥤ D} (hF : IsZero F) {X Y : C}
    (f : X ⟶ Y) : F.map f = 0 :=
  (hF.obj _).eq_of_src _ _
#align category_theory.limits.is_zero.map CategoryTheory.Limits.IsZero.map

/- warning: category_theory.functor.zero_obj -> CategoryTheory.Functor.zero_obj is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u3, u4} D _inst_2] (X : C), CategoryTheory.Limits.IsZero.{u3, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (OfNat.mk.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u3, u4} D _inst_2] (X : C), CategoryTheory.Limits.IsZero.{u3, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.zero_obj CategoryTheory.Functor.zero_objₓ'. -/
@[simp]
theorem CategoryTheory.Functor.zero_obj [HasZeroObject D] (X : C) : IsZero ((0 : C ⥤ D).obj X) :=
  (isZero_zero _).obj _
#align category_theory.functor.zero_obj CategoryTheory.Functor.zero_obj

/- warning: category_theory.zero_map -> CategoryTheory.zero_map is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u3, u4} D _inst_2] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u3, u4} D _inst_2] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), Eq.{succ u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (OfNat.mk.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (OfNat.mk.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) Y)) (CategoryTheory.Functor.map.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (OfNat.mk.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X Y f) (OfNat.ofNat.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) Y)) 0 (OfNat.mk.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) Y)) 0 (Zero.zero.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) Y)) (CategoryTheory.Limits.HasZeroMorphisms.hasZero.{u3, u4} D _inst_2 _inst_4 (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) X) (CategoryTheory.Functor.obj.{u1, u3, u2, u4} C _inst_1 D _inst_2 (Zero.zero.{max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max u1 u3 u2 u4} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.CategoryTheory.Functor.hasZeroObject.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))) Y)))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u3, u4} D] [_inst_3 : CategoryTheory.Limits.HasZeroObject.{u3, u4} D _inst_2] [_inst_4 : CategoryTheory.Limits.HasZeroMorphisms.{u3, u4} D _inst_2] {X : C} {Y : C} (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X Y), Eq.{succ u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) Y)) (Prefunctor.map.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X Y f) (OfNat.ofNat.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) Y)) 0 (Zero.toOfNat0.{u3} (Quiver.Hom.{succ u3, u4} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) Y)) (CategoryTheory.Limits.HasZeroMorphisms.Zero.{u3, u4} D _inst_2 _inst_4 (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) X) (Prefunctor.obj.{succ u1, succ u3, u2, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u3, u4} D (CategoryTheory.Category.toCategoryStruct.{u3, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u3, u2, u4} C _inst_1 D _inst_2 (OfNat.ofNat.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) 0 (Zero.toOfNat0.{max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.zero'.{max u2 u3, max (max (max u2 u4) u1) u3} (CategoryTheory.Functor.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u3, u2, u4} C _inst_1 D _inst_2) (CategoryTheory.Limits.HasZeroObject.instHasZeroObjectFunctorCategory.{u3, u4, u2, u1} D _inst_2 _inst_3 C _inst_1))))) Y))))
Case conversion may be inaccurate. Consider using '#align category_theory.zero_map CategoryTheory.zero_mapₓ'. -/
@[simp]
theorem CategoryTheory.zero_map [HasZeroObject D] [HasZeroMorphisms D] {X Y : C} (f : X ⟶ Y) :
    (0 : C ⥤ D).map f = 0 :=
  (isZero_zero _).map _
#align category_theory.zero_map CategoryTheory.zero_map

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

#print CategoryTheory.Limits.id_zero /-
@[simp]
theorem id_zero : 𝟙 (0 : C) = (0 : 0 ⟶ 0) := by ext
#align category_theory.limits.id_zero CategoryTheory.Limits.id_zero
-/

#print CategoryTheory.Limits.zero_of_to_zero /-
-- This can't be a `simp` lemma because the left hand side would be a metavariable.
/-- An arrow ending in the zero object is zero -/
theorem zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 := by ext
#align category_theory.limits.zero_of_to_zero CategoryTheory.Limits.zero_of_to_zero
-/

#print CategoryTheory.Limits.zero_of_target_iso_zero /-
theorem zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 :=
  by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [iso.hom_inv_id, id_comp, comp_id]
  simpa using h
#align category_theory.limits.zero_of_target_iso_zero CategoryTheory.Limits.zero_of_target_iso_zero
-/

#print CategoryTheory.Limits.zero_of_from_zero /-
/-- An arrow starting at the zero object is zero -/
theorem zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 := by ext
#align category_theory.limits.zero_of_from_zero CategoryTheory.Limits.zero_of_from_zero
-/

#print CategoryTheory.Limits.zero_of_source_iso_zero /-
theorem zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 :=
  by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [iso.hom_inv_id_assoc, id_comp, comp_id]
  simpa using h
#align category_theory.limits.zero_of_source_iso_zero CategoryTheory.Limits.zero_of_source_iso_zero
-/

#print CategoryTheory.Limits.zero_of_source_iso_zero' /-
theorem zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0) : f = 0 :=
  zero_of_source_iso_zero f (Nonempty.some i)
#align category_theory.limits.zero_of_source_iso_zero' CategoryTheory.Limits.zero_of_source_iso_zero'
-/

#print CategoryTheory.Limits.zero_of_target_iso_zero' /-
theorem zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0) : f = 0 :=
  zero_of_target_iso_zero f (Nonempty.some i)
#align category_theory.limits.zero_of_target_iso_zero' CategoryTheory.Limits.zero_of_target_iso_zero'
-/

#print CategoryTheory.Limits.mono_of_source_iso_zero /-
theorem mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : Mono f :=
  ⟨fun Z g h w => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩
#align category_theory.limits.mono_of_source_iso_zero CategoryTheory.Limits.mono_of_source_iso_zero
-/

#print CategoryTheory.Limits.epi_of_target_iso_zero /-
theorem epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f :=
  ⟨fun Z g h w => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩
#align category_theory.limits.epi_of_target_iso_zero CategoryTheory.Limits.epi_of_target_iso_zero
-/

#print CategoryTheory.Limits.idZeroEquivIsoZero /-
/-- An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
def idZeroEquivIsoZero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0)
    where
  toFun h :=
    { Hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.limits.id_zero_equiv_iso_zero CategoryTheory.Limits.idZeroEquivIsoZero
-/

#print CategoryTheory.Limits.idZeroEquivIsoZero_apply_hom /-
@[simp]
theorem idZeroEquivIsoZero_apply_hom (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).Hom = 0 :=
  rfl
#align category_theory.limits.id_zero_equiv_iso_zero_apply_hom CategoryTheory.Limits.idZeroEquivIsoZero_apply_hom
-/

#print CategoryTheory.Limits.idZeroEquivIsoZero_apply_inv /-
@[simp]
theorem idZeroEquivIsoZero_apply_inv (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).inv = 0 :=
  rfl
#align category_theory.limits.id_zero_equiv_iso_zero_apply_inv CategoryTheory.Limits.idZeroEquivIsoZero_apply_inv
-/

#print CategoryTheory.Limits.isoZeroOfMonoZero /-
/-- If `0 : X ⟶ Y` is an monomorphism, then `X ≅ 0`. -/
@[simps]
def isoZeroOfMonoZero {X Y : C} (h : Mono (0 : X ⟶ Y)) : X ≅ 0
    where
  Hom := 0
  inv := 0
  hom_inv_id' := (cancel_mono (0 : X ⟶ Y)).mp (by simp)
#align category_theory.limits.iso_zero_of_mono_zero CategoryTheory.Limits.isoZeroOfMonoZero
-/

#print CategoryTheory.Limits.isoZeroOfEpiZero /-
/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
def isoZeroOfEpiZero {X Y : C} (h : Epi (0 : X ⟶ Y)) : Y ≅ 0
    where
  Hom := 0
  inv := 0
  hom_inv_id' := (cancel_epi (0 : X ⟶ Y)).mp (by simp)
#align category_theory.limits.iso_zero_of_epi_zero CategoryTheory.Limits.isoZeroOfEpiZero
-/

#print CategoryTheory.Limits.isoZeroOfMonoEqZero /-
/-- If a monomorphism out of `X` is zero, then `X ≅ 0`. -/
def isoZeroOfMonoEqZero {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0) : X ≅ 0 :=
  by
  subst h
  apply iso_zero_of_mono_zero ‹_›
#align category_theory.limits.iso_zero_of_mono_eq_zero CategoryTheory.Limits.isoZeroOfMonoEqZero
-/

#print CategoryTheory.Limits.isoZeroOfEpiEqZero /-
/-- If an epimorphism in to `Y` is zero, then `Y ≅ 0`. -/
def isoZeroOfEpiEqZero {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0) : Y ≅ 0 :=
  by
  subst h
  apply iso_zero_of_epi_zero ‹_›
#align category_theory.limits.iso_zero_of_epi_eq_zero CategoryTheory.Limits.isoZeroOfEpiEqZero
-/

#print CategoryTheory.Limits.isoOfIsIsomorphicZero /-
/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
def isoOfIsIsomorphicZero {X : C} (P : IsIsomorphic X 0) : X ≅ 0
    where
  Hom := 0
  inv := 0
  hom_inv_id' := by
    cases P
    rw [← P.hom_inv_id]
    rw [← category.id_comp P.inv]
    simp
  inv_hom_id' := by simp
#align category_theory.limits.iso_of_is_isomorphic_zero CategoryTheory.Limits.isoOfIsIsomorphicZero
-/

end

section IsIso

variable [HasZeroMorphisms C]

#print CategoryTheory.Limits.isIsoZeroEquiv /-
/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
@[simps]
def isIsoZeroEquiv (X Y : C) : IsIso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0
    where
  toFun := by
    intro i
    rw [← is_iso.hom_inv_id (0 : X ⟶ Y)]
    rw [← is_iso.inv_hom_id (0 : X ⟶ Y)]
    simp
  invFun h := ⟨⟨(0 : Y ⟶ X), by tidy⟩⟩
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.limits.is_iso_zero_equiv CategoryTheory.Limits.isIsoZeroEquiv
-/

#print CategoryTheory.Limits.isIsoZeroSelfEquiv /-
/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def isIsoZeroSelfEquiv (X : C) : IsIso (0 : X ⟶ X) ≃ 𝟙 X = 0 := by simpa using is_iso_zero_equiv X X
#align category_theory.limits.is_iso_zero_self_equiv CategoryTheory.Limits.isIsoZeroSelfEquiv
-/

variable [HasZeroObject C]

open ZeroObject

#print CategoryTheory.Limits.isIsoZeroEquivIsoZero /-
/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
def isIsoZeroEquivIsoZero (X Y : C) : IsIso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0) :=
  by
  -- This is lame, because `prod` can't cope with `Prop`, so we can't use `equiv.prod_congr`.
  refine' (is_iso_zero_equiv X Y).trans _
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    exact (id_zero_equiv_iso_zero X).symm eX
    exact (id_zero_equiv_iso_zero Y).symm eY
  · rintro ⟨hX, hY⟩
    fconstructor
    exact (id_zero_equiv_iso_zero X) hX
    exact (id_zero_equiv_iso_zero Y) hY
  · tidy
  · tidy
#align category_theory.limits.is_iso_zero_equiv_iso_zero CategoryTheory.Limits.isIsoZeroEquivIsoZero
-/

#print CategoryTheory.Limits.isIso_of_source_target_iso_zero /-
theorem isIso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) : IsIso f :=
  by
  rw [zero_of_source_iso_zero f i]
  exact (is_iso_zero_equiv_iso_zero _ _).invFun ⟨i, j⟩
#align category_theory.limits.is_iso_of_source_target_iso_zero CategoryTheory.Limits.isIso_of_source_target_iso_zero
-/

#print CategoryTheory.Limits.isIsoZeroSelfEquivIsoZero /-
/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def isIsoZeroSelfEquivIsoZero (X : C) : IsIso (0 : X ⟶ X) ≃ (X ≅ 0) :=
  (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv
#align category_theory.limits.is_iso_zero_self_equiv_iso_zero CategoryTheory.Limits.isIsoZeroSelfEquivIsoZero
-/

end IsIso

#print CategoryTheory.Limits.hasZeroObject_of_hasInitial_object /-
/-- If there are zero morphisms, any initial object is a zero object. -/
theorem hasZeroObject_of_hasInitial_object [HasZeroMorphisms C] [HasInitial C] : HasZeroObject C :=
  by
  refine' ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by tidy⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (category.comp_id _).symm
    _ = f ≫ 0 := by congr
    _ = 0 := has_zero_morphisms.comp_zero _ _
    
#align category_theory.limits.has_zero_object_of_has_initial_object CategoryTheory.Limits.hasZeroObject_of_hasInitial_object
-/

#print CategoryTheory.Limits.hasZeroObject_of_hasTerminal_object /-
/-- If there are zero morphisms, any terminal object is a zero object. -/
theorem hasZeroObject_of_hasTerminal_object [HasZeroMorphisms C] [HasTerminal C] :
    HasZeroObject C :=
  by
  refine' ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, by tidy⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (category.id_comp _).symm
    _ = 0 ≫ f := by congr
    _ = 0 := zero_comp
    
#align category_theory.limits.has_zero_object_of_has_terminal_object CategoryTheory.Limits.hasZeroObject_of_hasTerminal_object
-/

section Image

variable [HasZeroMorphisms C]

#print CategoryTheory.Limits.image_ι_comp_eq_zero /-
theorem image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
    [Epi (factorThruImage f)] (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
  zero_of_epi_comp (factorThruImage f) <| by simp [h]
#align category_theory.limits.image_ι_comp_eq_zero CategoryTheory.Limits.image_ι_comp_eq_zero
-/

#print CategoryTheory.Limits.comp_factorThruImage_eq_zero /-
theorem comp_factorThruImage_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
    (h : f ≫ g = 0) : f ≫ factorThruImage g = 0 :=
  zero_of_comp_mono (image.ι g) <| by simp [h]
#align category_theory.limits.comp_factor_thru_image_eq_zero CategoryTheory.Limits.comp_factorThruImage_eq_zero
-/

variable [HasZeroObject C]

open ZeroObject

#print CategoryTheory.Limits.monoFactorisationZero /-
/-- The zero morphism has a `mono_factorisation` through the zero object.
-/
@[simps]
def monoFactorisationZero (X Y : C) : MonoFactorisation (0 : X ⟶ Y)
    where
  i := 0
  m := 0
  e := 0
#align category_theory.limits.mono_factorisation_zero CategoryTheory.Limits.monoFactorisationZero
-/

#print CategoryTheory.Limits.imageFactorisationZero /-
/-- The factorisation through the zero object is an image factorisation.
-/
def imageFactorisationZero (X Y : C) : ImageFactorisation (0 : X ⟶ Y)
    where
  f := monoFactorisationZero X Y
  IsImage := { lift := fun F' => 0 }
#align category_theory.limits.image_factorisation_zero CategoryTheory.Limits.imageFactorisationZero
-/

#print CategoryTheory.Limits.hasImage_zero /-
instance hasImage_zero {X Y : C} : HasImage (0 : X ⟶ Y) :=
  HasImage.mk <| imageFactorisationZero _ _
#align category_theory.limits.has_image_zero CategoryTheory.Limits.hasImage_zero
-/

#print CategoryTheory.Limits.imageZero /-
/-- The image of a zero morphism is the zero object. -/
def imageZero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
  IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).IsImage
#align category_theory.limits.image_zero CategoryTheory.Limits.imageZero
-/

#print CategoryTheory.Limits.imageZero' /-
/-- The image of a morphism which is equal to zero is the zero object. -/
def imageZero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] : image f ≅ 0 :=
  image.eqToIso h ≪≫ imageZero
#align category_theory.limits.image_zero' CategoryTheory.Limits.imageZero'
-/

#print CategoryTheory.Limits.image.ι_zero /-
@[simp]
theorem image.ι_zero {X Y : C} [HasImage (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 :=
  by
  rw [← image.lift_fac (mono_factorisation_zero X Y)]
  simp
#align category_theory.limits.image.ι_zero CategoryTheory.Limits.image.ι_zero
-/

#print CategoryTheory.Limits.image.ι_zero' /-
/-- If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
theorem image.ι_zero' [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] :
    image.ι f = 0 := by
  rw [image.eq_fac h]
  simp
#align category_theory.limits.image.ι_zero' CategoryTheory.Limits.image.ι_zero'
-/

end Image

#print CategoryTheory.Limits.isSplitMono_sigma_ι /-
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_sigma_ι {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasColimit (Discrete.functor f)] (b : β) : IsSplitMono (Sigma.ι f b) :=
  IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }
#align category_theory.limits.is_split_mono_sigma_ι CategoryTheory.Limits.isSplitMono_sigma_ι
-/

#print CategoryTheory.Limits.isSplitEpi_pi_π /-
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_pi_π {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasLimit (Discrete.functor f)] (b : β) : IsSplitEpi (Pi.π f b) :=
  IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }
#align category_theory.limits.is_split_epi_pi_π CategoryTheory.Limits.isSplitEpi_pi_π
-/

#print CategoryTheory.Limits.isSplitMono_coprod_inl /-
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_coprod_inl [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inl : X ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }
#align category_theory.limits.is_split_mono_coprod_inl CategoryTheory.Limits.isSplitMono_coprod_inl
-/

#print CategoryTheory.Limits.isSplitMono_coprod_inr /-
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_coprod_inr [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }
#align category_theory.limits.is_split_mono_coprod_inr CategoryTheory.Limits.isSplitMono_coprod_inr
-/

#print CategoryTheory.Limits.isSplitEpi_prod_fst /-
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_prod_fst [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.fst : X ⨯ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }
#align category_theory.limits.is_split_epi_prod_fst CategoryTheory.Limits.isSplitEpi_prod_fst
-/

#print CategoryTheory.Limits.isSplitEpi_prod_snd /-
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_prod_snd [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.snd : X ⨯ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }
#align category_theory.limits.is_split_epi_prod_snd CategoryTheory.Limits.isSplitEpi_prod_snd
-/

end CategoryTheory.Limits

