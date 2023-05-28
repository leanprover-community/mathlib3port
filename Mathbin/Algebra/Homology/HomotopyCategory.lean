/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.homotopy_category
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.CategoryTheory.Quotient

/-!
# The homotopy category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`homotopy_category V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/


universe v u

open Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable (V : Type u) [Category.{v} V] [Preadditive V]

variable (c : ComplexShape ι)

#print homotopic /-
/-- The congruence on `homological_complex V c` given by the existence of a homotopy.
-/
def homotopic : HomRel (HomologicalComplex V c) := fun C D f g => Nonempty (Homotopy f g)
#align homotopic homotopic
-/

#print homotopy_congruence /-
instance homotopy_congruence : Congruence (homotopic V c)
    where
  IsEquiv C D :=
    { refl := fun C => ⟨Homotopy.refl C⟩
      symm := fun f g ⟨w⟩ => ⟨w.symm⟩
      trans := fun f g h ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  compLeft := fun E F G m₁ m₂ g ⟨i⟩ => ⟨i.compLeft _⟩
  compRight := fun E F G f m₁ m₂ ⟨i⟩ => ⟨i.compRight _⟩
#align homotopy_congruence homotopy_congruence
-/

#print HomotopyCategory /-
/-- `homotopy_category V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic. -/
def HomotopyCategory :=
  CategoryTheory.Quotient (homotopic V c)deriving Category
#align homotopy_category HomotopyCategory
-/

-- TODO the homotopy_category is preadditive
namespace HomotopyCategory

#print HomotopyCategory.quotient /-
/-- The quotient functor from complexes to the homotopy category. -/
def quotient : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _
#align homotopy_category.quotient HomotopyCategory.quotient
-/

open ZeroObject

-- TODO upgrade this to `has_zero_object`, presumably for any `quotient`.
instance [HasZeroObject V] : Inhabited (HomotopyCategory V c) :=
  ⟨(quotient V c).obj 0⟩

variable {V c}

/- warning: homotopy_category.quotient_obj_as -> HomotopyCategory.quotient_obj_as is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} (C : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c), Eq.{max (succ u2) (succ u3) (succ u1)} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Quotient.as.{max u2 u3 u1, max u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (homotopic.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.Functor.obj.{max u3 u1, max u3 u1, max u2 u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c) C)) C
but is expected to have type
  forall {ι : Type.{u1}} {V : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u2, u3} V] [_inst_2 : CategoryTheory.Preadditive.{u2, u3} V _inst_1] {c : ComplexShape.{u1} ι} (C : HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.Quotient.as.{max (max u3 u2) u1, max u2 u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (homotopic.{u2, u3, u1} ι V _inst_1 _inst_2 c) (Prefunctor.obj.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (max u3 u2) u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c))) (HomotopyCategory.{u2, u3, u1} ι V _inst_1 _inst_2 c) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max (max u3 u2) u1} (HomotopyCategory.{u2, u3, u1} ι V _inst_1 _inst_2 c) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max (max u3 u2) u1} (HomotopyCategory.{u2, u3, u1} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u2, u3, u1} V _inst_1 _inst_2 ι c))) (CategoryTheory.Functor.toPrefunctor.{max u2 u1, max u2 u1, max (max u3 u2) u1, max (max u3 u2) u1} (HomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u3, u1} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u3} V _inst_1 _inst_2) c) (HomotopyCategory.{u2, u3, u1} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u2, u3, u1} V _inst_1 _inst_2 ι c) (HomotopyCategory.quotient.{u2, u3, u1} ι V _inst_1 _inst_2 c)) C)) C
Case conversion may be inaccurate. Consider using '#align homotopy_category.quotient_obj_as HomotopyCategory.quotient_obj_asₓ'. -/
@[simp]
theorem quotient_obj_as (C : HomologicalComplex V c) : ((quotient V c).obj C).as = C :=
  rfl
#align homotopy_category.quotient_obj_as HomotopyCategory.quotient_obj_as

/- warning: homotopy_category.quotient_map_out -> HomotopyCategory.quotient_map_out is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.quotient_map_out HomotopyCategory.quotient_map_outₓ'. -/
@[simp]
theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (quotient V c).map f.out = f :=
  Quot.out_eq _
#align homotopy_category.quotient_map_out HomotopyCategory.quotient_map_out

/- warning: homotopy_category.eq_of_homotopy -> HomotopyCategory.eq_of_homotopy is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.eq_of_homotopy HomotopyCategory.eq_of_homotopyₓ'. -/
theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
    (quotient V c).map f = (quotient V c).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩
#align homotopy_category.eq_of_homotopy HomotopyCategory.eq_of_homotopy

/- warning: homotopy_category.homotopy_of_eq -> HomotopyCategory.homotopyOfEq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.homotopy_of_eq HomotopyCategory.homotopyOfEqₓ'. -/
/-- If two chain maps become equal in the homotopy category, then they are homotopic. -/
def homotopyOfEq {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (w : (quotient V c).map f = (quotient V c).map g) : Homotopy f g :=
  ((Quotient.functor_map_eq_iff _ _ _).mp w).some
#align homotopy_category.homotopy_of_eq HomotopyCategory.homotopyOfEq

/- warning: homotopy_category.homotopy_out_map -> HomotopyCategory.homotopyOutMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.homotopy_out_map HomotopyCategory.homotopyOutMapₓ'. -/
/-- An arbitrarily chosen representation of the image of a chain map in the homotopy category
is homotopic to the original chain map.
-/
def homotopyOutMap {C D : HomologicalComplex V c} (f : C ⟶ D) :
    Homotopy ((quotient V c).map f).out f :=
  by
  apply homotopy_of_eq
  simp
#align homotopy_category.homotopy_out_map HomotopyCategory.homotopyOutMap

/- warning: homotopy_category.quotient_map_out_comp_out -> HomotopyCategory.quotient_map_out_comp_out is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.quotient_map_out_comp_out HomotopyCategory.quotient_map_out_comp_outₓ'. -/
@[simp]
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
    (quotient V c).map (Quot.out f ≫ Quot.out g) = f ≫ g := by
  conv_rhs => erw [← quotient_map_out f, ← quotient_map_out g, ← (Quotient V c).map_comp]
#align homotopy_category.quotient_map_out_comp_out HomotopyCategory.quotient_map_out_comp_out

/- warning: homotopy_category.iso_of_homotopy_equiv -> HomotopyCategory.isoOfHomotopyEquiv is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} {C : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c} {D : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c}, (HomotopyEquiv.{u1, u2, u3} ι V _inst_1 _inst_2 c C D) -> (CategoryTheory.Iso.{max u3 u1, max u2 u3 u1} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (CategoryTheory.Functor.obj.{max u3 u1, max u3 u1, max u2 u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c) C) (CategoryTheory.Functor.obj.{max u3 u1, max u3 u1, max u2 u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c) D))
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} {C : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c} {D : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c}, (HomotopyEquiv.{u1, u2, u3} ι V _inst_1 _inst_2 c C D) -> (CategoryTheory.Iso.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (Prefunctor.obj.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c))) (CategoryTheory.Functor.toPrefunctor.{max u1 u3, max u1 u3, max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c)) C) (Prefunctor.obj.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c))) (CategoryTheory.Functor.toPrefunctor.{max u1 u3, max u1 u3, max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c)) D))
Case conversion may be inaccurate. Consider using '#align homotopy_category.iso_of_homotopy_equiv HomotopyCategory.isoOfHomotopyEquivₓ'. -/
/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
def isoOfHomotopyEquiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) :
    (quotient V c).obj C ≅ (quotient V c).obj D
    where
  Hom := (quotient V c).map f.Hom
  inv := (quotient V c).map f.inv
  hom_inv_id' := by
    rw [← (Quotient V c).map_comp, ← (Quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopy_hom_inv_id
  inv_hom_id' := by
    rw [← (Quotient V c).map_comp, ← (Quotient V c).map_id]
    exact eq_of_homotopy _ _ f.homotopy_inv_hom_id
#align homotopy_category.iso_of_homotopy_equiv HomotopyCategory.isoOfHomotopyEquiv

/- warning: homotopy_category.homotopy_equiv_of_iso -> HomotopyCategory.homotopyEquivOfIso is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} {C : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c} {D : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c}, (CategoryTheory.Iso.{max u3 u1, max u2 u3 u1} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (CategoryTheory.Functor.obj.{max u3 u1, max u3 u1, max u2 u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c) C) (CategoryTheory.Functor.obj.{max u3 u1, max u3 u1, max u2 u3 u1, max u2 u3 u1} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c) D)) -> (HomotopyEquiv.{u1, u2, u3} ι V _inst_1 _inst_2 c C D)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {c : ComplexShape.{u3} ι} {C : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c} {D : HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c}, (CategoryTheory.Iso.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (Prefunctor.obj.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c))) (CategoryTheory.Functor.toPrefunctor.{max u1 u3, max u1 u3, max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c)) C) (Prefunctor.obj.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c))) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (CategoryTheory.Category.toCategoryStruct.{max u1 u3, max (max u2 u1) u3} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c))) (CategoryTheory.Functor.toPrefunctor.{max u1 u3, max u1 u3, max (max u2 u1) u3, max (max u2 u1) u3} (HomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u1, u2} V _inst_1 _inst_2) c) (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.quotient.{u1, u2, u3} ι V _inst_1 _inst_2 c)) D)) -> (HomotopyEquiv.{u1, u2, u3} ι V _inst_1 _inst_2 c C D)
Case conversion may be inaccurate. Consider using '#align homotopy_category.homotopy_equiv_of_iso HomotopyCategory.homotopyEquivOfIsoₓ'. -/
/-- If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent. -/
def homotopyEquivOfIso {C D : HomologicalComplex V c}
    (i : (quotient V c).obj C ≅ (quotient V c).obj D) : HomotopyEquiv C D
    where
  Hom := Quot.out i.Hom
  inv := Quot.out i.inv
  homotopyHomInvId := homotopyOfEq _ _ (by simp; rfl)
  homotopyInvHomId := homotopyOfEq _ _ (by simp; rfl)
#align homotopy_category.homotopy_equiv_of_iso HomotopyCategory.homotopyEquivOfIso

variable (V c) [HasEqualizers V] [HasImages V] [HasImageMaps V] [HasCokernels V]

#print HomotopyCategory.homologyFunctor /-
/-- The `i`-th homology, as a functor from the homotopy category. -/
def homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V :=
  CategoryTheory.Quotient.lift _ (homologyFunctor V c i) fun C D f g ⟨h⟩ =>
    homology_map_eq_of_homotopy h i
#align homotopy_category.homology_functor HomotopyCategory.homologyFunctor
-/

#print HomotopyCategory.homologyFactors /-
/-- The homology functor on the homotopy category is just the usual homology functor. -/
def homologyFactors (i : ι) : quotient V c ⋙ homologyFunctor V c i ≅ homologyFunctor V c i :=
  CategoryTheory.Quotient.lift.isLift _ _ _
#align homotopy_category.homology_factors HomotopyCategory.homologyFactors
-/

/- warning: homotopy_category.homology_factors_hom_app -> HomotopyCategory.homologyFactors_hom_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.homology_factors_hom_app HomotopyCategory.homologyFactors_hom_appₓ'. -/
@[simp]
theorem homologyFactors_hom_app (i : ι) (C : HomologicalComplex V c) :
    (homologyFactors V c i).Hom.app C = 𝟙 _ :=
  rfl
#align homotopy_category.homology_factors_hom_app HomotopyCategory.homologyFactors_hom_app

/- warning: homotopy_category.homology_factors_inv_app -> HomotopyCategory.homologyFactors_inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.homology_factors_inv_app HomotopyCategory.homologyFactors_inv_appₓ'. -/
@[simp]
theorem homologyFactors_inv_app (i : ι) (C : HomologicalComplex V c) :
    (homologyFactors V c i).inv.app C = 𝟙 _ :=
  rfl
#align homotopy_category.homology_factors_inv_app HomotopyCategory.homologyFactors_inv_app

/- warning: homotopy_category.homology_functor_map_factors -> HomotopyCategory.homologyFunctor_map_factors is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homotopy_category.homology_functor_map_factors HomotopyCategory.homologyFunctor_map_factorsₓ'. -/
theorem homologyFunctor_map_factors (i : ι) {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (homologyFunctor V c i).map f = ((homologyFunctor V c i).map ((quotient V c).map f) : _) :=
  (CategoryTheory.Quotient.lift_map_functor_map _ (homologyFunctor V c i) _ f).symm
#align homotopy_category.homology_functor_map_factors HomotopyCategory.homologyFunctor_map_factors

end HomotopyCategory

namespace CategoryTheory

variable {V} {W : Type _} [Category W] [Preadditive W]

/- warning: category_theory.functor.map_homotopy_category -> CategoryTheory.Functor.mapHomotopyCategory is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (c : ComplexShape.{u3} ι) (F : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 F], CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (c : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) [F : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 c] (_inst_5 : ComplexShape.{u3} ι), CategoryTheory.Functor.{max u1 u3, max u3 u5, max (max u3 u2) u1, max (max u3 u4) u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 _inst_5) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι _inst_5) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 _inst_5) (instCategoryHomotopyCategory.{u5, u4, u3} W _inst_3 _inst_4 ι _inst_5)
Case conversion may be inaccurate. Consider using '#align category_theory.functor.map_homotopy_category CategoryTheory.Functor.mapHomotopyCategoryₓ'. -/
/-- An additive functor induces a functor between homotopy categories. -/
@[simps]
def Functor.mapHomotopyCategory (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    HomotopyCategory V c ⥤ HomotopyCategory W c
    where
  obj C := (HomotopyCategory.quotient W c).obj ((F.mapHomologicalComplex c).obj C.as)
  map C D f := (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map (Quot.out f))
  map_id' C := by
    rw [← (HomotopyCategory.quotient W c).map_id]
    apply HomotopyCategory.eq_of_homotopy
    rw [← (F.map_homological_complex c).map_id]
    apply F.map_homotopy
    apply HomotopyCategory.homotopyOfEq
    exact Quot.out_eq _
  map_comp' C D E f g := by
    rw [← (HomotopyCategory.quotient W c).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    rw [← (F.map_homological_complex c).map_comp]
    apply F.map_homotopy
    apply HomotopyCategory.homotopyOfEq
    convert Quot.out_eq _
    exact HomotopyCategory.quotient_map_out_comp_out _ _
#align category_theory.functor.map_homotopy_category CategoryTheory.Functor.mapHomotopyCategory

/- warning: category_theory.nat_trans.map_homotopy_category -> CategoryTheory.NatTrans.mapHomotopyCategory is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] {F : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3} {G : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3} [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 F] [_inst_6 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 G], (Quiver.Hom.{succ (max u2 u5), max u1 u5 u2 u4} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max u1 u5 u2 u4} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max u1 u5 u2 u4} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.Functor.category.{u1, u5, u2, u4} V _inst_1 W _inst_3))) F G) -> (forall (c : ComplexShape.{u3} ι), Quiver.Hom.{succ (max (max u2 u3 u1) u3 u5), max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u3 u1) u3 u5, max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u3 u1) u3 u5, max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.Functor.category.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)))) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 c F _inst_5) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 c G _inst_6))
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] {F : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3} {G : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3} [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 F] [_inst_6 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 G], (Quiver.Hom.{max (succ u2) (succ u5), max (max (max u2 u1) u4) u5} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u5, max (max (max u2 u1) u4) u5} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max (max (max u2 u1) u4) u5} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.Functor.category.{u1, u5, u2, u4} V _inst_1 W _inst_3))) F G) -> (forall (c : ComplexShape.{u3} ι), Quiver.Hom.{max (max (max (succ u2) (succ u1)) (succ u3)) (succ u5), max (max (max (max u2 u1) u3) u4) u5} (CategoryTheory.Functor.{max u1 u3, max u3 u5, max (max u3 u2) u1, max (max u3 u4) u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u5, u4, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u2 u1) u3) u5, max (max (max (max u2 u1) u3) u4) u5} (CategoryTheory.Functor.{max u1 u3, max u3 u5, max (max u3 u2) u1, max (max u3 u4) u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u5, u4, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.Category.toCategoryStruct.{max (max (max u2 u1) u3) u5, max (max (max (max u2 u1) u3) u4) u5} (CategoryTheory.Functor.{max u1 u3, max u3 u5, max (max u3 u2) u1, max (max u3 u4) u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u5, u4, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.Functor.category.{max u1 u3, max u3 u5, max (max u2 u1) u3, max (max u3 u4) u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u1, u2, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u5, u4, u3} W _inst_3 _inst_4 ι c)))) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F _inst_5 c) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 G _inst_6 c))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.map_homotopy_category CategoryTheory.NatTrans.mapHomotopyCategoryₓ'. -/
-- TODO `F.map_homotopy_category c` is additive (and linear when `F` is linear).
/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
def NatTrans.mapHomotopyCategory {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ⟶ G.mapHomotopyCategory c
    where
  app C := (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app C.as)
  naturality' C D f := by
    dsimp
    simp only [← functor.map_comp]
    congr 1
    ext
    dsimp
    simp
#align category_theory.nat_trans.map_homotopy_category CategoryTheory.NatTrans.mapHomotopyCategory

/- warning: category_theory.nat_trans.map_homotopy_category_id -> CategoryTheory.NatTrans.mapHomotopyCategory_id is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {V : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Preadditive.{u1, u2} V _inst_1] {W : Type.{u4}} [_inst_3 : CategoryTheory.Category.{u5, u4} W] [_inst_4 : CategoryTheory.Preadditive.{u5, u4} W _inst_3] (c : ComplexShape.{u3} ι) (F : CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u2, u4, u1, u5} V W _inst_1 _inst_3 _inst_2 _inst_4 F], Eq.{succ (max (max u2 u3 u1) u3 u5)} (Quiver.Hom.{succ (max (max u2 u3 u1) u3 u5), max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.CategoryStruct.toQuiver.{max (max u2 u3 u1) u3 u5, max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u3 u1) u3 u5, max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.Functor.category.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)))) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 c F _inst_5) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 c F _inst_5)) (CategoryTheory.NatTrans.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F F _inst_5 _inst_5 (CategoryTheory.CategoryStruct.id.{max u2 u5, max u1 u5 u2 u4} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u2 u5, max u1 u5 u2 u4} (CategoryTheory.Functor.{u1, u5, u2, u4} V _inst_1 W _inst_3) (CategoryTheory.Functor.category.{u1, u5, u2, u4} V _inst_1 W _inst_3)) F) c) (CategoryTheory.CategoryStruct.id.{max (max u2 u3 u1) u3 u5, max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.Category.toCategoryStruct.{max (max u2 u3 u1) u3 u5, max (max u3 u1) (max u3 u5) (max u2 u3 u1) u4 u3 u5} (CategoryTheory.Functor.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c)) (CategoryTheory.Functor.category.{max u3 u1, max u3 u5, max u2 u3 u1, max u4 u3 u5} (HomotopyCategory.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomotopyCategory.category.{u1, u3, u2} ι V _inst_1 _inst_2 c) (HomotopyCategory.{u5, u4, u3} ι W _inst_3 _inst_4 c) (HomotopyCategory.category.{u5, u3, u4} ι W _inst_3 _inst_4 c))) (CategoryTheory.Functor.mapHomotopyCategory.{u1, u2, u3, u4, u5} ι V _inst_1 _inst_2 W _inst_3 _inst_4 c F _inst_5))
but is expected to have type
  forall {ι : Type.{u3}} {V : Type.{u5}} [_inst_1 : CategoryTheory.Category.{u4, u5} V] [_inst_2 : CategoryTheory.Preadditive.{u4, u5} V _inst_1] {W : Type.{u1}} [_inst_3 : CategoryTheory.Category.{u2, u1} W] [_inst_4 : CategoryTheory.Preadditive.{u2, u1} W _inst_3] (c : ComplexShape.{u3} ι) (F : CategoryTheory.Functor.{u4, u2, u5, u1} V _inst_1 W _inst_3) [_inst_5 : CategoryTheory.Functor.Additive.{u5, u1, u4, u2} V W _inst_1 _inst_3 _inst_2 _inst_4 F], Eq.{max (max (max (succ u5) (succ u4)) (succ u3)) (succ u2)} (Quiver.Hom.{max (max (max (succ u5) (succ u4)) (succ u3)) (succ u2), max (max (max (max u5 u4) u3) u1) u2} (CategoryTheory.Functor.{max u4 u3, max u3 u2, max (max u3 u5) u4, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u5 u4) u3) u2, max (max (max (max u5 u4) u3) u1) u2} (CategoryTheory.Functor.{max u4 u3, max u3 u2, max (max u3 u5) u4, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.Category.toCategoryStruct.{max (max (max u5 u4) u3) u2, max (max (max (max u5 u4) u3) u1) u2} (CategoryTheory.Functor.{max u4 u3, max u3 u2, max (max u3 u5) u4, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.Functor.category.{max u4 u3, max u3 u2, max (max u5 u4) u3, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c)))) (CategoryTheory.Functor.mapHomotopyCategory.{u4, u5, u3, u1, u2} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F _inst_5 c) (CategoryTheory.Functor.mapHomotopyCategory.{u4, u5, u3, u1, u2} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F _inst_5 c)) (CategoryTheory.NatTrans.mapHomotopyCategory.{u4, u5, u3, u1, u2} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F F _inst_5 _inst_5 (CategoryTheory.CategoryStruct.id.{max u5 u2, max (max (max u5 u4) u1) u2} (CategoryTheory.Functor.{u4, u2, u5, u1} V _inst_1 W _inst_3) (CategoryTheory.Category.toCategoryStruct.{max u5 u2, max (max (max u5 u4) u1) u2} (CategoryTheory.Functor.{u4, u2, u5, u1} V _inst_1 W _inst_3) (CategoryTheory.Functor.category.{u4, u2, u5, u1} V _inst_1 W _inst_3)) F) c) (CategoryTheory.CategoryStruct.id.{max (max (max u5 u4) u3) u2, max (max (max (max u5 u4) u3) u1) u2} (CategoryTheory.Functor.{max u4 u3, max u3 u2, max (max u3 u5) u4, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.Category.toCategoryStruct.{max (max (max u5 u4) u3) u2, max (max (max (max u5 u4) u3) u1) u2} (CategoryTheory.Functor.{max u4 u3, max u3 u2, max (max u3 u5) u4, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c)) (CategoryTheory.Functor.category.{max u4 u3, max u3 u2, max (max u5 u4) u3, max (max u3 u1) u2} (HomotopyCategory.{u4, u5, u3} ι V _inst_1 _inst_2 c) (instCategoryHomotopyCategory.{u4, u5, u3} V _inst_1 _inst_2 ι c) (HomotopyCategory.{u2, u1, u3} ι W _inst_3 _inst_4 c) (instCategoryHomotopyCategory.{u2, u1, u3} W _inst_3 _inst_4 ι c))) (CategoryTheory.Functor.mapHomotopyCategory.{u4, u5, u3, u1, u2} ι V _inst_1 _inst_2 W _inst_3 _inst_4 F _inst_5 c))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.map_homotopy_category_id CategoryTheory.NatTrans.mapHomotopyCategory_idₓ'. -/
@[simp]
theorem NatTrans.mapHomotopyCategory_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomotopyCategory (𝟙 F) c = 𝟙 (F.mapHomotopyCategory c) := by tidy
#align category_theory.nat_trans.map_homotopy_category_id CategoryTheory.NatTrans.mapHomotopyCategory_id

/- warning: category_theory.nat_trans.map_homotopy_category_comp -> CategoryTheory.NatTrans.mapHomotopyCategory_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.map_homotopy_category_comp CategoryTheory.NatTrans.mapHomotopyCategory_compₓ'. -/
@[simp]
theorem NatTrans.mapHomotopyCategory_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive]
    [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomotopyCategory (α ≫ β) c =
      NatTrans.mapHomotopyCategory α c ≫ NatTrans.mapHomotopyCategory β c :=
  by tidy
#align category_theory.nat_trans.map_homotopy_category_comp CategoryTheory.NatTrans.mapHomotopyCategory_comp

end CategoryTheory

