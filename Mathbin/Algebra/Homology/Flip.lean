/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.flip
! leanprover-community/mathlib commit 8eb9c42d4d34c77f6ee84ea766ae4070233a973c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.HomologicalComplex

/-!
# Flip a complex of complexes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For now we don't have double complexes as a distinct thing,
but we can model them as complexes of complexes.

Here we show how to flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.

-/


universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {ι : Type _} {c : ComplexShape ι} {ι' : Type _} {c' : ComplexShape ι'}

#print HomologicalComplex.flipObj /-
/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flipObj (C : HomologicalComplex (HomologicalComplex V c) c') :
    HomologicalComplex (HomologicalComplex V c') c
    where
  pt i :=
    { pt := fun j => (C.pt j).pt i
      d := fun j j' => (C.d j j').f i
      shape' := fun j j' w => by rw [C.shape j j' w]; simp
      d_comp_d' := fun j₁ j₂ j₃ _ _ => congr_hom (C.d_comp_d j₁ j₂ j₃) i }
  d i i' :=
    { f := fun j => (C.pt j).d i i'
      comm' := fun j j' h => ((C.d j j').comm i i').symm }
  shape' i i' w := by ext j; exact (C.X j).shape i i' w
#align homological_complex.flip_obj HomologicalComplex.flipObj
-/

variable (V c c')

#print HomologicalComplex.flip /-
/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flip :
    HomologicalComplex (HomologicalComplex V c) c' ⥤ HomologicalComplex (HomologicalComplex V c') c
    where
  obj C := flipObj C
  map C D f :=
    {
      f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := fun j j' h => congr_hom (f.comm j j') i } }
#align homological_complex.flip HomologicalComplex.flip
-/

#print HomologicalComplex.flipEquivalenceUnitIso /-
/-- Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex (HomologicalComplex V c) c') ≅ flip V c c' ⋙ flip V c' c :=
  NatIso.ofComponents
    (fun C =>
      { Hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.pt i).pt j) }
            comm' := fun i j h => by ext; dsimp; simp only [category.id_comp, category.comp_id] }
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.pt i).pt j) }
            comm' := fun i j h => by ext; dsimp; simp only [category.id_comp, category.comp_id] } })
    fun X Y f => by ext; dsimp; simp only [category.id_comp, category.comp_id]
#align homological_complex.flip_equivalence_unit_iso HomologicalComplex.flipEquivalenceUnitIso
-/

#print HomologicalComplex.flipEquivalenceCounitIso /-
/-- Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flipEquivalenceCounitIso :
    flip V c' c ⋙ flip V c c' ≅ 𝟭 (HomologicalComplex (HomologicalComplex V c') c) :=
  NatIso.ofComponents
    (fun C =>
      { Hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.pt i).pt j) }
            comm' := fun i j h => by ext; dsimp; simp only [category.id_comp, category.comp_id] }
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.pt i).pt j) }
            comm' := fun i j h => by ext; dsimp; simp only [category.id_comp, category.comp_id] } })
    fun X Y f => by ext; dsimp; simp only [category.id_comp, category.comp_id]
#align homological_complex.flip_equivalence_counit_iso HomologicalComplex.flipEquivalenceCounitIso
-/

/- warning: homological_complex.flip_equivalence -> HomologicalComplex.flipEquivalence is a dubious translation:
lean 3 declaration is
  forall (V : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {ι : Type.{u3}} (c : ComplexShape.{u3} ι) {ι' : Type.{u4}} (c' : ComplexShape.{u4} ι'), CategoryTheory.Equivalence.{max u4 u3 u1, max u3 u4 u1, max (max u2 u3 u1) u4 u3 u1, max (max u2 u4 u1) u3 u4 u1} (HomologicalComplex.{max u3 u1, max u2 u3 u1, u4} ι' (HomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.CategoryTheory.Limits.hasZeroMorphisms.{u1, u2, u3} ι V _inst_1 _inst_2 c) c') (HomologicalComplex.CategoryTheory.category.{max u3 u1, max u2 u3 u1, u4} ι' (HomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.CategoryTheory.category.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.CategoryTheory.Limits.hasZeroMorphisms.{u1, u2, u3} ι V _inst_1 _inst_2 c) c') (HomologicalComplex.{max u4 u1, max u2 u4 u1, u3} ι (HomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.CategoryTheory.category.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.CategoryTheory.Limits.hasZeroMorphisms.{u1, u2, u4} ι' V _inst_1 _inst_2 c') c) (HomologicalComplex.CategoryTheory.category.{max u4 u1, max u2 u4 u1, u3} ι (HomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.CategoryTheory.category.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.CategoryTheory.Limits.hasZeroMorphisms.{u1, u2, u4} ι' V _inst_1 _inst_2 c') c)
but is expected to have type
  forall (V : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} V] [_inst_2 : CategoryTheory.Limits.HasZeroMorphisms.{u1, u2} V _inst_1] {ι : Type.{u3}} (c : ComplexShape.{u3} ι) {ι' : Type.{u4}} (c' : ComplexShape.{u4} ι'), CategoryTheory.Equivalence.{max (max u1 u3) u4, max (max u1 u3) u4, max (max u4 (max u3 u2) u1) u1 u3, max (max u3 (max u4 u2) u1) u1 u4} (HomologicalComplex.{max u1 u3, max (max u3 u2) u1, u4} ι' (HomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.instHasZeroMorphismsHomologicalComplexInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) c') (HomologicalComplex.{max u1 u4, max (max u4 u2) u1, u3} ι (HomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.instHasZeroMorphismsHomologicalComplexInstCategoryHomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') c) (HomologicalComplex.instCategoryHomologicalComplex.{max u1 u3, max (max u2 u1) u3, u4} ι' (HomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) (HomologicalComplex.instHasZeroMorphismsHomologicalComplexInstCategoryHomologicalComplex.{u1, u2, u3} ι V _inst_1 _inst_2 c) c') (HomologicalComplex.instCategoryHomologicalComplex.{max u1 u4, max (max u2 u1) u4, u3} ι (HomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.instCategoryHomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') (HomologicalComplex.instHasZeroMorphismsHomologicalComplexInstCategoryHomologicalComplex.{u1, u2, u4} ι' V _inst_1 _inst_2 c') c)
Case conversion may be inaccurate. Consider using '#align homological_complex.flip_equivalence HomologicalComplex.flipEquivalenceₓ'. -/
/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flipEquivalence :
    HomologicalComplex (HomologicalComplex V c) c' ≌ HomologicalComplex (HomologicalComplex V c') c
    where
  Functor := flip V c c'
  inverse := flip V c' c
  unitIso := flipEquivalenceUnitIso V c c'
  counitIso := flipEquivalenceCounitIso V c c'
#align homological_complex.flip_equivalence HomologicalComplex.flipEquivalence

end HomologicalComplex

