/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.HomologicalComplex

/-!
# Flip a complex of complexes

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

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flipObj (C : HomologicalComplex (HomologicalComplex V c) c') : HomologicalComplex (HomologicalComplex V c') c where
  x := fun i =>
    { x := fun j => (C.x j).x i, d := fun j j' => (C.d j j').f i,
      shape' := fun j j' w => by
        rw [C.shape j j' w]
        simp ,
      d_comp_d' := fun j₁ j₂ j₃ _ _ => congr_hom (C.d_comp_d j₁ j₂ j₃) i }
  d := fun i i' => { f := fun j => (C.x j).d i i', comm' := fun j j' h => ((C.d j j').comm i i').symm }
  shape' := fun i i' w => by
    ext j
    exact (C.X j).shape i i' w

variable (V c c')

/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flip : HomologicalComplex (HomologicalComplex V c) c' ⥤ HomologicalComplex (HomologicalComplex V c') c where
  obj := fun C => flipObj C
  map := fun C D f => { f := fun i => { f := fun j => (f.f j).f i, comm' := fun j j' h => congr_hom (f.comm j j') i } }

/-- Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flipEquivalenceUnitIso : 𝟭 (HomologicalComplex (HomologicalComplex V c) c') ≅ flip V c c' ⋙ flip V c' c :=
  NatIso.ofComponents
    (fun C =>
      { Hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.x i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] },
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.x i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] } })
    fun X Y f => by
    ext
    dsimp
    simp only [category.id_comp, category.comp_id]

/-- Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flipEquivalenceCounitIso : flip V c' c ⋙ flip V c c' ≅ 𝟭 (HomologicalComplex (HomologicalComplex V c') c) :=
  NatIso.ofComponents
    (fun C =>
      { Hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.x i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] },
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.x i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] } })
    fun X Y f => by
    ext
    dsimp
    simp only [category.id_comp, category.comp_id]

/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flipEquivalence :
    HomologicalComplex (HomologicalComplex V c) c' ≌ HomologicalComplex (HomologicalComplex V c') c where
  Functor := flip V c c'
  inverse := flip V c' c
  unitIso := flipEquivalenceUnitIso V c c'
  counitIso := flipEquivalenceCounitIso V c c'

end HomologicalComplex

