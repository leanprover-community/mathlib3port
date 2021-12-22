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

variable {V : Type u} [category.{v} V] [has_zero_morphisms V]

variable {ι : Type _} {c : ComplexShape ι} {ι' : Type _} {c' : ComplexShape ι'}

/-- 
Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flip_obj (C : HomologicalComplex (HomologicalComplex V c) c') : HomologicalComplex (HomologicalComplex V c') c :=
  { x := fun i =>
      { x := fun j => (C.X j).x i, d := fun j j' => (C.d j j').f i,
        shape' := fun j j' w => by
          rw [C.shape j j' w]
          simp ,
        d_comp_d' := fun j₁ j₂ j₃ _ _ => congr_hom (C.d_comp_d j₁ j₂ j₃) i },
    d := fun i i' => { f := fun j => (C.X j).d i i', comm' := fun j j' h => ((C.d j j').comm i i').symm },
    shape' := fun i i' w => by
      ext j
      exact (C.X j).shape i i' w }

variable (V c c')

/--  Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flip : HomologicalComplex (HomologicalComplex V c) c' ⥤ HomologicalComplex (HomologicalComplex V c') c :=
  { obj := fun C => flip_obj C,
    map := fun C D f =>
      { f := fun i => { f := fun j => (f.f j).f i, comm' := fun j j' h => congr_hom (f.comm j j') i } } }

/--  Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flip_equivalence_unit_iso : 𝟭 (HomologicalComplex (HomologicalComplex V c) c') ≅ flip V c c' ⋙ flip V c' c :=
  nat_iso.of_components
    (fun C =>
      { Hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] },
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] } })
    fun X Y f => by
    ext
    dsimp
    simp only [category.id_comp, category.comp_id]

/--  Auxiliary definition for `homological_complex.flip_equivalence` .-/
@[simps]
def flip_equivalence_counit_iso : flip V c' c ⋙ flip V c c' ≅ 𝟭 (HomologicalComplex (HomologicalComplex V c') c) :=
  nat_iso.of_components
    (fun C =>
      { Hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] },
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).x j) },
            comm' := fun i j h => by
              ext
              dsimp
              simp only [category.id_comp, category.comp_id] } })
    fun X Y f => by
    ext
    dsimp
    simp only [category.id_comp, category.comp_id]

/--  Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flip_equivalence :
    HomologicalComplex (HomologicalComplex V c) c' ≌ HomologicalComplex (HomologicalComplex V c') c :=
  { Functor := flip V c c', inverse := flip V c' c, unitIso := flip_equivalence_unit_iso V c c',
    counitIso := flip_equivalence_counit_iso V c c' }

end HomologicalComplex

