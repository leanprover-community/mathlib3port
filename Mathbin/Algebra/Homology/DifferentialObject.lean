import Mathbin.Algebra.Homology.HomologicalComplex 
import Mathbin.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `homological_complex` indexed by an `add_comm_group` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/


open CategoryTheory

open CategoryTheory.Limits

open_locale Classical

noncomputable theory

namespace HomologicalComplex

variable {β : Type _} [AddCommGroupₓ β] (b : β)

variable (V : Type _) [category V] [has_zero_morphisms V]

/--
The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgo_to_homological_complex :
  differential_object (graded_object_with_shift b V) ⥤ HomologicalComplex V (ComplexShape.up' b) :=
  { obj :=
      fun X =>
        { x := fun i => X.X i, d := fun i j => if h : (i+b) = j then X.d i ≫ eq_to_hom (congr_argₓ X.X h) else 0,
          shape' :=
            fun i j w =>
              by 
                dsimp  at w 
                rw [dif_neg w],
          d_comp_d' :=
            fun i j k hij hjk =>
              by 
                dsimp  at hij hjk 
                substs hij hjk 
                simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl]
                exact congr_funₓ X.d_squared i },
    map :=
      fun X Y f =>
        { f := f.f,
          comm' :=
            fun i j h =>
              by 
                dsimp  at h⊢
                subst h 
                simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl]
                exact (congr_funₓ f.comm i).symm } }

/--
The functor from homological complexes to differential graded objects.
-/
@[simps]
def homological_complex_to_dgo :
  HomologicalComplex V (ComplexShape.up' b) ⥤ differential_object (graded_object_with_shift b V) :=
  { obj :=
      fun X =>
        { x := fun i => X.X i, d := fun i => X.d i (i+b),
          d_squared' :=
            by 
              ext i 
              dsimp 
              simp  },
    map :=
      fun X Y f =>
        { f := f.f,
          comm' :=
            by 
              ext i 
              dsimp 
              simp  } }

/--
The unit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_unit_iso :
  𝟭 (differential_object (graded_object_with_shift b V)) ≅
    dgo_to_homological_complex b V ⋙ homological_complex_to_dgo b V :=
  nat_iso.of_components (fun X => { Hom := { f := fun i => 𝟙 (X.X i) }, inv := { f := fun i => 𝟙 (X.X i) } })
    (by 
      tidy)

/--
The counit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_counit_iso :
  homological_complex_to_dgo b V ⋙ dgo_to_homological_complex b V ≅ 𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  nat_iso.of_components
    (fun X =>
      { Hom :=
          { f := fun i => 𝟙 (X.X i),
            comm' :=
              fun i j h =>
                by 
                  dsimp  at h⊢
                  subst h 
                  simp only [category.comp_id, category.id_comp, dif_pos rfl, eq_to_hom_refl] },
        inv :=
          { f := fun i => 𝟙 (X.X i),
            comm' :=
              fun i j h =>
                by 
                  dsimp  at h⊢
                  subst h 
                  simp only [category.comp_id, category.id_comp, dif_pos rfl, eq_to_hom_refl] } })
    (by 
      tidy)

/--
The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgo_equiv_homological_complex :
  differential_object (graded_object_with_shift b V) ≌ HomologicalComplex V (ComplexShape.up' b) :=
  { Functor := dgo_to_homological_complex b V, inverse := homological_complex_to_dgo b V,
    unitIso := dgo_equiv_homological_complex_unit_iso b V, counitIso := dgo_equiv_homological_complex_counit_iso b V }

end HomologicalComplex

