import Mathbin.Algebra.Homology.Homology

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Prove the 2-out-of-3 property.
Define the derived category as the localization at quasi-isomorphisms?
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {ι : Type _}

variable {V : Type u} [category.{v} V] [has_zero_morphisms V] [has_zero_object V]

variable [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

/--
A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class QuasiIso (f : C ⟶ D) : Prop where 
  IsIso : ∀ i, is_iso ((homologyFunctor V c i).map f)

attribute [instance] QuasiIso.is_iso

instance (priority := 100) quasi_iso_of_iso (f : C ⟶ D) [is_iso f] : QuasiIso f :=
  { IsIso :=
      fun i =>
        by 
          change is_iso ((homologyFunctor V c i).mapIso (as_iso f)).Hom 
          infer_instance }

instance quasi_iso_comp (f : C ⟶ D) [QuasiIso f] (g : D ⟶ E) [QuasiIso g] : QuasiIso (f ≫ g) :=
  { IsIso :=
      fun i =>
        by 
          rw [functor.map_comp]
          infer_instance }

