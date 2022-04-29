/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.Homology

/-!
# Quasi-isomorphisms

A chain map is a quasi-isomorphism if it induces isomorphisms on homology.

## Future work

Define the derived category as the localization at quasi-isomorphisms?
-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable [HasEqualizers V] [HasImages V] [HasImageMaps V] [HasCokernels V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

/-- A chain map is a quasi-isomorphism if it induces isomorphisms on homology.
-/
class QuasiIso (f : C ⟶ D) : Prop where
  IsIso : ∀ i, IsIso ((homologyFunctor V c i).map f)

attribute [instance] QuasiIso.is_iso

instance (priority := 100) quasi_iso_of_iso (f : C ⟶ D) [IsIso f] : QuasiIso f where
  IsIso := fun i => by
    change is_iso ((homologyFunctor V c i).mapIso (as_iso f)).Hom
    infer_instance

instance quasi_iso_comp (f : C ⟶ D) [QuasiIso f] (g : D ⟶ E) [QuasiIso g] : QuasiIso (f ≫ g) where
  IsIso := fun i => by
    rw [functor.map_comp]
    infer_instance

theorem quasi_iso_of_comp_left (f : C ⟶ D) [QuasiIso f] (g : D ⟶ E) [QuasiIso (f ≫ g)] : QuasiIso g :=
  { IsIso := fun i => IsIso.of_is_iso_fac_left ((homologyFunctor V c i).map_comp f g).symm }

theorem quasi_iso_of_comp_right (f : C ⟶ D) (g : D ⟶ E) [QuasiIso g] [QuasiIso (f ≫ g)] : QuasiIso f :=
  { IsIso := fun i => IsIso.of_is_iso_fac_right ((homologyFunctor V c i).map_comp f g).symm }

