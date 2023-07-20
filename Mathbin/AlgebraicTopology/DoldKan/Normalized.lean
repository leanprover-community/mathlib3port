/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN

#align_import algebraic_topology.dold_kan.normalized from "leanprover-community/mathlib"@"9d2f0748e6c50d7a2657c564b1ff2c695b39148d"

/-!

# Comparison with the normalized Moore complex functor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

TODO (@joelriou) continue adding the various files referenced below

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_normalized_Moore_complex_comp_to_karoubi` between
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)`
defined in `functor_n.lean` and the composition of
`normalized_Moore_complex A` with the inclusion
`chain_complex A ℕ ⥤ karoubi (chain_complex A ℕ)`.

This isomorphism shall be used in `equivalence.lean` in order to obtain
the Dold-Kan equivalence
`category_theory.abelian.dold_kan.equivalence : simplicial_object A ≌ chain_complex A ℕ`
with a functor (definitionally) equal to `normalized_Moore_complex A`.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject
  CategoryTheory.Idempotents

open scoped DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type _} [Category A] [Abelian A] {X : SimplicialObject A}

#print AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap /-
theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j hj =>
  by
  dsimp [inclusion_of_Moore_complex_map]
  rw [←
    factor_thru_arrow _ _
      (finset_inf_arrow_factors Finset.univ _ j (by simp only [Finset.mem_univ])),
    assoc, kernel_subobject_arrow_comp, comp_zero]
#align algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap
-/

#print AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty /-
theorem factors_normalizedMooreComplex_PInfty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (PInfty.f n) :=
  by
  cases n
  · apply top_factors
  · rw [P_infty_f, normalized_Moore_complex.obj_X, finset_inf_factors]
    intro i hi
    apply kernel_subobject_factors
    exact (higher_faces_vanish.of_P (n + 1) n) i le_add_self
#align algebraic_topology.dold_kan.factors_normalized_Moore_complex_P_infty AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty
-/

#print AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex /-
/-- P_infty factors through the normalized Moore complex -/
@[simps]
def PInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => factorThru _ _ (factors_normalizedMooreComplex_PInfty n))
    fun n =>
    by
    rw [← cancel_mono (normalized_Moore_complex.obj_X X n).arrow, assoc, assoc, factor_thru_arrow, ←
      inclusion_of_Moore_complex_map_f, ← normalized_Moore_complex_obj_d, ←
      (inclusion_of_Moore_complex_map X).comm' (n + 1) n rfl, inclusion_of_Moore_complex_map_f,
      factor_thru_arrow_assoc, ← alternating_face_map_complex_obj_d]
    exact P_infty.comm' (n + 1) n rfl
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
-/

#print AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap /-
@[simp, reassoc]
theorem PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
-/

#print AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality /-
@[simp, reassoc]
theorem PInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ PInftyToNormalizedMooreComplex Y =
      PInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f :=
  by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_naturality AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality
-/

#print AlgebraicTopology.DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex /-
@[simp, reassoc]
theorem PInfty_comp_PInftyToNormalizedMooreComplex (X : SimplicialObject A) :
    PInfty ≫ PInftyToNormalizedMooreComplex X = PInftyToNormalizedMooreComplex X := by tidy
#align algebraic_topology.dold_kan.P_infty_comp_P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex
-/

#print AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty /-
@[simp, reassoc]
theorem inclusionOfMooreComplexMap_comp_PInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X :=
  by
  ext n
  cases n
  · dsimp; simp only [comp_id]
  · exact (higher_faces_vanish.inclusion_of_Moore_complex_map n).comp_P_eq_self
#align algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty
-/

instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun Y f₁ f₂ hf => by ext n; exact HomologicalComplex.congr_hom hf n⟩

#print AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap /-
/-- `inclusion_of_Moore_complex_map X` is a split mono. -/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) :
    SplitMono (inclusionOfMooreComplexMap X)
    where
  retraction := PInftyToNormalizedMooreComplex X
  id' := by
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X), assoc, id_comp,
      P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      inclusion_of_Moore_complex_map_comp_P_infty]
#align algebraic_topology.dold_kan.split_mono_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap
-/

variable (A)

#print AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi /-
/-- When the category `A` is abelian,
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)` defined
using `P_infty` identifies to the composition of the normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
def N₁_iso_normalizedMooreComplex_comp_toKaroubi : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _
    where
  Hom :=
    { app := fun X =>
        { f := PInftyToNormalizedMooreComplex X
          comm := by erw [comp_id, P_infty_comp_P_infty_to_normalized_Moore_complex] }
      naturality' := fun X Y f => by
        simp only [functor.comp_map, normalized_Moore_complex_map,
          P_infty_to_normalized_Moore_complex_naturality, karoubi.hom_ext, karoubi.comp_f, N₁_map_f,
          P_infty_comp_P_infty_to_normalized_Moore_complex_assoc, to_karoubi_map_f, assoc] }
  inv :=
    { app := fun X =>
        { f := inclusionOfMooreComplexMap X
          comm := by erw [inclusion_of_Moore_complex_map_comp_P_infty, id_comp] }
      naturality' := fun X Y f => by ext;
        simp only [functor.comp_map, normalized_Moore_complex_map, karoubi.comp_f, to_karoubi_map_f,
          HomologicalComplex.comp_f, normalized_Moore_complex.map_f,
          inclusion_of_Moore_complex_map_f, factor_thru_arrow, N₁_map_f,
          inclusion_of_Moore_complex_map_comp_P_infty_assoc, alternating_face_map_complex.map_f] }
  hom_inv_id' := by
    ext X : 3
    simp only [P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      nat_trans.comp_app, karoubi.comp_f, N₁_obj_p, nat_trans.id_app, karoubi.id_eq]
  inv_hom_id' := by
    ext X : 3
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X), nat_trans.comp_app, karoubi.comp_f,
      assoc, nat_trans.id_app, karoubi.id_eq,
      P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      inclusion_of_Moore_complex_map_comp_P_infty]
    dsimp only [functor.comp_obj, to_karoubi]
    rw [id_comp]
#align algebraic_topology.dold_kan.N₁_iso_normalized_Moore_complex_comp_to_karoubi AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
-/

end DoldKan

end AlgebraicTopology

