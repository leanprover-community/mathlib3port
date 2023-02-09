/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.normalized
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN

/-!

# Comparison with the normalized Moore complex functor

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


open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject CategoryTheory.Idempotents

open DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type _} [Category A] [Abelian A] {X : SimplicialObject A}

theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j hj =>
  by
  dsimp [inclusionOfMooreComplexMap]
  rw [←
    factorThru_arrow _ _
      (finset_inf_arrow_factors Finset.univ _ j (by simp only [Finset.mem_univ])),
    assoc, kernelSubobject_arrow_comp, comp_zero]
#align algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap

theorem factors_normalized_Moore_complex_pInfty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (pInfty.f n) :=
  by
  cases n
  · apply top_factors
  · rw [pInfty_f, NormalizedMooreComplex.objX, finset_inf_factors]
    intro i hi
    apply kernelSubobject_factors
    exact (HigherFacesVanish.of_p (n + 1) n) i le_add_self
#align algebraic_topology.dold_kan.factors_normalized_Moore_complex_P_infty AlgebraicTopology.DoldKan.factors_normalized_Moore_complex_pInfty

/-- P_infty factors through the normalized Moore complex -/
@[simps]
def pInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => factorThru _ _ (factors_normalized_Moore_complex_pInfty n)) fun n =>
    by
    rw [← cancel_mono (NormalizedMooreComplex.objX X n).arrow, assoc, assoc, factorThru_arrow, ←
      inclusionOfMooreComplexMap_f, ← normalizedMooreComplex_objD, ←
      (inclusionOfMooreComplexMap X).comm' (n + 1) n rfl, inclusionOfMooreComplexMap_f,
      factorThru_arrow_assoc, ← alternatingFaceMapComplex_objD]
    exact P_infty.comm' (n + 1) n rfl
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.pInftyToNormalizedMooreComplex

@[simp, reassoc.1]
theorem pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    pInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = pInfty := by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap

@[simp, reassoc.1]
theorem pInftyToNormalizedMooreComplex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ pInftyToNormalizedMooreComplex Y =
      pInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f :=
  by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_naturality AlgebraicTopology.DoldKan.pInftyToNormalizedMooreComplex_naturality

@[simp, reassoc.1]
theorem pInfty_comp_pInftyToNormalizedMooreComplex (X : SimplicialObject A) :
    pInfty ≫ pInftyToNormalizedMooreComplex X = pInftyToNormalizedMooreComplex X := by tidy
#align algebraic_topology.dold_kan.P_infty_comp_P_infty_to_normalized_Moore_complex AlgebraicTopology.DoldKan.pInfty_comp_pInftyToNormalizedMooreComplex

@[simp, reassoc.1]
theorem inclusionOfMooreComplexMap_comp_pInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ pInfty = inclusionOfMooreComplexMap X :=
  by
  ext n
  cases n
  · dsimp
    simp only [comp_id]
  · exact (HigherFacesVanish.inclusionOfMooreComplexMap n).comp_p_eq_self
#align algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_pInfty

instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun Y f₁ f₂ hf => by
    ext n
    exact HomologicalComplex.congr_hom hf n⟩

/-- `inclusion_of_Moore_complex_map X` is a split mono. -/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) :
    SplitMono (inclusionOfMooreComplexMap X)
    where
  retraction := pInftyToNormalizedMooreComplex X
  id' := by
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), assoc, id_comp,
      pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_pInfty]
#align algebraic_topology.dold_kan.split_mono_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap

variable (A)

/-- When the category `A` is abelian,
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)` defined
using `P_infty` identifies to the composition of the normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
def n₁IsoNormalizedMooreComplexCompToKaroubi : n₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _
    where
  Hom :=
    { app := fun X =>
        { f := pInftyToNormalizedMooreComplex X
          comm := by erw [comp_id, pInfty_comp_pInftyToNormalizedMooreComplex] }
      naturality' := fun X Y f => by
        simp only [Functor.comp_map, normalizedMooreComplex_map,
          pInftyToNormalizedMooreComplex_naturality, Karoubi.hom_ext, Karoubi.comp_f, n₁_map_f,
          pInfty_comp_pInftyToNormalizedMooreComplex_assoc, toKaroubi_map_f, assoc] }
  inv :=
    { app := fun X =>
        { f := inclusionOfMooreComplexMap X
          comm := by erw [inclusionOfMooreComplexMap_comp_pInfty, id_comp] }
      naturality' := fun X Y f => by
        ext
        simp only [Functor.comp_map, normalizedMooreComplex_map, Karoubi.comp_f, toKaroubi_map_f,
          HomologicalComplex.comp_f, NormalizedMooreComplex.map_f, inclusionOfMooreComplexMap_f,
          factorThru_arrow, n₁_map_f, inclusionOfMooreComplexMap_comp_pInfty_assoc,
          AlternatingFaceMapComplex.map_f] }
  hom_inv_id' := by
    ext X : 3
    simp only [pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap, NatTrans.comp_app,
      Karoubi.comp_f, n₁_obj_p, NatTrans.id_app, Karoubi.id_eq]
  inv_hom_id' := by
    ext X : 3
    simp only [← cancel_mono (inclusionOfMooreComplexMap X), NatTrans.comp_app, Karoubi.comp_f,
      assoc, NatTrans.id_app, Karoubi.id_eq,
      pInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      inclusionOfMooreComplexMap_comp_pInfty]
    dsimp only [Functor.comp_obj, toKaroubi]
    rw [id_comp]
#align algebraic_topology.dold_kan.N₁_iso_normalized_Moore_complex_comp_to_karoubi AlgebraicTopology.DoldKan.n₁IsoNormalizedMooreComplexCompToKaroubi

end DoldKan

end AlgebraicTopology

