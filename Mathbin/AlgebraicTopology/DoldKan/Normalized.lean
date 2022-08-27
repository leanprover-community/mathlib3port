/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
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


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject CategoryTheory.Idempotents

open DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type _} [Category A] [Abelian A] {X : SimplicialObject A}

theorem HigherFacesVanish.inclusion_of_Moore_complex_map (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j hj => by
  dsimp' [inclusion_of_Moore_complex_map]
  rw [←
    factor_thru_arrow _ _
      (finset_inf_arrow_factors Finset.univ _ j
        (by
          simp only [Finset.mem_univ])),
    assoc, kernel_subobject_arrow_comp, comp_zero]

theorem factors_normalized_Moore_complex_P_infty (n : ℕ) :
    Subobject.Factors (NormalizedMooreComplex.objX X n) (pInfty.f n) := by
  cases n
  · apply top_factors
    
  · rw [P_infty_f, normalized_Moore_complex.obj_X, finset_inf_factors]
    intro i hi
    apply kernel_subobject_factors
    exact (higher_faces_vanish.of_P (n + 1) n) i le_add_self
    

/-- P_infty factors through the normalized Moore complex -/
@[simps]
def pInftyToNormalizedMooreComplex (X : SimplicialObject A) : K[X] ⟶ N[X] :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => factorThru _ _ (factors_normalized_Moore_complex_P_infty n)) fun n => by
    rw [← cancel_mono (normalized_Moore_complex.obj_X X n).arrow, assoc, assoc, factor_thru_arrow, ←
      inclusion_of_Moore_complex_map_f, ← normalized_Moore_complex_obj_d, ←
      (inclusion_of_Moore_complex_map X).comm' (n + 1) n rfl, inclusion_of_Moore_complex_map_f, factor_thru_arrow_assoc,
      ← alternating_face_map_complex_obj_d]
    exact P_infty.comm' (n + 1) n rfl

@[simp, reassoc]
theorem P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map (X : SimplicialObject A) :
    pInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = P_infty := by
  tidy

@[simp, reassoc]
theorem P_infty_to_normalized_Moore_complex_naturality {X Y : SimplicialObject A} (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map f ≫ pInftyToNormalizedMooreComplex Y =
      pInftyToNormalizedMooreComplex X ≫ NormalizedMooreComplex.map f :=
  by
  tidy

@[simp, reassoc]
theorem P_infty_comp_P_infty_to_normalized_Moore_complex (X : SimplicialObject A) :
    P_infty ≫ pInftyToNormalizedMooreComplex X = pInftyToNormalizedMooreComplex X := by
  tidy

@[simp, reassoc]
theorem inclusion_of_Moore_complex_map_comp_P_infty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ P_infty = inclusionOfMooreComplexMap X := by
  ext n
  cases n
  · dsimp'
    simp only [comp_id]
    
  · exact (higher_faces_vanish.inclusion_of_Moore_complex_map n).comp_P_eq_self
    

instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun Y f₁ f₂ hf => by
    ext n
    exact HomologicalComplex.congr_hom hf n⟩

/-- `inclusion_of_Moore_complex_map X` is a split mono. -/
def splitMonoInclusionOfMooreComplexMap (X : SimplicialObject A) : SplitMono (inclusionOfMooreComplexMap X) where
  retraction := pInftyToNormalizedMooreComplex X
  id' := by
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X), assoc, id_comp,
      P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      inclusion_of_Moore_complex_map_comp_P_infty]

variable (A)

/-- When the category `A` is abelian,
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)` defined
using `P_infty` identifies to the composition of the normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
def n₁IsoNormalizedMooreComplexCompToKaroubi : N₁ ≅ normalizedMooreComplex A ⋙ toKaroubi _ where
  Hom :=
    { app := fun X =>
        { f := pInftyToNormalizedMooreComplex X,
          comm := by
            tidy } }
  inv :=
    { app := fun X =>
        { f := inclusionOfMooreComplexMap X,
          comm := by
            tidy } }
  hom_inv_id' := by
    ext X : 3
    simp only [P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map, nat_trans.comp_app,
      karoubi.comp, N₁_obj_p, nat_trans.id_app, karoubi.id_eq]
  inv_hom_id' := by
    ext X : 3
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X), nat_trans.comp_app, karoubi.comp, assoc,
      nat_trans.id_app, karoubi.id_eq, P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
      inclusion_of_Moore_complex_map_comp_P_infty]
    dsimp' only [functor.comp_obj, to_karoubi]
    rw [id_comp]

end DoldKan

end AlgebraicTopology

