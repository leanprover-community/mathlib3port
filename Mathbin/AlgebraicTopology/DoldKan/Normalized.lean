/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.normalized
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN

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


open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Subobject CategoryTheory.Idempotents

open DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

universe v

variable {A : Type _} [Category A] [Abelian A] {X : SimplicialObject A}

/- warning: algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map -> AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMapₓ'. -/
theorem HigherFacesVanish.inclusionOfMooreComplexMap (n : ℕ) :
    HigherFacesVanish (n + 1) ((inclusionOfMooreComplexMap X).f (n + 1)) := fun j hj =>
  by
  dsimp [inclusion_of_Moore_complex_map]
  rw [←
    factor_thru_arrow _ _
      (finset_inf_arrow_factors Finset.univ _ j (by simp only [Finset.mem_univ])),
    assoc, kernel_subobject_arrow_comp, comp_zero]
#align algebraic_topology.dold_kan.higher_faces_vanish.inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.HigherFacesVanish.inclusionOfMooreComplexMap

/- warning: algebraic_topology.dold_kan.factors_normalized_Moore_complex_P_infty -> AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInfty is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} A] [_inst_2 : CategoryTheory.Abelian.{u2, u1} A _inst_1] {X : CategoryTheory.SimplicialObject.{u2, u1} A _inst_1} (n : Nat), CategoryTheory.Subobject.Factors.{u2, u1} A _inst_1 (HomologicalComplex.x.{u2, u1, 0} Nat A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) n) (CategoryTheory.Functor.obj.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) A _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (AlgebraicTopology.NormalizedMooreComplex.objX.{u1, u2} A _inst_1 _inst_2 X n) (HomologicalComplex.Hom.f.{u2, u1, 0} Nat A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) (AlgebraicTopology.DoldKan.PInfty.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) n)
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} A] [_inst_2 : CategoryTheory.Abelian.{u2, u1} A _inst_1] {X : CategoryTheory.SimplicialObject.{u2, u1} A _inst_1} (n : Nat), CategoryTheory.Subobject.Factors.{u2, u1} A _inst_1 (HomologicalComplex.X.{u2, u1, 0} Nat A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) n) (Prefunctor.obj.{1, succ u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) A (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} A (CategoryTheory.Category.toCategoryStruct.{u2, u1} A _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u2, 0, u1} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) A _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (AlgebraicTopology.NormalizedMooreComplex.objX.{u1, u2} A _inst_1 _inst_2 X n) (HomologicalComplex.Hom.f.{u2, u1, 0} Nat A _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) (AlgebraicTopology.DoldKan.PInfty.{u1, u2} A _inst_1 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_1 _inst_2) X) n)
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.factors_normalized_Moore_complex_P_infty AlgebraicTopology.DoldKan.factors_normalizedMooreComplex_PInftyₓ'. -/
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

/- warning: algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map -> AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMapₓ'. -/
@[simp, reassoc]
theorem PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap (X : SimplicialObject A) :
    PInftyToNormalizedMooreComplex X ≫ inclusionOfMooreComplexMap X = PInfty := by tidy
#align algebraic_topology.dold_kan.P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap

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

/- warning: algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty -> AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInftyₓ'. -/
@[simp, reassoc]
theorem inclusionOfMooreComplexMap_comp_PInfty (X : SimplicialObject A) :
    inclusionOfMooreComplexMap X ≫ PInfty = inclusionOfMooreComplexMap X :=
  by
  ext n
  cases n
  · dsimp
    simp only [comp_id]
  · exact (higher_faces_vanish.inclusion_of_Moore_complex_map n).comp_P_eq_self
#align algebraic_topology.dold_kan.inclusion_of_Moore_complex_map_comp_P_infty AlgebraicTopology.DoldKan.inclusionOfMooreComplexMap_comp_PInfty

instance : Mono (inclusionOfMooreComplexMap X) :=
  ⟨fun Y f₁ f₂ hf => by
    ext n
    exact HomologicalComplex.congr_hom hf n⟩

/- warning: algebraic_topology.dold_kan.split_mono_inclusion_of_Moore_complex_map -> AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.split_mono_inclusion_of_Moore_complex_map AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMapₓ'. -/
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

variable (A)

/- warning: algebraic_topology.dold_kan.N₁_iso_normalized_Moore_complex_comp_to_karoubi -> AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.N₁_iso_normalized_Moore_complex_comp_to_karoubi AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubiₓ'. -/
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
      naturality' := fun X Y f => by
        ext
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

end DoldKan

end AlgebraicTopology

