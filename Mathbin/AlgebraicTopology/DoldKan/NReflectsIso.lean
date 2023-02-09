/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.n_reflects_iso
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN
import Mathbin.AlgebraicTopology.DoldKan.Decomposition
import Mathbin.CategoryTheory.Idempotents.HomologicalComplex
import Mathbin.CategoryTheory.Idempotents.KaroubiKaroubi

/-!

# N₁ and N₂ reflects isomorphisms

In this file, it is shown that the functors
`N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)` and
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ))`
reflect isomorphisms for any preadditive category `C`.

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Idempotents

open Opposite

open Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

open MorphComponents

instance : ReflectsIsomorphisms (n₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)) :=
  ⟨fun X Y f => by
    intro
    -- restating the result in a way that allows induction on the degree n
    suffices ∀ n : ℕ, IsIso (f.app (op [n]))
      by
      haveI : ∀ Δ : SimplexCategoryᵒᵖ, IsIso (f.app Δ) := fun Δ => this Δ.unop.len
      apply NatIso.isIso_of_isIso_app
    -- restating the assumption in a more practical form
    have h₁ := HomologicalComplex.congr_hom (karoubi.hom_ext.mp (IsIso.hom_inv_id (N₁.map f)))
    have h₂ := HomologicalComplex.congr_hom (karoubi.hom_ext.mp (IsIso.inv_hom_id (N₁.map f)))
    have h₃ := fun n =>
      Karoubi.HomologicalComplex.p_comm_f_assoc (inv (N₁.map f)) n (f.app (op [n]))
    simp only [n₁_map_f, Karoubi.comp_f, HomologicalComplex.comp_f, AlternatingFaceMapComplex.map_f,
      n₁_obj_p, Karoubi.id_eq, assoc] at h₁ h₂ h₃
    -- we have to construct an inverse to f in degree n, by induction on n
    intro n
    induction' n with n hn
    -- degree 0
    · use (inv (N₁.map f)).f.f 0
      have h₁₀ := h₁ 0
      have h₂₀ := h₂ 0
      dsimp at h₁₀ h₂₀
      simp only [id_comp, comp_id] at h₁₀ h₂₀
      tauto
    -- induction step
    · haveI := hn
      use φ {
            a := P_infty.f (n + 1) ≫ (inv (N₁.map f)).f.f (n + 1)
            b := fun i => inv (f.app (op [n])) ≫ X.σ i }
      simp only [MorphComponents.id, ← id_φ, ← preComp_φ, preComp, ← postComp_φ, postComp,
        pInfty_f_naturality_assoc, IsIso.hom_inv_id_assoc, assoc, IsIso.inv_hom_id_assoc,
        SimplicialObject.σ_naturality, h₁, h₂, h₃]
      tauto⟩

theorem compatibility_n₂_n₁_karoubi :
    n₂ ⋙ (karoubiChainComplexEquivalence C ℕ).functor =
      karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C ⋙
        n₁ ⋙
          (karoubiChainComplexEquivalence (Karoubi C) ℕ).functor ⋙
            Functor.mapHomologicalComplex (KaroubiKaroubi.equivalence C).inverse _ :=
  by
  refine' CategoryTheory.Functor.ext (fun P => _) fun P Q f => _
  · refine' HomologicalComplex.ext _ _
    · ext n
      · dsimp
        simp only [karoubi_pInfty_f, comp_id, pInfty_f_naturality, id_comp]
      · rfl
    · rintro _ n (rfl : n + 1 = _)
      ext
      have h := (AlternatingFaceMapComplex.map P.p).comm (n + 1) n
      dsimp [n₂, karoubiChainComplexEquivalence, KaroubiKaroubi.inverse,
        KaroubiHomologicalComplexEquivalence.Functor.obj] at h⊢
      simp only [Karoubi.comp_f, assoc, Karoubi.eqToHom_f, eqToHom_refl, id_comp, comp_id,
        karoubi_alternating_face_map_complex_d, karoubi_pInfty_f, ←
        HomologicalComplex.Hom.comm_assoc, ← h, app_idem_assoc]
  · ext n
    dsimp [KaroubiKaroubi.inverse, karoubiFunctorCategoryEmbedding,
      KaroubiFunctorCategoryEmbedding.map]
    simp only [Karoubi.comp_f, karoubi_pInfty_f, HomologicalComplex.eqToHom_f, Karoubi.eqToHom_f,
      assoc, comp_id, pInfty_f_naturality, app_p_comp,
      karoubiChainComplexEquivalence_functor_obj_x_p, n₂_obj_p_f, eqToHom_refl,
      pInfty_f_naturality_assoc, app_comp_p, pInfty_f_idem_assoc]
#align algebraic_topology.dold_kan.compatibility_N₂_N₁_karoubi AlgebraicTopology.DoldKan.compatibility_n₂_n₁_karoubi

/-- We deduce that `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ))`
reflects isomorphisms from the fact that
`N₁ : simplicial_object (karoubi C) ⥤ karoubi (chain_complex (karoubi C) ℕ)` does. -/
instance : ReflectsIsomorphisms (n₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)) :=
  ⟨fun X Y f => by
    intro
    -- The following functor `F` reflects isomorphism because it is
    -- a composition of four functors which reflects isomorphisms.
    -- Then, it suffices to show that `F.map f` is an isomorphism.
    let F :=
      karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C ⋙
        n₁ ⋙
          (karoubiChainComplexEquivalence (Karoubi C) ℕ).functor ⋙
            Functor.mapHomologicalComplex (KaroubiKaroubi.equivalence C).inverse
              (ComplexShape.down ℕ)
    have : IsIso (F.map f) := by
      dsimp only [F]
      rw [← compatibility_n₂_n₁_karoubi, Functor.comp_map]
      apply Functor.map_isIso
    exact isIso_of_reflects_iso f F⟩

end DoldKan

end AlgebraicTopology

