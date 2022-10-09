/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorN
import Mathbin.AlgebraicTopology.DoldKan.Decomposition
import Mathbin.CategoryTheory.Idempotents.HomologicalComplex

/-!

# N₁ and N₂ reflects isomorphisms

In this file, it is shown that the functor
`N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
reflects isomorphisms for any preadditive category `C`.

TODO @joelriou: deduce that `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
also reflects isomorphisms.

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
    suffices ∀ n : ℕ, is_iso (f.app (op [n])) by
      haveI : ∀ Δ : SimplexCategoryᵒᵖ, is_iso (f.app Δ) := fun Δ => this Δ.unop.len
      apply nat_iso.is_iso_of_is_iso_app
    -- restating the assumption in a more practical form
    have h₁ := HomologicalComplex.congr_hom (karoubi.hom_ext.mp (is_iso.hom_inv_id (N₁.map f)))
    have h₂ := HomologicalComplex.congr_hom (karoubi.hom_ext.mp (is_iso.inv_hom_id (N₁.map f)))
    have h₃ := fun n => karoubi.homological_complex.p_comm_f_assoc (inv (N₁.map f)) n (f.app (op [n]))
    simp only [N₁_map_f, karoubi.comp, HomologicalComplex.comp_f, alternating_face_map_complex.map_f, N₁_obj_p,
      karoubi.id_eq, assoc] at h₁ h₂ h₃
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
      use φ { a := P_infty.f (n + 1) ≫ (inv (N₁.map f)).f.f (n + 1), b := fun i => inv (f.app (op [n])) ≫ X.σ i }
      simp only [morph_components.id, ← id_φ, ← pre_comp_φ, pre_comp, ← post_comp_φ, post_comp,
        P_infty_f_naturality_assoc, is_iso.hom_inv_id_assoc, assoc, is_iso.inv_hom_id_assoc,
        simplicial_object.σ_naturality, h₁, h₂, h₃]
      tauto
      ⟩

end DoldKan

end AlgebraicTopology

