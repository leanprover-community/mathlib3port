/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.n_comp_gamma
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.GammaCompN
import Mathbin.AlgebraicTopology.DoldKan.NReflectsIso

/-! The unit isomorphism of the Dold-Kan equivalence

In order to construct the unit isomorphism of the Dold-Kan equivalence,
we first construct natural transformations
`Γ₂N₁.nat_trans : N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)` and
`Γ₂N₂.nat_trans : N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)`.
It is then shown that `Γ₂N₂.nat_trans` is an isomorphism by using
that it becomes an isomorphism after the application of the functor
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
which reflects isomorphisms.

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents SimplexCategory Opposite SimplicialObject

open Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C]

theorem pInfty_comp_map_mono_eq_zero (X : SimplicialObject C) {n : ℕ} {Δ' : SimplexCategory}
    (i : Δ' ⟶ [n]) [hi : Mono i] (h₁ : Δ'.len ≠ n) (h₂ : ¬Isδ₀ i) : pInfty.f n ≫ X.map i.op = 0 :=
  by
  induction' Δ' using SimplexCategory.rec with m
  obtain ⟨k, hk⟩ :=
    Nat.exists_eq_add_of_lt
      (len_lt_of_mono i fun h => by
        rw [← h] at h₁
        exact h₁ rfl)
  simp only [len_mk] at hk
  cases k
  · change n = m + 1 at hk
    subst hk
    obtain ⟨j, rfl⟩ := eq_δ_of_mono i
    rw [Isδ₀.iff] at h₂
    have h₃ : 1 ≤ (j : ℕ) := by
      by_contra
      exact h₂ (by simpa only [Fin.ext_iff, not_le, Nat.lt_one_iff] using h)
    exact (HigherFacesVanish.of_p (m + 1) m).comp_δ_eq_zero j h₂ (by linarith)
  · simp only [Nat.succ_eq_add_one, ← add_assoc] at hk
    clear h₂ hi
    subst hk
    obtain ⟨j₁, i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h =>
        by
        have h' := len_le_of_epi (SimplexCategory.epi_iff_surjective.2 h)
        dsimp at h'
        linarith
    obtain ⟨j₂, i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h =>
        by
        have h' := len_le_of_epi (SimplexCategory.epi_iff_surjective.2 h)
        dsimp at h'
        linarith
    by_cases hj₁ : j₁ = 0
    · subst hj₁
      rw [assoc, ← SimplexCategory.δ_comp_δ'' (Fin.zero_le _)]
      simp only [op_comp, X.map_comp, assoc, pInfty_f]
      erw [(HigherFacesVanish.of_p _ _).comp_δ_eq_zero_assoc _ j₂.succ_ne_zero, zero_comp]
      rw [Fin.val_succ]
      linarith
    · simp only [op_comp, X.map_comp, assoc, pInfty_f]
      erw [(HigherFacesVanish.of_p _ _).comp_δ_eq_zero_assoc _ hj₁, zero_comp]
      by_contra
      exact
        hj₁
          (by
            simp only [Fin.ext_iff, Fin.val_zero]
            linarith)
#align algebraic_topology.dold_kan.P_infty_comp_map_mono_eq_zero AlgebraicTopology.DoldKan.pInfty_comp_map_mono_eq_zero

@[reassoc.1]
theorem Γ₀_obj_termwise_mapMono_comp_pInfty (X : SimplicialObject C) {Δ Δ' : SimplexCategory}
    (i : Δ ⟶ Δ') [Mono i] :
    Γ₀.Obj.Termwise.mapMono (AlternatingFaceMapComplex.obj X) i ≫ pInfty.f Δ.len =
      pInfty.f Δ'.len ≫ X.map i.op :=
  by
  induction' Δ using SimplexCategory.rec with n
  induction' Δ' using SimplexCategory.rec with n'
  dsimp
  -- We start with the case `i` is an identity
  by_cases n = n'
  · subst h
    simp only [SimplexCategory.eq_id_of_mono i, Γ₀.Obj.Termwise.mapMono_id, op_id, X.map_id]
    dsimp
    simp only [id_comp, comp_id]
  by_cases hi : Isδ₀ i
  -- The case `i = δ 0`
  · have h' : n' = n + 1 := hi.left
    subst h'
    simp only [Γ₀.Obj.Termwise.mapMono_δ₀' _ i hi]
    dsimp
    rw [← P_infty.comm' _ n rfl, AlternatingFaceMapComplex.obj_d_eq]
    simp only [eq_self_iff_true, id_comp, if_true, Preadditive.comp_sum]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    rotate_left
    · intro b hb hb'
      rw [Preadditive.comp_zsmul]
      erw [pInfty_comp_map_mono_eq_zero X (SimplexCategory.δ b) h
          (by
            rw [Isδ₀.iff]
            exact hb'),
        zsmul_zero]
    · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
    · simpa only [hi.eq_δ₀, Fin.val_zero, pow_zero, one_zsmul]
  -- The case `i ≠ δ 0`
  · rw [Γ₀.Obj.Termwise.mapMono_eq_zero _ i _ hi, zero_comp]
    swap
    · by_contra h'
      exact h (congr_arg SimplexCategory.len h'.symm)
    rw [pInfty_comp_map_mono_eq_zero]
    · exact h
    · by_contra h'
      exact hi h'
#align algebraic_topology.dold_kan.Γ₀_obj_termwise_map_mono_comp_P_infty AlgebraicTopology.DoldKan.Γ₀_obj_termwise_mapMono_comp_pInfty

variable [HasFiniteCoproducts C]

namespace Γ₂N₁

/-- The natural transformation `N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)`. -/
@[simps]
def natTrans : (n₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ ⟶ toKaroubi _
    where
  app X :=
    { f :=
        { app := fun Δ => (Γ₀.splitting K[X]).desc Δ fun A => pInfty.f A.1.unop.len ≫ X.map A.e.op
          naturality' := fun Δ Δ' θ =>
            by
            apply (Γ₀.splitting K[X]).hom_ext'
            intro A
            change _ ≫ (Γ₀.obj K[X]).map θ ≫ _ = _
            simp only [Splitting.ι_desc_assoc, assoc, Γ₀.obj.map_on_summand'_assoc,
              Splitting.ι_desc]
            erw [Γ₀_obj_termwise_mapMono_comp_pInfty_assoc X (image.ι (θ.unop ≫ A.e))]
            dsimp only [toKaroubi]
            simp only [← X.map_comp]
            congr 2
            simp only [eqToHom_refl, id_comp, comp_id, ← op_comp]
            exact Quiver.Hom.unop_inj (A.fac_pull θ) }
      comm := by
        apply (Γ₀.splitting K[X]).hom_ext
        intro n
        dsimp [n₁]
        simp only [← Splitting.ιSummand_id, Splitting.ι_desc, comp_id, Splitting.ι_desc_assoc,
          assoc, pInfty_f_idem_assoc] }
  naturality' X Y f := by
    ext1
    apply (Γ₀.splitting K[X]).hom_ext
    intro n
    dsimp [n₁, toKaroubi]
    simpa only [← Splitting.ιSummand_id, Splitting.ι_desc, Splitting.ι_desc_assoc, assoc,
      pInfty_f_idem_assoc, Karoubi.comp_f, NatTrans.comp_app, Γ₂_map_f_app,
      HomologicalComplex.comp_f, AlternatingFaceMapComplex.map_f, pInfty_f_naturality_assoc,
      NatTrans.naturality]
#align algebraic_topology.dold_kan.Γ₂N₁.nat_trans AlgebraicTopology.DoldKan.Γ₂N₁.natTrans

end Γ₂N₁

/-- The compatibility isomorphism relating `N₂ ⋙ Γ₂` and `N₁ ⋙ Γ₂`. -/
@[simps]
def compatibilityΓ₂N₁Γ₂N₂ : toKaroubi (SimplicialObject C) ⋙ n₂ ⋙ Γ₂ ≅ n₁ ⋙ Γ₂ :=
  eqToIso (Functor.congr_obj (functorExtension₁_comp_whiskeringLeft_toKaroubi _ _) (n₁ ⋙ Γ₂))
#align algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂ AlgebraicTopology.DoldKan.compatibilityΓ₂N₁Γ₂N₂

namespace Γ₂N₂

/-- The natural transformation `N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)`. -/
def natTrans : (n₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ Γ₂ ⟶ 𝟭 _ :=
  ((whiskeringLeft _ _ _).obj _).preimage (compatibilityΓ₂N₁Γ₂N₂.hom ≫ Γ₂N₁.natTrans)
#align algebraic_topology.dold_kan.Γ₂N₂.nat_trans AlgebraicTopology.DoldKan.Γ₂N₂.natTrans

theorem natTrans_app_f_app (P : Karoubi (SimplicialObject C)) :
    Γ₂N₂.natTrans.app P =
      (n₂ ⋙ Γ₂).map P.decompIdI ≫
        (compatibilityΓ₂N₁Γ₂N₂.hom ≫ Γ₂N₁.natTrans).app P.x ≫ P.decompIdP :=
  whiskeringLeft_obj_preimage_app (compatibilityΓ₂N₁Γ₂N₂.hom ≫ Γ₂N₁.natTrans) P
#align algebraic_topology.dold_kan.Γ₂N₂.nat_trans_app_f_app AlgebraicTopology.DoldKan.Γ₂N₂.natTrans_app_f_app

end Γ₂N₂

theorem compatibilityΓ₂N₁Γ₂N₂_natTrans (X : SimplicialObject C) :
    Γ₂N₁.natTrans.app X =
      (compatibilityΓ₂N₁Γ₂N₂.app X).inv ≫ Γ₂N₂.natTrans.app ((toKaroubi _).obj X) :=
  by
  rw [← cancel_epi (compatibility_Γ₂N₁_Γ₂N₂.app X).hom, Iso.hom_inv_id_assoc]
  exact
    congr_app
      (((whiskeringLeft _ _ _).obj _).image_preimage
          (compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.natTrans : _ ⟶ toKaroubi _ ⋙ 𝟭 _)).symm
      X
#align algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂_nat_trans AlgebraicTopology.DoldKan.compatibilityΓ₂N₁Γ₂N₂_natTrans

theorem identity_n₂_objectwise (P : Karoubi (SimplicialObject C)) :
    n₂Γ₂.inv.app (n₂.obj P) ≫ n₂.map (Γ₂N₂.natTrans.app P) = 𝟙 (n₂.obj P) :=
  by
  ext n
  have eq₁ :
    (N₂Γ₂.inv.app (N₂.obj P)).f.f n =
      P_infty.f n ≫
        P.p.app (op [n]) ≫ (Γ₀.splitting (N₂.obj P).x).ιSummand (Splitting.IndexSet.id (op [n])) :=
    by simp only [n₂Γ₂_inv_app_f_f, n₂_obj_p_f, assoc]
  have eq₂ :
    (Γ₀.splitting (N₂.obj P).x).ιSummand (Splitting.IndexSet.id (op [n])) ≫
        (N₂.map (Γ₂N₂.nat_trans.app P)).f.f n =
      P_infty.f n ≫ P.p.app (op [n]) :=
    by
    dsimp [n₂]
    simp only [Γ₂N₂.natTrans_app_f_app, pInfty_on_Γ₀_splitting_summand_eq_self_assoc,
      Functor.comp_map, compatibilityΓ₂N₁Γ₂N₂_hom, NatTrans.comp_app, eqToHom_app, assoc,
      Karoubi.comp_f, Karoubi.eqToHom_f, eqToHom_refl, comp_id, Karoubi.decompIdP_f,
      Karoubi.comp_p_assoc, Γ₂_map_f_app, n₂_map_f_f, Karoubi.decompIdI_f, Γ₂N₁.natTrans_app_f_app]
    erw [Splitting.ι_desc_assoc, assoc, assoc, Splitting.ι_desc_assoc]
    dsimp [Splitting.IndexSet.id, Splitting.IndexSet.e]
    simp only [assoc, NatTrans.naturality, pInfty_f_naturality_assoc, app_idem_assoc,
      pInfty_f_idem_assoc]
    erw [P.X.map_id, comp_id]
  simp only [Karoubi.comp_f, HomologicalComplex.comp_f, Karoubi.id_eq, n₂_obj_p_f, assoc, eq₁, eq₂,
    pInfty_f_naturality_assoc, app_idem, pInfty_f_idem_assoc]
#align algebraic_topology.dold_kan.identity_N₂_objectwise AlgebraicTopology.DoldKan.identity_n₂_objectwise

theorem identity_n₂ :
    ((𝟙 (n₂ : Karoubi (SimplicialObject C) ⥤ _) ◫ n₂Γ₂.inv) ≫ Γ₂N₂.natTrans ◫ 𝟙 n₂ : n₂ ⟶ n₂) =
      𝟙 n₂ :=
  by
  ext P : 2
  dsimp
  rw [Γ₂.map_id, N₂.map_id, comp_id, id_comp, identity_n₂_objectwise P]
#align algebraic_topology.dold_kan.identity_N₂ AlgebraicTopology.DoldKan.identity_n₂

instance : IsIso (Γ₂N₂.natTrans : (n₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ _ ⟶ _) :=
  by
  have : ∀ P : Karoubi (SimplicialObject C), IsIso (Γ₂N₂.nat_trans.app P) :=
    by
    intro P
    have : IsIso (N₂.map (Γ₂N₂.nat_trans.app P)) :=
      by
      have h := identity_n₂_objectwise P
      erw [hom_comp_eq_id] at h
      rw [h]
      infer_instance
    exact isIso_of_reflects_iso _ n₂
  apply NatIso.isIso_of_isIso_app

instance : IsIso (Γ₂N₁.natTrans : (n₁ : SimplicialObject C ⥤ _) ⋙ _ ⟶ _) :=
  by
  have : ∀ X : SimplicialObject C, IsIso (Γ₂N₁.nat_trans.app X) :=
    by
    intro X
    rw [compatibilityΓ₂N₁Γ₂N₂_natTrans]
    infer_instance
  apply NatIso.isIso_of_isIso_app

/-- The unit isomorphism of the Dold-Kan equivalence. -/
@[simp]
def Γ₂N₂ : 𝟭 _ ≅ (n₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ Γ₂ :=
  (asIso Γ₂N₂.natTrans).symm
#align algebraic_topology.dold_kan.Γ₂N₂ AlgebraicTopology.DoldKan.Γ₂N₂

/-- The natural isomorphism `to_karoubi (simplicial_object C) ≅ N₁ ⋙ Γ₂`. -/
@[simps]
def Γ₂N₁ : toKaroubi _ ≅ (n₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ :=
  (asIso Γ₂N₁.natTrans).symm
#align algebraic_topology.dold_kan.Γ₂N₁ AlgebraicTopology.DoldKan.Γ₂N₁

end DoldKan

end AlgebraicTopology

