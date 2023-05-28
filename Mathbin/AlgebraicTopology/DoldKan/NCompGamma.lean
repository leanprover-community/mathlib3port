/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.n_comp_gamma
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.GammaCompN
import Mathbin.AlgebraicTopology.DoldKan.NReflectsIso

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 The unit isomorphism of the Dold-Kan equivalence

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

/- warning: algebraic_topology.dold_kan.P_infty_comp_map_mono_eq_zero -> AlgebraicTopology.DoldKan.PInfty_comp_map_mono_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.P_infty_comp_map_mono_eq_zero AlgebraicTopology.DoldKan.PInfty_comp_map_mono_eq_zeroₓ'. -/
theorem PInfty_comp_map_mono_eq_zero (X : SimplicialObject C) {n : ℕ} {Δ' : SimplexCategory}
    (i : Δ' ⟶ [n]) [hi : Mono i] (h₁ : Δ'.len ≠ n) (h₂ : ¬Isδ₀ i) : PInfty.f n ≫ X.map i.op = 0 :=
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
    rw [is_δ₀.iff] at h₂
    have h₃ : 1 ≤ (j : ℕ) := by
      by_contra
      exact h₂ (by simpa only [Fin.ext_iff, not_le, Nat.lt_one_iff] using h)
    exact (higher_faces_vanish.of_P (m + 1) m).comp_δ_eq_zero j h₂ (by linarith)
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
      simp only [op_comp, X.map_comp, assoc, P_infty_f]
      erw [(higher_faces_vanish.of_P _ _).comp_δ_eq_zero_assoc _ j₂.succ_ne_zero, zero_comp]
      rw [Fin.val_succ]
      linarith
    · simp only [op_comp, X.map_comp, assoc, P_infty_f]
      erw [(higher_faces_vanish.of_P _ _).comp_δ_eq_zero_assoc _ hj₁, zero_comp]
      by_contra
      exact
        hj₁
          (by
            simp only [Fin.ext_iff, Fin.val_zero]
            linarith)
#align algebraic_topology.dold_kan.P_infty_comp_map_mono_eq_zero AlgebraicTopology.DoldKan.PInfty_comp_map_mono_eq_zero

/- warning: algebraic_topology.dold_kan.Γ₀_obj_termwise_map_mono_comp_P_infty -> AlgebraicTopology.DoldKan.Γ₀_obj_termwise_mapMono_comp_PInfty is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Γ₀_obj_termwise_map_mono_comp_P_infty AlgebraicTopology.DoldKan.Γ₀_obj_termwise_mapMono_comp_PInftyₓ'. -/
@[reassoc]
theorem Γ₀_obj_termwise_mapMono_comp_PInfty (X : SimplicialObject C) {Δ Δ' : SimplexCategory}
    (i : Δ ⟶ Δ') [Mono i] :
    Γ₀.Obj.Termwise.mapMono (AlternatingFaceMapComplex.obj X) i ≫ PInfty.f Δ.len =
      PInfty.f Δ'.len ≫ X.map i.op :=
  by
  induction' Δ using SimplexCategory.rec with n
  induction' Δ' using SimplexCategory.rec with n'
  dsimp
  -- We start with the case `i` is an identity
  by_cases n = n'
  · subst h
    simp only [SimplexCategory.eq_id_of_mono i, Γ₀.obj.termwise.map_mono_id, op_id, X.map_id]
    dsimp
    simp only [id_comp, comp_id]
  by_cases hi : is_δ₀ i
  -- The case `i = δ 0`
  · have h' : n' = n + 1 := hi.left
    subst h'
    simp only [Γ₀.obj.termwise.map_mono_δ₀' _ i hi]
    dsimp
    rw [← P_infty.comm' _ n rfl, alternating_face_map_complex.obj_d_eq]
    simp only [eq_self_iff_true, id_comp, if_true, preadditive.comp_sum]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    rotate_left
    · intro b hb hb'
      rw [preadditive.comp_zsmul]
      erw [P_infty_comp_map_mono_eq_zero X (SimplexCategory.δ b) h
          (by
            rw [is_δ₀.iff]
            exact hb'),
        zsmul_zero]
    · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
    · simpa only [hi.eq_δ₀, Fin.val_zero, pow_zero, one_zsmul]
  -- The case `i ≠ δ 0`
  · rw [Γ₀.obj.termwise.map_mono_eq_zero _ i _ hi, zero_comp]
    swap
    · by_contra h'
      exact h (congr_arg SimplexCategory.len h'.symm)
    rw [P_infty_comp_map_mono_eq_zero]
    · exact h
    · by_contra h'
      exact hi h'
#align algebraic_topology.dold_kan.Γ₀_obj_termwise_map_mono_comp_P_infty AlgebraicTopology.DoldKan.Γ₀_obj_termwise_mapMono_comp_PInfty

variable [HasFiniteCoproducts C]

namespace Γ₂N₁

/- warning: algebraic_topology.dold_kan.Γ₂N₁.nat_trans -> AlgebraicTopology.DoldKan.Γ₂N₁.natTrans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Γ₂N₁.nat_trans AlgebraicTopology.DoldKan.Γ₂N₁.natTransₓ'. -/
/-- The natural transformation `N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)`. -/
@[simps]
def natTrans : (N₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ ⟶ toKaroubi _
    where
  app X :=
    { f :=
        { app := fun Δ => (Γ₀.splitting K[X]).desc Δ fun A => PInfty.f A.1.unop.len ≫ X.map A.e.op
          naturality' := fun Δ Δ' θ =>
            by
            apply (Γ₀.splitting K[X]).hom_ext'
            intro A
            change _ ≫ (Γ₀.obj K[X]).map θ ≫ _ = _
            simp only [splitting.ι_desc_assoc, assoc, Γ₀.obj.map_on_summand'_assoc,
              splitting.ι_desc]
            erw [Γ₀_obj_termwise_map_mono_comp_P_infty_assoc X (image.ι (θ.unop ≫ A.e))]
            dsimp only [to_karoubi]
            simp only [← X.map_comp]
            congr 2
            simp only [eq_to_hom_refl, id_comp, comp_id, ← op_comp]
            exact Quiver.Hom.unop_inj (A.fac_pull θ) }
      comm := by
        apply (Γ₀.splitting K[X]).hom_ext
        intro n
        dsimp [N₁]
        simp only [← splitting.ι_summand_id, splitting.ι_desc, comp_id, splitting.ι_desc_assoc,
          assoc, P_infty_f_idem_assoc] }
  naturality' X Y f := by
    ext1
    apply (Γ₀.splitting K[X]).hom_ext
    intro n
    dsimp [N₁, to_karoubi]
    simpa only [← splitting.ι_summand_id, splitting.ι_desc, splitting.ι_desc_assoc, assoc,
      P_infty_f_idem_assoc, karoubi.comp_f, nat_trans.comp_app, Γ₂_map_f_app,
      HomologicalComplex.comp_f, alternating_face_map_complex.map_f, P_infty_f_naturality_assoc,
      nat_trans.naturality]
#align algebraic_topology.dold_kan.Γ₂N₁.nat_trans AlgebraicTopology.DoldKan.Γ₂N₁.natTrans

end Γ₂N₁

/- warning: algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂ -> AlgebraicTopology.DoldKan.compatibility_Γ₂N₁_Γ₂N₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂ AlgebraicTopology.DoldKan.compatibility_Γ₂N₁_Γ₂N₂ₓ'. -/
/-- The compatibility isomorphism relating `N₂ ⋙ Γ₂` and `N₁ ⋙ Γ₂`. -/
@[simps]
def compatibility_Γ₂N₁_Γ₂N₂ : toKaroubi (SimplicialObject C) ⋙ N₂ ⋙ Γ₂ ≅ N₁ ⋙ Γ₂ :=
  eqToIso (Functor.congr_obj (functorExtension₁_comp_whiskeringLeft_toKaroubi _ _) (N₁ ⋙ Γ₂))
#align algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂ AlgebraicTopology.DoldKan.compatibility_Γ₂N₁_Γ₂N₂

namespace Γ₂N₂

/- warning: algebraic_topology.dold_kan.Γ₂N₂.nat_trans -> AlgebraicTopology.DoldKan.Γ₂N₂.natTrans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Γ₂N₂.nat_trans AlgebraicTopology.DoldKan.Γ₂N₂.natTransₓ'. -/
/-- The natural transformation `N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)`. -/
def natTrans : (N₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ Γ₂ ⟶ 𝟭 _ :=
  ((whiskeringLeft _ _ _).obj _).Preimage (compatibility_Γ₂N₁_Γ₂N₂.Hom ≫ Γ₂N₁.natTrans)
#align algebraic_topology.dold_kan.Γ₂N₂.nat_trans AlgebraicTopology.DoldKan.Γ₂N₂.natTrans

/- warning: algebraic_topology.dold_kan.Γ₂N₂.nat_trans_app_f_app -> AlgebraicTopology.DoldKan.Γ₂N₂.natTrans_app_f_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Γ₂N₂.nat_trans_app_f_app AlgebraicTopology.DoldKan.Γ₂N₂.natTrans_app_f_appₓ'. -/
theorem natTrans_app_f_app (P : Karoubi (SimplicialObject C)) :
    Γ₂N₂.natTrans.app P =
      (N₂ ⋙ Γ₂).map P.decompId_i ≫
        (compatibility_Γ₂N₁_Γ₂N₂.Hom ≫ Γ₂N₁.natTrans).app P.pt ≫ P.decompId_p :=
  whiskeringLeft_obj_preimage_app (compatibility_Γ₂N₁_Γ₂N₂.Hom ≫ Γ₂N₁.natTrans) P
#align algebraic_topology.dold_kan.Γ₂N₂.nat_trans_app_f_app AlgebraicTopology.DoldKan.Γ₂N₂.natTrans_app_f_app

end Γ₂N₂

/- warning: algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂_nat_trans -> AlgebraicTopology.DoldKan.compatibility_Γ₂N₁_Γ₂N₂_natTrans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂_nat_trans AlgebraicTopology.DoldKan.compatibility_Γ₂N₁_Γ₂N₂_natTransₓ'. -/
theorem compatibility_Γ₂N₁_Γ₂N₂_natTrans (X : SimplicialObject C) :
    Γ₂N₁.natTrans.app X =
      (compatibility_Γ₂N₁_Γ₂N₂.app X).inv ≫ Γ₂N₂.natTrans.app ((toKaroubi _).obj X) :=
  by
  rw [← cancel_epi (compatibility_Γ₂N₁_Γ₂N₂.app X).Hom, iso.hom_inv_id_assoc]
  exact
    congr_app
      (((whiskering_left _ _ _).obj _).image_preimage
          (compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.nat_trans : _ ⟶ to_karoubi _ ⋙ 𝟭 _)).symm
      X
#align algebraic_topology.dold_kan.compatibility_Γ₂N₁_Γ₂N₂_nat_trans AlgebraicTopology.DoldKan.compatibility_Γ₂N₁_Γ₂N₂_natTrans

/- warning: algebraic_topology.dold_kan.identity_N₂_objectwise -> AlgebraicTopology.DoldKan.identity_N₂_objectwise is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.identity_N₂_objectwise AlgebraicTopology.DoldKan.identity_N₂_objectwiseₓ'. -/
theorem identity_N₂_objectwise (P : Karoubi (SimplicialObject C)) :
    N₂Γ₂.inv.app (N₂.obj P) ≫ N₂.map (Γ₂N₂.natTrans.app P) = 𝟙 (N₂.obj P) :=
  by
  ext n
  have eq₁ :
    (N₂Γ₂.inv.app (N₂.obj P)).f.f n =
      P_infty.f n ≫
        P.p.app (op [n]) ≫
          (Γ₀.splitting (N₂.obj P).pt).ιSummand (splitting.index_set.id (op [n])) :=
    by simp only [N₂Γ₂_inv_app_f_f, N₂_obj_p_f, assoc]
  have eq₂ :
    (Γ₀.splitting (N₂.obj P).pt).ιSummand (splitting.index_set.id (op [n])) ≫
        (N₂.map (Γ₂N₂.nat_trans.app P)).f.f n =
      P_infty.f n ≫ P.p.app (op [n]) :=
    by
    dsimp [N₂]
    simp only [Γ₂N₂.nat_trans_app_f_app, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
      functor.comp_map, compatibility_Γ₂N₁_Γ₂N₂_hom, nat_trans.comp_app, eq_to_hom_app, assoc,
      karoubi.comp_f, karoubi.eq_to_hom_f, eq_to_hom_refl, comp_id, karoubi.decomp_id_p_f,
      karoubi.comp_p_assoc, Γ₂_map_f_app, N₂_map_f_f, karoubi.decomp_id_i_f,
      Γ₂N₁.nat_trans_app_f_app]
    erw [splitting.ι_desc_assoc, assoc, assoc, splitting.ι_desc_assoc]
    dsimp [splitting.index_set.id, splitting.index_set.e]
    simp only [assoc, nat_trans.naturality, P_infty_f_naturality_assoc, app_idem_assoc,
      P_infty_f_idem_assoc]
    erw [P.X.map_id, comp_id]
  simp only [karoubi.comp_f, HomologicalComplex.comp_f, karoubi.id_eq, N₂_obj_p_f, assoc, eq₁, eq₂,
    P_infty_f_naturality_assoc, app_idem, P_infty_f_idem_assoc]
#align algebraic_topology.dold_kan.identity_N₂_objectwise AlgebraicTopology.DoldKan.identity_N₂_objectwise

/- warning: algebraic_topology.dold_kan.identity_N₂ -> AlgebraicTopology.DoldKan.identity_N₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.identity_N₂ AlgebraicTopology.DoldKan.identity_N₂ₓ'. -/
theorem identity_N₂ :
    ((𝟙 (N₂ : Karoubi (SimplicialObject C) ⥤ _) ◫ N₂Γ₂.inv) ≫ Γ₂N₂.natTrans ◫ 𝟙 N₂ : N₂ ⟶ N₂) =
      𝟙 N₂ :=
  by
  ext P : 2
  dsimp
  rw [Γ₂.map_id, N₂.map_id, comp_id, id_comp, identity_N₂_objectwise P]
#align algebraic_topology.dold_kan.identity_N₂ AlgebraicTopology.DoldKan.identity_N₂

instance : IsIso (Γ₂N₂.natTrans : (N₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ _ ⟶ _) :=
  by
  have : ∀ P : karoubi (simplicial_object C), is_iso (Γ₂N₂.nat_trans.app P) :=
    by
    intro P
    have : is_iso (N₂.map (Γ₂N₂.nat_trans.app P)) :=
      by
      have h := identity_N₂_objectwise P
      erw [hom_comp_eq_id] at h
      rw [h]
      infer_instance
    exact is_iso_of_reflects_iso _ N₂
  apply nat_iso.is_iso_of_is_iso_app

instance : IsIso (Γ₂N₁.natTrans : (N₁ : SimplicialObject C ⥤ _) ⋙ _ ⟶ _) :=
  by
  have : ∀ X : simplicial_object C, is_iso (Γ₂N₁.nat_trans.app X) :=
    by
    intro X
    rw [compatibility_Γ₂N₁_Γ₂N₂_nat_trans]
    infer_instance
  apply nat_iso.is_iso_of_is_iso_app

/- warning: algebraic_topology.dold_kan.Γ₂N₂ -> AlgebraicTopology.DoldKan.Γ₂N₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Γ₂N₂ AlgebraicTopology.DoldKan.Γ₂N₂ₓ'. -/
/-- The unit isomorphism of the Dold-Kan equivalence. -/
@[simp]
def Γ₂N₂ : 𝟭 _ ≅ (N₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ Γ₂ :=
  (asIso Γ₂N₂.natTrans).symm
#align algebraic_topology.dold_kan.Γ₂N₂ AlgebraicTopology.DoldKan.Γ₂N₂

/- warning: algebraic_topology.dold_kan.Γ₂N₁ -> AlgebraicTopology.DoldKan.Γ₂N₁ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasFiniteCoproducts.{u2, u1} C _inst_1], CategoryTheory.Iso.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u2, u2, max u2 u1, max u2 u1} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1))) (CategoryTheory.Functor.category.{u2, u2, max u2 u1, max u2 u1} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1))) (CategoryTheory.Idempotents.toKaroubi.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1)) (CategoryTheory.Functor.comp.{u2, u2, u2, max u2 u1, max u1 u2, max u2 u1} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (HomologicalComplex.CategoryTheory.category.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne))) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u1 u2, u2} (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (HomologicalComplex.CategoryTheory.category.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne))) (CategoryTheory.Idempotents.Karoubi.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.CategoryTheory.category.{max u2 u1, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.SimplicialObject.category.{u2, u1} C _inst_1)) (AlgebraicTopology.DoldKan.N₁.{u1, u2} C _inst_1 _inst_2) (AlgebraicTopology.DoldKan.Γ₂.{u1, u2} C _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Limits.HasFiniteCoproducts.{u2, u1} C _inst_1], CategoryTheory.Iso.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1))) (CategoryTheory.Functor.category.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1))) (CategoryTheory.Idempotents.toKaroubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1)) (CategoryTheory.Functor.comp.{u2, u2, u2, max u1 u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)))) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (ChainComplex.{u2, u1, 0} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)))) (CategoryTheory.Idempotents.Karoubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1)) (CategoryTheory.Idempotents.Karoubi.instCategoryKaroubi.{max u1 u2, u2} (CategoryTheory.SimplicialObject.{u2, u1} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u2, u1} C _inst_1)) (AlgebraicTopology.DoldKan.N₁.{u1, u2} C _inst_1 _inst_2) (AlgebraicTopology.DoldKan.Γ₂.{u1, u2} C _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.Γ₂N₁ AlgebraicTopology.DoldKan.Γ₂N₁ₓ'. -/
/-- The natural isomorphism `to_karoubi (simplicial_object C) ≅ N₁ ⋙ Γ₂`. -/
@[simps]
def Γ₂N₁ : toKaroubi _ ≅ (N₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ :=
  (asIso Γ₂N₁.natTrans).symm
#align algebraic_topology.dold_kan.Γ₂N₁ AlgebraicTopology.DoldKan.Γ₂N₁

end DoldKan

end AlgebraicTopology

