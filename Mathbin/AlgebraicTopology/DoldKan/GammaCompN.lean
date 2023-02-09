/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.gamma_comp_n
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorGamma
import Mathbin.CategoryTheory.Idempotents.HomologicalComplex

/-! The counit isomorphism of the Dold-Kan equivalence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ))`.

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents Opposite SimplicialObject

open Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] [HasFiniteCoproducts C]

/-- The isomorphism  `(Γ₀.splitting K).nondeg_complex ≅ K` for all `K : chain_complex C ℕ`. -/
@[simps]
def Γ₀NondegComplexIso (K : ChainComplex C ℕ) : (Γ₀.splitting K).nondegComplex ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      dsimp
      simp only [id_comp, comp_id, AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp,
        Preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      · simp only [Fin.val_zero, pow_zero, one_zsmul]
        erw [Γ₀.obj.mapMono_on_summand_id_assoc, Γ₀.Obj.Termwise.mapMono_δ₀,
          Splitting.ι_πSummand_eq_id, comp_id]
      · intro i hi
        dsimp
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
        erw [Γ₀.obj.mapMono_on_summand_id_assoc, Γ₀.Obj.Termwise.mapMono_eq_zero, zero_comp,
          zsmul_zero]
        · intro h
          replace h := congr_arg SimplexCategory.len h
          change n + 1 = n at h
          linarith
        · simpa only [Isδ₀.iff] using hi)
#align algebraic_topology.dold_kan.Γ₀_nondeg_complex_iso AlgebraicTopology.DoldKan.Γ₀NondegComplexIso

/-- The natural isomorphism `(Γ₀.splitting K).nondeg_complex ≅ K` for `K : chain_complex C ℕ`. -/
def Γ₀'CompNondegComplexFunctor : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C ℕ) :=
  NatIso.ofComponents Γ₀NondegComplexIso fun X Y f =>
    by
    ext n
    dsimp
    simp only [comp_id, id_comp]
#align algebraic_topology.dold_kan.Γ₀'_comp_nondeg_complex_functor AlgebraicTopology.DoldKan.Γ₀'CompNondegComplexFunctor

/-- The natural isomorphism `Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`. -/
def n₁Γ₀ : Γ₀ ⋙ n₁ ≅ toKaroubi (ChainComplex C ℕ) :=
  calc
    Γ₀ ⋙ n₁ ≅ Γ₀' ⋙ Split.forget C ⋙ n₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ toKaroubi (ChainComplex C ℕ) := isoWhiskerRight Γ₀'CompNondegComplexFunctor _
    _ ≅ toKaroubi (ChainComplex C ℕ) := Functor.leftUnitor _
    
#align algebraic_topology.dold_kan.N₁Γ₀ AlgebraicTopology.DoldKan.n₁Γ₀

theorem n₁Γ₀_app (K : ChainComplex C ℕ) :
    n₁Γ₀.app K =
      (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.symm ≪≫
        (toKaroubi _).mapIso (Γ₀NondegComplexIso K) :=
  by
  ext1
  dsimp [n₁Γ₀]
  erw [id_comp, comp_id, comp_id]
  rfl
#align algebraic_topology.dold_kan.N₁Γ₀_app AlgebraicTopology.DoldKan.n₁Γ₀_app

theorem n₁Γ₀_hom_app (K : ChainComplex C ℕ) :
    n₁Γ₀.hom.app K =
      (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv ≫
        (toKaroubi _).map (Γ₀NondegComplexIso K).hom :=
  by
  change (N₁Γ₀.app K).hom = _
  simpa only [n₁Γ₀_app]
#align algebraic_topology.dold_kan.N₁Γ₀_hom_app AlgebraicTopology.DoldKan.n₁Γ₀_hom_app

theorem n₁Γ₀_inv_app (K : ChainComplex C ℕ) :
    n₁Γ₀.inv.app K =
      (toKaroubi _).map (Γ₀NondegComplexIso K).inv ≫
        (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom :=
  by
  change (N₁Γ₀.app K).inv = _
  simpa only [n₁Γ₀_app]
#align algebraic_topology.dold_kan.N₁Γ₀_inv_app AlgebraicTopology.DoldKan.n₁Γ₀_inv_app

@[simp]
theorem n₁Γ₀_hom_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (n₁Γ₀.hom.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv.f.f n :=
  by
  rw [n₁Γ₀_hom_app]
  apply comp_id
#align algebraic_topology.dold_kan.N₁Γ₀_hom_app_f_f AlgebraicTopology.DoldKan.n₁Γ₀_hom_app_f_f

@[simp]
theorem n₁Γ₀_inv_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (n₁Γ₀.inv.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom.f.f n :=
  by
  rw [n₁Γ₀_inv_app]
  apply id_comp
#align algebraic_topology.dold_kan.N₁Γ₀_inv_app_f_f AlgebraicTopology.DoldKan.n₁Γ₀_inv_app_f_f

theorem N₂Γ₂_toKaroubi : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ n₂ = Γ₀ ⋙ n₁ :=
  by
  have h :=
    Functor.congr_obj
      (functorExtension₂_comp_whiskeringLeft_toKaroubi (ChainComplex C ℕ) (SimplicialObject C)) Γ₀
  have h' :=
    Functor.congr_obj
      (functorExtension₁_comp_whiskeringLeft_toKaroubi (SimplicialObject C) (ChainComplex C ℕ)) n₁
  dsimp [n₂, Γ₂, functorExtension₁] at h h'⊢
  rw [← Functor.assoc, h, Functor.assoc, h']
#align algebraic_topology.dold_kan.N₂Γ₂_to_karoubi AlgebraicTopology.DoldKan.N₂Γ₂_toKaroubi

/-- Compatibility isomorphism between `to_karoubi _ ⋙ Γ₂ ⋙ N₂` and `Γ₀ ⋙ N₁` which
are functors `chain_complex C ℕ ⥤ karoubi (chain_complex C ℕ)`. -/
@[simps]
def n₂Γ₂ToKaroubiIso : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ n₂ ≅ Γ₀ ⋙ n₁ :=
  eqToIso N₂Γ₂_toKaroubi
#align algebraic_topology.dold_kan.N₂Γ₂_to_karoubi_iso AlgebraicTopology.DoldKan.n₂Γ₂ToKaroubiIso

/-- The counit isomorphism of the Dold-Kan equivalence for additive categories. -/
def n₂Γ₂ : Γ₂ ⋙ n₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ)) :=
  ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C ℕ))).preimageIso (n₂Γ₂ToKaroubiIso ≪≫ n₁Γ₀)
#align algebraic_topology.dold_kan.N₂Γ₂ AlgebraicTopology.DoldKan.n₂Γ₂

theorem n₂Γ₂_compatible_with_n₁Γ₀ (K : ChainComplex C ℕ) :
    n₂Γ₂.hom.app ((toKaroubi _).obj K) = n₂Γ₂ToKaroubiIso.hom.app K ≫ n₁Γ₀.hom.app K :=
  congr_app
    (((whiskeringLeft _ _ (Karoubi (ChainComplex C ℕ))).obj
          (toKaroubi (ChainComplex C ℕ))).image_preimage
      (n₂Γ₂ToKaroubiIso.hom ≫ n₁Γ₀.hom : _ ⟶ toKaroubi _ ⋙ 𝟭 _))
    K
#align algebraic_topology.dold_kan.N₂Γ₂_compatible_with_N₁Γ₀ AlgebraicTopology.DoldKan.n₂Γ₂_compatible_with_n₁Γ₀

@[simp]
theorem n₂Γ₂_inv_app_f_f (X : Karoubi (ChainComplex C ℕ)) (n : ℕ) :
    (n₂Γ₂.inv.app X).f.f n =
      X.p.f n ≫ (Γ₀.splitting X.x).ιSummand (Splitting.IndexSet.id (op [n])) :=
  by
  dsimp only [n₂Γ₂, Functor.preimageIso, Iso.trans]
  simp only [whiskeringLeft_obj_preimage_app, n₂Γ₂ToKaroubiIso_inv, Functor.id_map,
    NatTrans.comp_app, eqToHom_app, Functor.comp_map, assoc, Karoubi.comp_f, Karoubi.eqToHom_f,
    eqToHom_refl, comp_id, Karoubi.comp_p_assoc, n₂_map_f_f, HomologicalComplex.comp_f,
    n₁Γ₀_inv_app_f_f, pInfty_on_Γ₀_splitting_summand_eq_self_assoc,
    Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f, Γ₂_map_f_app, Karoubi.decompIdP_f]
  dsimp [toKaroubi]
  rw [Splitting.ι_desc]
  dsimp [Splitting.IndexSet.id]
  rw [Karoubi.HomologicalComplex.p_idem_assoc]
#align algebraic_topology.dold_kan.N₂Γ₂_inv_app_f_f AlgebraicTopology.DoldKan.n₂Γ₂_inv_app_f_f

end DoldKan

end AlgebraicTopology

