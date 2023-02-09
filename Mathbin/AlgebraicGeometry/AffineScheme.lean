/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.AffineScheme
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.GammaSpecAdjunction
import Mathbin.AlgebraicGeometry.OpenImmersion
import Mathbin.CategoryTheory.Limits.Opposites
import Mathbin.RingTheory.Localization.InvSubmonoid

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `algebraic_geometry.is_affine_open.from_Spec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/-- The category of affine schemes -/
@[nolint has_nonempty_instance]
def AffineScheme :=
  Scheme.spec.EssImageSubcategory deriving Category
#align algebraic_geometry.AffineScheme AlgebraicGeometry.AffineScheme

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso (ΓSpec.adjunction.unit.app X)
#align algebraic_geometry.is_affine AlgebraicGeometry.IsAffine

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Scheme.spec.obj (op <| Scheme.Γ.obj <| op X) :=
  asIso (ΓSpec.adjunction.unit.app X)
#align algebraic_geometry.Scheme.iso_Spec AlgebraicGeometry.Scheme.isoSpec

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typclass version. -/
@[simps]
def AffineScheme.mk (X : Scheme) (h : IsAffine X) : AffineScheme :=
  ⟨X, @mem_essImage_of_unit_isIso _ _ _ _ h.1⟩
#align algebraic_geometry.AffineScheme.mk AlgebraicGeometry.AffineScheme.mk

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h
#align algebraic_geometry.AffineScheme.of AlgebraicGeometry.AffineScheme.of

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    AffineScheme.of X ⟶ AffineScheme.of Y :=
  f
#align algebraic_geometry.AffineScheme.of_hom AlgebraicGeometry.AffineScheme.ofHom

theorem mem_spec_essImage (X : Scheme) : X ∈ Scheme.spec.essImage ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.essImage.unit_isIso h⟩, fun h => @mem_essImage_of_unit_isIso _ _ _ X h.1⟩
#align algebraic_geometry.mem_Spec_ess_image AlgebraicGeometry.mem_spec_essImage

instance isAffineAffineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.essImage.unit_isIso X.property⟩
#align algebraic_geometry.is_affine_AffineScheme AlgebraicGeometry.isAffineAffineScheme

instance specIsAffine (R : CommRingCatᵒᵖ) : IsAffine (Scheme.spec.obj R) :=
  AlgebraicGeometry.isAffineAffineScheme ⟨_, Scheme.spec.obj_mem_essImage R⟩
#align algebraic_geometry.Spec_is_affine AlgebraicGeometry.specIsAffine

theorem isAffineOfIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X :=
  by
  rw [← mem_spec_essImage] at h⊢
  exact Functor.essImage.ofIso (asIso f).symm h
#align algebraic_geometry.is_affine_of_iso AlgebraicGeometry.isAffineOfIso

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
def spec : CommRingCatᵒᵖ ⥤ AffineScheme :=
  Scheme.spec.toEssImage deriving Full, Faithful, EssSurj
#align algebraic_geometry.AffineScheme.Spec AlgebraicGeometry.AffineScheme.spec

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps]
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.spec.essImageInclusion deriving Full, Faithful
#align algebraic_geometry.AffineScheme.forget_to_Scheme AlgebraicGeometry.AffineScheme.forgetToScheme

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingCat :=
  forgetToScheme.op ⋙ Scheme.Γ
#align algebraic_geometry.AffineScheme.Γ AlgebraicGeometry.AffineScheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equivCommRing : AffineScheme ≌ CommRingCatᵒᵖ :=
  equivEssImageOfReflective.symm
#align algebraic_geometry.AffineScheme.equiv_CommRing AlgebraicGeometry.AffineScheme.equivCommRing

instance ΓIsEquiv : IsEquivalence Γ.{u} :=
  haveI : IsEquivalence Γ.{u}.rightOp.op := IsEquivalence.ofEquivalence equiv_CommRing.op
  (Functor.isEquivalenceTrans Γ.{u}.rightOp.op (opOpEquivalence _).functor : _)
#align algebraic_geometry.AffineScheme.Γ_is_equiv AlgebraicGeometry.AffineScheme.ΓIsEquiv

instance : HasColimits AffineScheme.{u} :=
  haveI := Adjunction.hasLimitsOfEquivalence.{u} Γ.{u}
  Adjunction.hasColimitsOfEquivalence.{u} (opOpEquivalence AffineScheme.{u}).inverse

instance : HasLimits AffineScheme.{u} :=
  by
  haveI := Adjunction.hasColimitsOfEquivalence Γ.{u}
  haveI : HasLimits AffineScheme.{u}ᵒᵖᵒᵖ := Limits.hasLimits_op_of_hasColimits
  exact Adjunction.hasLimitsOfEquivalence (opOpEquivalence AffineScheme.{u}).inverse

noncomputable instance : PreservesLimits Γ.{u}.rightOp :=
  @Adjunction.isEquivalencePreservesLimits _ _ Γ.rightOp (IsEquivalence.ofEquivalence equivCommRing)

noncomputable instance : PreservesLimits forgetToScheme :=
  by
  apply (config := { instances := false })
    @preserves_limits_of_nat_iso _ _ (isoWhiskerRight equiv_CommRing.unit_iso forgetToScheme).symm
  change PreservesLimits (equiv_CommRing.functor ⋙ Scheme.spec)
  infer_instance

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def IsAffineOpen {X : Scheme} (U : Opens X.carrier) : Prop :=
  IsAffine (X.restrict U.openEmbedding)
#align algebraic_geometry.is_affine_open AlgebraicGeometry.IsAffineOpen

/-- The set of affine opens as a subset of `opens X.carrier`. -/
def Scheme.affineOpens (X : Scheme) : Set (Opens X.carrier) :=
  { U : Opens X.carrier | IsAffineOpen U }
#align algebraic_geometry.Scheme.affine_opens AlgebraicGeometry.Scheme.affineOpens

theorem range_isAffineOpen_of_open_immersion {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen f.opensRange :=
  by
  refine' isAffineOfIso (IsOpenImmersion.isoOfRangeEq f (Y.of_restrict _) _).inv
  exact subtype.range_coe.symm
  infer_instance
#align algebraic_geometry.range_is_affine_open_of_open_immersion AlgebraicGeometry.range_isAffineOpen_of_open_immersion

theorem top_isAffineOpen (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : Opens X.carrier) :=
  by
  convert range_isAffineOpen_of_open_immersion (𝟙 X)
  ext1
  exact set.range_id.symm
#align algebraic_geometry.top_is_affine_open AlgebraicGeometry.top_isAffineOpen

instance Scheme.affineCoverIsAffine (X : Scheme) (i : X.affineCover.J) :
    IsAffine (X.affineCover.obj i) :=
  AlgebraicGeometry.specIsAffine _
#align algebraic_geometry.Scheme.affine_cover_is_affine AlgebraicGeometry.Scheme.affineCoverIsAffine

instance Scheme.affineBasisCoverIsAffine (X : Scheme) (i : X.affineBasisCover.J) :
    IsAffine (X.affineBasisCover.obj i) :=
  AlgebraicGeometry.specIsAffine _
#align algebraic_geometry.Scheme.affine_basis_cover_is_affine AlgebraicGeometry.Scheme.affineBasisCoverIsAffine

theorem isBasis_affine_open (X : Scheme) : Opens.IsBasis X.affineOpens :=
  by
  rw [Opens.isBasis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X.carrier))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop
  refine' ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact range_isAffineOpen_of_open_immersion _
#align algebraic_geometry.is_basis_affine_open AlgebraicGeometry.isBasis_affine_open

/-- The open immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`. -/
def IsAffineOpen.fromSpec {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) :
    Scheme.spec.obj (op <| X.presheaf.obj <| op U) ⟶ X :=
  by
  haveI : IsAffine (X.restrict U.open_embedding) := hU
  have : U.open_embedding.is_open_map.functor.obj ⊤ = U :=
    by
    ext1
    exact set.image_univ.trans Subtype.range_coe
  exact
    Scheme.Spec.map (X.presheaf.map (eqToHom this.symm).op).op ≫
      (X.restrict U.open_embedding).isoSpec.inv ≫ X.of_restrict _
#align algebraic_geometry.is_affine_open.from_Spec AlgebraicGeometry.IsAffineOpen.fromSpec

instance IsAffineOpen.isOpenImmersion_fromSpec {X : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) : IsOpenImmersion hU.fromSpec :=
  by
  delta is_affine_open.from_Spec
  infer_instance
#align algebraic_geometry.is_affine_open.is_open_immersion_from_Spec AlgebraicGeometry.IsAffineOpen.isOpenImmersion_fromSpec

theorem IsAffineOpen.fromSpec_range {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) :
    Set.range hU.fromSpec.1.base = (U : Set X.carrier) :=
  by
  delta is_affine_open.from_Spec
  erw [← Category.assoc, Scheme.comp_val_base]
  rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
  exact Subtype.range_coe
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.is_affine_open.from_Spec_range AlgebraicGeometry.IsAffineOpen.fromSpec_range

theorem IsAffineOpen.fromSpec_image_top {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) :
    hU.isOpenImmersion_fromSpec.base_open.isOpenMap.functor.obj ⊤ = U :=
  by
  ext1
  exact set.image_univ.trans hU.from_Spec_range
#align algebraic_geometry.is_affine_open.from_Spec_image_top AlgebraicGeometry.IsAffineOpen.fromSpec_image_top

theorem IsAffineOpen.isCompact {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) :
    IsCompact (U : Set X.carrier) :=
  by
  convert
    @is_compact.image _ _ _ _ Set.univ hU.from_Spec.1.base PrimeSpectrum.compactSpace.1
      (by continuity)
  convert hU.from_Spec_range.symm
  exact Set.image_univ
#align algebraic_geometry.is_affine_open.is_compact AlgebraicGeometry.IsAffineOpen.isCompact

theorem IsAffineOpen.image_isOpenImmersion {X Y : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen (f.opensFunctor.obj U) :=
  by
  haveI : IsAffine _ := hU
  convert range_isAffineOpen_of_open_immersion (X.of_restrict U.open_embedding ≫ f)
  ext1
  change f.1.base '' U.1 = Set.range (f.1.base ∘ coe)
  rw [Set.range_comp, Subtype.range_coe]
#align algebraic_geometry.is_affine_open.image_is_open_immersion AlgebraicGeometry.IsAffineOpen.image_isOpenImmersion

theorem isAffineOpen_iff_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    (U : Opens X.carrier) : IsAffineOpen (H.openFunctor.obj U) ↔ IsAffineOpen U :=
  by
  refine' ⟨fun hU => @is_affine_of_iso _ _ hU, fun hU => hU.image_isOpenImmersion f⟩
  refine' (IsOpenImmersion.isoOfRangeEq (X.of_restrict _ ≫ f) (Y.of_restrict _) _).hom
  · rw [Scheme.comp_val_base, coe_comp, Set.range_comp]
    dsimp [Opens.inclusion]
    rw [Subtype.range_coe, Subtype.range_coe]
    rfl
  · infer_instance
#align algebraic_geometry.is_affine_open_iff_of_is_open_immersion AlgebraicGeometry.isAffineOpen_iff_of_isOpenImmersion

instance Scheme.quasi_compact_of_affine (X : Scheme) [IsAffine X] : CompactSpace X.carrier :=
  ⟨(top_isAffineOpen X).isCompact⟩
#align algebraic_geometry.Scheme.quasi_compact_of_affine AlgebraicGeometry.Scheme.quasi_compact_of_affine

theorem IsAffineOpen.fromSpec_base_preimage {X : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) : (Opens.map hU.fromSpec.val.base).obj U = ⊤ :=
  by
  ext1
  change hU.from_Spec.1.base ⁻¹' (U : Set X.carrier) = Set.univ
  rw [← hU.from_Spec_range, ← Set.image_univ]
  exact Set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
#align algebraic_geometry.is_affine_open.from_Spec_base_preimage AlgebraicGeometry.IsAffineOpen.fromSpec_base_preimage

theorem Scheme.specMap_presheaf_map_eqToHom {X : Scheme} {U V : Opens X.carrier} (h : U = V) (W) :
    (Scheme.spec.map (X.presheaf.map (eqToHom h).op).op).val.c.app W =
      eqToHom
        (by
          cases h
          dsimp
          induction W using Opposite.rec
          congr
          ext1
          simpa) :=
  by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine' (Scheme.congr_app this _).trans _
  erw [Category.id_comp]
  simpa [eqToHom_map]
#align algebraic_geometry.Scheme.Spec_map_presheaf_map_eq_to_hom AlgebraicGeometry.Scheme.specMap_presheaf_map_eqToHom

theorem IsAffineOpen.specΓIdentity_hom_app_fromSpec {X : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) :
    specΓIdentity.hom.app (X.presheaf.obj <| op U) ≫ hU.fromSpec.1.c.app (op U) =
      (Scheme.spec.obj _).presheaf.map (eqToHom hU.fromSpec_base_preimage).op :=
  by
  haveI : IsAffine _ := hU
  have e₁ := Spec_Γ_identity.hom.naturality (X.presheaf.map (eqToHom U.open_embedding_obj_top).op)
  rw [← IsIso.comp_inv_eq] at e₁
  have e₂ := ΓSpec.adjunction_unit_app_app_top (X.restrict U.open_embedding)
  erw [← e₂] at e₁
  simp only [Functor.id_map, Quiver.Hom.unop_op, Functor.comp_map, ← Functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, Category.assoc, Functor.rightOp_map, inv_eqToHom] at e₁
  delta is_affine_open.from_Spec Scheme.iso_Spec
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app, ← e₁]
  simp_rw [Category.assoc]
  erw [← X.presheaf.map_comp_assoc]
  rw [← op_comp]
  have e₃ :
    U.open_embedding.is_open_map.adjunction.counit.app U ≫ eqToHom U.open_embedding_obj_top.symm =
      U.open_embedding.is_open_map.functor.map (eqToHom U.inclusion_map_eq_top) :=
    Subsingleton.elim _ _
  have e₄ : X.presheaf.map _ ≫ _ = _ :=
    (asIso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).inv.1.c.naturality_assoc
      (eqToHom U.inclusion_map_eq_top).op _
  erw [e₃, e₄, ← Scheme.comp_val_c_app_assoc, Iso.inv_hom_id]
  simp only [eqToHom_map, eqToHom_op, Scheme.specMap_presheaf_map_eqToHom]
  erw [Scheme.specMap_presheaf_map_eqToHom, Category.id_comp]
  simpa only [eqToHom_trans]
#align algebraic_geometry.is_affine_open.Spec_Γ_identity_hom_app_from_Spec AlgebraicGeometry.IsAffineOpen.specΓIdentity_hom_app_fromSpec

@[elementwise]
theorem IsAffineOpen.fromSpec_app_eq {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) :
    hU.fromSpec.1.c.app (op U) =
      specΓIdentity.inv.app (X.presheaf.obj <| op U) ≫
        (Scheme.spec.obj _).presheaf.map (eqToHom hU.fromSpec_base_preimage).op :=
  by rw [← hU.Spec_Γ_identity_hom_app_from_Spec, Iso.inv_hom_id_app_assoc]
#align algebraic_geometry.is_affine_open.from_Spec_app_eq AlgebraicGeometry.IsAffineOpen.fromSpec_app_eq

theorem IsAffineOpen.basicOpen_is_affine {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (f : X.presheaf.obj (op U)) : IsAffineOpen (X.basicOpen f) :=
  by
  convert
    range_isAffineOpen_of_open_immersion
      (Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op U)) (Localization.Away f))).op ≫
        hU.from_Spec)
  ext1
  have :
    hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : Set X.carrier)) =
      (X.basic_open f : Set X.carrier) :=
    by
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, hU.from_Spec_range]
    exact Scheme.basicOpen_le _ _
  rw [Scheme.Hom.opensRange_coe, Scheme.comp_val_base, ← this, coe_comp, Set.range_comp]
  congr 1
  refine' (congr_arg coe <| Scheme.preimage_basicOpen hU.from_Spec f).trans _
  refine' Eq.trans _ (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  congr 1
  have : (Opens.map hU.from_Spec.val.base).obj U = ⊤ :=
    by
    ext1
    change hU.from_Spec.1.base ⁻¹' (U : Set X.carrier) = Set.univ
    rw [← hU.from_Spec_range, ← Set.image_univ]
    exact Set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
  refine' Eq.trans _ (basicOpen_eq_of_affine f)
  have lm : ∀ s, (Opens.map hU.from_Spec.val.base).obj U ⊓ s = s := fun s => this.symm ▸ top_inf_eq
  refine' Eq.trans _ (lm _)
  refine'
    Eq.trans _ ((Scheme.Spec.obj <| op <| X.presheaf.obj <| op U).basicOpen_res _ (eqToHom this).op)
  rw [← comp_apply]
  congr 2
  rw [Iso.eq_inv_comp]
  erw [hU.Spec_Γ_identity_hom_app_from_Spec]
#align algebraic_geometry.is_affine_open.basic_open_is_affine AlgebraicGeometry.IsAffineOpen.basicOpen_is_affine

theorem IsAffineOpen.map_restrict_basicOpen {X : Scheme} (r : X.presheaf.obj (op ⊤))
    {U : Opens X.carrier} (hU : IsAffineOpen U) :
    IsAffineOpen ((Opens.map (X.ofRestrict (X.basicOpen r).openEmbedding).1.base).obj U) :=
  by
  apply (isAffineOpen_iff_of_isOpenImmersion (X.of_restrict (X.basic_open r).openEmbedding) _).mp
  delta PresheafedSpace.is_open_immersion.open_functor
  dsimp
  rw [Opens.functor_obj_map_obj, Opens.openEmbedding_obj_top, inf_comm, ←
    Scheme.basicOpen_res _ _ (homOfLe le_top).op]
  exact hU.basic_open_is_affine _
#align algebraic_geometry.is_affine_open.map_restrict_basic_open AlgebraicGeometry.IsAffineOpen.map_restrict_basicOpen

theorem Scheme.map_prime_spectrum_basicOpen_of_affine (X : Scheme) [IsAffine X]
    (f : Scheme.Γ.obj (op X)) :
    (Opens.map X.isoSpec.hom.1.base).obj (PrimeSpectrum.basicOpen f) = X.basicOpen f :=
  by
  rw [← basicOpen_eq_of_affine]
  trans
    (Opens.map X.iso_Spec.hom.1.base).obj
      ((Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))).basicOpen
        ((inv (X.iso_Spec.hom.1.c.app (op ((Opens.map (inv X.iso_Spec.hom).val.base).obj ⊤))))
          ((X.presheaf.map (eqToHom _)) f)))
  congr
  · rw [← IsIso.inv_eq_inv, IsIso.inv_inv, IsIso.Iso.inv_inv, NatIso.app_hom]
    erw [← ΓSpec.adjunction_unit_app_app_top]
    rfl
  · rw [eqToHom_map]
    rfl
  · dsimp
    congr
  · refine' (Scheme.preimage_basicOpen _ _).trans _
    rw [IsIso.inv_hom_id_apply, Scheme.basicOpen_res_eq]
#align algebraic_geometry.Scheme.map_prime_spectrum_basic_open_of_affine AlgebraicGeometry.Scheme.map_prime_spectrum_basicOpen_of_affine

theorem isBasis_basicOpen (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.range (X.basicOpen : X.presheaf.obj (op ⊤) → Opens X.carrier)) :=
  by
  delta opens.is_basis
  convert
    prime_spectrum.is_basis_basic_opens.inducing
      (TopCat.homeoOfIso (Scheme.forget_to_Top.map_iso X.iso_Spec)).inducing using
    1
  ext
  simp only [Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine' ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, _⟩
    exact congr_arg Subtype.val (X.map_prime_spectrum_basic_open_of_affine x)
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    refine' ⟨_, ⟨x, rfl⟩, _⟩
    exact congr_arg Subtype.val (X.map_prime_spectrum_basic_open_of_affine x).symm
#align algebraic_geometry.is_basis_basic_open AlgebraicGeometry.isBasis_basicOpen

theorem IsAffineOpen.exists_basicOpen_le {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    {V : Opens X.carrier} (x : V) (h : ↑x ∈ U) :
    ∃ f : X.presheaf.obj (op U), X.basicOpen f ≤ V ∧ ↑x ∈ X.basicOpen f :=
  by
  haveI : IsAffine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ :=
    (isBasis_basicOpen (X.restrict U.open_embedding)).exists_subset_of_mem_open _
      ((Opens.map U.inclusion).obj V).prop
  swap
  exact ⟨x, h⟩
  have :
    U.open_embedding.is_open_map.functor.obj ((X.restrict U.open_embedding).basicOpen r) =
      X.basic_open (X.presheaf.map (eqToHom U.open_embedding_obj_top.symm).op r) :=
    by
    refine' (Scheme.image_basicOpen (X.of_restrict U.open_embedding) r).trans _
    erw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.open_embedding_obj_top).op]
    rw [← comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id, Scheme.Hom.invApp]
    erw [PresheafedSpace.IsOpenImmersion.ofRestrict_invApp]
    congr
  use X.presheaf.map (eqToHom U.open_embedding_obj_top.symm).op r
  rw [← this]
  exact ⟨set.image_subset_iff.mpr h₂, Set.mem_image_of_mem _ h₁⟩
  exact x.prop
#align algebraic_geometry.is_affine_open.exists_basic_open_le AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le

instance {X : Scheme} {U : Opens X.carrier} (f : X.presheaf.obj (op U)) :
    Algebra (X.presheaf.obj (op U)) (X.presheaf.obj (op <| X.basicOpen f)) :=
  (X.presheaf.map (homOfLe <| RingedSpace.basicOpen_le _ f : _ ⟶ U).op).toAlgebra

theorem IsAffineOpen.opens_map_fromSpec_basicOpen {X : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) (f : X.presheaf.obj (op U)) :
    (Opens.map hU.fromSpec.val.base).obj (X.basicOpen f) =
      RingedSpace.basicOpen _ (specΓIdentity.inv.app (X.presheaf.obj <| op U) f) :=
  by
  erw [LocallyRingedSpace.preimage_basicOpen]
  refine'
    Eq.trans _
      (RingedSpace.basicOpen_res_eq
        (Scheme.Spec.obj <| op <| X.presheaf.obj (op U)).toLocallyRingedSpace.toRingedSpace
        (eqToHom hU.from_Spec_base_preimage).op _)
  congr
  rw [← comp_apply]
  congr
  erw [← hU.Spec_Γ_identity_hom_app_from_Spec]
  rw [Iso.inv_hom_id_app_assoc]
#align algebraic_geometry.is_affine_open.opens_map_from_Spec_basic_open AlgebraicGeometry.IsAffineOpen.opens_map_fromSpec_basicOpen

/-- The canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(Spec_Γ_identity.inv f))`
This is an isomorphism, as witnessed by an `is_iso` instance. -/
def basicOpenSectionsToAffine {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (f : X.presheaf.obj (op U)) :
    X.presheaf.obj (op <| X.basicOpen f) ⟶
      (Scheme.spec.obj <| op <| X.presheaf.obj (op U)).presheaf.obj
        (op <| Scheme.basicOpen _ <| specΓIdentity.inv.app (X.presheaf.obj (op U)) f) :=
  hU.fromSpec.1.c.app (op <| X.basicOpen f) ≫
    (Scheme.spec.obj <| op <| X.presheaf.obj (op U)).presheaf.map
      (eqToHom <| (hU.opens_map_fromSpec_basicOpen f).symm).op
#align algebraic_geometry.basic_open_sections_to_affine AlgebraicGeometry.basicOpenSectionsToAffine

instance {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U) (f : X.presheaf.obj (op U)) :
    IsIso (basicOpenSectionsToAffine hU f) :=
  by
  delta basic_open_sections_to_affine
  apply (config := { instances := false }) IsIso.comp_isIso
  · apply PresheafedSpace.IsOpenImmersion.isIso_of_subset
    rw [hU.from_Spec_range]
    exact RingedSpace.basicOpen_le _ _
  infer_instance

theorem is_localization_basicOpen {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (f : X.presheaf.obj (op U)) : IsLocalization.Away f (X.presheaf.obj (op <| X.basicOpen f)) :=
  by
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers f)
        (asIso <|
            basicOpenSectionsToAffine hU f ≫
              (Scheme.Spec.obj _).presheaf.map
                (eqToHom (basicOpen_eq_of_affine _).symm).op).commRingIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_basicOpen _ f
  change _ ≫ basicOpenSectionsToAffine hU f ≫ _ = _
  delta basic_open_sections_to_affine
  erw [RingHom.algebraMap_toAlgebra]
  simp only [Scheme.comp_val_c_app, Category.assoc]
  erw [hU.from_Spec.val.c.naturality_assoc]
  rw [hU.from_Spec_app_eq]
  dsimp
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
  apply StructureSheaf.toOpen_res
#align algebraic_geometry.is_localization_basic_open AlgebraicGeometry.is_localization_basicOpen

instance {X : Scheme} [IsAffine X] (r : X.presheaf.obj (op ⊤)) :
    IsLocalization.Away r (X.presheaf.obj (op <| X.basicOpen r)) :=
  is_localization_basicOpen (top_isAffineOpen X) r

theorem is_localization_of_eq_basicOpen {X : Scheme} {U V : Opens X.carrier} (i : V ⟶ U)
    (hU : IsAffineOpen U) (r : X.presheaf.obj (op U)) (e : V = X.basicOpen r) :
    @IsLocalization.Away _ r (X.presheaf.obj (op V)) _ (X.presheaf.map i.op).toAlgebra :=
  by
  subst e
  convert is_localization_basicOpen hU r using 3
#align algebraic_geometry.is_localization_of_eq_basic_open AlgebraicGeometry.is_localization_of_eq_basicOpen

instance ΓRestrictAlgebra {X : Scheme} {Y : TopCat} {f : Y ⟶ X.carrier} (hf : OpenEmbedding f) :
    Algebra (Scheme.Γ.obj (op X)) (Scheme.Γ.obj (op <| X.restrict hf)) :=
  (Scheme.Γ.map (X.ofRestrict hf).op).toAlgebra
#align algebraic_geometry.Γ_restrict_algebra AlgebraicGeometry.ΓRestrictAlgebra

instance Γ_restrict_is_localization (X : Scheme.{u}) [IsAffine X] (r : Scheme.Γ.obj (op X)) :
    IsLocalization.Away r (Scheme.Γ.obj (op <| X.restrict (X.basicOpen r).openEmbedding)) :=
  is_localization_of_eq_basicOpen _ (top_isAffineOpen X) r (Opens.openEmbedding_obj_top _)
#align algebraic_geometry.Γ_restrict_is_localization AlgebraicGeometry.Γ_restrict_is_localization

theorem basicOpen_basicOpen_is_basicOpen {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (f : X.presheaf.obj (op U)) (g : X.presheaf.obj (op <| X.basicOpen f)) :
    ∃ f' : X.presheaf.obj (op U), X.basicOpen f' = X.basicOpen g :=
  by
  haveI := is_localization_basicOpen hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basicOpen_mul, Scheme.basicOpen_mul]
  erw [Scheme.basicOpen_res]
  refine' (inf_eq_left.mpr _).symm
  convert inf_le_left using 1
  apply Scheme.basicOpen_of_isUnit
  apply
    Submonoid.leftInv_le_is_unit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (X.presheaf.obj (op <| X.basic_open f))
          _).prop
#align algebraic_geometry.basic_open_basic_open_is_basic_open AlgebraicGeometry.basicOpen_basicOpen_is_basicOpen

theorem exists_basicOpen_le_affine_inter {X : Scheme} {U V : Opens X.carrier} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (x : X.carrier) (hx : x ∈ U ∩ V) :
    ∃ (f : X.presheaf.obj <| op U)(g : X.presheaf.obj <| op V),
      X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f :=
  by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basic_open_le ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basic_open_le ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ :=
    basicOpen_basicOpen_is_basicOpen hU f (X.presheaf.map (homOfLe hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basicOpen_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩
#align algebraic_geometry.exists_basic_open_le_affine_inter AlgebraicGeometry.exists_basicOpen_le_affine_inter

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable def IsAffineOpen.primeIdealOf {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (x : U) : PrimeSpectrum (X.presheaf.obj <| op U) :=
  (Scheme.spec.map
          (X.presheaf.map
              (eqToHom <|
                  show U.openEmbedding.isOpenMap.functor.obj ⊤ = U from
                    Opens.ext (Set.image_univ.trans Subtype.range_coe)).op).op).1.base
    ((@Scheme.isoSpec (X.restrict U.openEmbedding) hU).hom.1.base x)
#align algebraic_geometry.is_affine_open.prime_ideal_of AlgebraicGeometry.IsAffineOpen.primeIdealOf

theorem IsAffineOpen.fromSpec_primeIdealOf {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (x : U) : hU.fromSpec.val.base (hU.primeIdealOf x) = x.1 :=
  by
  dsimp only [IsAffineOpen.fromSpec, Subtype.coe_mk]
  erw [← Scheme.comp_val_base_apply, ← Scheme.comp_val_base_apply]
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, eqToHom_trans, op_id,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
#align algebraic_geometry.is_affine_open.from_Spec_prime_ideal_of AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf

theorem IsAffineOpen.is_localization_stalk_aux {X : Scheme} (U : Opens X.carrier)
    [IsAffine (X.restrict U.openEmbedding)] :
    (inv (ΓSpec.adjunction.unit.app (X.restrict U.openEmbedding))).1.c.app
        (op ((Opens.map U.inclusion).obj U)) =
      X.presheaf.map
          (eqToHom <| by rw [Opens.inclusion_map_eq_top] :
              U.openEmbedding.isOpenMap.functor.obj ⊤ ⟶
                U.openEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion).obj U)).op ≫
        toSpecΓ (X.presheaf.obj <| op (U.openEmbedding.isOpenMap.functor.obj ⊤)) ≫
          (Scheme.spec.obj <| op <| X.presheaf.obj <| _).presheaf.map
            (eqToHom
                  (by
                    rw [Opens.inclusion_map_eq_top]
                    rfl) :
                unop _ ⟶ ⊤).op :=
  by
  have e :
    (Opens.map (inv (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).1.base).obj
        ((Opens.map U.inclusion).obj U) =
      ⊤ :=
    by
    rw [Opens.inclusion_map_eq_top]
    rfl
  rw [Scheme.inv_val_c_app, IsIso.comp_inv_eq, Scheme.app_eq _ e, ΓSpec.adjunction_unit_app_app_top]
  simp only [Category.assoc, eqToHom_op]
  erw [← Functor.map_comp_assoc]
  rw [eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Spec_Γ_identity.inv_hom_id_app_assoc]
  simp only [eqToHom_map, eqToHom_trans]
#align algebraic_geometry.is_affine_open.is_localization_stalk_aux AlgebraicGeometry.IsAffineOpen.is_localization_stalk_aux

theorem IsAffineOpen.is_localization_stalk {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (x : U) : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asIdeal :=
  by
  haveI : IsAffine _ := hU
  haveI : Nonempty U := ⟨x⟩
  rcases x with ⟨x, hx⟩
  let y := hU.prime_ideal_of ⟨x, hx⟩
  have : hU.from_Spec.val.base y = x := hU.from_Spec_prime_ideal_of ⟨x, hx⟩
  change IsLocalization y.as_ideal.prime_compl _
  clear_value y
  subst this
  apply
    (IsLocalization.isLocalization_iff_of_ringEquiv _
        (asIso <| PresheafedSpace.stalkMap hU.from_Spec.1 y).commRingIsoToRingEquiv).mpr
  convert StructureSheaf.IsLocalization.to_stalk _ _ using 1
  delta structure_sheaf.stalk_algebra
  congr 1
  rw [RingHom.algebraMap_toAlgebra]
  refine' (PresheafedSpace.stalkMap_germ hU.from_Spec.1 _ ⟨_, _⟩).trans _
  delta is_affine_open.from_Spec Scheme.iso_Spec structure_sheaf.to_stalk
  simp only [Scheme.comp_val_c_app, Category.assoc]
  dsimp only [Functor.op, asIso_inv, unop_op]
  erw [IsAffineOpen.is_localization_stalk_aux]
  simp only [Category.assoc]
  conv_lhs => rw [← Category.assoc]
  erw [← X.presheaf.map_comp, Spec_Γ_naturality_assoc]
  congr 1
  simp only [← Category.assoc]
  trans _ ≫ (structureSheaf (X.presheaf.obj <| op U)).presheaf.germ ⟨_, _⟩
  · rfl
  convert (structureSheaf (X.presheaf.obj <| op U)).Presheaf.germ_res (homOfLe le_top) ⟨_, _⟩ using
    2
  rw [Category.assoc]
  erw [NatTrans.naturality]
  rw [← LocallyRingedSpace.Γ_map_op, ← LocallyRingedSpace.Γ.map_comp_assoc, ← op_comp]
  erw [← Scheme.Spec.map_comp]
  rw [← op_comp, ← X.presheaf.map_comp]
  trans
    LocallyRingedSpace.Γ.map (Quiver.Hom.op <| Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op) ≫ _
  · congr
  simp only [CategoryTheory.Functor.map_id, op_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp]
  rfl
#align algebraic_geometry.is_affine_open.is_localization_stalk AlgebraicGeometry.IsAffineOpen.is_localization_stalk

/-- The basic open set of a section `f` on an an affine open as an `X.affine_opens`. -/
@[simps]
def Scheme.affineBasicOpen (X : Scheme) {U : X.affineOpens} (f : X.presheaf.obj <| op U) :
    X.affineOpens :=
  ⟨X.basicOpen f, U.prop.basicOpen_is_affine f⟩
#align algebraic_geometry.Scheme.affine_basic_open AlgebraicGeometry.Scheme.affineBasicOpen

@[simp]
theorem IsAffineOpen.basicOpen_fromSpec_app {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (f : X.presheaf.obj (op U)) :
    @Scheme.basicOpen (Scheme.spec.obj <| op (X.presheaf.obj <| op U))
        ((Opens.map hU.fromSpec.1.base).obj U) (hU.fromSpec.1.c.app (op U) f) =
      PrimeSpectrum.basicOpen f :=
  by
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom hU.from_Spec_base_preimage.symm).op,
    basicOpen_eq_of_affine', IsAffineOpen.fromSpec_app_eq]
  congr
  rw [← comp_apply, ← comp_apply, Category.assoc, ← Functor.map_comp_assoc, eqToHom_op, eqToHom_op,
    eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, ← Iso.app_inv,
    Iso.inv_hom_id]
  rfl
#align algebraic_geometry.is_affine_open.basic_open_from_Spec_app AlgebraicGeometry.IsAffineOpen.basicOpen_fromSpec_app

theorem IsAffineOpen.fromSpec_map_basicOpen {X : Scheme} {U : Opens X.carrier} (hU : IsAffineOpen U)
    (f : X.presheaf.obj (op U)) :
    (Opens.map hU.fromSpec.val.base).obj (X.basicOpen f) = PrimeSpectrum.basicOpen f := by simp
#align algebraic_geometry.is_affine_open.from_Spec_map_basic_open AlgebraicGeometry.IsAffineOpen.fromSpec_map_basicOpen

theorem IsAffineOpen.basicOpen_union_eq_self_iff {X : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) (s : Set (X.presheaf.obj <| op U)) :
    (⨆ f : s, X.basicOpen (f : X.presheaf.obj <| op U)) = U ↔ Ideal.span s = ⊤ :=
  by
  trans (⋃ i : s, (PrimeSpectrum.basicOpen i.1).1) = Set.univ
  trans
    hU.from_Spec.1.base ⁻¹' (⨆ f : s, X.basic_open (f : X.presheaf.obj <| op U)).1 =
      hU.from_Spec.1.base ⁻¹' U.1
  · refine' ⟨fun h => by rw [h], _⟩
    intro h
    apply_fun Set.image hU.from_Spec.1.base  at h
    rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range, hU.from_Spec_range] at
      h
    simp only [Set.inter_self, Subtype.val_eq_coe, Set.inter_eq_right_iff_subset] at h
    ext1
    refine' le_antisymm _ h
    simp only [Set.unionᵢ_subset_iff, SetCoe.forall, Opens.supᵢ_def, Set.le_eq_subset,
      Subtype.coe_mk]
    intro x hx
    exact X.basic_open_le x
  · simp only [Opens.supᵢ_def, Subtype.coe_mk, Set.preimage_unionᵢ, Subtype.val_eq_coe]
    congr 3
    · ext1 x
      exact congr_arg Subtype.val (hU.from_Spec_map_basic_open _)
    · exact congr_arg Subtype.val hU.from_Spec_base_preimage
  · simp only [Subtype.val_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [← Set.compl_interᵢ, Set.compl_univ_iff, ← PrimeSpectrum.zeroLocus_unionᵢ, ←
      PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span]
    simp only [Set.unionᵢ_singleton_eq_range, Subtype.range_coe_subtype, Set.setOf_mem_eq]
#align algebraic_geometry.is_affine_open.basic_open_union_eq_self_iff AlgebraicGeometry.IsAffineOpen.basicOpen_union_eq_self_iff

theorem IsAffineOpen.self_le_basicOpen_union_iff {X : Scheme} {U : Opens X.carrier}
    (hU : IsAffineOpen U) (s : Set (X.presheaf.obj <| op U)) :
    (U ≤ ⨆ f : s, X.basicOpen (f : X.presheaf.obj <| op U)) ↔ Ideal.span s = ⊤ :=
  by
  rw [← hU.basic_open_union_eq_self_iff, @comm _ Eq]
  refine' ⟨fun h => le_antisymm h _, le_of_eq⟩
  simp only [supᵢ_le_iff, SetCoe.forall]
  intro x hx
  exact X.basic_open_le x
#align algebraic_geometry.is_affine_open.self_le_basic_open_union_iff AlgebraicGeometry.IsAffineOpen.self_le_basicOpen_union_iff

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in [*The rising sea*][RisingSea]. -/
@[elab_as_elim]
theorem of_affine_open_cover {X : Scheme} (V : X.affineOpens) (S : Set X.affineOpens)
    {P : X.affineOpens → Prop}
    (hP₁ : ∀ (U : X.affineOpens) (f : X.presheaf.obj <| op U.1), P U → P (X.affineBasicOpen f))
    (hP₂ :
      ∀ (U : X.affineOpens) (s : Finset (X.presheaf.obj <| op U))
        (hs : Ideal.span (s : Set (X.presheaf.obj <| op U)) = ⊤),
        (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hS : (⋃ i : S, i : Set X.carrier) = Set.univ) (hS' : ∀ U : S, P U) : P V := by
  classical
    have :
      ∀ x : V, ∃ f : X.presheaf.obj <| op V.1, ↑x ∈ X.basic_open f ∧ P (X.affine_basic_open f) :=
      by
      intro x
      have : ↑x ∈ (Set.univ : Set X.carrier) := trivial
      rw [← hS] at this
      obtain ⟨W, hW⟩ := set.mem_Union.mp this
      obtain ⟨f, g, e, hf⟩ := exists_basicOpen_le_affine_inter V.prop W.1.prop x ⟨x.prop, hW⟩
      refine' ⟨f, hf, _⟩
      convert hP₁ _ g (hS' W) using 1
      ext1
      exact e
    choose f hf₁ hf₂ using this
    suffices Ideal.span (Set.range f) = ⊤
      by
      obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp this
      apply hP₂ V t ht₂
      rintro ⟨i, hi⟩
      obtain ⟨x, rfl⟩ := ht₁ hi
      exact hf₂ x
    rw [← V.prop.self_le_basic_open_union_iff]
    intro x hx
    simp only [exists_prop, Set.mem_unionᵢ, Set.mem_range, SetCoe.exists, Opens.supᵢ_def,
      exists_exists_eq_and, Opens.mem_coe, Subtype.coe_mk]
    refine' ⟨_, hf₁ ⟨x, hx⟩⟩
#align algebraic_geometry.of_affine_open_cover AlgebraicGeometry.of_affine_open_cover

end AlgebraicGeometry

