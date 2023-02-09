/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.ring_hom_properties
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.Morphisms.Basic
import Mathbin.RingTheory.LocalProperties

/-!

# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that come from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `target_affine_locally (affine_and P)`: the preimage of an affine open `U = Spec A` is affine
  (`= Spec B`) and `A ⟶ B` satisfies `P`. (TODO)
- `affine_locally P`: For each pair of affine open `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`,
  the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on the source (`ring_hom.respects_iso P`, `ring_hom.localization_preserves P`,
`ring_hom.of_localization_span`), and `target_affine_locally (affine_and P)` will be local on
the target. (TODO)

For the latter `P` should be local on the target (`ring_hom.property_is_local P`), and
`affine_locally P` will be local on both the source and the target.

Further more, these properties are stable under compositions (resp. base change) if `P` is. (TODO)

-/


universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S), Prop)

namespace RingHom

include P

variable {P}

theorem RespectsIso.basicOpen_iff (hP : RespectsIso @P) {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (r : Y.presheaf.obj (Opposite.op ⊤)) :
    P (Scheme.Γ.map (f ∣_ Y.basicOpen r).op) ↔
      P
        (@IsLocalization.Away.map (Y.presheaf.obj (Opposite.op ⊤)) _
          (Y.presheaf.obj (Opposite.op <| Y.basicOpen r)) _ _ (X.presheaf.obj (Opposite.op ⊤)) _
          (X.presheaf.obj (Opposite.op <| X.basicOpen (Scheme.Γ.map f.op r))) _ _
          (Scheme.Γ.map f.op) r _ _) :=
  by
  rw [Γ_map_morphismRestrict, hP.cancel_left_is_iso, hP.cancel_right_is_iso, ←
    hP.cancel_right_is_iso (f.val.c.app (Opposite.op (Y.basic_open r)))
      (X.presheaf.map (eqToHom (Scheme.preimage_basicOpen f r).symm).op),
    ← eq_iff_iff]
  congr
  delta IsLocalization.Away.map
  refine' IsLocalization.ringHom_ext (Submonoid.powers r) _
  convert (IsLocalization.map_comp _).symm using 1
  change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _
  rw [f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr
#align ring_hom.respects_iso.basic_open_iff RingHom.RespectsIso.basicOpen_iff

theorem RespectsIso.basicOpen_iff_localization (hP : RespectsIso @P) {X Y : Scheme} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (Opposite.op ⊤)) :
    P (Scheme.Γ.map (f ∣_ Y.basicOpen r).op) ↔ P (Localization.awayMap (Scheme.Γ.map f.op) r) :=
  (hP.basicOpen_iff _ _).trans (hP.is_localization_away_iff _ _ _ _).symm
#align ring_hom.respects_iso.basic_open_iff_localization RingHom.RespectsIso.basicOpen_iff_localization

theorem RespectsIso.ofRestrict_morphismRestrict_iff (hP : RingHom.RespectsIso @P) {X Y : Scheme}
    [IsAffine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (Opposite.op ⊤)) (U : Opens X.carrier)
    (hU : IsAffineOpen U) {V : Opens _}
    (e : V = (Opens.map (X.ofRestrict ((Opens.map f.1.base).obj _).openEmbedding).1.base).obj U) :
    P
        (Scheme.Γ.map
          ((X.restrict ((Opens.map f.1.base).obj _).openEmbedding).ofRestrict V.openEmbedding ≫
              f ∣_ Y.basicOpen r).op) ↔
      P (Localization.awayMap (Scheme.Γ.map (X.ofRestrict U.openEmbedding ≫ f).op) r) :=
  by
  subst e
  convert (hP.is_localization_away_iff _ _ _ _).symm
  rotate_left
  · infer_instance
  · apply RingHom.toAlgebra
    refine'
      X.presheaf.map
        (@hom_of_le _ _ ((IsOpenMap.functor _).obj _) ((IsOpenMap.functor _).obj _) _).op
    rw [Opens.le_def]
    dsimp
    change coe '' (coe '' Set.univ) ⊆ coe '' Set.univ
    rw [Subtype.coe_image_univ, Subtype.coe_image_univ]
    exact Set.image_preimage_subset _ _
  · exact AlgebraicGeometry.Γ_restrict_is_localization Y r
  · rw [← U.open_embedding_obj_top] at hU
    dsimp [Scheme.Γ_obj_op, Scheme.Γ_map_op, Scheme.restrict]
    apply AlgebraicGeometry.is_localization_of_eq_basicOpen _ hU
    rw [Opens.openEmbedding_obj_top, Opens.functor_obj_map_obj]
    convert (X.basic_open_res (Scheme.Γ.map f.op r) (homOfLe le_top).op).symm using 1
    rw [Opens.openEmbedding_obj_top, Opens.openEmbedding_obj_top, inf_comm, Scheme.Γ_map_op, ←
      Scheme.preimage_basicOpen]
  · apply IsLocalization.ringHom_ext (Submonoid.powers r) _
    swap
    · exact AlgebraicGeometry.Γ_restrict_is_localization Y r
    rw [IsLocalization.Away.map, IsLocalization.map_comp, RingHom.algebraMap_toAlgebra,
      RingHom.algebraMap_toAlgebra, op_comp, Functor.map_comp, op_comp, Functor.map_comp]
    refine' (@category.assoc CommRingCat _ _ _ _ _ _ _ _).symm.trans _
    refine' Eq.trans _ (@category.assoc CommRingCat _ _ _ _ _ _ _ _)
    dsimp only [Scheme.Γ_map, Quiver.Hom.unop_op]
    rw [morphismRestrict_c_app, Category.assoc, Category.assoc, Category.assoc]
    erw [f.1.c.naturality_assoc, ← X.presheaf.map_comp, ← X.presheaf.map_comp, ←
      X.presheaf.map_comp]
    congr
#align ring_hom.respects_iso.of_restrict_morphism_restrict_iff RingHom.RespectsIso.ofRestrict_morphismRestrict_iff

theorem StableUnderBaseChange.ΓPullbackFst (hP : StableUnderBaseChange @P) (hP' : RespectsIso @P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P (Scheme.Γ.map g.op)) : P (Scheme.Γ.map (pullback.fst : pullback f g ⟶ _).op) :=
  by
  rw [←
    PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g),
    op_comp, Functor.map_comp, hP'.cancel_right_is_iso, AffineScheme.forgetToScheme_map]
  have :=
    congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.right_op (AffineScheme.ofHom f)
        (AffineScheme.ofHom g))
  simp only [Quiver.Hom.unop_op, Functor.rightOp_map, unop_comp] at this
  delta AffineScheme.Γ at this
  simp only [Quiver.Hom.unop_op, Functor.comp_map, AffineScheme.forgetToScheme_map,
    Functor.op_map] at this
  rw [← this, hP'.cancel_right_is_iso, ←
    pushoutIsoUnopPullback_inl_hom (Quiver.Hom.unop _) (Quiver.Hom.unop _), hP'.cancel_right_is_iso]
  exact hP.pushout_inl _ hP' _ _ H
#align ring_hom.stable_under_base_change.Γ_pullback_fst RingHom.StableUnderBaseChange.ΓPullbackFst

end RingHom

namespace AlgebraicGeometry

/-- For `P` a property of ring homomorphisms, `source_affine_locally P` holds for `f : X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`. -/
def sourceAffineLocally : AffineTargetMorphismProperty := fun X Y f hY =>
  ∀ U : X.affineOpens, P (Scheme.Γ.map (X.ofRestrict U.1.openEmbedding ≫ f).op)
#align algebraic_geometry.source_affine_locally AlgebraicGeometry.sourceAffineLocally

/-- For `P` a property of ring homomorphisms, `affine_locally P` holds for `f : X ⟶ Y` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.
Also see `affine_locally_iff_affine_opens_le`. -/
abbrev affineLocally : MorphismProperty Scheme :=
  targetAffineLocally (sourceAffineLocally @P)
#align algebraic_geometry.affine_locally AlgebraicGeometry.affineLocally

variable {P}

theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso @P) :
    (sourceAffineLocally @P).toProperty.RespectsIso :=
  by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (Scheme.restrictMapIso e.inv U.1).hom.op), ←
      Functor.map_comp, ← op_comp]
    convert H ⟨_, U.prop.map_is_iso e.inv⟩ using 3
    rw [IsOpenImmersion.isoOfRangeEq_hom, IsOpenImmersion.lift_fac_assoc, Category.assoc,
      e.inv_hom_id_assoc]
    rfl
  · introv H U
    rw [← Category.assoc, op_comp, Functor.map_comp, h₁.cancel_left_is_iso]
    exact H U
#align algebraic_geometry.source_affine_locally_respects_iso AlgebraicGeometry.sourceAffineLocally_respectsIso

theorem affineLocally_respectsIso (h : RingHom.RespectsIso @P) : (affineLocally @P).RespectsIso :=
  targetAffineLocally_respectsIso (sourceAffineLocally_respectsIso h)
#align algebraic_geometry.affine_locally_respects_iso AlgebraicGeometry.affineLocally_respectsIso

theorem affineLocally_iff_affineOpens_le (hP : RingHom.RespectsIso @P) {X Y : Scheme} (f : X ⟶ Y) :
    affineLocally (@P) f ↔
      ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ (Opens.map f.1.base).obj U.1),
        P (f.appLe e) :=
  by
  apply forall_congr'
  intro U
  delta source_affine_locally
  simp_rw [op_comp, Scheme.Γ.map_comp, Γ_map_morphismRestrict, Category.assoc, Scheme.Γ_map_op,
    hP.cancel_left_is_iso]
  constructor
  · intro H V e
    let U' := (Opens.map f.val.base).obj U.1
    have e' : U'.open_embedding.is_open_map.functor.obj ((Opens.map U'.inclusion).obj V.1) = V.1 :=
      by
      ext1
      refine' set.image_preimage_eq_inter_range.trans (set.inter_eq_left_iff_subset.mpr _)
      convert e
      exact Subtype.range_coe
    have := H ⟨(Opens.map (X.of_restrict U'.open_embedding).1.base).obj V.1, _⟩
    erw [← X.presheaf.map_comp] at this
    rw [← hP.cancel_right_is_iso _ (X.presheaf.map (eqToHom _)), Category.assoc, ←
      X.presheaf.map_comp]
    convert this using 1
    · dsimp only [Functor.op, unop_op]
      rw [Opens.openEmbedding_obj_top]
      congr 1
      exact e'.symm
    · infer_instance
    · apply (isAffineOpen_iff_of_isOpenImmersion (X.of_restrict _) _).mp
      convert V.2
      infer_instance
  · intro H V
    specialize H ⟨_, V.2.image_isOpenImmersion (X.of_restrict _)⟩ (Subtype.coe_image_subset _ _)
    erw [← X.presheaf.map_comp]
    rw [← hP.cancel_right_is_iso _ (X.presheaf.map (eqToHom _)), Category.assoc, ←
      X.presheaf.map_comp]
    convert H
    · dsimp only [Functor.op, unop_op]
      rw [Opens.openEmbedding_obj_top]
      rfl
    · infer_instance
#align algebraic_geometry.affine_locally_iff_affine_opens_le AlgebraicGeometry.affineLocally_iff_affineOpens_le

theorem schemeRestrictBasicOpenOfLocalizationPreserves (h₁ : RingHom.RespectsIso @P)
    (h₂ : RingHom.LocalizationPreserves @P) {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y)
    (r : Y.presheaf.obj (op ⊤)) (H : sourceAffineLocally (@P) f)
    (U : (X.restrict ((Opens.map f.1.base).obj <| Y.basicOpen r).openEmbedding).affineOpens) :
    P
      (Scheme.Γ.map
        ((X.restrict ((Opens.map f.1.base).obj <| Y.basicOpen r).openEmbedding).ofRestrict
              U.1.openEmbedding ≫
            f ∣_ Y.basicOpen r).op) :=
  by
  specialize H ⟨_, U.2.image_isOpenImmersion (X.of_restrict _)⟩
  convert (h₁.of_restrict_morphism_restrict_iff _ _ _ _ _).mpr _ using 1
  pick_goal 5
  · exact h₂.away r H
  · infer_instance
  · exact U.2.image_isOpenImmersion _
  · ext1
    exact (Set.preimage_image_eq _ Subtype.coe_injective).symm
#align algebraic_geometry.Scheme_restrict_basic_open_of_localization_preserves AlgebraicGeometry.schemeRestrictBasicOpenOfLocalizationPreserves

/- ./././Mathport/Syntax/Translate/Basic.lean:629:2: warning: expanding binder collection (V «expr = » (opens.map[topological_space.opens.map]
  f.val.base).{ident := obj, full_name := category_theory.functor.obj}
 (Y.basic_open r.val)) -/
theorem sourceAffineLocallyIsLocal (h₁ : RingHom.RespectsIso @P)
    (h₂ : RingHom.LocalizationPreserves @P) (h₃ : RingHom.OfLocalizationSpan @P) :
    (sourceAffineLocally @P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso h₁
  · introv H U
    apply schemeRestrictBasicOpenOfLocalizationPreserves h₁ h₂ <;> assumption
  · introv hs hs' U
    skip
    apply h₃ _ _ hs
    intro r
    have := hs' r ⟨(Opens.map (X.of_restrict _).1.base).obj U.1, _⟩
    rwa [h₁.of_restrict_morphism_restrict_iff] at this
    · exact U.2
    · rfl
    · infer_instance
    · suffices
        ∀ (V) (_ : V = (Opens.map f.val.base).obj (Y.basic_open r.val)),
          IsAffineOpen ((Opens.map (X.of_restrict V.openEmbedding).1.base).obj U.1)
        by exact this _ rfl
      intro V hV
      rw [Scheme.preimage_basicOpen] at hV
      subst hV
      exact U.2.map_restrict_basicOpen (Scheme.Γ.map f.op r.1)
#align algebraic_geometry.source_affine_locally_is_local AlgebraicGeometry.sourceAffineLocallyIsLocal

variable {P} (hP : RingHom.PropertyIsLocal @P)

theorem source_affine_locally_of_source_open_cover_aux (h₁ : RingHom.RespectsIso @P)
    (h₃ : RingHom.OfLocalizationSpanTarget @P) {X Y : Scheme} (f : X ⟶ Y) (U : X.affineOpens)
    (s : Set (X.presheaf.obj (op U.1))) (hs : Ideal.span s = ⊤)
    (hs' : ∀ r : s, P (Scheme.Γ.map (X.ofRestrict (X.basicOpen r.1).openEmbedding ≫ f).op)) :
    P (Scheme.Γ.map (X.ofRestrict U.1.openEmbedding ≫ f).op) :=
  by
  apply_fun Ideal.map (X.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op)  at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply h₃ _ _ hs
  rintro ⟨s, r, hr, hs⟩
  have :=
    (@localization.alg_equiv _ _ _ _ _
          (@algebraic_geometry.Γ_restrict_is_localization _ U.2 s)).toRingEquiv.toCommRingIso
  refine'
    (h₁.cancel_right_is_iso _
          (@localization.alg_equiv _ _ _ _ _
                  (@algebraic_geometry.Γ_restrict_is_localization _ U.2
                    s)).toRingEquiv.toCommRingIso.hom).mp
      _
  subst hs
  rw [CommRingCat.comp_eq_ring_hom_comp, ← RingHom.comp_assoc]
  erw [IsLocalization.map_comp, RingHom.comp_id]
  rw [RingHom.algebraMap_toAlgebra, op_comp, Functor.map_comp, ← CommRingCat.comp_eq_ring_hom_comp,
    Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.Γ_map_op, Category.assoc]
  erw [← X.presheaf.map_comp]
  rw [← h₁.cancel_right_is_iso _ (X.presheaf.map (eqToHom _))]
  convert hs' ⟨r, hr⟩ using 1
  · erw [Category.assoc]
    rw [← X.presheaf.map_comp, op_comp, Scheme.Γ.map_comp, Scheme.Γ_map_op, Scheme.Γ_map_op]
    congr
  · dsimp [Functor.op]
    conv_lhs => rw [Opens.openEmbedding_obj_top]
    conv_rhs => rw [Opens.openEmbedding_obj_top]
    erw [Scheme.image_basicOpen (X.of_restrict U.1.openEmbedding)]
    erw [PresheafedSpace.IsOpenImmersion.ofRestrict_invApp_apply]
    rw [Scheme.basicOpen_res_eq]
  · infer_instance
#align algebraic_geometry.source_affine_locally_of_source_open_cover_aux AlgebraicGeometry.source_affine_locally_of_source_open_cover_aux

theorem isOpenImmersionCompOfSourceAffineLocally (h₁ : RingHom.RespectsIso @P) {X Y Z : Scheme}
    [IsAffine X] [IsAffine Z] (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z)
    (h₂ : sourceAffineLocally (@P) g) : P (Scheme.Γ.map (f ≫ g).op) :=
  by
  rw [←
    h₁.cancel_right_is_iso _
      (Scheme.Γ.map (IsOpenImmersion.isoOfRangeEq (Y.of_restrict _) f _).hom.op),
    ← Functor.map_comp, ← op_comp]
  convert h₂ ⟨_, range_isAffineOpen_of_open_immersion f⟩ using 3
  · rw [IsOpenImmersion.isoOfRangeEq_hom, IsOpenImmersion.lift_fac_assoc]
  · infer_instance
  · exact Subtype.range_coe
  · infer_instance
#align algebraic_geometry.is_open_immersion_comp_of_source_affine_locally AlgebraicGeometry.isOpenImmersionCompOfSourceAffineLocally

end AlgebraicGeometry

open AlgebraicGeometry

namespace RingHom.PropertyIsLocal

variable {P} (hP : RingHom.PropertyIsLocal @P)

include hP

theorem sourceAffineLocallyOfSourceOpenCover {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.obj i)] (H : ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :
    sourceAffineLocally (@P) f :=
  by
  let S i :=
    (⟨⟨Set.range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
        range_isAffineOpen_of_open_immersion (𝒰.map i)⟩ :
      X.affine_opens)
  intro U
  apply of_affine_open_cover U
  pick_goal 5; · exact Set.range S
  · intro U r H
    convert hP.stable_under_composition _ _ H _ using 1
    swap
    · refine'
        X.presheaf.map
          (@hom_of_le _ _ ((IsOpenMap.functor _).obj _) ((IsOpenMap.functor _).obj _) _).op
      rw [unop_op, unop_op, Opens.openEmbedding_obj_top, Opens.openEmbedding_obj_top]
      exact X.basic_open_le _
    · rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
      refine' (Eq.trans _ (Category.assoc _ _ _).symm : _)
      congr 1
      refine' Eq.trans _ (X.presheaf.map_comp _ _)
      change X.presheaf.map _ = _
      congr
    convert
      hP.holds_for_localization_away _ (X.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op r)
    · exact (RingHom.algebraMap_toAlgebra _).symm
    · dsimp [Scheme.Γ]
      have := U.2
      rw [← U.1.openEmbedding_obj_top] at this
      convert is_localization_basicOpen this _ using 6 <;> rw [Opens.openEmbedding_obj_top] <;>
        exact (Scheme.basicOpen_res_eq _ _ _).symm
  · introv hs hs'
    exact source_affine_locally_of_source_open_cover_aux hP.respects_iso hP.2 _ _ _ hs hs'
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_unionᵢ]
    exact ⟨⟨_, 𝒰.f x, rfl⟩, 𝒰.covers x⟩
  · rintro ⟨_, i, rfl⟩
    specialize H i
    rw [←
      hP.respects_iso.cancel_right_is_iso _
        (Scheme.Γ.map
          (IsOpenImmersion.isoOfRangeEq (𝒰.map i) (X.of_restrict (S i).1.openEmbedding)
                subtype.range_coe.symm).inv.op)] at
      H
    rwa [← Scheme.Γ.map_comp, ← op_comp, IsOpenImmersion.isoOfRangeEq_inv,
      IsOpenImmersion.lift_fac_assoc] at H
#align ring_hom.property_is_local.source_affine_locally_of_source_open_cover RingHom.PropertyIsLocal.sourceAffineLocallyOfSourceOpenCover

theorem affine_openCover_tFAE {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    TFAE
      [sourceAffineLocally (@P) f,
        ∃ (𝒰 : Scheme.OpenCover.{u} X)(_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, P (Scheme.Γ.map (𝒰.map i ≫ f).op),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          P (Scheme.Γ.map (𝒰.map i ≫ f).op),
        ∀ {U : Scheme} (g : U ⟶ X) [IsAffine U] [IsOpenImmersion g], P (Scheme.Γ.map (g ≫ f).op)] :=
  by
  tfae_have 1 → 4
  · intro H U g _ hg
    skip
    specialize H ⟨⟨_, hg.base_open.open_range⟩, range_isAffineOpen_of_open_immersion g⟩
    rw [←
      hP.respects_iso.cancel_right_is_iso _
        (Scheme.Γ.map
          (IsOpenImmersion.isoOfRangeEq g
                (X.of_restrict (Opens.openEmbedding ⟨_, hg.base_open.open_range⟩))
                subtype.range_coe.symm).hom.op),
      ← Scheme.Γ.map_comp, ← op_comp, IsOpenImmersion.isoOfRangeEq_hom] at H
    erw [IsOpenImmersion.lift_fac_assoc] at H
    exact H
  tfae_have 4 → 3
  · intro H 𝒰 _ i
    skip
    apply H
  tfae_have 3 → 2
  · intro H
    refine' ⟨X.affine_cover, inferInstance, H _⟩
  tfae_have 2 → 1
  · rintro ⟨𝒰, _, h𝒰⟩
    exact hP.source_affine_locally_of_source_open_cover f 𝒰 h𝒰
  tfae_finish
#align ring_hom.property_is_local.affine_open_cover_tfae RingHom.PropertyIsLocal.affine_openCover_tFAE

theorem openCover_tFAE {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    TFAE
      [sourceAffineLocally (@P) f,
        ∃ 𝒰 : Scheme.OpenCover.{u} X, ∀ i : 𝒰.J, sourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) (i : 𝒰.J), sourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ {U : Scheme} (g : U ⟶ X) [IsOpenImmersion g], sourceAffineLocally (@P) (g ≫ f)] :=
  by
  tfae_have 1 → 4
  · intro H U g hg V
    skip
    rw [(hP.affine_open_cover_tfae f).out 0 3] at H
    haveI : IsAffine _ := V.2
    rw [← Category.assoc]
    apply H
  tfae_have 4 → 3
  · intro H 𝒰 _ i
    skip
    apply H
  tfae_have 3 → 2
  · intro H
    refine' ⟨X.affine_cover, H _⟩
  tfae_have 2 → 1
  · rintro ⟨𝒰, h𝒰⟩
    rw [(hP.affine_open_cover_tfae f).out 0 1]
    refine' ⟨𝒰.bind fun _ => Scheme.affineCover _, _, _⟩
    · intro i
      dsimp
      infer_instance
    · intro i
      specialize h𝒰 i.1
      rw [(hP.affine_open_cover_tfae (𝒰.map i.fst ≫ f)).out 0 3] at h𝒰
      erw [Category.assoc]
      apply @h𝒰 _ (show _ from _)
      dsimp
      infer_instance
  tfae_finish
#align ring_hom.property_is_local.open_cover_tfae RingHom.PropertyIsLocal.openCover_tFAE

theorem sourceAffineLocallyCompOfIsOpenImmersion {X Y Z : Scheme.{u}} [IsAffine Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsOpenImmersion f] (H : sourceAffineLocally (@P) g) :
    sourceAffineLocally (@P) (f ≫ g) := by apply ((hP.open_cover_tfae g).out 0 3).mp H
#align ring_hom.property_is_local.source_affine_locally_comp_of_is_open_immersion RingHom.PropertyIsLocal.sourceAffineLocallyCompOfIsOpenImmersion

theorem source_affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (𝒰 : Scheme.OpenCover.{u} X) [∀ i, IsAffine (𝒰.obj i)] :
    sourceAffineLocally (@P) f ↔ ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op) :=
  ⟨fun H =>
    let h := ((hP.affine_openCover_tFAE f).out 0 2).mp H
    h 𝒰,
    fun H =>
    let h := ((hP.affine_openCover_tFAE f).out 1 0).mp
    h ⟨𝒰, inferInstance, H⟩⟩
#align ring_hom.property_is_local.source_affine_open_cover_iff RingHom.PropertyIsLocal.source_affine_openCover_iff

theorem isLocalSourceAffineLocally : (sourceAffineLocally @P).IsLocal :=
  sourceAffineLocallyIsLocal hP.respectsIso hP.localizationPreserves
    (@RingHom.PropertyIsLocal.ofLocalizationSpan _ hP)
#align ring_hom.property_is_local.is_local_source_affine_locally RingHom.PropertyIsLocal.isLocalSourceAffineLocally

theorem isLocalAffineLocally : PropertyIsLocalAtTarget (affineLocally @P) :=
  hP.isLocalSourceAffineLocally.targetAffineLocallyIsLocal
#align ring_hom.property_is_local.is_local_affine_locally RingHom.PropertyIsLocal.isLocalAffineLocally

theorem affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i))
    [∀ i j, IsAffine ((𝒰' i).obj j)] :
    affineLocally (@P) f ↔ ∀ i j, P (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op) :=
  (hP.isLocalSourceAffineLocally.affine_openCover_iff f 𝒰).trans
    (forall_congr' fun i => hP.source_affine_openCover_iff _ (𝒰' i))
#align ring_hom.property_is_local.affine_open_cover_iff RingHom.PropertyIsLocal.affine_openCover_iff

theorem source_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} X) :
    affineLocally (@P) f ↔ ∀ i, affineLocally (@P) (𝒰.map i ≫ f) :=
  by
  constructor
  · intro H i U
    rw [morphismRestrict_comp]
    delta morphism_restrict
    apply hP.source_affine_locally_comp_of_is_open_immersion
    apply H
  · intro H U
    haveI : IsAffine _ := U.2
    apply ((hP.open_cover_tfae (f ∣_ U.1)).out 1 0).mp
    use 𝒰.pullback_cover (X.of_restrict _)
    intro i
    specialize H i U
    rw [morphismRestrict_comp] at H
    delta morphism_restrict at H
    have := sourceAffineLocally_respectsIso hP.respects_iso
    rw [Category.assoc, affine_cancel_left_isIso this, ←
      affine_cancel_left_isIso this (pullbackSymmetry _ _).hom,
      pullbackSymmetry_hom_comp_snd_assoc] at H
    exact H
#align ring_hom.property_is_local.source_open_cover_iff RingHom.PropertyIsLocal.source_openCover_iff

theorem affineLocally_of_isOpenImmersion (hP : RingHom.PropertyIsLocal @P) {X Y : Scheme}
    (f : X ⟶ Y) [hf : IsOpenImmersion f] : affineLocally (@P) f :=
  by
  intro U
  haveI H : IsAffine _ := U.2
  rw [← Category.comp_id (f ∣_ U)]
  apply hP.source_affine_locally_comp_of_is_open_immersion
  rw [hP.source_affine_open_cover_iff _ (Scheme.openCoverOfIsIso (𝟙 _))]
  · intro i
    erw [Category.id_comp, op_id, Scheme.Γ.map_id]
    convert hP.holds_for_localization_away _ (1 : Scheme.Γ.obj _)
    · exact (RingHom.algebraMap_toAlgebra _).symm
    · infer_instance
    · refine' IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  · intro i
    exact H
#align ring_hom.property_is_local.affine_locally_of_is_open_immersion RingHom.PropertyIsLocal.affineLocally_of_isOpenImmersion

theorem affineLocally_of_comp
    (H :
      ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
        ∀ (f : R →+* S) (g : S →+* T), P (g.comp f) → P g)
    {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} (h : affineLocally (@P) (f ≫ g)) :
    affineLocally (@P) f :=
  by
  let 𝒰 : ∀ i, ((Z.affine_cover.pullback_cover (f ≫ g)).obj i).OpenCover :=
    by
    intro i
    refine' Scheme.OpenCover.bind _ fun i => Scheme.affineCover _
    apply
      Scheme.OpenCover.pushforwardIso _ (pullbackRightPullbackFstIso g (Z.affine_cover.map i) f).hom
    apply Scheme.Pullback.openCoverOfRight
    exact (pullback g (Z.affine_cover.map i)).affineCover
  have h𝒰 : ∀ i j, IsAffine ((𝒰 i).obj j) := by
    dsimp
    infer_instance
  let 𝒰' := (Z.affine_cover.pullback_cover g).bind fun i => Scheme.affineCover _
  have h𝒰' : ∀ i, IsAffine (𝒰'.obj i) := by
    dsimp
    infer_instance
  rw [hP.affine_open_cover_iff f 𝒰' fun i => Scheme.affineCover _]
  rw [hP.affine_open_cover_iff (f ≫ g) Z.affine_cover 𝒰] at h
  rintro ⟨i, j⟩ k
  dsimp at i j k
  specialize h i ⟨j, k⟩
  dsimp only [Scheme.OpenCover.bind_map, Scheme.OpenCover.pushforwardIso_obj,
    Scheme.Pullback.openCoverOfRight_obj, Scheme.OpenCover.pushforwardIso_map,
    Scheme.Pullback.openCoverOfRight_map, Scheme.OpenCover.bind_obj,
    Scheme.OpenCover.pullbackCover_obj, Scheme.OpenCover.pullbackCover_map] at h⊢
  rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc,
    Category.assoc, ← Category.assoc, op_comp, Functor.map_comp] at h
  exact H _ _ h
#align ring_hom.property_is_local.affine_locally_of_comp RingHom.PropertyIsLocal.affineLocally_of_comp

theorem affineLocally_stableUnderComposition : (affineLocally @P).StableUnderComposition :=
  by
  intro X Y S f g hf hg
  let 𝒰 : ∀ i, ((S.affine_cover.pullback_cover (f ≫ g)).obj i).OpenCover :=
    by
    intro i
    refine' Scheme.OpenCover.bind _ fun i => Scheme.affineCover _
    apply
      Scheme.OpenCover.pushforwardIso _ (pullbackRightPullbackFstIso g (S.affine_cover.map i) f).hom
    apply Scheme.Pullback.openCoverOfRight
    exact (pullback g (S.affine_cover.map i)).affineCover
  rw [hP.affine_open_cover_iff (f ≫ g) S.affine_cover _]
  rotate_left
  · exact 𝒰
  · intro i j
    dsimp at *
    infer_instance
  · rintro i ⟨j, k⟩
    dsimp at i j k
    dsimp only [Scheme.OpenCover.bind_map, Scheme.OpenCover.pushforwardIso_obj,
      Scheme.Pullback.openCoverOfRight_obj, Scheme.OpenCover.pushforwardIso_map,
      Scheme.Pullback.openCoverOfRight_map, Scheme.OpenCover.bind_obj]
    rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      pullback.lift_snd_assoc, Category.assoc, ← Category.assoc, op_comp, Functor.map_comp]
    apply hP.stable_under_composition
    · exact (hP.affine_open_cover_iff _ _ _).mp hg _ _
    · delta affine_locally at hf
      rw [(hP.is_local_source_affine_locally.affine_open_cover_tfae f).out 0 3] at hf
      specialize hf ((pullback g (S.affine_cover.map i)).affineCover.map j ≫ pullback.fst)
      rw [(hP.affine_open_cover_tfae
              (pullback.snd :
                pullback f ((pullback g (S.affine_cover.map i)).affineCover.map j ≫ pullback.fst) ⟶
                  _)).out
          0 3] at
        hf
      apply hf
#align ring_hom.property_is_local.affine_locally_stable_under_composition RingHom.PropertyIsLocal.affineLocally_stableUnderComposition

end RingHom.PropertyIsLocal

