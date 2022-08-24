/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Morphisms.Basic
import Mathbin.Topology.Spectral.Hom

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasi_compact_iff_forall_affine`).

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `quasi-compact` if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class QuasiCompact (f : X ⟶ Y) : Prop where
  is_compact_preimage : ∀ U : Set Y.Carrier, IsOpen U → IsCompact U → IsCompact (f.1.base ⁻¹' U)

theorem quasi_compact_iff_spectral : QuasiCompact f ↔ IsSpectralMap f.1.base :=
  ⟨fun ⟨h⟩ =>
    ⟨by
      continuity, h⟩,
    fun h => ⟨h.2⟩⟩

/-- The `affine_target_morphism_property` corresponding to `quasi_compact`, asserting that the
domain is a quasi-compact scheme. -/
def QuasiCompact.AffineProperty : AffineTargetMorphismProperty := fun X Y f hf => CompactSpace X.Carrier

instance (priority := 900) quasi_compact_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : QuasiCompact f := by
  constructor
  intro U hU hU'
  convert hU'.image (inv f.1.base).continuous_to_fun using 1
  rw [Set.image_eq_preimage_of_inverse]
  delta' Function.LeftInverse
  exacts[is_iso.inv_hom_id_apply f.1.base, is_iso.hom_inv_id_apply f.1.base]

instance quasi_compact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.comp_val_base, coe_comp, Set.preimage_comp]
  apply quasi_compact.is_compact_preimage
  · exact
      Continuous.is_open_preimage
        (by
          continuity)
        _ hU
    
  apply quasi_compact.is_compact_preimage <;> assumption

theorem is_compact_open_iff_eq_finset_affine_union {X : Scheme} (U : Set X.Carrier) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set X.AffineOpens, s.Finite ∧ U = ⋃ (i : X.AffineOpens) (h : i ∈ s), i := by
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis (coe : X.affine_opens → opens X.carrier)
  · rw [Subtype.range_coe]
    exact is_basis_affine_open X
    
  · intro i
    exact i.2.IsCompact
    

theorem is_compact_open_iff_eq_basic_open_union {X : Scheme} [IsAffine X] (U : Set X.Carrier) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set (X.Presheaf.obj (op ⊤)), s.Finite ∧ U = ⋃ (i : X.Presheaf.obj (op ⊤)) (h : i ∈ s), X.basicOpen i :=
  by
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis
  · exact is_basis_basic_open X
    
  · intro i
    exact ((top_is_affine_open _).basic_open_is_affine _).IsCompact
    

theorem quasi_compact_iff_forall_affine :
    QuasiCompact f ↔ ∀ U : Opens Y.Carrier, IsAffineOpen U → IsCompact (f.1.base ⁻¹' (U : Set Y.Carrier)) := by
  rw [quasi_compact_iff]
  refine' ⟨fun H U hU => H U U.Prop hU.IsCompact, _⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩
  simp only [Set.preimage_Union, Subtype.val_eq_coe]
  exact hS.compact_bUnion fun i _ => H i i.Prop

@[simp]
theorem QuasiCompact.affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
    (QuasiCompact.AffineProperty : _).ToProperty f ↔ IsAffine Y ∧ CompactSpace X.Carrier := by
  delta' affine_target_morphism_property.to_property quasi_compact.affine_property
  simp

theorem quasi_compact_iff_affine_property : QuasiCompact f ↔ TargetAffineLocally QuasiCompact.AffineProperty f := by
  rw [quasi_compact_iff_forall_affine]
  trans ∀ U : Y.affine_opens, IsCompact (f.1.base ⁻¹' (U : Set Y.carrier))
  · exact ⟨fun h U => h U U.Prop, fun h U hU => h ⟨U, hU⟩⟩
    
  apply forall_congrₓ
  exact fun _ => is_compact_iff_compact_space

theorem quasi_compact_eq_affine_property : @QuasiCompact = TargetAffineLocally QuasiCompact.AffineProperty := by
  ext
  exact quasi_compact_iff_affine_property _

theorem is_compact_basic_open (X : Scheme) {U : Opens X.Carrier} (hU : IsCompact (U : Set X.Carrier))
    (f : X.Presheaf.obj (op U)) : IsCompact (X.basicOpen f : Set X.Carrier) := by
  classical
  refine' ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_finset_affine_union _).mp ⟨hU, U.prop⟩
  let g : s → X.affine_opens := by
    intro V
    use V.1 ∩ X.basic_open f
    have : V.1.1 ⟶ U := by
      apply hom_of_le
      change _ ⊆ (U : Set X.carrier)
      rw [e]
      convert @Set.subset_Union₂ _ _ _ (fun (U : X.affine_opens) (h : U ∈ s) => ↑U) V V.prop using 1
      rfl
    erw [← X.to_LocallyRingedSpace.to_RingedSpace.basic_open_res this.op]
    exact is_affine_open.basic_open_is_affine V.1.Prop _
  haveI : Finite s := hs.to_subtype
  refine' ⟨Set.Range g, Set.finite_range g, _⟩
  refine' (set.inter_eq_right_iff_subset.mpr (RingedSpace.basic_open_subset _ _)).symm.trans _
  rw [e, Set.Union₂_inter]
  apply le_antisymmₓ <;> apply Set.Union₂_subset
  · intro i hi
    refine' Set.Subset.trans _ (Set.subset_Union₂ _ (Set.mem_range_self ⟨i, hi⟩))
    exact Set.Subset.rfl
    
  · rintro ⟨i, hi⟩ ⟨⟨j, hj⟩, hj'⟩
    rw [← hj']
    refine' Set.Subset.trans _ (Set.subset_Union₂ j hj)
    exact Set.Subset.rfl
    

theorem QuasiCompact.affine_property_is_local : (QuasiCompact.AffineProperty : _).IsLocal := by
  constructor
  · apply affine_target_morphism_property.respects_iso_mk <;> rintro X Y Z _ _ _ H
    exacts[@Homeomorph.compact_space _ _ H (Top.homeoOfIso (as_iso e.inv.1.base)), H]
    
  · introv H
    delta' quasi_compact.affine_property  at H⊢
    change CompactSpace ((opens.map f.val.base).obj (Y.basic_open r))
    rw [Scheme.preimage_basic_open f r]
    erw [← is_compact_iff_compact_space]
    rw [← is_compact_univ_iff] at H
    exact is_compact_basic_open X H _
    
  · rintro X Y H f S hS hS'
    skip
    rw [← is_affine_open.basic_open_union_eq_self_iff] at hS
    delta' quasi_compact.affine_property
    rw [← is_compact_univ_iff]
    change IsCompact ((opens.map f.val.base).obj ⊤).1
    rw [← hS]
    dsimp' [opens.map]
    simp only [opens.coe_supr, Set.preimage_Union, Subtype.val_eq_coe]
    exacts[compact_Union fun i => is_compact_iff_compact_space.mpr (hS' i), top_is_affine_open _]
    

theorem QuasiCompact.affine_open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Tfae
      [QuasiCompact f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y)(_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, CompactSpace (pullback f (𝒰.map i)).Carrier,
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J), CompactSpace (pullback f (𝒰.map i)).Carrier,
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g], CompactSpace (pullback f g).Carrier,
        ∃ (ι : Type u)(U : ι → Opens Y.Carrier)(hU : supr U = ⊤)(hU' : ∀ i, IsAffineOpen (U i)),
          ∀ i, CompactSpace (f.1.base ⁻¹' (U i).1)] :=
  quasi_compact_eq_affine_property.symm ▸ QuasiCompact.affine_property_is_local.affine_open_cover_tfae f

theorem QuasiCompact.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Tfae
      [QuasiCompact f,
        ∃ 𝒰 : Scheme.OpenCover.{u} Y, ∀ i : 𝒰.J, QuasiCompact (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J), QuasiCompact (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.Carrier, QuasiCompact (f ∣_ U),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersion g], QuasiCompact (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u)(U : ι → Opens Y.Carrier)(hU : supr U = ⊤), ∀ i, QuasiCompact (f ∣_ U i)] :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affine_property_is_local.target_affine_locally_is_local.open_cover_tfae f

theorem quasi_compact_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X.Carrier :=
  quasi_compact_eq_affine_property.symm ▸ QuasiCompact.affine_property_is_local.affine_target_iff f

theorem QuasiCompact.affine_open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (f : X ⟶ Y) : QuasiCompact f ↔ ∀ i, CompactSpace (pullback f (𝒰.map i)).Carrier :=
  quasi_compact_eq_affine_property.symm ▸ QuasiCompact.affine_property_is_local.affine_open_cover_iff f 𝒰

theorem QuasiCompact.open_cover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y) (f : X ⟶ Y) :
    QuasiCompact f ↔ ∀ i, QuasiCompact (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affine_property_is_local.target_affine_locally_is_local.open_cover_iff f 𝒰

theorem quasi_compact_respects_iso : MorphismProperty.RespectsIso @QuasiCompact :=
  quasi_compact_eq_affine_property.symm ▸ target_affine_locally_respects_iso QuasiCompact.affine_property_is_local.1

theorem quasi_compact_stable_under_composition : MorphismProperty.StableUnderComposition @QuasiCompact :=
  fun _ _ _ _ _ _ _ => inferInstance

@[elabAsElim]
theorem compact_open_induction_on {P : Opens X.Carrier → Prop} (S : Opens X.Carrier) (hS : IsCompact S.1) (h₁ : P ⊥)
    (h₂ : ∀ (S : Opens X.Carrier) (hS : IsCompact S.1) (U : X.AffineOpens), P S → P (S⊔U)) : P S := by
  classical
  obtain ⟨s, hs, hs'⟩ := (is_compact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩
  replace hs' : S = supr fun i : s => (i : opens X.carrier) := by
    ext1
    simpa using hs'
  subst hs'
  apply hs.induction_on
  · convert h₁
    rw [supr_eq_bot]
    rintro ⟨_, h⟩
    exact h.elim
    
  · intro x s h₃ hs h₄
    have : IsCompact (⨆ i : s, (i : opens X.carrier)).1 := by
      refine' ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1
      exact
        ⟨s, hs, by
          simp ⟩
    convert h₂ _ this x h₄
    simp only [coe_coe]
    rw [supr_subtype, sup_comm]
    conv_rhs => rw [supr_subtype]
    exact supr_insert
    

end AlgebraicGeometry

