/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.quasi_compact
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.Morphisms.Basic
import Mathbin.Topology.Spectral.Hom
import Mathbin.AlgebraicGeometry.Limits

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

open AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : SchemeCat.{u}} (f : X ⟶ Y)

/--
A morphism is `quasi-compact` if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class QuasiCompact (f : X ⟶ Y) : Prop where
  is_compact_preimage : ∀ U : Set Y.carrier, IsOpen U → IsCompact U → IsCompact (f.1.base ⁻¹' U)
#align algebraic_geometry.quasi_compact AlgebraicGeometry.QuasiCompact

theorem quasi_compact_iff_spectral : QuasiCompact f ↔ IsSpectralMap f.1.base :=
  ⟨fun ⟨h⟩ => ⟨by continuity, h⟩, fun h => ⟨h.2⟩⟩
#align algebraic_geometry.quasi_compact_iff_spectral AlgebraicGeometry.quasi_compact_iff_spectral

/-- The `affine_target_morphism_property` corresponding to `quasi_compact`, asserting that the
domain is a quasi-compact scheme. -/
def QuasiCompact.affineProperty : AffineTargetMorphismProperty := fun X Y f hf =>
  CompactSpace X.carrier
#align
  algebraic_geometry.quasi_compact.affine_property AlgebraicGeometry.QuasiCompact.affineProperty

instance (priority := 900) quasi_compact_of_is_iso {X Y : SchemeCat} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := by 
  constructor
  intro U hU hU'
  convert hU'.image (inv f.1.base).continuous_to_fun using 1
  rw [Set.image_eq_preimage_of_inverse]
  delta Function.LeftInverse
  exacts[is_iso.inv_hom_id_apply f.1.base, is_iso.hom_inv_id_apply f.1.base]
#align algebraic_geometry.quasi_compact_of_is_iso AlgebraicGeometry.quasi_compact_of_is_iso

instance quasi_compact_comp {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] : QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.comp_val_base, coe_comp, Set.preimage_comp]
  apply quasi_compact.is_compact_preimage
  · exact Continuous.is_open_preimage (by continuity) _ hU
  apply quasi_compact.is_compact_preimage <;> assumption
#align algebraic_geometry.quasi_compact_comp AlgebraicGeometry.quasi_compact_comp

theorem is_compact_open_iff_eq_finset_affine_union {X : SchemeCat} (U : Set X.carrier) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set X.affineOpens, s.Finite ∧ U = ⋃ (i : X.affineOpens) (h : i ∈ s), i :=
  by
  apply
    opens.is_compact_open_iff_eq_finite_Union_of_is_basis (coe : X.affine_opens → opens X.carrier)
  · rw [Subtype.range_coe]
    exact is_basis_affine_open X
  · intro i
    exact i.2.IsCompact
#align
  algebraic_geometry.is_compact_open_iff_eq_finset_affine_union AlgebraicGeometry.is_compact_open_iff_eq_finset_affine_union

theorem is_compact_open_iff_eq_basic_open_union {X : SchemeCat} [IsAffine X] (U : Set X.carrier) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set (X.Presheaf.obj (op ⊤)),
        s.Finite ∧ U = ⋃ (i : X.Presheaf.obj (op ⊤)) (h : i ∈ s), X.basicOpen i :=
  by 
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis
  · exact is_basis_basic_open X
  · intro i
    exact ((top_is_affine_open _).basic_open_is_affine _).IsCompact
#align
  algebraic_geometry.is_compact_open_iff_eq_basic_open_union AlgebraicGeometry.is_compact_open_iff_eq_basic_open_union

theorem quasi_compact_iff_forall_affine :
    QuasiCompact f ↔
      ∀ U : Opens Y.carrier, IsAffineOpen U → IsCompact (f.1.base ⁻¹' (U : Set Y.carrier)) :=
  by 
  rw [quasi_compact_iff]
  refine' ⟨fun H U hU => H U U.Prop hU.IsCompact, _⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩
  simp only [Set.preimage_Union, Subtype.val_eq_coe]
  exact hS.is_compact_bUnion fun i _ => H i i.Prop
#align
  algebraic_geometry.quasi_compact_iff_forall_affine AlgebraicGeometry.quasi_compact_iff_forall_affine

@[simp]
theorem QuasiCompact.affine_property_to_property {X Y : SchemeCat} (f : X ⟶ Y) :
    (QuasiCompact.affineProperty : _).toProperty f ↔ IsAffine Y ∧ CompactSpace X.carrier := by
  delta affine_target_morphism_property.to_property quasi_compact.affine_property
  simp
#align
  algebraic_geometry.quasi_compact.affine_property_to_property AlgebraicGeometry.QuasiCompact.affine_property_to_property

theorem quasi_compact_iff_affine_property :
    QuasiCompact f ↔ targetAffineLocally QuasiCompact.affineProperty f := by
  rw [quasi_compact_iff_forall_affine]
  trans ∀ U : Y.affine_opens, IsCompact (f.1.base ⁻¹' (U : Set Y.carrier))
  · exact ⟨fun h U => h U U.Prop, fun h U hU => h ⟨U, hU⟩⟩
  apply forall_congr'
  exact fun _ => is_compact_iff_compact_space
#align
  algebraic_geometry.quasi_compact_iff_affine_property AlgebraicGeometry.quasi_compact_iff_affine_property

theorem quasi_compact_eq_affine_property :
    @QuasiCompact = targetAffineLocally QuasiCompact.affineProperty := by
  ext
  exact quasi_compact_iff_affine_property _
#align
  algebraic_geometry.quasi_compact_eq_affine_property AlgebraicGeometry.quasi_compact_eq_affine_property

theorem is_compact_basic_open (X : SchemeCat) {U : Opens X.carrier}
    (hU : IsCompact (U : Set X.carrier)) (f : X.Presheaf.obj (op U)) :
    IsCompact (X.basicOpen f : Set X.carrier) := by
  classical 
    refine' ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1
    obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_finset_affine_union _).mp ⟨hU, U.prop⟩
    let g : s → X.affine_opens := by 
      intro V
      use V.1 ⊓ X.basic_open f
      have : V.1.1 ⟶ U := by 
        apply hom_of_le
        change _ ⊆ (U : Set X.carrier)
        rw [e]
        convert @Set.subset_Union₂ _ _ _ (fun (U : X.affine_opens) (h : U ∈ s) => ↑U) V V.prop using
          1
        rfl
      erw [← X.to_LocallyRingedSpace.to_RingedSpace.basic_open_res this.op]
      exact is_affine_open.basic_open_is_affine V.1.Prop _
    haveI : Finite s := hs.to_subtype
    refine' ⟨Set.range g, Set.finite_range g, _⟩
    refine' (set.inter_eq_right_iff_subset.mpr (RingedSpace.basic_open_le _ _)).symm.trans _
    rw [e, Set.Union₂_inter]
    apply le_antisymm <;> apply Set.Union₂_subset
    · intro i hi
      refine' Set.Subset.trans _ (Set.subset_Union₂ _ (Set.mem_range_self ⟨i, hi⟩))
      exact Set.Subset.rfl
    · rintro ⟨i, hi⟩ ⟨⟨j, hj⟩, hj'⟩
      rw [← hj']
      refine' Set.Subset.trans _ (Set.subset_Union₂ j hj)
      exact Set.Subset.rfl
#align algebraic_geometry.is_compact_basic_open AlgebraicGeometry.is_compact_basic_open

theorem QuasiCompact.affinePropertyIsLocal : (QuasiCompact.affineProperty : _).IsLocal := by
  constructor
  · apply affine_target_morphism_property.respects_iso_mk <;> rintro X Y Z _ _ _ H
    exacts[@Homeomorph.compact_space _ _ H (TopCat.homeoOfIso (as_iso e.inv.1.base)), H]
  · introv H
    delta quasi_compact.affine_property at H⊢
    change CompactSpace ((opens.map f.val.base).obj (Y.basic_open r))
    rw [Scheme.preimage_basic_open f r]
    erw [← is_compact_iff_compact_space]
    rw [← is_compact_univ_iff] at H
    exact is_compact_basic_open X H _
  · rintro X Y H f S hS hS'
    skip
    rw [← is_affine_open.basic_open_union_eq_self_iff] at hS
    delta quasi_compact.affine_property
    rw [← is_compact_univ_iff]
    change IsCompact ((opens.map f.val.base).obj ⊤).1
    rw [← hS]
    dsimp [opens.map]
    simp only [opens.coe_supr, Set.preimage_Union, Subtype.val_eq_coe]
    exacts[is_compact_Union fun i => is_compact_iff_compact_space.mpr (hS' i), top_is_affine_open _]
#align
  algebraic_geometry.quasi_compact.affine_property_is_local AlgebraicGeometry.QuasiCompact.affinePropertyIsLocal

theorem QuasiCompact.affine_open_cover_tfae {X Y : SchemeCat.{u}} (f : X ⟶ Y) :
    Tfae
      [QuasiCompact f,
        ∃ (𝒰 : SchemeCat.OpenCover.{u} Y)(_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, CompactSpace (pullback f (𝒰.map i)).carrier,
        ∀ (𝒰 : SchemeCat.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          CompactSpace (pullback f (𝒰.map i)).carrier,
        ∀ {U : SchemeCat} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g],
          CompactSpace (pullback f g).carrier,
        ∃ (ι : Type u)(U : ι → Opens Y.carrier)(hU : supᵢ U = ⊤)(hU' : ∀ i, IsAffineOpen (U i)),
          ∀ i, CompactSpace (f.1.base ⁻¹' (U i).1)] :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affinePropertyIsLocal.affine_open_cover_tfae f
#align
  algebraic_geometry.quasi_compact.affine_open_cover_tfae AlgebraicGeometry.QuasiCompact.affine_open_cover_tfae

theorem QuasiCompact.is_local_at_target : PropertyIsLocalAtTarget @QuasiCompact :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affinePropertyIsLocal.target_affine_locally_is_local
#align
  algebraic_geometry.quasi_compact.is_local_at_target AlgebraicGeometry.QuasiCompact.is_local_at_target

theorem QuasiCompact.open_cover_tfae {X Y : SchemeCat.{u}} (f : X ⟶ Y) :
    Tfae
      [QuasiCompact f,
        ∃ 𝒰 : SchemeCat.OpenCover.{u} Y,
          ∀ i : 𝒰.J, QuasiCompact (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : SchemeCat.OpenCover.{u} Y) (i : 𝒰.J),
          QuasiCompact (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, QuasiCompact (f ∣_ U),
        ∀ {U : SchemeCat} (g : U ⟶ Y) [IsOpenImmersion g],
          QuasiCompact (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u)(U : ι → Opens Y.carrier)(hU : supᵢ U = ⊤), ∀ i, QuasiCompact (f ∣_ U i)] :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affinePropertyIsLocal.target_affine_locally_is_local.open_cover_tfae f
#align
  algebraic_geometry.quasi_compact.open_cover_tfae AlgebraicGeometry.QuasiCompact.open_cover_tfae

theorem quasi_compact_over_affine_iff {X Y : SchemeCat} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X.carrier :=
  quasi_compact_eq_affine_property.symm ▸ QuasiCompact.affinePropertyIsLocal.affine_target_iff f
#align
  algebraic_geometry.quasi_compact_over_affine_iff AlgebraicGeometry.quasi_compact_over_affine_iff

theorem compact_space_iff_quasi_compact (X : SchemeCat) :
    CompactSpace X.carrier ↔ QuasiCompact (terminal.from X) :=
  (quasi_compact_over_affine_iff _).symm
#align
  algebraic_geometry.compact_space_iff_quasi_compact AlgebraicGeometry.compact_space_iff_quasi_compact

theorem QuasiCompact.affine_open_cover_iff {X Y : SchemeCat.{u}} (𝒰 : SchemeCat.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (f : X ⟶ Y) :
    QuasiCompact f ↔ ∀ i, CompactSpace (pullback f (𝒰.map i)).carrier :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affinePropertyIsLocal.affine_open_cover_iff f 𝒰
#align
  algebraic_geometry.quasi_compact.affine_open_cover_iff AlgebraicGeometry.QuasiCompact.affine_open_cover_iff

theorem QuasiCompact.open_cover_iff {X Y : SchemeCat.{u}} (𝒰 : SchemeCat.OpenCover.{u} Y)
    (f : X ⟶ Y) : QuasiCompact f ↔ ∀ i, QuasiCompact (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affinePropertyIsLocal.target_affine_locally_is_local.open_cover_iff f 𝒰
#align algebraic_geometry.quasi_compact.open_cover_iff AlgebraicGeometry.QuasiCompact.open_cover_iff

theorem quasi_compact_respects_iso : MorphismProperty.RespectsIso @QuasiCompact :=
  quasi_compact_eq_affine_property.symm ▸
    target_affine_locally_respects_iso QuasiCompact.affinePropertyIsLocal.1
#align algebraic_geometry.quasi_compact_respects_iso AlgebraicGeometry.quasi_compact_respects_iso

theorem quasi_compact_stable_under_composition :
    MorphismProperty.StableUnderComposition @QuasiCompact := fun _ _ _ _ _ _ _ => inferInstance
#align
  algebraic_geometry.quasi_compact_stable_under_composition AlgebraicGeometry.quasi_compact_stable_under_composition

attribute [-simp] PresheafedSpace.as_coe SheafedSpace.as_coe

theorem QuasiCompact.affine_property_stable_under_base_change :
    QuasiCompact.affineProperty.StableUnderBaseChange := by
  intro X Y S _ _ f g h
  rw [quasi_compact.affine_property] at h⊢
  skip
  let 𝒰 := Scheme.pullback.open_cover_of_right Y.affine_cover.finite_subcover f g
  have : Finite 𝒰.J := by 
    dsimp [𝒰]
    infer_instance
  have : ∀ i, CompactSpace (𝒰.obj i).carrier := by
    intro i
    dsimp
    infer_instance
  exact 𝒰.compact_space
#align
  algebraic_geometry.quasi_compact.affine_property_stable_under_base_change AlgebraicGeometry.QuasiCompact.affine_property_stable_under_base_change

theorem quasi_compact_stable_under_base_change :
    MorphismProperty.StableUnderBaseChange @QuasiCompact :=
  quasi_compact_eq_affine_property.symm ▸
    QuasiCompact.affinePropertyIsLocal.StableUnderBaseChange
      QuasiCompact.affine_property_stable_under_base_change
#align
  algebraic_geometry.quasi_compact_stable_under_base_change AlgebraicGeometry.quasi_compact_stable_under_base_change

variable {Z : SchemeCat.{u}}

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] :
    QuasiCompact (pullback.fst : pullback f g ⟶ X) :=
  quasi_compact_stable_under_base_change.fst f g inferInstance

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] :
    QuasiCompact (pullback.snd : pullback f g ⟶ Y) :=
  quasi_compact_stable_under_base_change.snd f g inferInstance

@[elab_as_elim]
theorem compact_open_induction_on {P : Opens X.carrier → Prop} (S : Opens X.carrier)
    (hS : IsCompact S.1) (h₁ : P ⊥)
    (h₂ : ∀ (S : Opens X.carrier) (hS : IsCompact S.1) (U : X.affineOpens), P S → P (S ⊔ U)) :
    P S := by
  classical 
    obtain ⟨s, hs, hs'⟩ := (is_compact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩
    replace hs' : S = supᵢ fun i : s => (i : opens X.carrier) := by
      ext1
      simpa using hs'
    subst hs'
    apply hs.induction_on
    · convert h₁
      rw [supᵢ_eq_bot]
      rintro ⟨_, h⟩
      exact h.elim
    · intro x s h₃ hs h₄
      have : IsCompact (⨆ i : s, (i : opens X.carrier)).1 := by
        refine' ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1
        exact ⟨s, hs, by simp⟩
      convert h₂ _ this x h₄
      simp only [coe_coe]
      rw [supᵢ_subtype, sup_comm]
      conv_rhs => rw [supᵢ_subtype]
      exact supᵢ_insert
#align algebraic_geometry.compact_open_induction_on AlgebraicGeometry.compact_open_induction_on

theorem exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open (X : SchemeCat)
    {U : Opens X.carrier} (hU : IsAffineOpen U) (x f : X.Presheaf.obj (op U))
    (H : x |_ X.basicOpen f = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  rw [← map_zero (X.presheaf.map (hom_of_le <| X.basic_open_le f : X.basic_open f ⟶ U).op)] at H
  have := (is_localization_basic_open hU f).3
  obtain ⟨⟨_, n, rfl⟩, e⟩ := this.mp H
  exact ⟨n, by simpa [mul_comm x] using e⟩
#align
  algebraic_geometry.exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open

/-- If `x : Γ(X, U)` is zero on `D(f)` for some `f : Γ(X, U)`, and `U` is quasi-compact, then
`f ^ n * x = 0` for some `n`. -/
theorem exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact (X : SchemeCat)
    {U : Opens X.carrier} (hU : IsCompact U.1) (x f : X.Presheaf.obj (op U))
    (H : x |_ X.basicOpen f = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_finset_affine_union U.1).mp ⟨hU, U.2⟩
  replace e : U = supᵢ fun i : s => (i : opens X.carrier)
  · ext1
    simpa using e
  have h₁ : ∀ i : s, i.1.1 ≤ U := by 
    intro i
    change (i : opens X.carrier) ≤ U
    rw [e]
    exact le_supᵢ _ _
  have H' := fun i : s =>
    exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open X i.1.2
      (X.presheaf.map (hom_of_le (h₁ i)).op x) (X.presheaf.map (hom_of_le (h₁ i)).op f) _
  swap
  · delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict at H⊢
    convert congr_arg (X.presheaf.map (hom_of_le _).op) H
    · simp only [← comp_apply, ← functor.map_comp]
      congr
    · rw [map_zero]
    · rw [X.basic_open_res]
      exact Set.inter_subset_right _ _
  choose n hn using H'
  haveI := hs.to_subtype
  cases nonempty_fintype s
  use finset.univ.sup n
  suffices ∀ i : s, X.presheaf.map (hom_of_le (h₁ i)).op (f ^ finset.univ.sup n * x) = 0 by
    subst e
    apply X.sheaf.eq_of_locally_eq fun i : s => (i : opens X.carrier)
    intro i
    rw [map_zero]
    apply this
  intro i
  replace hn :=
    congr_arg (fun x => X.presheaf.map (hom_of_le (h₁ i)).op (f ^ (finset.univ.sup n - n i)) * x)
      (hn i)
  dsimp at hn
  simp only [← map_mul, ← map_pow] at hn
  rwa [mul_zero, ← mul_assoc, ← pow_add, tsub_add_cancel_of_le] at hn
  apply Finset.le_sup (Finset.mem_univ i)
#align
  algebraic_geometry.exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact

end AlgebraicGeometry

