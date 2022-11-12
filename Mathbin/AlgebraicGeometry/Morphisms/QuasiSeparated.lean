/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathbin.Topology.QuasiSeparated

/-!
# Quasi-separated morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-separated if the diagonal morphism `X ⟶ X ×[Y] X` is
quasi-compact.

A scheme is quasi-separated if the intersections of any two affine open sets is quasi-compact.
(`algebraic_geometry.quasi_separated_space_iff_affine`)

We show that a morphism is quasi-separated if the preimage of every affine open is quasi-separated.

We also show that this property is local at the target,
and is stable under compositions and base-changes.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : SchemeCat.{u}} (f : X ⟶ Y)

/-- A morphism is `quasi_separated` if diagonal map is quasi-compact. -/
@[mk_iff]
class QuasiSeparated (f : X ⟶ Y) : Prop where
  diagonalQuasiCompact : QuasiCompact (pullback.diagonal f)
#align algebraic_geometry.quasi_separated AlgebraicGeometry.QuasiSeparated

/-- The `affine_target_morphism_property` corresponding to `quasi_separated`, asserting that the
domain is a quasi-separated scheme. -/
def QuasiSeparated.affineProperty : AffineTargetMorphismProperty := fun X Y f _ => QuasiSeparatedSpace X.Carrier
#align algebraic_geometry.quasi_separated.affine_property AlgebraicGeometry.QuasiSeparated.affineProperty

theorem quasi_separated_space_iff_affine (X : SchemeCat) :
    QuasiSeparatedSpace X.Carrier ↔ ∀ U V : X.AffineOpens, IsCompact (U ∩ V : Set X.Carrier) := by
  rw [quasi_separated_space_iff]
  constructor
  · intro H U V
    exact H U V U.1.2 U.2.IsCompact V.1.2 V.2.IsCompact
    
  · intro H
    suffices
      ∀ (U : opens X.carrier) (hU : IsCompact U.1) (V : opens X.carrier) (hV : IsCompact V.1), IsCompact (U ⊓ V).1 by
      intro U V hU hU' hV hV'
      exact this ⟨U, hU⟩ hU' ⟨V, hV⟩ hV'
    intro U hU V hV
    apply compact_open_induction_on V hV
    · simp
      
    · intro S hS V hV
      change IsCompact (U.1 ∩ (S.1 ∪ V.1))
      rw [Set.inter_union_distrib_left]
      apply hV.union
      clear hV
      apply compact_open_induction_on U hU
      · simp
        
      · intro S hS W hW
        change IsCompact ((S.1 ∪ W.1) ∩ V.1)
        rw [Set.union_inter_distrib_right]
        apply hW.union
        apply H
        
      
    
#align algebraic_geometry.quasi_separated_space_iff_affine AlgebraicGeometry.quasi_separated_space_iff_affine

theorem quasi_compact_affine_property_iff_quasi_separated_space {X Y : SchemeCat} [IsAffine Y] (f : X ⟶ Y) :
    QuasiCompact.affineProperty.diagonal f ↔ QuasiSeparatedSpace X.Carrier := by
  delta affine_target_morphism_property.diagonal
  rw [quasi_separated_space_iff_affine]
  constructor
  · intro H U V
    haveI : is_affine _ := U.2
    haveI : is_affine _ := V.2
    let g : pullback (X.of_restrict U.1.OpenEmbedding) (X.of_restrict V.1.OpenEmbedding) ⟶ X :=
      pullback.fst ≫ X.of_restrict _
    have : is_open_immersion g := inferInstance
    have e := Homeomorph.ofEmbedding _ this.base_open.to_embedding
    rw [is_open_immersion.range_pullback_to_base_of_left] at e
    erw [Subtype.range_coe, Subtype.range_coe] at e
    rw [is_compact_iff_compact_space]
    exact @Homeomorph.compact_space _ _ (H _ _) e
    
  · introv H h₁ h₂
    skip
    let g : pullback f₁ f₂ ⟶ X := pullback.fst ≫ f₁
    have : is_open_immersion g := inferInstance
    have e := Homeomorph.ofEmbedding _ this.base_open.to_embedding
    rw [is_open_immersion.range_pullback_to_base_of_left] at e
    simp_rw [is_compact_iff_compact_space] at H
    exact
      @Homeomorph.compact_space _ _
        (H ⟨⟨_, h₁.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩
          ⟨⟨_, h₂.base_open.open_range⟩, range_is_affine_open_of_open_immersion _⟩)
        e.symm
    
#align
  algebraic_geometry.quasi_compact_affine_property_iff_quasi_separated_space AlgebraicGeometry.quasi_compact_affine_property_iff_quasi_separated_space

theorem quasi_separated_eq_diagonal_is_quasi_compact : @QuasiSeparated = MorphismProperty.Diagonal @QuasiCompact := by
  ext
  exact quasi_separated_iff _
#align
  algebraic_geometry.quasi_separated_eq_diagonal_is_quasi_compact AlgebraicGeometry.quasi_separated_eq_diagonal_is_quasi_compact

theorem quasi_compact_affine_property_diagonal_eq :
    QuasiCompact.affineProperty.diagonal = quasi_separated.affine_property := by
  ext
  rw [quasi_compact_affine_property_iff_quasi_separated_space]
  rfl
#align
  algebraic_geometry.quasi_compact_affine_property_diagonal_eq AlgebraicGeometry.quasi_compact_affine_property_diagonal_eq

theorem quasi_separated_eq_affine_property_diagonal :
    @QuasiSeparated = TargetAffineLocally QuasiCompact.affineProperty.diagonal := by
  rw [quasi_separated_eq_diagonal_is_quasi_compact, quasi_compact_eq_affine_property]
  exact diagonal_target_affine_locally_eq_target_affine_locally _ quasi_compact.affine_property_is_local
#align
  algebraic_geometry.quasi_separated_eq_affine_property_diagonal AlgebraicGeometry.quasi_separated_eq_affine_property_diagonal

theorem quasi_separated_eq_affine_property : @QuasiSeparated = TargetAffineLocally QuasiSeparated.affineProperty := by
  rw [quasi_separated_eq_affine_property_diagonal, quasi_compact_affine_property_diagonal_eq]
#align algebraic_geometry.quasi_separated_eq_affine_property AlgebraicGeometry.quasi_separated_eq_affine_property

theorem QuasiSeparated.affinePropertyIsLocal : QuasiSeparated.affineProperty.IsLocal :=
  quasi_compact_affine_property_diagonal_eq ▸ QuasiCompact.affinePropertyIsLocal.diagonal
#align
  algebraic_geometry.quasi_separated.affine_property_is_local AlgebraicGeometry.QuasiSeparated.affinePropertyIsLocal

instance (priority := 900) quasiSeparatedOfMono {X Y : SchemeCat} (f : X ⟶ Y) [Mono f] : QuasiSeparated f :=
  ⟨inferInstance⟩
#align algebraic_geometry.quasi_separated_of_mono AlgebraicGeometry.quasiSeparatedOfMono

theorem quasi_separated_stable_under_composition : MorphismProperty.StableUnderComposition @QuasiSeparated :=
  quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
    quasi_compact_stable_under_composition.diagonal quasi_compact_respects_iso quasi_compact_stable_under_base_change
#align
  algebraic_geometry.quasi_separated_stable_under_composition AlgebraicGeometry.quasi_separated_stable_under_composition

theorem quasi_separated_stable_under_base_change : MorphismProperty.StableUnderBaseChange @QuasiSeparated :=
  quasi_separated_eq_diagonal_is_quasi_compact.symm ▸
    quasi_compact_stable_under_base_change.diagonal quasi_compact_respects_iso
#align
  algebraic_geometry.quasi_separated_stable_under_base_change AlgebraicGeometry.quasi_separated_stable_under_base_change

instance quasiSeparatedComp {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  quasi_separated_stable_under_composition f g inferInstance inferInstance
#align algebraic_geometry.quasi_separated_comp AlgebraicGeometry.quasiSeparatedComp

theorem quasi_separated_respects_iso : MorphismProperty.RespectsIso @QuasiSeparated :=
  quasi_separated_eq_diagonal_is_quasi_compact.symm ▸ quasi_compact_respects_iso.diagonal
#align algebraic_geometry.quasi_separated_respects_iso AlgebraicGeometry.quasi_separated_respects_iso

theorem QuasiSeparated.affine_open_cover_tfae {X Y : SchemeCat.{u}} (f : X ⟶ Y) :
    Tfae
      [QuasiSeparated f,
        ∃ (𝒰 : SchemeCat.OpenCover.{u} Y)(_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, QuasiSeparatedSpace (pullback f (𝒰.map i)).Carrier,
        ∀ (𝒰 : SchemeCat.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          QuasiSeparatedSpace (pullback f (𝒰.map i)).Carrier,
        ∀ {U : SchemeCat} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g], QuasiSeparatedSpace (pullback f g).Carrier,
        ∃ (𝒰 : SchemeCat.OpenCover.{u} Y)(_ : ∀ i, IsAffine (𝒰.obj i))(𝒰' :
          ∀ i : 𝒰.J, SchemeCat.OpenCover.{u} (pullback f (𝒰.map i)))(_ : ∀ i j, IsAffine ((𝒰' i).obj j)),
          ∀ (i : 𝒰.J) (j k : (𝒰' i).J), CompactSpace (pullback ((𝒰' i).map j) ((𝒰' i).map k)).Carrier] :=
  by
  have := quasi_compact.affine_property_is_local.diagonal_affine_open_cover_tfae f
  simp_rw [← quasi_compact_eq_affine_property, ← quasi_separated_eq_diagonal_is_quasi_compact,
    quasi_compact_affine_property_diagonal_eq] at this
  exact this
#align algebraic_geometry.quasi_separated.affine_open_cover_tfae AlgebraicGeometry.QuasiSeparated.affine_open_cover_tfae

theorem QuasiSeparated.isLocalAtTarget : PropertyIsLocalAtTarget @QuasiSeparated :=
  quasi_separated_eq_affine_property_diagonal.symm ▸
    QuasiCompact.affinePropertyIsLocal.diagonal.targetAffineLocallyIsLocal
#align algebraic_geometry.quasi_separated.is_local_at_target AlgebraicGeometry.QuasiSeparated.isLocalAtTarget

theorem QuasiSeparated.open_cover_tfae {X Y : SchemeCat.{u}} (f : X ⟶ Y) :
    Tfae
      [QuasiSeparated f,
        ∃ 𝒰 : SchemeCat.OpenCover.{u} Y, ∀ i : 𝒰.J, QuasiSeparated (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : SchemeCat.OpenCover.{u} Y) (i : 𝒰.J),
          QuasiSeparated (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.Carrier, QuasiSeparated (f ∣_ U),
        ∀ {U : SchemeCat} (g : U ⟶ Y) [IsOpenImmersion g], QuasiSeparated (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u)(U : ι → Opens Y.Carrier)(hU : supr U = ⊤), ∀ i, QuasiSeparated (f ∣_ U i)] :=
  QuasiSeparated.isLocalAtTarget.open_cover_tfae f
#align algebraic_geometry.quasi_separated.open_cover_tfae AlgebraicGeometry.QuasiSeparated.open_cover_tfae

theorem quasi_separated_over_affine_iff {X Y : SchemeCat} (f : X ⟶ Y) [IsAffine Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X.Carrier := by
  rw [quasi_separated_eq_affine_property, quasi_separated.affine_property_is_local.affine_target_iff f,
    quasi_separated.affine_property]
#align algebraic_geometry.quasi_separated_over_affine_iff AlgebraicGeometry.quasi_separated_over_affine_iff

theorem quasi_separated_space_iff_quasi_separated (X : SchemeCat) :
    QuasiSeparatedSpace X.Carrier ↔ QuasiSeparated (terminal.from X) :=
  (quasi_separated_over_affine_iff _).symm
#align
  algebraic_geometry.quasi_separated_space_iff_quasi_separated AlgebraicGeometry.quasi_separated_space_iff_quasi_separated

theorem QuasiSeparated.affine_open_cover_iff {X Y : SchemeCat.{u}} (𝒰 : SchemeCat.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (f : X ⟶ Y) :
    QuasiSeparated f ↔ ∀ i, QuasiSeparatedSpace (pullback f (𝒰.map i)).Carrier := by
  rw [quasi_separated_eq_affine_property, quasi_separated.affine_property_is_local.affine_open_cover_iff f 𝒰]
  rfl
#align algebraic_geometry.quasi_separated.affine_open_cover_iff AlgebraicGeometry.QuasiSeparated.affine_open_cover_iff

theorem QuasiSeparated.open_cover_iff {X Y : SchemeCat.{u}} (𝒰 : SchemeCat.OpenCover.{u} Y) (f : X ⟶ Y) :
    QuasiSeparated f ↔ ∀ i, QuasiSeparated (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  QuasiSeparated.isLocalAtTarget.open_cover_iff f 𝒰
#align algebraic_geometry.quasi_separated.open_cover_iff AlgebraicGeometry.QuasiSeparated.open_cover_iff

instance {X Y S : SchemeCat} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated g] :
    QuasiSeparated (pullback.fst : pullback f g ⟶ X) :=
  quasi_separated_stable_under_base_change.fst f g inferInstance

instance {X Y S : SchemeCat} (f : X ⟶ S) (g : Y ⟶ S) [QuasiSeparated f] :
    QuasiSeparated (pullback.snd : pullback f g ⟶ Y) :=
  quasi_separated_stable_under_base_change.snd f g inferInstance

instance {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiSeparated f] [QuasiSeparated g] : QuasiSeparated (f ≫ g) :=
  quasi_separated_stable_under_composition f g inferInstance inferInstance

theorem quasi_separated_space_of_quasi_separated {X Y : SchemeCat} (f : X ⟶ Y) [hY : QuasiSeparatedSpace Y.Carrier]
    [QuasiSeparated f] : QuasiSeparatedSpace X.Carrier := by
  rw [quasi_separated_space_iff_quasi_separated] at hY⊢
  have : f ≫ terminal.from Y = terminal.from X := terminal_is_terminal.hom_ext _ _
  rw [← this]
  skip
  infer_instance
#align
  algebraic_geometry.quasi_separated_space_of_quasi_separated AlgebraicGeometry.quasi_separated_space_of_quasi_separated

instance quasi_separated_space_of_is_affine (X : SchemeCat) [IsAffine X] : QuasiSeparatedSpace X.Carrier := by
  constructor
  intro U V hU hU' hV hV'
  obtain ⟨s, hs, e⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hU', hU⟩
  obtain ⟨s', hs', e'⟩ := (is_compact_open_iff_eq_basic_open_union _).mp ⟨hV', hV⟩
  rw [e, e', Set.Union₂_inter]
  simp_rw [Set.inter_Union₂]
  apply hs.is_compact_bUnion
  · intro i hi
    apply hs'.is_compact_bUnion
    intro i' hi'
    change IsCompact (X.basic_open i ⊓ X.basic_open i').1
    rw [← Scheme.basic_open_mul]
    exact ((top_is_affine_open _).basic_open_is_affine _).IsCompact
    
#align algebraic_geometry.quasi_separated_space_of_is_affine AlgebraicGeometry.quasi_separated_space_of_is_affine

theorem IsAffineOpen.is_quasi_separated {X : SchemeCat} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    IsQuasiSeparated (U : Set X.Carrier) := by
  rw [is_quasi_separated_iff_quasi_separated_space]
  exacts[@AlgebraicGeometry.quasi_separated_space_of_is_affine _ hU, U.prop]
#align algebraic_geometry.is_affine_open.is_quasi_separated AlgebraicGeometry.IsAffineOpen.is_quasi_separated

theorem quasiSeparatedOfComp {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) [H : QuasiSeparated (f ≫ g)] :
    QuasiSeparated f := by
  rw [(quasi_separated.affine_open_cover_tfae f).out 0 1]
  rw [(quasi_separated.affine_open_cover_tfae (f ≫ g)).out 0 2] at H
  use (Z.affine_cover.pullback_cover g).bind fun x => Scheme.affine_cover _
  constructor
  · intro i
    dsimp
    infer_instance
    
  rintro ⟨i, j⟩
  dsimp at *
  specialize H _ i
  refine' @quasi_separated_space_of_quasi_separated _ H _
  · exact
      pullback.map _ _ _ _ (𝟙 _) _ _ (by simp) (category.comp_id _) ≫
        (pullback_right_pullback_fst_iso g (Z.affine_cover.map i) f).Hom
    
  · apply AlgebraicGeometry.quasiSeparatedOfMono
    
#align algebraic_geometry.quasi_separated_of_comp AlgebraicGeometry.quasiSeparatedOfComp

end AlgebraicGeometry

