/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/
import Mathbin.Topology.Category.CompHausCat.Default
import Mathbin.Topology.Connected
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.LocallyConstant.Basic
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono
import Mathbin.CategoryTheory.FintypeCat

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. finite coproducts
2. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/


universe u

open CategoryTheory

/-- The type of profinite topological spaces. -/
structure ProfiniteCat where
  toCompHaus : CompHausCat
  [IsTotallyDisconnected : TotallyDisconnectedSpace to_CompHaus]
#align Profinite ProfiniteCat

namespace ProfiniteCat

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] : ProfiniteCat :=
  ⟨⟨⟨X⟩⟩⟩
#align Profinite.of ProfiniteCat.of

instance : Inhabited ProfiniteCat :=
  ⟨ProfiniteCat.of PEmpty⟩

instance category : Category ProfiniteCat :=
  InducedCategory.category toCompHaus
#align Profinite.category ProfiniteCat.category

instance concreteCategory : ConcreteCategory ProfiniteCat :=
  InducedCategory.concreteCategory _
#align Profinite.concrete_category ProfiniteCat.concreteCategory

instance hasForget₂ : HasForget₂ ProfiniteCat TopCat :=
  InducedCategory.hasForget₂ _
#align Profinite.has_forget₂ ProfiniteCat.hasForget₂

instance : CoeSort ProfiniteCat (Type _) :=
  ⟨fun X => X.toCompHaus⟩

instance {X : ProfiniteCat} : TotallyDisconnectedSpace X :=
  X.IsTotallyDisconnected

-- We check that we automatically infer that Profinite sets are compact and Hausdorff.
example {X : ProfiniteCat} : CompactSpace X :=
  inferInstance

example {X : ProfiniteCat} : T2Space X :=
  inferInstance

@[simp]
theorem coe_to_CompHaus {X : ProfiniteCat} : (X.toCompHaus : Type _) = X :=
  rfl
#align Profinite.coe_to_CompHaus ProfiniteCat.coe_to_CompHaus

@[simp]
theorem coe_id (X : ProfiniteCat) : (𝟙 X : X → X) = id :=
  rfl
#align Profinite.coe_id ProfiniteCat.coe_id

@[simp]
theorem coe_comp {X Y Z : ProfiniteCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl
#align Profinite.coe_comp ProfiniteCat.coe_comp

end ProfiniteCat

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps]
def profiniteToCompHaus : ProfiniteCat ⥤ CompHausCat :=
  inducedFunctor _ deriving Full, Faithful
#align Profinite_to_CompHaus profiniteToCompHaus

/-- The fully faithful embedding of `Profinite` in `Top`. This is definitionally the same as the
obvious composite. -/
@[simps]
def ProfiniteCat.toTop : ProfiniteCat ⥤ TopCat :=
  forget₂ _ _ deriving Full, Faithful
#align Profinite.to_Top ProfiniteCat.toTop

@[simp]
theorem ProfiniteCat.to_CompHaus_to_Top : profiniteToCompHaus ⋙ compHausToTop = ProfiniteCat.toTop :=
  rfl
#align Profinite.to_CompHaus_to_Top ProfiniteCat.to_CompHaus_to_Top

section ProfiniteCat

-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
/-- (Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
def CompHausCat.toProfiniteObj (X : CompHausCat.{u}) : ProfiniteCat.{u} where
  toCompHaus :=
    { toTop := TopCat.of (ConnectedComponents X), IsCompact := Quotient.compact_space,
      isHausdorff := ConnectedComponents.t2 }
  IsTotallyDisconnected := ConnectedComponents.totally_disconnected_space
#align CompHaus.to_Profinite_obj CompHausCat.toProfiniteObj

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def ProfiniteCat.toCompHausEquivalence (X : CompHausCat.{u}) (Y : ProfiniteCat.{u}) :
    (CompHausCat.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := f.comp ⟨Quotient.mk', continuous_quotient_mk⟩
  invFun g :=
    { toFun := Continuous.connectedComponentsLift g.2,
      continuous_to_fun := Continuous.connected_components_lift_continuous g.2 }
  left_inv f := ContinuousMap.ext <| ConnectedComponents.surjective_coe.forall.2 fun a => rfl
  right_inv f := ContinuousMap.ext fun x => rfl
#align Profinite.to_CompHaus_equivalence ProfiniteCat.toCompHausEquivalence

/-- The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHausCat.toProfinite : CompHausCat ⥤ ProfiniteCat :=
  Adjunction.leftAdjointOfEquiv ProfiniteCat.toCompHausEquivalence fun _ _ _ _ _ => rfl
#align CompHaus.to_Profinite CompHausCat.toProfinite

theorem CompHausCat.to_Profinite_obj' (X : CompHausCat) : ↥(CompHausCat.toProfinite.obj X) = ConnectedComponents X :=
  rfl
#align CompHaus.to_Profinite_obj' CompHausCat.to_Profinite_obj'

/-- Finite types are given the discrete topology. -/
def FintypeCat.discreteTopology (A : FintypeCat) : TopologicalSpace A :=
  ⊥
#align Fintype.discrete_topology FintypeCat.discreteTopology

section DiscreteTopology

attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps]
def FintypeCat.toProfinite : FintypeCat ⥤ ProfiniteCat where
  obj A := ProfiniteCat.of A
  map _ _ f := ⟨f⟩
#align Fintype.to_Profinite FintypeCat.toProfinite

end DiscreteTopology

end ProfiniteCat

namespace ProfiniteCat

-- TODO the following construction of limits could be generalised
-- to allow diagrams in lower universes.
/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`Top.limit_cone`. -/
def limitCone {J : Type u} [SmallCategory J] (F : J ⥤ ProfiniteCat.{u}) : Limits.Cone F where
  x :=
    { toCompHaus := (CompHausCat.limitCone.{u, u} (F ⋙ profiniteToCompHaus)).x,
      IsTotallyDisconnected := by
        change TotallyDisconnectedSpace ↥{ u : ∀ j : J, F.obj j | _ }
        exact Subtype.totally_disconnected_space }
  π := { app := (CompHausCat.limitCone.{u, u} (F ⋙ profiniteToCompHaus)).π.app }
#align Profinite.limit_cone ProfiniteCat.limitCone

/-- The limit cone `Profinite.limit_cone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type u} [SmallCategory J] (F : J ⥤ ProfiniteCat.{u}) : Limits.IsLimit (limitCone F) where
  lift S := (CompHausCat.limitConeIsLimit.{u, u} (F ⋙ profiniteToCompHaus)).lift (profiniteToCompHaus.mapCone S)
  uniq' S m h := (CompHausCat.limitConeIsLimit.{u, u} _).uniq (profiniteToCompHaus.mapCone S) _ h
#align Profinite.limit_cone_is_limit ProfiniteCat.limitConeIsLimit

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def toProfiniteAdjToCompHaus : CompHausCat.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _
#align Profinite.to_Profinite_adj_to_CompHaus ProfiniteCat.toProfiniteAdjToCompHaus

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance toCompHaus.reflective :
    Reflective
      profiniteToCompHaus where toIsRightAdjoint := ⟨CompHausCat.toProfinite, ProfiniteCat.toProfiniteAdjToCompHaus⟩
#align Profinite.to_CompHaus.reflective ProfiniteCat.toCompHaus.reflective

noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _
#align Profinite.to_CompHaus.creates_limits ProfiniteCat.toCompHaus.createsLimits

noncomputable instance toTop.reflective : Reflective ProfiniteCat.toTop :=
  Reflective.comp profiniteToCompHaus compHausToTop
#align Profinite.to_Top.reflective ProfiniteCat.toTop.reflective

noncomputable instance toTop.createsLimits : CreatesLimits ProfiniteCat.toTop :=
  monadicCreatesLimits _
#align Profinite.to_Top.creates_limits ProfiniteCat.toTop.createsLimits

instance has_limits : Limits.HasLimits ProfiniteCat :=
  has_limits_of_has_limits_creates_limits ProfiniteCat.toTop
#align Profinite.has_limits ProfiniteCat.has_limits

instance has_colimits : Limits.HasColimits ProfiniteCat :=
  has_colimits_of_reflective profiniteToCompHaus
#align Profinite.has_colimits ProfiniteCat.has_colimits

noncomputable instance forgetPreservesLimits : Limits.PreservesLimits (forget ProfiniteCat) := by
  apply limits.comp_preserves_limits ProfiniteCat.toTop (forget TopCat)
#align Profinite.forget_preserves_limits ProfiniteCat.forgetPreservesLimits

variable {X Y : ProfiniteCat.{u}} (f : X ⟶ Y)

/-- Any morphism of profinite spaces is a closed map. -/
theorem is_closed_map : IsClosedMap f :=
  CompHausCat.is_closed_map _
#align Profinite.is_closed_map ProfiniteCat.is_closed_map

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
theorem is_iso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHausCat.is_iso_of_bijective (Profinite_to_CompHaus.map f) bij
  is_iso_of_fully_faithful profiniteToCompHaus _
#align Profinite.is_iso_of_bijective ProfiniteCat.is_iso_of_bijective

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := ProfiniteCat.is_iso_of_bijective f bij
  as_iso f
#align Profinite.iso_of_bijective ProfiniteCat.isoOfBijective

instance forget_reflects_isomorphisms : ReflectsIsomorphisms (forget ProfiniteCat) :=
  ⟨by intro A B f hf <;> exact ProfiniteCat.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩
#align Profinite.forget_reflects_isomorphisms ProfiniteCat.forget_reflects_isomorphisms

/-- Construct an isomorphism from a homeomorphism. -/
@[simps Hom inv]
def isoOfHomeo (f : X ≃ₜ Y) : X ≅ Y where
  Hom := ⟨f, f.Continuous⟩
  inv := ⟨f.symm, f.symm.Continuous⟩
  hom_inv_id' := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id' := by
    ext x
    exact f.apply_symm_apply x
#align Profinite.iso_of_homeo ProfiniteCat.isoOfHomeo

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.Hom
  invFun := f.inv
  left_inv x := by
    change (f.hom ≫ f.inv) x = x
    rw [iso.hom_inv_id, coe_id, id.def]
  right_inv x := by
    change (f.inv ≫ f.hom) x = x
    rw [iso.inv_hom_id, coe_id, id.def]
  continuous_to_fun := f.Hom.Continuous
  continuous_inv_fun := f.inv.Continuous
#align Profinite.homeo_of_iso ProfiniteCat.homeoOfIso

/-- The equivalence between isomorphisms in `Profinite` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
#align Profinite.iso_equiv_homeo ProfiniteCat.isoEquivHomeo

theorem epi_iff_surjective {X Y : ProfiniteCat.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (is_compact_range f.continuous).IsClosed
    let U := Cᶜ
    have hU : IsOpen U := is_open_compl_iff.mpr hC
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hU.mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := is_topological_basis_clopen.mem_nhds_iff.mp hUy
    classical letI : TopologicalSpace (ULift.{u} <| Fin 2) := ⊥
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      have H : h = g
      apply_fun fun e => (e y).down  at H
      rw [if_pos hyV] at H
    
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget ProfiniteCat).epi_of_epi_map
    
#align Profinite.epi_iff_surjective ProfiniteCat.epi_iff_surjective

theorem mono_iff_injective {X Y : ProfiniteCat.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro h
    haveI : limits.preserves_limits profiniteToCompHaus := inferInstance
    haveI : mono (Profinite_to_CompHaus.map f) := inferInstance
    rwa [← CompHausCat.mono_iff_injective]
    
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget ProfiniteCat).mono_of_mono_map
    
#align Profinite.mono_iff_injective ProfiniteCat.mono_iff_injective

end ProfiniteCat

