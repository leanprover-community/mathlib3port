/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathbin.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathbin.RingTheory.RingHom.FiniteType

/-!
# Morphisms of finite type

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : SchemeCat.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteTypeOfAffineSubset :
    ∀ (U : Y.AffineOpens) (V : X.AffineOpens) (e : V.1 ≤ (Opens.map f.1.base).obj U.1), (f.appLe e).FiniteType

theorem locally_of_finite_type_eq : @LocallyOfFiniteType = AffineLocally @RingHom.FiniteType := by
  ext X Y f
  rw [locally_of_finite_type_iff, affine_locally_iff_affine_opens_le]
  exact RingHom.finiteTypeRespectsIso

instance (priority := 900) locallyOfFiniteTypeOfIsOpenImmersion {X Y : SchemeCat} (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  locally_of_finite_type_eq.symm ▸ RingHom.finiteTypeIsLocal.affineLocallyOfIsOpenImmersion f

theorem locally_of_finite_type_stable_under_composition :
    MorphismProperty.StableUnderComposition @LocallyOfFiniteType :=
  locally_of_finite_type_eq.symm ▸ RingHom.finiteTypeIsLocal.affine_locally_stable_under_composition

instance locallyOfFiniteTypeComp {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : LocallyOfFiniteType f]
    [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  locally_of_finite_type_stable_under_composition f g hf hg

theorem locallyOfFiniteTypeOfComp {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : LocallyOfFiniteType (f ≫ g)] :
    LocallyOfFiniteType f := by
  revert hf
  rw [locally_of_finite_type_eq]
  apply ring_hom.finite_type_is_local.affine_locally_of_comp
  introv H
  exact RingHom.FiniteType.ofCompFiniteType H

theorem LocallyOfFiniteType.affine_open_cover_iff {X Y : SchemeCat.{u}} (f : X ⟶ Y) (𝒰 : SchemeCat.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (𝒰' : ∀ i, SchemeCat.OpenCover.{u} ((𝒰.pullbackCover f).obj i))
    [∀ i j, IsAffine ((𝒰' i).obj j)] :
    LocallyOfFiniteType f ↔ ∀ i j, (SchemeCat.Γ.map ((𝒰' i).map j ≫ pullback.snd).op).FiniteType :=
  locally_of_finite_type_eq.symm ▸ RingHom.finiteTypeIsLocal.affine_open_cover_iff f 𝒰 𝒰'

theorem LocallyOfFiniteType.source_open_cover_iff {X Y : SchemeCat.{u}} (f : X ⟶ Y) (𝒰 : SchemeCat.OpenCover.{u} X) :
    LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (𝒰.map i ≫ f) :=
  locally_of_finite_type_eq.symm ▸ RingHom.finiteTypeIsLocal.source_open_cover_iff f 𝒰

theorem LocallyOfFiniteType.open_cover_iff {X Y : SchemeCat.{u}} (f : X ⟶ Y) (𝒰 : SchemeCat.OpenCover.{u} Y) :
    LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  locally_of_finite_type_eq.symm ▸ RingHom.finiteTypeIsLocal.isLocalAffineLocally.open_cover_iff f 𝒰

theorem locally_of_finite_type_respects_iso : MorphismProperty.RespectsIso @LocallyOfFiniteType :=
  locally_of_finite_type_eq.symm ▸
    target_affine_locally_respects_iso (source_affine_locally_respects_iso RingHom.finiteTypeRespectsIso)

end AlgebraicGeometry

