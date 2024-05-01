/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import AlgebraicGeometry.Morphisms.RingHomProperties
import RingTheory.RingHom.FiniteType

#align_import algebraic_geometry.morphisms.finite_type from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-!
# Morphisms of finite type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.

A morphism of schemes is of finite type if it is both locally of finite type and quasi-compact.

We show that these properties are local, and are stable under compositions.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

#print AlgebraicGeometry.LocallyOfFiniteType /-
/-- A morphism of schemes `f : X ⟶ Y` is locally of finite type if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite type.
-/
@[mk_iff]
class LocallyOfFiniteType (f : X ⟶ Y) : Prop where
  finiteType_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ (Opens.map f.1.base).obj U.1),
      (f.appLe e).FiniteType
#align algebraic_geometry.locally_of_finite_type AlgebraicGeometry.LocallyOfFiniteType
-/

#print AlgebraicGeometry.locallyOfFiniteType_eq /-
theorem locallyOfFiniteType_eq : @LocallyOfFiniteType = affineLocally @RingHom.FiniteType :=
  by
  ext X Y f
  rw [locally_of_finite_type_iff, affine_locally_iff_affine_opens_le]
  exact RingHom.finiteType_respectsIso
#align algebraic_geometry.locally_of_finite_type_eq AlgebraicGeometry.locallyOfFiniteType_eq
-/

#print AlgebraicGeometry.locallyOfFiniteTypeOfIsOpenImmersion /-
instance (priority := 900) locallyOfFiniteTypeOfIsOpenImmersion {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersionCat f] : LocallyOfFiniteType f :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.affineLocally_of_isOpenImmersion f
#align algebraic_geometry.locally_of_finite_type_of_is_open_immersion AlgebraicGeometry.locallyOfFiniteTypeOfIsOpenImmersion
-/

#print AlgebraicGeometry.locallyOfFiniteType_isStableUnderComposition /-
theorem locallyOfFiniteType_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @LocallyOfFiniteType :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.affineLocally_isStableUnderComposition
#align algebraic_geometry.locally_of_finite_type_stable_under_composition AlgebraicGeometry.locallyOfFiniteType_isStableUnderComposition
-/

#print AlgebraicGeometry.locallyOfFiniteTypeComp /-
instance locallyOfFiniteTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType f] [hg : LocallyOfFiniteType g] : LocallyOfFiniteType (f ≫ g) :=
  locallyOfFiniteType_isStableUnderComposition f g hf hg
#align algebraic_geometry.locally_of_finite_type_comp AlgebraicGeometry.locallyOfFiniteTypeComp
-/

#print AlgebraicGeometry.locallyOfFiniteTypeOfComp /-
theorem locallyOfFiniteTypeOfComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f :=
  by
  revert hf
  rw [locally_of_finite_type_eq]
  apply ring_hom.finite_type_is_local.affine_locally_of_comp
  introv H
  exact RingHom.FiniteType.of_comp_finiteType H
#align algebraic_geometry.locally_of_finite_type_of_comp AlgebraicGeometry.locallyOfFiniteTypeOfComp
-/

#print AlgebraicGeometry.LocallyOfFiniteType.affine_openCover_iff /-
theorem LocallyOfFiniteType.affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i)) [∀ i j, IsAffine ((𝒰' i).obj j)] :
    LocallyOfFiniteType f ↔ ∀ i j, (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op).FiniteType :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.affine_openCover_iff f 𝒰 𝒰'
#align algebraic_geometry.locally_of_finite_type.affine_open_cover_iff AlgebraicGeometry.LocallyOfFiniteType.affine_openCover_iff
-/

#print AlgebraicGeometry.LocallyOfFiniteType.source_openCover_iff /-
theorem LocallyOfFiniteType.source_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} X) : LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (𝒰.map i ≫ f) :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.source_openCover_iff f 𝒰
#align algebraic_geometry.locally_of_finite_type.source_open_cover_iff AlgebraicGeometry.LocallyOfFiniteType.source_openCover_iff
-/

#print AlgebraicGeometry.LocallyOfFiniteType.openCover_iff /-
theorem LocallyOfFiniteType.openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.OpenCover.{u} Y) :
    LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  locallyOfFiniteType_eq.symm ▸ RingHom.finiteType_is_local.is_local_affineLocally.openCover_iff f 𝒰
#align algebraic_geometry.locally_of_finite_type.open_cover_iff AlgebraicGeometry.LocallyOfFiniteType.openCover_iff
-/

#print AlgebraicGeometry.locallyOfFiniteType_respectsIso /-
theorem locallyOfFiniteType_respectsIso : MorphismProperty.RespectsIso @LocallyOfFiniteType :=
  locallyOfFiniteType_eq.symm ▸
    targetAffineLocally_respectsIso (sourceAffineLocally_respectsIso RingHom.finiteType_respectsIso)
#align algebraic_geometry.locally_of_finite_type_respects_iso AlgebraicGeometry.locallyOfFiniteType_respectsIso
-/

end AlgebraicGeometry

