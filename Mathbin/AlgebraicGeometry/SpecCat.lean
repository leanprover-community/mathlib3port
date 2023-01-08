/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer

! This file was ported from Lean 3 source module algebraic_geometry.Spec
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.LocallyRingedSpace
import Mathbin.AlgebraicGeometry.StructureSheaf
import Mathbin.Logic.Equiv.TransferInstance
import Mathbin.RingTheory.Localization.LocalizationLocalization
import Mathbin.Topology.Sheaves.SheafCondition.Sites
import Mathbin.Topology.Sheaves.Functors
import Mathbin.Algebra.Module.LocalizedModule

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.to_Top`, valued in the category of topological spaces,
2. `Spec.to_SheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.to_LocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.to_PresheafedSpace` as a composition of `Spec.to_SheafedSpace` with
a forgetful functor.

## Related results

The adjunction `Γ ⊣ Spec` is constructed in `algebraic_geometry/Gamma_Spec_adjunction.lean`.

-/


noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open SpecCat (structureSheaf)

/-- The spectrum of a commutative ring, as a topological space.
-/
def SpecCat.topObj (R : CommRingCat) : TopCat :=
  TopCat.of (PrimeSpectrum R)
#align algebraic_geometry.Spec.Top_obj AlgebraicGeometry.SpecCat.topObj

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def SpecCat.topMap {R S : CommRingCat} (f : R ⟶ S) : SpecCat.topObj S ⟶ SpecCat.topObj R :=
  PrimeSpectrum.comap f
#align algebraic_geometry.Spec.Top_map AlgebraicGeometry.SpecCat.topMap

@[simp]
theorem SpecCat.Top_map_id (R : CommRingCat) : SpecCat.topMap (𝟙 R) = 𝟙 (SpecCat.topObj R) :=
  PrimeSpectrum.comap_id
#align algebraic_geometry.Spec.Top_map_id AlgebraicGeometry.SpecCat.Top_map_id

theorem SpecCat.Top_map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    SpecCat.topMap (f ≫ g) = SpecCat.topMap g ≫ SpecCat.topMap f :=
  PrimeSpectrum.comap_comp _ _
#align algebraic_geometry.Spec.Top_map_comp AlgebraicGeometry.SpecCat.Top_map_comp

/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps]
def SpecCat.toTop : CommRingCatᵒᵖ ⥤ TopCat
    where
  obj R := SpecCat.topObj (unop R)
  map R S f := SpecCat.topMap f.unop
  map_id' R := by rw [unop_id, Spec.Top_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec.Top_map_comp]
#align algebraic_geometry.Spec.to_Top AlgebraicGeometry.SpecCat.toTop

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def SpecCat.sheafedSpaceObj (R : CommRingCat) : SheafedSpaceCat CommRingCat
    where
  carrier := SpecCat.topObj R
  Presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2
#align algebraic_geometry.Spec.SheafedSpace_obj AlgebraicGeometry.SpecCat.sheafedSpaceObj

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps]
def SpecCat.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    SpecCat.sheafedSpaceObj S ⟶ SpecCat.sheafedSpaceObj R
    where
  base := SpecCat.topMap f
  c :=
    { app := fun U =>
        comap f (unop U) ((TopologicalSpace.Opens.map (SpecCat.topMap f)).obj (unop U)) fun p => id
      naturality' := fun U V i => RingHom.ext fun s => Subtype.eq <| funext fun p => rfl }
#align algebraic_geometry.Spec.SheafedSpace_map AlgebraicGeometry.SpecCat.sheafedSpaceMap

@[simp]
theorem SpecCat.SheafedSpace_map_id {R : CommRingCat} :
    SpecCat.sheafedSpaceMap (𝟙 R) = 𝟙 (SpecCat.sheafedSpaceObj R) :=
  PresheafedSpaceCat.ext _ _ (SpecCat.Top_map_id R) <|
    NatTrans.ext _ _ <|
      funext fun U => by
        dsimp
        erw [PresheafedSpace.id_c_app, comap_id]; swap
        · rw [Spec.Top_map_id, TopologicalSpace.Opens.map_id_obj_unop]
        simpa [eq_to_hom_map]
#align algebraic_geometry.Spec.SheafedSpace_map_id AlgebraicGeometry.SpecCat.SheafedSpace_map_id

theorem SpecCat.SheafedSpace_map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    SpecCat.sheafedSpaceMap (f ≫ g) = SpecCat.sheafedSpaceMap g ≫ SpecCat.sheafedSpaceMap f :=
  PresheafedSpaceCat.ext _ _ (SpecCat.Top_map_comp f g) <|
    NatTrans.ext _ _ <|
      funext fun U => by
        dsimp
        rw [CategoryTheory.Functor.map_id]
        rw [category.comp_id]
        erw [comap_comp f g]
        rfl
#align algebraic_geometry.Spec.SheafedSpace_map_comp AlgebraicGeometry.SpecCat.SheafedSpace_map_comp

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def SpecCat.toSheafedSpace : CommRingCatᵒᵖ ⥤ SheafedSpaceCat CommRingCat
    where
  obj R := SpecCat.sheafedSpaceObj (unop R)
  map R S f := SpecCat.sheafedSpaceMap f.unop
  map_id' R := by rw [unop_id, Spec.SheafedSpace_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec.SheafedSpace_map_comp]
#align algebraic_geometry.Spec.to_SheafedSpace AlgebraicGeometry.SpecCat.toSheafedSpace

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def SpecCat.toPresheafedSpace : CommRingCatᵒᵖ ⥤ PresheafedSpaceCat.{u} CommRingCat.{u} :=
  Spec.to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace
#align algebraic_geometry.Spec.to_PresheafedSpace AlgebraicGeometry.SpecCat.toPresheafedSpace

@[simp]
theorem SpecCat.to_PresheafedSpace_obj (R : CommRingCatᵒᵖ) :
    SpecCat.toPresheafedSpace.obj R = (SpecCat.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl
#align
  algebraic_geometry.Spec.to_PresheafedSpace_obj AlgebraicGeometry.SpecCat.to_PresheafedSpace_obj

theorem SpecCat.to_PresheafedSpace_obj_op (R : CommRingCat) :
    SpecCat.toPresheafedSpace.obj (op R) = (SpecCat.sheafedSpaceObj R).toPresheafedSpace :=
  rfl
#align
  algebraic_geometry.Spec.to_PresheafedSpace_obj_op AlgebraicGeometry.SpecCat.to_PresheafedSpace_obj_op

@[simp]
theorem SpecCat.to_PresheafedSpace_map (R S : CommRingCatᵒᵖ) (f : R ⟶ S) :
    SpecCat.toPresheafedSpace.map f = SpecCat.sheafedSpaceMap f.unop :=
  rfl
#align
  algebraic_geometry.Spec.to_PresheafedSpace_map AlgebraicGeometry.SpecCat.to_PresheafedSpace_map

theorem SpecCat.to_PresheafedSpace_map_op (R S : CommRingCat) (f : R ⟶ S) :
    SpecCat.toPresheafedSpace.map f.op = SpecCat.sheafedSpaceMap f :=
  rfl
#align
  algebraic_geometry.Spec.to_PresheafedSpace_map_op AlgebraicGeometry.SpecCat.to_PresheafedSpace_map_op

theorem SpecCat.basic_open_hom_ext {X : RingedSpaceCat} {R : CommRingCat}
    {α β : X ⟶ SpecCat.sheafedSpaceObj R} (w : α.base = β.base)
    (h :
      ∀ r : R,
        let U := PrimeSpectrum.basicOpen r
        (toOpen R U ≫ α.c.app (op U)) ≫ X.Presheaf.map (eqToHom (by rw [w])) =
          toOpen R U ≫ β.c.app (op U)) :
    α = β := by
  ext1
  · apply
      ((TopCat.Sheaf.pushforward β.base).obj X.sheaf).hom_ext _ PrimeSpectrum.is_basis_basic_opens
    intro r
    apply (structure_sheaf.to_basic_open_epi R r).1
    simpa using h r
  exact w
#align algebraic_geometry.Spec.basic_open_hom_ext AlgebraicGeometry.SpecCat.basic_open_hom_ext

/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps]
def SpecCat.locallyRingedSpaceObj (R : CommRingCat) : LocallyRingedSpaceCat :=
  { SpecCat.sheafedSpaceObj R with
    LocalRing := fun x =>
      @RingEquiv.local_ring _ (show LocalRing (Localization.AtPrime _) by infer_instance) _
        (iso.CommRing_iso_to_ring_equiv <| stalkIso R x).symm }
#align
  algebraic_geometry.Spec.LocallyRingedSpace_obj AlgebraicGeometry.SpecCat.locallyRingedSpaceObj

@[elementwise]
theorem stalk_map_to_stalk {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f p) ≫
        PresheafedSpaceCat.stalkMap (SpecCat.sheafedSpaceMap f) p =
      f ≫ toStalk S p :=
  by
  erw [← to_open_germ S ⊤ ⟨p, trivial⟩, ← to_open_germ R ⊤ ⟨PrimeSpectrum.comap f p, trivial⟩,
    category.assoc, PresheafedSpace.stalk_map_germ (Spec.SheafedSpace_map f) ⊤ ⟨p, trivial⟩,
    Spec.SheafedSpace_map_c_app, to_open_comp_comap_assoc]
  rfl
#align algebraic_geometry.stalk_map_to_stalk AlgebraicGeometry.stalk_map_to_stalk

/-- Under the isomorphisms `stalk_iso`, the map `stalk_map (Spec.SheafedSpace_map f) p` corresponds
to the induced local ring homomorphism `localization.local_ring_hom`.
-/
@[elementwise]
theorem local_ring_hom_comp_stalk_iso {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (stalkIso R (PrimeSpectrum.comap f p)).Hom ≫
        @CategoryStruct.comp _ _
          (CommRingCat.of (Localization.AtPrime (PrimeSpectrum.comap f p).asIdeal))
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) _
          (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl)
          (stalkIso S p).inv =
      PresheafedSpaceCat.stalkMap (SpecCat.sheafedSpaceMap f) p :=
  (stalkIso R (PrimeSpectrum.comap f p)).eq_inv_comp.mp <|
    (stalkIso S p).comp_inv_eq.mpr <|
      (Localization.local_ring_hom_unique _ _ _ _) fun x => by
        rw [stalk_iso_hom, stalk_iso_inv, comp_apply, comp_apply, localization_to_stalk_of,
          stalk_map_to_stalk_apply, stalk_to_fiber_ring_hom_to_stalk]
#align
  algebraic_geometry.local_ring_hom_comp_stalk_iso AlgebraicGeometry.local_ring_hom_comp_stalk_iso

/--
The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps]
def SpecCat.locallyRingedSpaceMap {R S : CommRingCat} (f : R ⟶ S) :
    SpecCat.locallyRingedSpaceObj S ⟶ SpecCat.locallyRingedSpaceObj R :=
  (LocallyRingedSpaceCat.Hom.mk (SpecCat.sheafedSpaceMap f)) fun p =>
    IsLocalRingHom.mk fun a ha =>
      by
      -- Here, we are showing that the map on prime spectra induced by `f` is really a morphism of
      -- *locally* ringed spaces, i.e. that the induced map on the stalks is a local ring homomorphism.
      rw [← local_ring_hom_comp_stalk_iso_apply] at ha
      replace ha := (stalk_iso S p).Hom.is_unit_map ha
      rw [iso.inv_hom_id_apply] at ha
      replace ha := IsLocalRingHom.map_nonunit _ ha
      convert RingHom.isUnit_map (stalk_iso R (PrimeSpectrum.comap f p)).inv ha
      rw [iso.hom_inv_id_apply]
#align
  algebraic_geometry.Spec.LocallyRingedSpace_map AlgebraicGeometry.SpecCat.locallyRingedSpaceMap

@[simp]
theorem SpecCat.LocallyRingedSpace_map_id (R : CommRingCat) :
    SpecCat.locallyRingedSpaceMap (𝟙 R) = 𝟙 (SpecCat.locallyRingedSpaceObj R) :=
  LocallyRingedSpaceCat.Hom.ext _ _ <|
    by
    rw [Spec.LocallyRingedSpace_map_val, Spec.SheafedSpace_map_id]
    rfl
#align
  algebraic_geometry.Spec.LocallyRingedSpace_map_id AlgebraicGeometry.SpecCat.LocallyRingedSpace_map_id

theorem SpecCat.LocallyRingedSpace_map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    SpecCat.locallyRingedSpaceMap (f ≫ g) =
      SpecCat.locallyRingedSpaceMap g ≫ SpecCat.locallyRingedSpaceMap f :=
  LocallyRingedSpaceCat.Hom.ext _ _ <|
    by
    rw [Spec.LocallyRingedSpace_map_val, Spec.SheafedSpace_map_comp]
    rfl
#align
  algebraic_geometry.Spec.LocallyRingedSpace_map_comp AlgebraicGeometry.SpecCat.LocallyRingedSpace_map_comp

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def SpecCat.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace
    where
  obj R := SpecCat.locallyRingedSpaceObj (unop R)
  map R S f := SpecCat.locallyRingedSpaceMap f.unop
  map_id' R := by rw [unop_id, Spec.LocallyRingedSpace_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec.LocallyRingedSpace_map_comp]
#align algebraic_geometry.Spec.to_LocallyRingedSpace AlgebraicGeometry.SpecCat.toLocallyRingedSpace

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpaceCat

/-- The counit morphism `R ⟶ Γ(Spec R)` given by `algebraic_geometry.structure_sheaf.to_open`.  -/
@[simps (config := { rhsMd := Tactic.Transparency.semireducible })]
def toSpecΓ (R : CommRingCat) : R ⟶ Γ.obj (op (SpecCat.toLocallyRingedSpace.obj (op R))) :=
  StructureSheaf.toOpen R ⊤
#align algebraic_geometry.to_Spec_Γ AlgebraicGeometry.toSpecΓ

instance is_iso_to_Spec_Γ (R : CommRingCat) : IsIso (toSpecΓ R) :=
  by
  cases R
  apply structure_sheaf.is_iso_to_global
#align algebraic_geometry.is_iso_to_Spec_Γ AlgebraicGeometry.is_iso_to_Spec_Γ

@[reassoc.1]
theorem Spec_Γ_naturality {R S : CommRingCat} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (SpecCat.toLocallyRingedSpace.map f.op).op :=
  by
  ext
  symm
  apply Localization.local_ring_hom_to_map
#align algebraic_geometry.Spec_Γ_naturality AlgebraicGeometry.Spec_Γ_naturality

/-- The counit (`Spec_Γ_identity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps hom_app inv_app]
def specΓIdentity : SpecCat.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  iso.symm <| NatIso.ofComponents (fun R => asIso (toSpecΓ R) : _) fun _ _ => Spec_Γ_naturality
#align algebraic_geometry.Spec_Γ_identity AlgebraicGeometry.specΓIdentity

end SpecΓ

/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
theorem Spec_map_localization_is_iso (R : CommRingCat) (M : Submonoid R)
    (x : PrimeSpectrum (Localization M)) :
    IsIso
      (PresheafedSpaceCat.stalkMap
        (SpecCat.toPresheafedSpace.map (CommRingCat.ofHom (algebraMap R (Localization M))).op) x) :=
  by
  erw [← local_ring_hom_comp_stalk_iso]
  apply (config := { instances := false }) is_iso.comp_is_iso
  infer_instance
  apply (config := { instances := false }) is_iso.comp_is_iso
  -- I do not know why this is defeq to the goal, but I'm happy to accept that it is.
  exact
    show
      is_iso
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M
                x.as_ideal).toRingEquiv.toCommRingIso.Hom
      by infer_instance
  infer_instance
#align
  algebraic_geometry.Spec_map_localization_is_iso AlgebraicGeometry.Spec_map_localization_is_iso

namespace StructureSheaf

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (p : PrimeSpectrum R)

/-- For an algebra `f : R →+* S`, this is the ring homomorphism `S →+* (f∗ 𝒪ₛ)ₚ` for a `p : Spec R`.
This is shown to be the localization at `p` in `is_localized_module_to_pushforward_stalk_alg_hom`.
-/
def toPushforwardStalk : S ⟶ (SpecCat.topMap f _* (structureSheaf S).1).stalk p :=
  StructureSheaf.toOpen S ⊤ ≫
    @TopCat.Presheaf.germ _ _ _ _ (SpecCat.topMap f _* (structureSheaf S).1) ⊤ ⟨p, trivial⟩
#align
  algebraic_geometry.structure_sheaf.to_pushforward_stalk AlgebraicGeometry.StructureSheaf.toPushforwardStalk

@[reassoc.1]
theorem to_pushforward_stalk_comp :
    f ≫ StructureSheaf.toPushforwardStalk f p =
      StructureSheaf.toStalk R p ≫
        (TopCat.Presheaf.stalkFunctor _ _).map (SpecCat.sheafedSpaceMap f).c :=
  by
  rw [structure_sheaf.to_stalk]
  erw [category.assoc]
  rw [TopCat.Presheaf.stalk_functor_map_germ]
  exact Spec_Γ_naturality_assoc f _
#align
  algebraic_geometry.structure_sheaf.to_pushforward_stalk_comp AlgebraicGeometry.StructureSheaf.to_pushforward_stalk_comp

instance : Algebra R ((SpecCat.topMap f _* (structureSheaf S).1).stalk p) :=
  (f ≫ StructureSheaf.toPushforwardStalk f p).toAlgebra

theorem algebra_map_pushforward_stalk :
    algebraMap R ((SpecCat.topMap f _* (structureSheaf S).1).stalk p) =
      f ≫ StructureSheaf.toPushforwardStalk f p :=
  rfl
#align
  algebraic_geometry.structure_sheaf.algebra_map_pushforward_stalk AlgebraicGeometry.StructureSheaf.algebra_map_pushforward_stalk

variable (R S) [Algebra R S]

/--
This is the `alg_hom` version of `to_pushforward_stalk`, which is the map `S ⟶ (f∗ 𝒪ₛ)ₚ` for some
algebra `R ⟶ S` and some `p : Spec R`.
-/
@[simps]
def toPushforwardStalkAlgHom :
    S →ₐ[R] (SpecCat.topMap (algebraMap R S) _* (structureSheaf S).1).stalk p :=
  { StructureSheaf.toPushforwardStalk (algebraMap R S) p with commutes' := fun _ => rfl }
#align
  algebraic_geometry.structure_sheaf.to_pushforward_stalk_alg_hom AlgebraicGeometry.StructureSheaf.toPushforwardStalkAlgHom

theorem is_localized_module_to_pushforward_stalk_alg_hom_aux (y) :
    ∃ x : S × p.asIdeal.primeCompl, x.2 • y = toPushforwardStalkAlgHom R S p x.1 :=
  by
  obtain ⟨U, hp, s, e⟩ := TopCat.Presheaf.germ_exist _ _ y
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.is_topological_basis_basic_opens.exists_subset_of_mem_open (show p ∈ U.1 from hp)
      U.2
  change PrimeSpectrum.basicOpen r ≤ U at hrU
  replace e :=
    ((Spec.Top_map (algebraMap R S) _* (structure_sheaf S).1).germ_res_apply (hom_of_le hrU)
          ⟨p, hpr⟩ _).trans
      e
  set s' := (Spec.Top_map (algebraMap R S) _* (structure_sheaf S).1).map (hom_of_le hrU).op s with h
  rw [← h] at e
  clear_value s'; clear! U
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hsn⟩ :=
    @IsLocalization.surj _ _ _ _ _ _
      (structure_sheaf.is_localization.to_basic_open S <| algebraMap R S r) s'
  refine' ⟨⟨s, ⟨r, hpr⟩ ^ n⟩, _⟩
  rw [Submonoid.smul_def, Algebra.smul_def, algebra_map_pushforward_stalk, to_pushforward_stalk,
    comp_apply, comp_apply]
  iterate 2
    erw [←
      (Spec.Top_map (algebraMap R S) _* (structure_sheaf S).1).germ_res_apply (hom_of_le le_top)
        ⟨p, hpr⟩]
  rw [← e, ← map_mul, mul_comm]
  dsimp only [Subtype.coe_mk] at hsn
  rw [← map_pow (algebraMap R S)] at hsn
  congr 1
#align
  algebraic_geometry.structure_sheaf.is_localized_module_to_pushforward_stalk_alg_hom_aux AlgebraicGeometry.StructureSheaf.is_localized_module_to_pushforward_stalk_alg_hom_aux

instance isLocalizedModuleToPushforwardStalkAlgHom :
    IsLocalizedModule p.asIdeal.primeCompl (toPushforwardStalkAlgHom R S p).toLinearMap :=
  by
  apply IsLocalizedModule.mkOfAlgebra
  · intro x hx
    rw [algebra_map_pushforward_stalk, to_pushforward_stalk_comp, comp_apply]
    exact (IsLocalization.map_units ((structure_sheaf R).Presheaf.stalk p) ⟨x, hx⟩).map _
  · apply is_localized_module_to_pushforward_stalk_alg_hom_aux
  · intro x hx
    rw [to_pushforward_stalk_alg_hom_apply, RingHom.toFun_eq_coe, ←
      (to_pushforward_stalk (algebraMap R S) p).map_zero, to_pushforward_stalk, comp_apply,
      comp_apply, map_zero] at hx
    obtain ⟨U, hpU, i₁, i₂, e⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ hx
    obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
      PrimeSpectrum.is_topological_basis_basic_opens.exists_subset_of_mem_open
        (show p ∈ U.1 from hpU) U.2
    change PrimeSpectrum.basicOpen r ≤ U at hrU
    apply_fun (Spec.Top_map (algebraMap R S) _* (structure_sheaf S).1).map (hom_of_le hrU).op  at e
    simp only [TopCat.Presheaf.pushforward_obj_map, functor.op_map, map_zero, ← comp_apply,
      to_open_res] at e
    have : to_open S (PrimeSpectrum.basicOpen <| algebraMap R S r) x = 0 :=
      by
      refine' Eq.trans _ e
      rfl
    have :=
      (@IsLocalization.mk'_one _ _ _ _ _ _
            (structure_sheaf.is_localization.to_basic_open S <| algebraMap R S r) x).trans
        this
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp this
    refine' ⟨⟨r, hpr⟩ ^ n, _⟩
    rw [Submonoid.smul_def, Algebra.smul_def, [anonymous], Subtype.coe_mk, mul_comm, map_pow]
    exact e
#align
  algebraic_geometry.structure_sheaf.is_localized_module_to_pushforward_stalk_alg_hom AlgebraicGeometry.StructureSheaf.isLocalizedModuleToPushforwardStalkAlgHom

end StructureSheaf

end AlgebraicGeometry

