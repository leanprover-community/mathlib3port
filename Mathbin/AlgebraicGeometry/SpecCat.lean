/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathbin.AlgebraicGeometry.LocallyRingedSpace
import Mathbin.AlgebraicGeometry.StructureSheaf
import Mathbin.Logic.Equiv.TransferInstance
import Mathbin.RingTheory.Localization.LocalizationLocalization
import Mathbin.Topology.Sheaves.SheafCondition.Sites
import Mathbin.Topology.Sheaves.Functors

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

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def SpecCat.topMap {R S : CommRingCat} (f : R ⟶ S) : SpecCat.topObj S ⟶ SpecCat.topObj R :=
  PrimeSpectrum.comap f

@[simp]
theorem SpecCat.Top_map_id (R : CommRingCat) : SpecCat.topMap (𝟙 R) = 𝟙 (SpecCat.topObj R) :=
  PrimeSpectrum.comap_id

theorem SpecCat.Top_map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    SpecCat.topMap (f ≫ g) = SpecCat.topMap g ≫ SpecCat.topMap f :=
  PrimeSpectrum.comap_comp _ _

/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps]
def SpecCat.toTop : CommRingCatᵒᵖ ⥤ TopCat where
  obj R := SpecCat.topObj (unop R)
  map R S f := SpecCat.topMap f.unop
  map_id' R := by rw [unop_id, Spec.Top_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec.Top_map_comp]

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def SpecCat.sheafedSpaceObj (R : CommRingCat) : SheafedSpaceCat CommRingCat where
  Carrier := SpecCat.topObj R
  Presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps]
def SpecCat.sheafedSpaceMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    SpecCat.sheafedSpaceObj S ⟶ SpecCat.sheafedSpaceObj R where
  base := SpecCat.topMap f
  c :=
    { app := fun U => comap f (unop U) ((TopologicalSpace.Opens.map (SpecCat.topMap f)).obj (unop U)) fun p => id,
      naturality' := fun U V i => RingHom.ext fun s => Subtype.eq <| funext fun p => rfl }

@[simp]
theorem SpecCat.SheafedSpace_map_id {R : CommRingCat} : SpecCat.sheafedSpaceMap (𝟙 R) = 𝟙 (SpecCat.sheafedSpaceObj R) :=
  PresheafedSpaceCat.ext _ _ (SpecCat.Top_map_id R) <|
    NatTrans.ext _ _ <|
      funext fun U => by
        dsimp
        erw [PresheafedSpace.id_c_app, comap_id]
        swap
        · rw [Spec.Top_map_id, TopologicalSpace.Opens.map_id_obj_unop]
          
        simpa [eq_to_hom_map]

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

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def SpecCat.toSheafedSpace : CommRingCatᵒᵖ ⥤ SheafedSpaceCat CommRingCat where
  obj R := SpecCat.sheafedSpaceObj (unop R)
  map R S f := SpecCat.sheafedSpaceMap f.unop
  map_id' R := by rw [unop_id, Spec.SheafedSpace_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec.SheafedSpace_map_comp]

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def SpecCat.toPresheafedSpace : CommRingCatᵒᵖ ⥤ PresheafedSpaceCat.{u} CommRingCat.{u} :=
  Spec.to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace

@[simp]
theorem SpecCat.to_PresheafedSpace_obj (R : CommRingCatᵒᵖ) :
    SpecCat.toPresheafedSpace.obj R = (SpecCat.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl

theorem SpecCat.to_PresheafedSpace_obj_op (R : CommRingCat) :
    SpecCat.toPresheafedSpace.obj (op R) = (SpecCat.sheafedSpaceObj R).toPresheafedSpace :=
  rfl

@[simp]
theorem SpecCat.to_PresheafedSpace_map (R S : CommRingCatᵒᵖ) (f : R ⟶ S) :
    SpecCat.toPresheafedSpace.map f = SpecCat.sheafedSpaceMap f.unop :=
  rfl

theorem SpecCat.to_PresheafedSpace_map_op (R S : CommRingCat) (f : R ⟶ S) :
    SpecCat.toPresheafedSpace.map f.op = SpecCat.sheafedSpaceMap f :=
  rfl

theorem SpecCat.basic_open_hom_ext {X : RingedSpaceCat} {R : CommRingCat} {α β : X ⟶ SpecCat.sheafedSpaceObj R}
    (w : α.base = β.base)
    (h :
      ∀ r : R,
        let U := PrimeSpectrum.basicOpen r
        (toOpen R U ≫ α.c.app (op U)) ≫ X.Presheaf.map (eqToHom (by rw [w])) = toOpen R U ≫ β.c.app (op U)) :
    α = β := by
  ext1
  · apply ((TopCat.Sheaf.pushforward β.base).obj X.sheaf).hom_ext _ PrimeSpectrum.is_basis_basic_opens
    intro r
    apply (structure_sheaf.to_basic_open_epi R r).1
    simpa using h r
    
  exact w

/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps]
def SpecCat.locallyRingedSpaceObj (R : CommRingCat) : LocallyRingedSpaceCat :=
  { SpecCat.sheafedSpaceObj R with
    LocalRing := fun x =>
      @RingEquiv.localRing _ (show LocalRing (Localization.AtPrime _) by infer_instance) _
        (iso.CommRing_iso_to_ring_equiv <| stalkIso R x).symm }

@[elementwise]
theorem stalk_map_to_stalk {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f p) ≫ PresheafedSpaceCat.stalkMap (SpecCat.sheafedSpaceMap f) p = f ≫ toStalk S p :=
  by
  erw [← to_open_germ S ⊤ ⟨p, trivial⟩, ← to_open_germ R ⊤ ⟨PrimeSpectrum.comap f p, trivial⟩, category.assoc,
    PresheafedSpace.stalk_map_germ (Spec.SheafedSpace_map f) ⊤ ⟨p, trivial⟩, Spec.SheafedSpace_map_c_app,
    to_open_comp_comap_assoc]
  rfl

/-- Under the isomorphisms `stalk_iso`, the map `stalk_map (Spec.SheafedSpace_map f) p` corresponds
to the induced local ring homomorphism `localization.local_ring_hom`.
-/
@[elementwise]
theorem local_ring_hom_comp_stalk_iso {R S : CommRingCat} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (stalkIso R (PrimeSpectrum.comap f p)).Hom ≫
        @CategoryStruct.comp _ _ (CommRingCat.of (Localization.AtPrime (PrimeSpectrum.comap f p).asIdeal))
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) _
          (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl) (stalkIso S p).inv =
      PresheafedSpaceCat.stalkMap (SpecCat.sheafedSpaceMap f) p :=
  (stalkIso R (PrimeSpectrum.comap f p)).eq_inv_comp.mp <|
    (stalkIso S p).comp_inv_eq.mpr <|
      (Localization.local_ring_hom_unique _ _ _ _) fun x => by
        rw [stalk_iso_hom, stalk_iso_inv, comp_apply, comp_apply, localization_to_stalk_of, stalk_map_to_stalk_apply,
          stalk_to_fiber_ring_hom_to_stalk]

/-- The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps]
def SpecCat.locallyRingedSpaceMap {R S : CommRingCat} (f : R ⟶ S) :
    SpecCat.locallyRingedSpaceObj S ⟶ SpecCat.locallyRingedSpaceObj R :=
  (LocallyRingedSpaceCat.Hom.mk (SpecCat.sheafedSpaceMap f)) fun p =>
    IsLocalRingHom.mk fun a ha => by
      -- Here, we are showing that the map on prime spectra induced by `f` is really a morphism of
      -- *locally* ringed spaces, i.e. that the induced map on the stalks is a local ring homomorphism.
      rw [← local_ring_hom_comp_stalk_iso_apply] at ha
      replace ha := (stalk_iso S p).Hom.is_unit_map ha
      rw [iso.inv_hom_id_apply] at ha
      replace ha := IsLocalRingHom.map_nonunit _ ha
      convert RingHom.is_unit_map (stalk_iso R (PrimeSpectrum.comap f p)).inv ha
      rw [iso.hom_inv_id_apply]

@[simp]
theorem SpecCat.LocallyRingedSpace_map_id (R : CommRingCat) :
    SpecCat.locallyRingedSpaceMap (𝟙 R) = 𝟙 (SpecCat.locallyRingedSpaceObj R) :=
  LocallyRingedSpaceCat.Hom.ext _ _ <| by
    rw [Spec.LocallyRingedSpace_map_val, Spec.SheafedSpace_map_id]
    rfl

theorem SpecCat.LocallyRingedSpace_map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    SpecCat.locallyRingedSpaceMap (f ≫ g) = SpecCat.locallyRingedSpaceMap g ≫ SpecCat.locallyRingedSpaceMap f :=
  LocallyRingedSpaceCat.Hom.ext _ _ <| by
    rw [Spec.LocallyRingedSpace_map_val, Spec.SheafedSpace_map_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def SpecCat.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace where
  obj R := SpecCat.locallyRingedSpaceObj (unop R)
  map R S f := SpecCat.locallyRingedSpaceMap f.unop
  map_id' R := by rw [unop_id, Spec.LocallyRingedSpace_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec.LocallyRingedSpace_map_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpaceCat

/-- The counit morphism `R ⟶ Γ(Spec R)` given by `algebraic_geometry.structure_sheaf.to_open`.  -/
@[simps]
def toSpecΓ (R : CommRingCat) : R ⟶ Γ.obj (op (SpecCat.toLocallyRingedSpace.obj (op R))) :=
  StructureSheaf.toOpen R ⊤

instance is_iso_to_Spec_Γ (R : CommRingCat) : IsIso (toSpecΓ R) := by
  cases R
  apply structure_sheaf.is_iso_to_global

@[reassoc]
theorem Spec_Γ_naturality {R S : CommRingCat} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (SpecCat.toLocallyRingedSpace.map f.op).op := by
  ext
  symm
  apply Localization.local_ring_hom_to_map

/-- The counit (`Spec_Γ_identity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps hom_app inv_app]
def specΓIdentity : SpecCat.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  iso.symm <| NatIso.ofComponents (fun R => asIso (toSpecΓ R) : _) fun _ _ => Spec_Γ_naturality

end SpecΓ

/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
theorem Spec_map_localization_is_iso (R : CommRingCat) (M : Submonoid R) (x : PrimeSpectrum (Localization M)) :
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
      is_iso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M x.as_ideal).toRingEquiv.toCommRingIso.Hom
      by infer_instance
  infer_instance

end AlgebraicGeometry

