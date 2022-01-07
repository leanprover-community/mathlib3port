import Mathbin.AlgebraicGeometry.LocallyRingedSpace
import Mathbin.AlgebraicGeometry.StructureSheaf
import Mathbin.Data.Equiv.TransferInstance
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

## In progress

Adjunction between `Γ` and `Spec`: Currently, the counit of the adjunction is proven to be a
natural transformation in `Spec_Γ_naturality`, and realized as a natural isomorphism in
`Spec_Γ_identity`.

TODO: provide the unit, and prove the triangle identities.

-/


noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

/-- The spectrum of a commutative ring, as a topological space.
-/
def Spec.Top_obj (R : CommRingₓₓ) : Top :=
  Top.of (PrimeSpectrum R)

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def Spec.Top_map {R S : CommRingₓₓ} (f : R ⟶ S) : Spec.Top_obj S ⟶ Spec.Top_obj R :=
  PrimeSpectrum.comap f

@[simp]
theorem Spec.Top_map_id (R : CommRingₓₓ) : Spec.Top_map (𝟙 R) = 𝟙 (Spec.Top_obj R) :=
  PrimeSpectrum.comap_id

theorem Spec.Top_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.Top_map (f ≫ g) = Spec.Top_map g ≫ Spec.Top_map f :=
  PrimeSpectrum.comap_comp _ _

/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps]
def Spec.to_Top : CommRingₓₓᵒᵖ ⥤ Top where
  obj := fun R => Spec.Top_obj (unop R)
  map := fun R S f => Spec.Top_map f.unop
  map_id' := fun R => by
    rw [unop_id, Spec.Top_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec.Top_map_comp]

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def Spec.SheafedSpace_obj (R : CommRingₓₓ) : SheafedSpace CommRingₓₓ where
  Carrier := Spec.Top_obj R
  Presheaf := (structure_sheaf R).1
  IsSheaf := (structure_sheaf R).2

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps]
def Spec.SheafedSpace_map {R S : CommRingₓₓ.{u}} (f : R ⟶ S) : Spec.SheafedSpace_obj S ⟶ Spec.SheafedSpace_obj R where
  base := Spec.Top_map f
  c :=
    { app := fun U => comap f (unop U) ((TopologicalSpace.Opens.map (Spec.Top_map f)).obj (unop U)) fun p => id,
      naturality' := fun U V i => RingHom.ext $ fun s => Subtype.eq $ funext $ fun p => rfl }

@[simp]
theorem Spec.SheafedSpace_map_id {R : CommRingₓₓ} : Spec.SheafedSpace_map (𝟙 R) = 𝟙 (Spec.SheafedSpace_obj R) :=
  PresheafedSpace.ext _ _ (Spec.Top_map_id R) $
    nat_trans.ext _ _ $
      funext $ fun U => by
        dsimp
        erw [PresheafedSpace.id_c_app, comap_id]
        swap
        · rw [Spec.Top_map_id, TopologicalSpace.Opens.map_id_obj_unop]
          
        simpa

theorem Spec.SheafedSpace_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.SheafedSpace_map (f ≫ g) = Spec.SheafedSpace_map g ≫ Spec.SheafedSpace_map f :=
  PresheafedSpace.ext _ _ (Spec.Top_map_comp f g) $
    nat_trans.ext _ _ $
      funext $ fun U => by
        dsimp
        rw [CategoryTheory.Functor.map_id]
        rw [category.comp_id]
        erw [comap_comp f g]
        rfl

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def Spec.to_SheafedSpace : CommRingₓₓᵒᵖ ⥤ SheafedSpace CommRingₓₓ where
  obj := fun R => Spec.SheafedSpace_obj (unop R)
  map := fun R S f => Spec.SheafedSpace_map f.unop
  map_id' := fun R => by
    rw [unop_id, Spec.SheafedSpace_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec.SheafedSpace_map_comp]

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.to_PresheafedSpace : CommRingₓₓᵒᵖ ⥤ PresheafedSpace CommRingₓₓ :=
  Spec.to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace

@[simp]
theorem Spec.to_PresheafedSpace_obj (R : CommRingₓₓᵒᵖ) :
    Spec.to_PresheafedSpace.obj R = (Spec.SheafedSpace_obj (unop R)).toPresheafedSpace :=
  rfl

theorem Spec.to_PresheafedSpace_obj_op (R : CommRingₓₓ) :
    Spec.to_PresheafedSpace.obj (op R) = (Spec.SheafedSpace_obj R).toPresheafedSpace :=
  rfl

@[simp]
theorem Spec.to_PresheafedSpace_map (R S : CommRingₓₓᵒᵖ) (f : R ⟶ S) :
    Spec.to_PresheafedSpace.map f = Spec.SheafedSpace_map f.unop :=
  rfl

theorem Spec.to_PresheafedSpace_map_op (R S : CommRingₓₓ) (f : R ⟶ S) :
    Spec.to_PresheafedSpace.map f.op = Spec.SheafedSpace_map f :=
  rfl

theorem Spec.basic_open_hom_ext {X : RingedSpace} {R : CommRingₓₓ} {α β : X ⟶ Spec.SheafedSpace_obj R}
    (w : α.base = β.base)
    (h :
      ∀ r : R,
        let U := PrimeSpectrum.basicOpen r
        (to_open R U ≫ α.c.app (op U)) ≫
            X.presheaf.map
              (eq_to_hom
                (by
                  rw [w])) =
          to_open R U ≫ β.c.app (op U)) :
    α = β := by
  ext1
  · apply ((Top.Sheaf.pushforward β.base).obj X.sheaf).hom_ext _ PrimeSpectrum.is_basis_basic_opens
    intro r
    apply (structure_sheaf.to_basic_open_epi R r).1
    simpa using h r
    
  exact w

/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps]
def Spec.LocallyRingedSpace_obj (R : CommRingₓₓ) : LocallyRingedSpace :=
  { Spec.SheafedSpace_obj R with
    LocalRing := fun x =>
      @RingEquiv.local_ring _
        (show LocalRing (Localization.AtPrime _) by
          infer_instance)
        _ (iso.CommRing_iso_to_ring_equiv $ stalk_iso R x).symm }

@[elementwise]
theorem stalk_map_to_stalk {R S : CommRingₓₓ} (f : R ⟶ S) (p : PrimeSpectrum S) :
    to_stalk R (PrimeSpectrum.comap f p) ≫ PresheafedSpace.stalk_map (Spec.SheafedSpace_map f) p = f ≫ to_stalk S p :=
  by
  erw [← to_open_germ S ⊤ ⟨p, trivialₓ⟩, ← to_open_germ R ⊤ ⟨PrimeSpectrum.comap f p, trivialₓ⟩, category.assoc,
    PresheafedSpace.stalk_map_germ (Spec.SheafedSpace_map f) ⊤ ⟨p, trivialₓ⟩, Spec.SheafedSpace_map_c_app,
    to_open_comp_comap_assoc]
  rfl

/-- Under the isomorphisms `stalk_iso`, the map `stalk_map (Spec.SheafedSpace_map f) p` corresponds
to the induced local ring homomorphism `localization.local_ring_hom`.
-/
@[elementwise]
theorem local_ring_hom_comp_stalk_iso {R S : CommRingₓₓ} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (stalk_iso R (PrimeSpectrum.comap f p)).Hom ≫
        @category_struct.comp _ _ (CommRingₓₓ.of (Localization.AtPrime (PrimeSpectrum.comap f p).asIdeal))
          (CommRingₓₓ.of (Localization.AtPrime p.as_ideal)) _
          (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.as_ideal f rfl) (stalk_iso S p).inv =
      PresheafedSpace.stalk_map (Spec.SheafedSpace_map f) p :=
  (stalk_iso R (PrimeSpectrum.comap f p)).eq_inv_comp.mp $
    (stalk_iso S p).comp_inv_eq.mpr $
      Localization.local_ring_hom_unique _ _ _ _ $ fun x => by
        rw [stalk_iso_hom, stalk_iso_inv, comp_apply, comp_apply, localization_to_stalk_of, stalk_map_to_stalk_apply,
          stalk_to_fiber_ring_hom_to_stalk]

/-- The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps]
def Spec.LocallyRingedSpace_map {R S : CommRingₓₓ} (f : R ⟶ S) :
    Spec.LocallyRingedSpace_obj S ⟶ Spec.LocallyRingedSpace_obj R :=
  Subtype.mk (Spec.SheafedSpace_map f) $ fun p =>
    IsLocalRingHom.mk $ fun a ha => by
      rw [← local_ring_hom_comp_stalk_iso_apply] at ha
      replace ha := (stalk_iso S p).Hom.is_unit_map ha
      rw [coe_inv_hom_id] at ha
      replace ha := IsLocalRingHom.map_nonunit _ ha
      convert RingHom.is_unit_map (stalk_iso R (PrimeSpectrum.comap f p)).inv ha
      rw [coe_hom_inv_id]

@[simp]
theorem Spec.LocallyRingedSpace_map_id (R : CommRingₓₓ) :
    Spec.LocallyRingedSpace_map (𝟙 R) = 𝟙 (Spec.LocallyRingedSpace_obj R) :=
  Subtype.ext $ by
    rw [Spec.LocallyRingedSpace_map_coe, Spec.SheafedSpace_map_id]
    rfl

theorem Spec.LocallyRingedSpace_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.LocallyRingedSpace_map (f ≫ g) = Spec.LocallyRingedSpace_map g ≫ Spec.LocallyRingedSpace_map f :=
  Subtype.ext $ by
    rw [Spec.LocallyRingedSpace_map_coe, Spec.SheafedSpace_map_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def Spec.to_LocallyRingedSpace : CommRingₓₓᵒᵖ ⥤ LocallyRingedSpace where
  obj := fun R => Spec.LocallyRingedSpace_obj (unop R)
  map := fun R S f => Spec.LocallyRingedSpace_map f.unop
  map_id' := fun R => by
    rw [unop_id, Spec.LocallyRingedSpace_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec.LocallyRingedSpace_map_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

/-- The counit morphism `R ⟶ Γ(Spec R)` given by `algebraic_geometry.structure_sheaf.to_open`.  -/
@[simps]
def to_Spec_Γ (R : CommRingₓₓ) : R ⟶ Γ.obj (op (Spec.to_LocallyRingedSpace.obj (op R))) :=
  structure_sheaf.to_open R ⊤

instance is_iso_to_Spec_Γ (R : CommRingₓₓ) : is_iso (to_Spec_Γ R) := by
  cases R
  apply structure_sheaf.is_iso_to_global

theorem Spec_Γ_naturality {R S : CommRingₓₓ} (f : R ⟶ S) :
    f ≫ to_Spec_Γ S = to_Spec_Γ R ≫ Γ.map (Spec.to_LocallyRingedSpace.map f.op).op := by
  ext
  symm
  apply Localization.local_ring_hom_to_map

/-- The counit (`Spec_Γ_identity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps]
def Spec_Γ_identity : Spec.to_LocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  iso.symm $ nat_iso.of_components (fun R => as_iso (to_Spec_Γ R) : _) fun _ _ => Spec_Γ_naturality

end SpecΓ

/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
theorem Spec_map_localization_is_iso (R : CommRingₓₓ) (M : Submonoid R) (x : PrimeSpectrum (Localization M)) :
    is_iso
      (PresheafedSpace.stalk_map (Spec.to_PresheafedSpace.map (CommRingₓₓ.ofHom (algebraMap R (Localization M))).op)
        x) :=
  by
  erw [← local_ring_hom_comp_stalk_iso]
  apply is_iso.comp_is_iso with { instances := ff }
  infer_instance
  apply is_iso.comp_is_iso with { instances := ff }
  exact
    show
      is_iso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M x.as_ideal).toRingEquiv.toCommRingIso.Hom
      by
      infer_instance
  infer_instance

end AlgebraicGeometry

