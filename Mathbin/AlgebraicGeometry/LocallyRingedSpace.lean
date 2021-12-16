import Mathbin.AlgebraicGeometry.RingedSpace 
import Mathbin.AlgebraicGeometry.Stalks 
import Mathbin.Data.Equiv.TransferInstance

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`is_local_ring_hom` on the stalk maps).
-/


universe v u

open CategoryTheory

open Top

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure LocallyRingedSpace extends SheafedSpace CommRingₓₓ where 
  LocalRing : ∀ x, LocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.local_ring

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace)

/--
An alias for `to_SheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
 -/
def to_RingedSpace : RingedSpace :=
  X.to_SheafedSpace

/-- The underlying topological space of a locally ringed space. -/
def to_Top : Top :=
  X.1.Carrier

instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.to_Top : Type u)⟩

/-- The structure sheaf of a locally ringed space. -/
def 𝒪 : sheaf CommRingₓₓ X.to_Top :=
  X.to_SheafedSpace.sheaf

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
def hom (X Y : LocallyRingedSpace) : Type _ :=
  { f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace // ∀ x, IsLocalRingHom (PresheafedSpace.stalk_map f x) }

instance : Quiver LocallyRingedSpace :=
  ⟨hom⟩

@[ext]
theorem hom_ext {X Y : LocallyRingedSpace} (f g : hom X Y) (w : f.1 = g.1) : f = g :=
  Subtype.eq w

/--
The stalk of a locally ringed space, just as a `CommRing`.
-/
noncomputable def stalk (X : LocallyRingedSpace) (x : X) : CommRingₓₓ :=
  X.presheaf.stalk x

/--
A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
noncomputable def stalk_map {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) : Y.stalk (f.1.1 x) ⟶ X.stalk x :=
  PresheafedSpace.stalk_map f.1 x

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) : IsLocalRingHom (stalk_map f x) :=
  f.2 x

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) : IsLocalRingHom (PresheafedSpace.stalk_map f.1 x) :=
  f.2 x

/-- The identity morphism on a locally ringed space. -/
@[simps]
def id (X : LocallyRingedSpace) : hom X X :=
  ⟨𝟙 _,
    fun x =>
      by 
        erw [PresheafedSpace.stalk_map.id]
        apply is_local_ring_hom_id⟩

instance (X : LocallyRingedSpace) : Inhabited (hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of locally ringed spaces. -/
@[simps]
def comp {X Y Z : LocallyRingedSpace} (f : hom X Y) (g : hom Y Z) : hom X Z :=
  ⟨f.val ≫ g.val,
    fun x =>
      by 
        erw [PresheafedSpace.stalk_map.comp]
        exact @is_local_ring_hom_comp _ _ _ _ _ _ _ _ (f.2 _) (g.2 _)⟩

/-- The category of locally ringed spaces. -/
instance : category LocallyRingedSpace :=
  { Hom := hom, id := id, comp := fun X Y Z f g => comp f g,
    comp_id' :=
      by 
        intros 
        ext1 
        simp ,
    id_comp' :=
      by 
        intros 
        ext1 
        simp ,
    assoc' :=
      by 
        intros 
        ext1 
        simp  }

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
def forget_to_SheafedSpace : LocallyRingedSpace ⥤ SheafedSpace CommRingₓₓ :=
  { obj := fun X => X.to_SheafedSpace, map := fun X Y f => f.1 }

instance : faithful forget_to_SheafedSpace :=
  {  }

/--
Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `iso_of_SheafedSpace_iso`.
-/
@[simps]
def hom_of_SheafedSpace_hom_of_is_iso {X Y : LocallyRingedSpace} (f : X.to_SheafedSpace ⟶ Y.to_SheafedSpace)
  [is_iso f] : X ⟶ Y :=
  Subtype.mk f$
    fun x =>
      show IsLocalRingHom (PresheafedSpace.stalk_map (SheafedSpace.forget_to_PresheafedSpace.map f) x)by 
        infer_instance

/--
Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forget_to_SheafedSpace` reflects isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphism between
_locally_ ringed spaces.
-/
def iso_of_SheafedSpace_iso {X Y : LocallyRingedSpace} (f : X.to_SheafedSpace ≅ Y.to_SheafedSpace) : X ≅ Y :=
  { Hom := hom_of_SheafedSpace_hom_of_is_iso f.hom, inv := hom_of_SheafedSpace_hom_of_is_iso f.inv,
    hom_inv_id' := hom_ext _ _ f.hom_inv_id, inv_hom_id' := hom_ext _ _ f.inv_hom_id }

instance : reflects_isomorphisms forget_to_SheafedSpace :=
  { reflects :=
      fun X Y f i =>
        { out :=
            by 
              exact
                ⟨hom_of_SheafedSpace_hom_of_is_iso (CategoryTheory.inv (forget_to_SheafedSpace.map f)),
                  hom_ext _ _ (is_iso.hom_inv_id _), hom_ext _ _ (is_iso.inv_hom_id _)⟩ } }

/--
The restriction of a locally ringed space along an open embedding.
-/
@[simps]
def restrict {U : Top} (X : LocallyRingedSpace) {f : U ⟶ X.to_Top} (h : OpenEmbedding f) : LocallyRingedSpace :=
  { X.to_SheafedSpace.restrict h with
    LocalRing :=
      by 
        intro x 
        dsimp  at *
        apply @RingEquiv.local_ring _ _ _ (X.local_ring (f x))
        exact (X.to_PresheafedSpace.restrict_stalk_iso h x).symm.commRingIsoToRingEquiv }

/--
The restriction of a locally ringed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrict_top_iso (X : LocallyRingedSpace) : X.restrict (opens.open_embedding ⊤) ≅ X :=
  @iso_of_SheafedSpace_iso (X.restrict (opens.open_embedding ⊤)) X X.to_SheafedSpace.restrict_top_iso

/--
The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpaceᵒᵖ ⥤ CommRingₓₓ :=
  forget_to_SheafedSpace.op ⋙ SheafedSpace.Γ

theorem Γ_def : Γ = forget_to_SheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : LocallyRingedSpaceᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : LocallyRingedSpace) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : LocallyRingedSpaceᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl

theorem preimage_basic_open {X Y : LocallyRingedSpace} (f : X ⟶ Y) {U : opens Y} (s : Y.presheaf.obj (op U)) :
  (opens.map f.1.base).obj (Y.to_RingedSpace.basic_open s) =
    @RingedSpace.basic_open X.to_RingedSpace ((opens.map f.1.base).obj U) (f.1.c.app _ s) :=
  by 
    ext 
    constructor
    ·
      rintro ⟨⟨y, hyU⟩, hy : IsUnit _, rfl : y = _⟩
      erw [RingedSpace.mem_basic_open _ _ ⟨x, show x ∈ (opens.map f.1.base).obj U from hyU⟩]
      rw [←PresheafedSpace.stalk_map_germ_apply]
      exact (PresheafedSpace.stalk_map f.1 _).is_unit_map hy
    ·
      rintro ⟨y, hy : IsUnit _, rfl⟩
      erw [RingedSpace.mem_basic_open _ _ ⟨f.1.base y.1, y.2⟩]
      rw [←PresheafedSpace.stalk_map_germ_apply] at hy 
      exact (is_unit_map_iff (PresheafedSpace.stalk_map f.1 _) _).mp hy

instance component_nontrivial (X : LocallyRingedSpace) (U : opens X.carrier) [hU : Nonempty U] :
  Nontrivial (X.presheaf.obj$ op U) :=
  (X.presheaf.germ hU.some).domain_nontrivial

end LocallyRingedSpace

end AlgebraicGeometry

