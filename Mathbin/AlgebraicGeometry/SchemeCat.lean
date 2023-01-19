/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebraic_geometry.Scheme
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.SpecCat
import Mathbin.Algebra.Category.RingCat.Constructions

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/


noncomputable section

open TopologicalSpace

open CategoryTheory

open TopCat

open Opposite

namespace AlgebraicGeometry

/- ./././Mathport/Syntax/Translate/Command.lean:417:11: unsupported: advanced extends in structure -/
/-- We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.to_LocallyRingedSpace.obj (op R)`
for some `R : CommRing`.
-/
structure SchemeCat extends
  "./././Mathport/Syntax/Translate/Command.lean:417:11: unsupported: advanced extends in structure" where
  local_affine :
    ∀ x : to_LocallyRingedSpace,
      ∃ (U : OpenNhds x)(R : CommRingCat),
        Nonempty
          (to_LocallyRingedSpace.restrict U.OpenEmbedding ≅ SpecCat.toLocallyRingedSpace.obj (op R))
#align algebraic_geometry.Scheme AlgebraicGeometry.SchemeCat

namespace SchemeCat

-- There isn't nessecarily a morphism between two schemes.
/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
@[nolint has_nonempty_instance]
def Hom (X Y : SchemeCat) : Type _ :=
  X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace
#align algebraic_geometry.Scheme.hom AlgebraicGeometry.SchemeCat.Hom

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : Category SchemeCat :=
  { InducedCategory.category SchemeCat.toLocallyRingedSpace with Hom := Hom }

/-- The structure sheaf of a Scheme. -/
protected abbrev sheaf (X : SchemeCat) :=
  X.toSheafedSpace.Sheaf
#align algebraic_geometry.Scheme.sheaf AlgebraicGeometry.SchemeCat.sheaf

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps]
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  inducedFunctor _ deriving Full, Faithful
#align algebraic_geometry.Scheme.forget_to_LocallyRingedSpace AlgebraicGeometry.SchemeCat.forgetToLocallyRingedSpace

@[simp]
theorem forget_to_LocallyRingedSpace_preimage {X Y : SchemeCat} (f : X ⟶ Y) :
    SchemeCat.forgetToLocallyRingedSpace.preimage f = f :=
  rfl
#align algebraic_geometry.Scheme.forget_to_LocallyRingedSpace_preimage AlgebraicGeometry.SchemeCat.forget_to_LocallyRingedSpace_preimage

/-- The forgetful functor from `Scheme` to `Top`. -/
@[simps]
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forget_to_LocallyRingedSpace ⋙ LocallyRingedSpace.forget_to_Top
#align algebraic_geometry.Scheme.forget_to_Top AlgebraicGeometry.SchemeCat.forgetToTop

@[simp]
theorem id_val_base (X : SchemeCat) : (𝟙 X : _).1.base = 𝟙 _ :=
  rfl
#align algebraic_geometry.Scheme.id_val_base AlgebraicGeometry.SchemeCat.id_val_base

@[simp]
theorem id_app {X : SchemeCat} (U : (Opens X.carrier)ᵒᵖ) :
    (𝟙 X : _).val.c.app U =
      X.Presheaf.map
        (eqToHom
          (by
            induction U using Opposite.rec
            cases U
            rfl)) :=
  PresheafedSpaceCat.id_c_app X.toPresheafedSpace U
#align algebraic_geometry.Scheme.id_app AlgebraicGeometry.SchemeCat.id_app

@[reassoc.1]
theorem comp_val {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl
#align algebraic_geometry.Scheme.comp_val AlgebraicGeometry.SchemeCat.comp_val

@[reassoc.1, simp]
theorem comp_coe_base {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl
#align algebraic_geometry.Scheme.comp_coe_base AlgebraicGeometry.SchemeCat.comp_coe_base

@[reassoc.1, elementwise]
theorem comp_val_base {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl
#align algebraic_geometry.Scheme.comp_val_base AlgebraicGeometry.SchemeCat.comp_val_base

@[reassoc.1, simp]
theorem comp_val_c_app {X Y Z : SchemeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ :=
  rfl
#align algebraic_geometry.Scheme.comp_val_c_app AlgebraicGeometry.SchemeCat.comp_val_c_app

theorem congr_app {X Y : SchemeCat} {f g : X ⟶ Y} (e : f = g) (U) :
    f.val.c.app U = g.val.c.app U ≫ X.Presheaf.map (eqToHom (by subst e)) :=
  by
  subst e
  dsimp
  simp
#align algebraic_geometry.Scheme.congr_app AlgebraicGeometry.SchemeCat.congr_app

theorem app_eq {X Y : SchemeCat} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    f.val.c.app (op U) =
      Y.Presheaf.map (eqToHom e.symm).op ≫
        f.val.c.app (op V) ≫ X.Presheaf.map (eqToHom (congr_arg (Opens.map f.val.base).obj e)).op :=
  by
  rw [← is_iso.inv_comp_eq, ← functor.map_inv, f.val.c.naturality, presheaf.pushforward_obj_map]
  congr
#align algebraic_geometry.Scheme.app_eq AlgebraicGeometry.SchemeCat.app_eq

instance is_LocallyRingedSpace_iso {X Y : SchemeCat} (f : X ⟶ Y) [IsIso f] :
    @IsIso LocallyRingedSpaceCat _ _ _ f :=
  forgetToLocallyRingedSpace.map_is_iso f
#align algebraic_geometry.Scheme.is_LocallyRingedSpace_iso AlgebraicGeometry.SchemeCat.is_LocallyRingedSpace_iso

@[simp]
theorem inv_val_c_app {X Y : SchemeCat} (f : X ⟶ Y) [IsIso f] (U : Opens X.carrier) :
    (inv f).val.c.app (op U) =
      X.Presheaf.map
          (eq_to_hom <| by
                rw [is_iso.hom_inv_id]
                ext1
                rfl :
              (Opens.map (f ≫ inv f).1.base).obj U ⟶ U).op ≫
        inv (f.val.c.app (op <| (Opens.map _).obj U)) :=
  by
  rw [is_iso.eq_comp_inv]
  erw [← Scheme.comp_val_c_app]
  rw [Scheme.congr_app (is_iso.hom_inv_id f), Scheme.id_app, ← functor.map_comp, eq_to_hom_trans,
    eq_to_hom_op]
  rfl
#align algebraic_geometry.Scheme.inv_val_c_app AlgebraicGeometry.SchemeCat.inv_val_c_app

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`. -/
abbrev Hom.appLe {X Y : SchemeCat} (f : X ⟶ Y) {V : Opens X.carrier} {U : Opens Y.carrier}
    (e : V ≤ (Opens.map f.1.base).obj U) : Y.Presheaf.obj (op U) ⟶ X.Presheaf.obj (op V) :=
  f.1.c.app (op U) ≫ X.Presheaf.map (homOfLe e).op
#align algebraic_geometry.Scheme.hom.app_le AlgebraicGeometry.SchemeCat.Hom.appLe

/-- The spectrum of a commutative ring, as a scheme.
-/
def specObj (R : CommRingCat) : SchemeCat
    where
  local_affine x := ⟨⟨⊤, trivial⟩, R, ⟨(SpecCat.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := SpecCat.locallyRingedSpaceObj R
#align algebraic_geometry.Scheme.Spec_obj AlgebraicGeometry.SchemeCat.specObj

@[simp]
theorem Spec_obj_to_LocallyRingedSpace (R : CommRingCat) :
    (specObj R).toLocallyRingedSpace = SpecCat.locallyRingedSpaceObj R :=
  rfl
#align algebraic_geometry.Scheme.Spec_obj_to_LocallyRingedSpace AlgebraicGeometry.SchemeCat.Spec_obj_to_LocallyRingedSpace

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def specMap {R S : CommRingCat} (f : R ⟶ S) : specObj S ⟶ specObj R :=
  (SpecCat.locallyRingedSpaceMap f :
    SpecCat.locallyRingedSpaceObj S ⟶ SpecCat.locallyRingedSpaceObj R)
#align algebraic_geometry.Scheme.Spec_map AlgebraicGeometry.SchemeCat.specMap

@[simp]
theorem Spec_map_id (R : CommRingCat) : specMap (𝟙 R) = 𝟙 (specObj R) :=
  SpecCat.LocallyRingedSpace_map_id R
#align algebraic_geometry.Scheme.Spec_map_id AlgebraicGeometry.SchemeCat.Spec_map_id

theorem Spec_map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    specMap (f ≫ g) = specMap g ≫ specMap f :=
  SpecCat.LocallyRingedSpace_map_comp f g
#align algebraic_geometry.Scheme.Spec_map_comp AlgebraicGeometry.SchemeCat.Spec_map_comp

/-- The spectrum, as a contravariant functor from commutative rings to schemes.
-/
@[simps]
def spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := specObj (unop R)
  map R S f := specMap f.unop
  map_id' R := by rw [unop_id, Spec_map_id]
  map_comp' R S T f g := by rw [unop_comp, Spec_map_comp]
#align algebraic_geometry.Scheme.Spec AlgebraicGeometry.SchemeCat.spec

/-- The empty scheme.
-/
@[simps]
def empty.{u} : SchemeCat.{u} where
  carrier := TopCat.of PEmpty
  Presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.is_sheaf_of_is_terminal _ CommRingCat.punitIsTerminal
  LocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x
#align algebraic_geometry.Scheme.empty AlgebraicGeometry.SchemeCat.empty

instance : EmptyCollection SchemeCat :=
  ⟨empty⟩

instance : Inhabited SchemeCat :=
  ⟨∅⟩

/-- The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRingCat :=
  (inducedFunctor SchemeCat.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ
#align algebraic_geometry.Scheme.Γ AlgebraicGeometry.SchemeCat.Γ

theorem Γ_def : Γ = (inducedFunctor SchemeCat.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ :=
  rfl
#align algebraic_geometry.Scheme.Γ_def AlgebraicGeometry.SchemeCat.Γ_def

@[simp]
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj AlgebraicGeometry.SchemeCat.Γ_obj

theorem Γ_obj_op (X : SchemeCat) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_obj_op AlgebraicGeometry.SchemeCat.Γ_obj_op

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_map AlgebraicGeometry.SchemeCat.Γ_map

theorem Γ_map_op {X Y : SchemeCat} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.Scheme.Γ_map_op AlgebraicGeometry.SchemeCat.Γ_map_op

section BasicOpen

variable (X : SchemeCat) {V U : Opens X.carrier} (f g : X.Presheaf.obj (op U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basicOpen : Opens X.carrier :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f
#align algebraic_geometry.Scheme.basic_open AlgebraicGeometry.SchemeCat.basicOpen

@[simp]
theorem mem_basic_open (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ x f) :=
  RingedSpaceCat.mem_basic_open _ _ _
#align algebraic_geometry.Scheme.mem_basic_open AlgebraicGeometry.SchemeCat.mem_basic_open

@[simp]
theorem mem_basic_open_top (f : X.Presheaf.obj (op ⊤)) (x : X.carrier) :
    x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ (⟨x, trivial⟩ : (⊤ : Opens _)) f) :=
  RingedSpaceCat.mem_basic_open _ f ⟨x, trivial⟩
#align algebraic_geometry.Scheme.mem_basic_open_top AlgebraicGeometry.SchemeCat.mem_basic_open_top

@[simp]
theorem basic_open_res (i : op U ⟶ op V) : X.basicOpen (X.Presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpaceCat.basic_open_res _ i f
#align algebraic_geometry.Scheme.basic_open_res AlgebraicGeometry.SchemeCat.basic_open_res

-- This should fire before `basic_open_res`.
@[simp]
theorem basic_open_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.Presheaf.map i f) = X.basicOpen f :=
  RingedSpaceCat.basic_open_res_eq _ i f
#align algebraic_geometry.Scheme.basic_open_res_eq AlgebraicGeometry.SchemeCat.basic_open_res_eq

@[sheaf_restrict]
theorem basic_open_le : X.basicOpen f ≤ U :=
  RingedSpaceCat.basic_open_le _ _
#align algebraic_geometry.Scheme.basic_open_le AlgebraicGeometry.SchemeCat.basic_open_le

@[simp]
theorem preimage_basic_open {X Y : SchemeCat} (f : X ⟶ Y) {U : Opens Y.carrier}
    (r : Y.Presheaf.obj <| op U) :
    (Opens.map f.1.base).obj (Y.basicOpen r) =
      @SchemeCat.basicOpen X ((Opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpaceCat.preimage_basic_open f r
#align algebraic_geometry.Scheme.preimage_basic_open AlgebraicGeometry.SchemeCat.preimage_basic_open

@[simp]
theorem basic_open_zero (U : Opens X.carrier) : X.basicOpen (0 : X.Presheaf.obj <| op U) = ⊥ :=
  LocallyRingedSpaceCat.basic_open_zero _ U
#align algebraic_geometry.Scheme.basic_open_zero AlgebraicGeometry.SchemeCat.basic_open_zero

@[simp]
theorem basic_open_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpaceCat.basic_open_mul _ _ _
#align algebraic_geometry.Scheme.basic_open_mul AlgebraicGeometry.SchemeCat.basic_open_mul

theorem basic_open_of_is_unit {f : X.Presheaf.obj (op U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpaceCat.basic_open_of_is_unit _ hf
#align algebraic_geometry.Scheme.basic_open_of_is_unit AlgebraicGeometry.SchemeCat.basic_open_of_is_unit

end BasicOpen

end SchemeCat

theorem basic_open_eq_of_affine {R : CommRingCat} (f : R) :
    (SchemeCat.spec.obj <| op R).basicOpen ((specΓIdentity.app R).inv f) =
      PrimeSpectrum.basicOpen f :=
  by
  ext
  erw [Scheme.mem_basic_open_top]
  suffices IsUnit (structure_sheaf.to_stalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by exact this
  erw [← is_unit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk]
  exact
    (IsLocalization.AtPrime.is_unit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
        (PrimeSpectrum.asIdeal x) f :
      _)
#align algebraic_geometry.basic_open_eq_of_affine AlgebraicGeometry.basic_open_eq_of_affine

@[simp]
theorem basic_open_eq_of_affine' {R : CommRingCat}
    (f : (SpecCat.toSheafedSpace.obj (op R)).Presheaf.obj (op ⊤)) :
    (SchemeCat.spec.obj <| op R).basicOpen f =
      PrimeSpectrum.basicOpen ((specΓIdentity.app R).Hom f) :=
  by
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).Hom f)
  exact (iso.hom_inv_id_apply _ _).symm
#align algebraic_geometry.basic_open_eq_of_affine' AlgebraicGeometry.basic_open_eq_of_affine'

end AlgebraicGeometry

