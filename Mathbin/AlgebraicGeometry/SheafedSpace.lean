/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.Topology.Sheaves.Functors

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe v u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Limits

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C] [HasProducts.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpaceCat extends PresheafedSpaceCat.{v} C where
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpaceCat

instance coeCarrier : Coe (SheafedSpaceCat C) TopCat where coe X := X.Carrier

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpaceCat C) : Sheaf C (X : TopCat.{v}) :=
  ⟨X.Presheaf, X.IsSheaf⟩

@[simp]
theorem as_coe (X : SheafedSpaceCat.{v} C) : X.Carrier = (X : TopCat.{v}) :=
  rfl

@[simp]
theorem mk_coe (carrier) (presheaf) (h) :
    (({ Carrier, Presheaf, IsSheaf := h } : SheafedSpaceCat.{v} C) : TopCat.{v}) = carrier :=
  rfl

instance (X : SheafedSpaceCat.{v} C) : TopologicalSpace X :=
  X.Carrier.str

/-- The trivial `unit` valued sheaf on any topological space. -/
def unit (X : TopCat) : SheafedSpaceCat (discrete Unit) :=
  { @PresheafedSpaceCat.const (discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.is_sheaf_unit _ }

instance : Inhabited (SheafedSpaceCat (discrete Unit)) :=
  ⟨unit (TopCat.of Pempty)⟩

instance : Category (SheafedSpaceCat C) :=
  show Category (InducedCategory (PresheafedSpaceCat.{v} C) SheafedSpaceCat.toPresheafedSpace) by infer_instance

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
def forgetToPresheafedSpace : SheafedSpaceCat.{v} C ⥤ PresheafedSpaceCat.{v} C :=
  inducedFunctor _ deriving Full, Faithful

instance is_PresheafedSpace_iso {X Y : SheafedSpaceCat.{v} C} (f : X ⟶ Y) [IsIso f] :
    @IsIso (PresheafedSpaceCat C) _ _ _ f :=
  SheafedSpaceCat.forgetToPresheafedSpace.map_is_iso f

variable {C}

section

attribute [local simp] id comp

@[simp]
theorem id_base (X : SheafedSpaceCat C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat.{v}) :=
  rfl

theorem id_c (X : SheafedSpaceCat C) : (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm :=
  rfl

@[simp]
theorem id_c_app (X : SheafedSpaceCat C) (U) :
    (𝟙 X : X ⟶ X).c.app U =
      eqToHom
        (by
          induction U using Opposite.rec
          cases U
          rfl) :=
  by
  induction U using Opposite.rec
  cases U
  simp only [id_c]
  dsimp
  simp

@[simp]
theorem comp_base {X Y Z : SheafedSpaceCat C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_c_app {X Y Z : SheafedSpaceCat C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

theorem comp_c_app' {X Y Z : SheafedSpaceCat C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app (op U) = β.c.app (op U) ≫ α.c.app (op ((Opens.map β.base).obj U)) :=
  rfl

theorem congr_app {X Y : SheafedSpaceCat C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.Presheaf.map (eqToHom (by subst h)) :=
  PresheafedSpaceCat.congr_app h U

variable (C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpaceCat C ⥤ TopCat where
  obj X := (X : TopCat.{v})
  map X Y f := f.base

end

open TopCat.Presheaf

/-- The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : TopCat} (X : SheafedSpaceCat C) {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) :
    SheafedSpaceCat C :=
  { X.toPresheafedSpace.restrict h with
    IsSheaf :=
      (is_sheaf_iff_is_sheaf_equalizer_products _).mpr fun ι 𝒰 =>
        ⟨IsLimit.ofIsoLimit
            ((IsLimit.postcomposeInvEquiv _ _).invFun
              ((is_sheaf_iff_is_sheaf_equalizer_products _).mp X.IsSheaf _).some)
            (SheafConditionEqualizerProducts.fork.isoOfOpenEmbedding h 𝒰).symm⟩ }

/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : SheafedSpaceCat C) : X.restrict (Opens.open_embedding ⊤) ≅ X :=
  forgetToPresheafedSpace.preimageIso X.toPresheafedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
def Γ : (SheafedSpaceCat C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : (SheafedSpaceCat C)ᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : SheafedSpaceCat C) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : (SheafedSpaceCat C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : SheafedSpaceCat C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

noncomputable instance [HasLimits C] : CreatesColimits (forgetToPresheafedSpace : SheafedSpaceCat C ⥤ _) :=
  ⟨fun J hJ =>
    ⟨fun K =>
      creates_colimit_of_fully_faithful_of_iso
        ⟨(PresheafedSpace.colimit_cocone (K ⋙ forget_to_PresheafedSpace)).x,
          limit_is_sheaf _ fun j => sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
        (colimit.iso_colimit_cocone ⟨_, PresheafedSpace.colimit_cocone_is_colimit _⟩).symm⟩⟩

instance [HasLimits C] : HasColimits (SheafedSpaceCat C) :=
  has_colimits_of_has_colimits_creates_colimits forgetToPresheafedSpace

noncomputable instance [HasLimits C] : PreservesColimits (forget C) :=
  Limits.compPreservesColimits forgetToPresheafedSpace (PresheafedSpaceCat.forget C)

end SheafedSpaceCat

end AlgebraicGeometry

