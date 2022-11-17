/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.Sheaves.Presheaf
import Mathbin.CategoryTheory.Adjunction.FullyFaithful

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe w v u

open CategoryTheory

open TopCat

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpaceCat where
  carrier : TopCat.{w}
  Presheaf : carrier.Presheaf C
#align algebraic_geometry.PresheafedSpace AlgebraicGeometry.PresheafedSpaceCat

variable {C}

namespace PresheafedSpaceCat

attribute [protected] presheaf

instance coeCarrier : Coe (PresheafedSpaceCat.{w, v, u} C) TopCat.{w} where coe X := X.carrier
#align algebraic_geometry.PresheafedSpace.coe_carrier AlgebraicGeometry.PresheafedSpaceCat.coeCarrier

@[simp]
theorem as_coe (X : PresheafedSpaceCat.{w, v, u} C) : X.carrier = (X : TopCat.{w}) :=
  rfl
#align algebraic_geometry.PresheafedSpace.as_coe AlgebraicGeometry.PresheafedSpaceCat.as_coe

@[simp]
theorem mk_coe (carrier) (presheaf) : (({ carrier, Presheaf } : PresheafedSpaceCat.{v} C) : TopCat.{v}) = carrier :=
  rfl
#align algebraic_geometry.PresheafedSpace.mk_coe AlgebraicGeometry.PresheafedSpaceCat.mk_coe

instance (X : PresheafedSpaceCat.{v} C) : TopologicalSpace X :=
  X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : TopCat) (Z : C) : PresheafedSpaceCat C where
  carrier := X
  Presheaf := { obj := fun U => Z, map := fun U V f => 𝟙 Z }
#align algebraic_geometry.PresheafedSpace.const AlgebraicGeometry.PresheafedSpaceCat.const

instance [Inhabited C] : Inhabited (PresheafedSpaceCat C) :=
  ⟨const (TopCat.of PEmpty) default⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure Hom (X Y : PresheafedSpaceCat.{w, v, u} C) where
  base : (X : TopCat.{w}) ⟶ (Y : TopCat.{w})
  c : Y.Presheaf ⟶ base _* X.Presheaf
#align algebraic_geometry.PresheafedSpace.hom AlgebraicGeometry.PresheafedSpaceCat.Hom

@[ext.1]
theorem ext {X Y : PresheafedSpaceCat C} (α β : Hom X Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β := by
  cases α
  cases β
  dsimp [presheaf.pushforward_obj] at *
  tidy
#align algebraic_geometry.PresheafedSpace.ext AlgebraicGeometry.PresheafedSpaceCat.ext

-- TODO including `injections` would make tidy work earlier.
theorem hext {X Y : PresheafedSpaceCat C} (α β : Hom X Y) (w : α.base = β.base) (h : α.c == β.c) : α = β := by
  cases α
  cases β
  congr
  exacts[w, h]
#align algebraic_geometry.PresheafedSpace.hext AlgebraicGeometry.PresheafedSpaceCat.hext

/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpaceCat.{w, v, u} C) : Hom X X where
  base := 𝟙 (X : TopCat.{w})
  c := eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm
#align algebraic_geometry.PresheafedSpace.id AlgebraicGeometry.PresheafedSpaceCat.id

instance homInhabited (X : PresheafedSpaceCat C) : Inhabited (Hom X X) :=
  ⟨id X⟩
#align algebraic_geometry.PresheafedSpace.hom_inhabited AlgebraicGeometry.PresheafedSpaceCat.homInhabited

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpaceCat C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  base := α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c
#align algebraic_geometry.PresheafedSpace.comp AlgebraicGeometry.PresheafedSpaceCat.comp

theorem comp_c {X Y Z : PresheafedSpaceCat C} (α : Hom X Y) (β : Hom Y Z) :
    (comp α β).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c :=
  rfl
#align algebraic_geometry.PresheafedSpace.comp_c AlgebraicGeometry.PresheafedSpaceCat.comp_c

variable (C)

section

attribute [local simp] id comp

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance categoryOfPresheafedSpaces : Category (PresheafedSpaceCat.{v, v, u} C) where
  Hom := Hom
  id := id
  comp X Y Z f g := comp f g
  id_comp' X Y f := by
    ext1
    · rw [comp_c]
      erw [eq_to_hom_map]
      simp only [eq_to_hom_refl, assoc, whisker_right_id']
      erw [comp_id, comp_id]
      
    apply id_comp
  comp_id' X Y f := by
    ext1
    · rw [comp_c]
      erw [congr_hom (presheaf.id_pushforward _) f.c]
      simp only [comp_id, functor.id_map, eq_to_hom_refl, assoc, whisker_right_id']
      erw [eq_to_hom_trans_assoc]
      simp only [id_comp, eq_to_hom_refl]
      erw [comp_id]
      
    apply comp_id
  assoc' W X Y Z f g h := by
    ext1
    repeat' rw [comp_c]
    simp only [eq_to_hom_refl, assoc, functor.map_comp, whisker_right_id']
    erw [comp_id]
    congr
    rfl
#align
  algebraic_geometry.PresheafedSpace.category_of_PresheafedSpaces AlgebraicGeometry.PresheafedSpaceCat.categoryOfPresheafedSpaces

end

variable {C}

attribute [local simp] eq_to_hom_map

@[simp]
theorem id_base (X : PresheafedSpaceCat.{v, v, u} C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat.{v}) :=
  rfl
#align algebraic_geometry.PresheafedSpace.id_base AlgebraicGeometry.PresheafedSpaceCat.id_base

theorem id_c (X : PresheafedSpaceCat.{v, v, u} C) :
    (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.Presheaf).symm :=
  rfl
#align algebraic_geometry.PresheafedSpace.id_c AlgebraicGeometry.PresheafedSpaceCat.id_c

@[simp]
theorem id_c_app (X : PresheafedSpaceCat.{v, v, u} C) (U) :
    (𝟙 X : X ⟶ X).c.app U =
      X.Presheaf.map
        (eqToHom
          (by
            induction U using Opposite.rec
            cases U
            rfl)) :=
  by
  induction U using Opposite.rec
  cases U
  simp only [id_c]
  dsimp
  simp
#align algebraic_geometry.PresheafedSpace.id_c_app AlgebraicGeometry.PresheafedSpaceCat.id_c_app

@[simp]
theorem comp_base {X Y Z : PresheafedSpaceCat.{v, v, u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.comp_base AlgebraicGeometry.PresheafedSpaceCat.comp_base

instance (X Y : PresheafedSpaceCat.{v, v, u} C) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨fun f => f.base⟩

theorem coe_to_fun_eq {X Y : PresheafedSpaceCat.{v, v, u} C} (f : X ⟶ Y) : (f : X → Y) = f.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.coe_to_fun_eq AlgebraicGeometry.PresheafedSpaceCat.coe_to_fun_eq

-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
theorem comp_c_app {X Y Z : PresheafedSpaceCat.{v, v, u} C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl
#align algebraic_geometry.PresheafedSpace.comp_c_app AlgebraicGeometry.PresheafedSpaceCat.comp_c_app

theorem congr_app {X Y : PresheafedSpaceCat.{v, v, u} C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.Presheaf.map (eqToHom (by subst h)) := by
  subst h
  dsimp
  simp
#align algebraic_geometry.PresheafedSpace.congr_app AlgebraicGeometry.PresheafedSpaceCat.congr_app

section

variable (C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpaceCat.{v, v, u} C ⥤ TopCat where
  obj X := (X : TopCat.{v})
  map X Y f := f.base
#align algebraic_geometry.PresheafedSpace.forget AlgebraicGeometry.PresheafedSpaceCat.forget

end

section Iso

variable {X Y : PresheafedSpaceCat.{v, v, u} C}

/-- An isomorphism of PresheafedSpaces is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps Hom inv]
def isoOfComponents (H : X.1 ≅ Y.1) (α : H.Hom _* X.2 ≅ Y.2) : X ≅ Y where
  Hom := { base := H.Hom, c := α.inv }
  inv := { base := H.inv, c := Presheaf.toPushforwardOfIso H α.Hom }
  hom_inv_id' := by
    ext
    · simp
      erw [category.id_comp]
      simpa
      
    simp
  inv_hom_id' := by
    ext x
    induction x using Opposite.rec
    simp only [comp_c_app, whisker_right_app, presheaf.to_pushforward_of_iso_app, nat_trans.comp_app, eq_to_hom_app,
      id_c_app, category.assoc]
    erw [← α.hom.naturality]
    have := nat_trans.congr_app α.inv_hom_id (op x)
    cases x
    rw [nat_trans.comp_app] at this
    convert this
    · dsimp
      simp
      
    · simp
      
    · simp
      
#align algebraic_geometry.PresheafedSpace.iso_of_components AlgebraicGeometry.PresheafedSpaceCat.isoOfComponents

/-- Isomorphic PresheafedSpaces have natural isomorphic presheaves. -/
@[simps]
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.Hom.base _* X.2 where
  Hom := H.Hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id' := by
    ext U
    have := congr_app H.inv_hom_id U
    simp only [comp_c_app, id_c_app, eq_to_hom_map, eq_to_hom_trans] at this
    generalize_proofs h  at this
    simpa using congr_arg (fun f => f ≫ eq_to_hom h.symm) this
  inv_hom_id' := by
    ext U
    simp only [presheaf.pushforward_to_of_iso_app, nat_trans.comp_app, category.assoc, nat_trans.id_app,
      H.hom.c.naturality]
    have := congr_app H.hom_inv_id ((opens.map H.hom.base).op.obj U)
    generalize_proofs h  at this
    simpa using congr_arg (fun f => f ≫ X.presheaf.map (eq_to_hom h.symm)) this
#align algebraic_geometry.PresheafedSpace.sheaf_iso_of_iso AlgebraicGeometry.PresheafedSpaceCat.sheafIsoOfIso

instance base_is_iso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  IsIso.of_iso ((forget _).mapIso (asIso f))
#align algebraic_geometry.PresheafedSpace.base_is_iso_of_iso AlgebraicGeometry.PresheafedSpaceCat.base_is_iso_of_iso

instance c_is_iso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  IsIso.of_iso (sheafIsoOfIso (asIso f))
#align algebraic_geometry.PresheafedSpace.c_is_iso_of_iso AlgebraicGeometry.PresheafedSpaceCat.c_is_iso_of_iso

/-- This could be used in conjunction with `category_theory.nat_iso.is_iso_of_is_iso_app`. -/
theorem is_iso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f := by
  convert is_iso.of_iso (iso_of_components (as_iso f.base) (as_iso f.c).symm)
  ext
  · simpa
    
  · simp
    
#align algebraic_geometry.PresheafedSpace.is_iso_of_components AlgebraicGeometry.PresheafedSpaceCat.is_iso_of_components

end Iso

section Restrict

/-- The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : TopCat} (X : PresheafedSpaceCat.{v, v, u} C) {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) :
    PresheafedSpaceCat C where
  carrier := U
  Presheaf := h.IsOpenMap.Functor.op ⋙ X.Presheaf
#align algebraic_geometry.PresheafedSpace.restrict AlgebraicGeometry.PresheafedSpaceCat.restrict

/-- The map from the restriction of a presheafed space.
-/
@[simps]
def ofRestrict {U : TopCat} (X : PresheafedSpaceCat.{v, v, u} C) {f : U ⟶ (X : TopCat.{v})} (h : OpenEmbedding f) :
    X.restrict h ⟶ X where
  base := f
  c :=
    { app := fun V => X.Presheaf.map (h.IsOpenMap.Adjunction.counit.app V.unop).op,
      naturality' := fun U V f =>
        show _ = _ ≫ X.Presheaf.map _ by
          rw [← map_comp, ← map_comp]
          rfl }
#align algebraic_geometry.PresheafedSpace.of_restrict AlgebraicGeometry.PresheafedSpaceCat.ofRestrict

instance of_restrict_mono {U : TopCat} (X : PresheafedSpaceCat C) (f : U ⟶ X.1) (hf : OpenEmbedding f) :
    Mono (X.ofRestrict hf) := by
  haveI : mono f := (TopCat.mono_iff_injective _).mpr hf.inj
  constructor
  intro Z g₁ g₂ eq
  ext V
  · induction V using Opposite.rec
    have hV : (opens.map (X.of_restrict hf).base).obj (hf.is_open_map.functor.obj V) = V := by
      cases V
      simp [opens.map, Set.preimage_image_eq _ hf.inj]
    haveI : is_iso (hf.is_open_map.adjunction.counit.app (unop (op (hf.is_open_map.functor.obj V)))) :=
      (nat_iso.is_iso_app_of_is_iso (whisker_left hf.is_open_map.functor hf.is_open_map.adjunction.counit) V : _)
    have := PresheafedSpace.congr_app Eq (op (hf.is_open_map.functor.obj V))
    simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, category.assoc, cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ := congr_arg (fun f => (X.restrict hf).Presheaf.map (eq_to_hom hV).op ≫ f) this
    erw [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [presheaf.pushforward_obj_map, eq_to_hom_op, category.assoc, eq_to_hom_map, eq_to_hom_trans] at h
    rw [← is_iso.comp_inv_eq] at h
    simpa using h
    
  · have := congr_arg PresheafedSpace.hom.base Eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.of_restrict_base] at this
    rw [cancel_mono] at this
    exact this
    
#align algebraic_geometry.PresheafedSpace.of_restrict_mono AlgebraicGeometry.PresheafedSpaceCat.of_restrict_mono

theorem restrict_top_presheaf (X : PresheafedSpaceCat C) :
    (X.restrict (Opens.open_embedding ⊤)).Presheaf = (Opens.inclusionTopIso X.carrier).inv _* X.Presheaf := by
  dsimp
  rw [opens.inclusion_top_functor X.carrier]
  rfl
#align
  algebraic_geometry.PresheafedSpace.restrict_top_presheaf AlgebraicGeometry.PresheafedSpaceCat.restrict_top_presheaf

theorem of_restrict_top_c (X : PresheafedSpaceCat C) :
    (X.ofRestrict (Opens.open_embedding ⊤)).c =
      eqToHom
        (by
          rw [restrict_top_presheaf, ← presheaf.pushforward.comp_eq]
          erw [iso.inv_hom_id]
          rw [presheaf.pushforward.id_eq]) :=
  by
  /- another approach would be to prove the left hand side
       is a natural isoomorphism, but I encountered a universe
       issue when `apply nat_iso.is_iso_of_is_iso_app`. -/
  ext U
  change X.presheaf.map _ = _
  convert eq_to_hom_map _ _ using 1
  congr
  simpa
  · induction U using Opposite.rec
    dsimp
    congr
    ext
    exact ⟨fun h => ⟨⟨x, trivial⟩, h, rfl⟩, fun ⟨⟨_, _⟩, h, rfl⟩ => h⟩
    
#align algebraic_geometry.PresheafedSpace.of_restrict_top_c AlgebraicGeometry.PresheafedSpaceCat.of_restrict_top_c

/- or `rw [opens.inclusion_top_functor, ←comp_obj, ←opens.map_comp_eq],
         erw iso.inv_hom_id, cases U, refl` after `dsimp` -/
/-- The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def toRestrictTop (X : PresheafedSpaceCat C) : X ⟶ X.restrict (Opens.open_embedding ⊤) where
  base := (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)
#align algebraic_geometry.PresheafedSpace.to_restrict_top AlgebraicGeometry.PresheafedSpaceCat.toRestrictTop

/-- The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrictTopIso (X : PresheafedSpaceCat C) : X.restrict (Opens.open_embedding ⊤) ≅ X where
  Hom := X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id' :=
    ext _ _ (ConcreteCategory.hom_ext _ _ $ fun ⟨x, _⟩ => rfl) $ by
      erw [comp_c]
      rw [X.of_restrict_top_c]
      ext
      simp
  inv_hom_id' :=
    ext _ _ rfl $ by
      erw [comp_c]
      rw [X.of_restrict_top_c]
      ext
      simpa [-eq_to_hom_refl]
#align algebraic_geometry.PresheafedSpace.restrict_top_iso AlgebraicGeometry.PresheafedSpaceCat.restrictTopIso

end Restrict

/-- The global sections, notated Gamma.
-/
@[simps]
def Γ : (PresheafedSpaceCat.{v, v, u} C)ᵒᵖ ⥤ C where
  obj X := (unop X).Presheaf.obj (op ⊤)
  map X Y f := f.unop.c.app (op ⊤)
#align algebraic_geometry.PresheafedSpace.Γ AlgebraicGeometry.PresheafedSpaceCat.Γ

theorem Γ_obj_op (X : PresheafedSpaceCat C) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl
#align algebraic_geometry.PresheafedSpace.Γ_obj_op AlgebraicGeometry.PresheafedSpaceCat.Γ_obj_op

theorem Γ_map_op {X Y : PresheafedSpaceCat.{v, v, u} C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl
#align algebraic_geometry.PresheafedSpace.Γ_map_op AlgebraicGeometry.PresheafedSpaceCat.Γ_map_op

end PresheafedSpaceCat

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpaceCat

variable {C}

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

attribute [local simp] presheaf.pushforward_obj

namespace Functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def mapPresheaf (F : C ⥤ D) : PresheafedSpaceCat.{v, v, u} C ⥤ PresheafedSpaceCat.{v, v, u} D where
  obj X := { carrier := X.carrier, Presheaf := X.Presheaf ⋙ F }
  map X Y f := { base := f.base, c := whiskerRight f.c F }
#align category_theory.functor.map_presheaf CategoryTheory.Functor.mapPresheaf

@[simp]
theorem map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpaceCat C) :
    (F.mapPresheaf.obj X : TopCat.{v}) = (X : TopCat.{v}) :=
  rfl
#align category_theory.functor.map_presheaf_obj_X CategoryTheory.Functor.map_presheaf_obj_X

@[simp]
theorem map_presheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpaceCat C) :
    (F.mapPresheaf.obj X).Presheaf = X.Presheaf ⋙ F :=
  rfl
#align category_theory.functor.map_presheaf_obj_presheaf CategoryTheory.Functor.map_presheaf_obj_presheaf

@[simp]
theorem map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpaceCat.{v, v, u} C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl
#align category_theory.functor.map_presheaf_map_f CategoryTheory.Functor.map_presheaf_map_f

@[simp]
theorem map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpaceCat.{v, v, u} C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).c = whiskerRight f.c F :=
  rfl
#align category_theory.functor.map_presheaf_map_c CategoryTheory.Functor.map_presheaf_map_c

end Functor

namespace NatTrans

/-- A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def onPresheaf {F G : C ⥤ D} (α : F ⟶ G) :
    G.mapPresheaf ⟶
      F.mapPresheaf where app X :=
    { base := 𝟙 _, c := whiskerLeft X.Presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }
#align category_theory.nat_trans.on_presheaf CategoryTheory.NatTrans.onPresheaf

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end NatTrans

end CategoryTheory

