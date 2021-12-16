import Mathbin.Topology.Sheaves.Presheaf 
import Mathbin.CategoryTheory.Adjunction.FullyFaithful

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe v u

open CategoryTheory

open Top

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

variable (C : Type u) [category.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace where 
  Carrier : Top 
  Presheaf : carrier.presheaf C

variable {C}

namespace PresheafedSpace

attribute [protected] presheaf

instance coe_carrier : Coe (PresheafedSpace C) Top :=
  { coe := fun X => X.carrier }

@[simp]
theorem as_coe (X : PresheafedSpace C) : X.carrier = (X : Top.{v}) :=
  rfl

@[simp]
theorem mk_coe carrier presheaf : (({ Carrier, Presheaf } : PresheafedSpace.{v} C) : Top.{v}) = carrier :=
  rfl

instance (X : PresheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : Top) (Z : C) : PresheafedSpace C :=
  { Carrier := X, Presheaf := { obj := fun U => Z, map := fun U V f => 𝟙 Z } }

instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (Top.of Pempty) (default C)⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom (X Y : PresheafedSpace C) where 
  base : (X : Top.{v}) ⟶ (Y : Top.{v})
  c : Y.presheaf ⟶ base _* X.presheaf

@[ext]
theorem ext {X Y : PresheafedSpace C} (α β : hom X Y) (w : α.base = β.base)
  (h :
    α.c ≫
        whisker_right
          (eq_to_hom
            (by 
              rw [w]))
          _ =
      β.c) :
  α = β :=
  by 
    cases α 
    cases β 
    dsimp [presheaf.pushforward_obj]  at *
    tidy

theorem hext {X Y : PresheafedSpace C} (α β : hom X Y) (w : α.base = β.base) (h : HEq α.c β.c) : α = β :=
  by 
    cases α 
    cases β 
    congr 
    exacts[w, h]

/-- The identity morphism of a `PresheafedSpace`. -/
def id (X : PresheafedSpace C) : hom X X :=
  { base := 𝟙 (X : Top.{v}), c := eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm }

instance hom_inhabited (X : PresheafedSpace C) : Inhabited (hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) : hom X Z :=
  { base := α.base ≫ β.base, c := β.c ≫ (presheaf.pushforward _ β.base).map α.c }

theorem comp_c {X Y Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) :
  (comp α β).c = β.c ≫ (presheaf.pushforward _ β.base).map α.c :=
  rfl

variable (C)

section 

attribute [local simp] id comp

/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance category_of_PresheafedSpaces : category (PresheafedSpace C) :=
  { Hom := hom, id := id, comp := fun X Y Z f g => comp f g,
    id_comp' :=
      fun X Y f =>
        by 
          ext1
          ·
            rw [comp_c]
            erw [eq_to_hom_map]
            simp only [eq_to_hom_refl, assoc, whisker_right_id']
            erw [comp_id, comp_id]
          apply id_comp,
    comp_id' :=
      fun X Y f =>
        by 
          ext1
          ·
            rw [comp_c]
            erw [congr_hom (presheaf.id_pushforward _) f.c]
            simp only [comp_id, functor.id_map, eq_to_hom_refl, assoc, whisker_right_id']
            erw [eq_to_hom_trans_assoc]
            simp only [id_comp, eq_to_hom_refl]
            erw [comp_id]
          apply comp_id,
    assoc' :=
      fun W X Y Z f g h =>
        by 
          ext1 
          repeat' 
            rw [comp_c]
          simp only [eq_to_hom_refl, assoc, functor.map_comp, whisker_right_id']
          erw [comp_id]
          congr 
          rfl }

end 

variable {C}

@[simp]
theorem id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : Top.{v}) :=
  rfl

theorem id_c (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm :=
  rfl

@[simp]
theorem id_c_app (X : PresheafedSpace C) U :
  (𝟙 X : X ⟶ X).c.app U =
    X.presheaf.map
      (eq_to_hom
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

@[simp]
theorem comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
theorem comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) U :
  (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((opens.map β.base).obj (unop U))) :=
  rfl

theorem congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) U :
  α.c.app U =
    β.c.app U ≫
      X.presheaf.map
        (eq_to_hom
          (by 
            subst h)) :=
  by 
    subst h 
    dsimp 
    simp 

section 

variable (C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace C ⥤ Top :=
  { obj := fun X => (X : Top.{v}), map := fun X Y f => f.base }

end 

section Iso

variable {X Y : PresheafedSpace C}

/--
An isomorphism of PresheafedSpaces is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps Hom inv]
def iso_of_components (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y :=
  { Hom := { base := H.hom, c := α.inv }, inv := { base := H.inv, c := presheaf.to_pushforward_of_iso H α.hom },
    hom_inv_id' :=
      by 
        ext
        ·
          simp 
          erw [category.id_comp]
          simpa 
        simp ,
    inv_hom_id' :=
      by 
        ext x 
        induction x using Opposite.rec 
        simp only [comp_c_app, whisker_right_app, presheaf.to_pushforward_of_iso_app, nat_trans.comp_app, eq_to_hom_app,
          id_c_app, category.assoc]
        erw [←α.hom.naturality]
        have  := nat_trans.congr_app α.inv_hom_id (op x)
        cases x 
        rw [nat_trans.comp_app] at this 
        convert this
        ·
          dsimp 
          simp 
        ·
          simp 
        ·
          simp  }

/-- Isomorphic PresheafedSpaces have natural isomorphic presheaves. -/
@[simps]
def sheaf_iso_of_iso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 :=
  { Hom := H.hom.c, inv := presheaf.pushforward_to_of_iso ((forget _).mapIso H).symm H.inv.c,
    hom_inv_id' :=
      by 
        ext U 
        have  := congr_app H.inv_hom_id U 
        simp only [comp_c_app, id_c_app, eq_to_hom_map, eq_to_hom_trans] at this 
        generalizeProofs h  at this 
        simpa using congr_argₓ (fun f => f ≫ eq_to_hom h.symm) this,
    inv_hom_id' :=
      by 
        ext U 
        simp only [presheaf.pushforward_to_of_iso_app, nat_trans.comp_app, category.assoc, nat_trans.id_app,
          H.hom.c.naturality]
        have  := congr_app H.hom_inv_id ((opens.map H.hom.base).op.obj U)
        generalizeProofs h  at this 
        simpa using congr_argₓ (fun f => f ≫ X.presheaf.map (eq_to_hom h.symm)) this }

instance base_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.base :=
  is_iso.of_iso ((forget _).mapIso (as_iso f))

instance c_is_iso_of_iso (f : X ⟶ Y) [is_iso f] : is_iso f.c :=
  is_iso.of_iso (sheaf_iso_of_iso (as_iso f))

/-- This could be used in conjunction with `category_theory.nat_iso.is_iso_of_is_iso_app`. -/
theorem is_iso_of_components (f : X ⟶ Y) [is_iso f.base] [is_iso f.c] : is_iso f :=
  by 
    convert is_iso.of_iso (iso_of_components (as_iso f.base) (as_iso f.c).symm)
    ext
    ·
      simpa
    ·
      simp 

end Iso

section Restrict

/--
The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : Top} (X : PresheafedSpace C) {f : U ⟶ (X : Top.{v})} (h : OpenEmbedding f) : PresheafedSpace C :=
  { Carrier := U, Presheaf := h.is_open_map.functor.op ⋙ X.presheaf }

/--
The map from the restriction of a presheafed space.
-/
@[simps]
def of_restrict {U : Top} (X : PresheafedSpace C) {f : U ⟶ (X : Top.{v})} (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  { base := f,
    c :=
      { app := fun V => X.presheaf.map (h.is_open_map.adjunction.counit.app V.unop).op,
        naturality' :=
          fun U V f =>
            show _ = _ ≫ X.presheaf.map _ by 
              rw [←map_comp, ←map_comp]
              rfl } }

instance of_restrict_mono {U : Top} (X : PresheafedSpace C) (f : U ⟶ X.1) (hf : OpenEmbedding f) :
  mono (X.of_restrict hf) :=
  by 
    have  : mono f := (Top.mono_iff_injective _).mpr hf.inj 
    constructor 
    intro Z g₁ g₂ eq 
    ext V
    ·
      induction V using Opposite.rec 
      have hV : (opens.map (X.of_restrict hf).base).obj (hf.is_open_map.functor.obj V) = V
      ·
        cases V 
        simp [opens.map, Set.preimage_image_eq _ hf.inj]
      have  : is_iso (hf.is_open_map.adjunction.counit.app (unop (op (hf.is_open_map.functor.obj V)))) :=
        (nat_iso.is_iso_app_of_is_iso (whisker_left hf.is_open_map.functor hf.is_open_map.adjunction.counit) V : _)
      have  := PresheafedSpace.congr_app Eq (op (hf.is_open_map.functor.obj V))
      simp only [PresheafedSpace.comp_c_app, PresheafedSpace.of_restrict_c_app, category.assoc, cancel_epi] at this 
      have h : _ ≫ _ = _ ≫ _ ≫ _ := congr_argₓ (fun f => (X.restrict hf).Presheaf.map (eq_to_hom hV).op ≫ f) this 
      erw [g₁.c.naturality, g₂.c.naturality_assoc] at h 
      simp only [presheaf.pushforward_obj_map, eq_to_hom_op, category.assoc, eq_to_hom_map, eq_to_hom_trans] at h 
      rw [←is_iso.comp_inv_eq] at h 
      simpa using h
    ·
      have  := congr_argₓ PresheafedSpace.hom.base Eq 
      simp only [PresheafedSpace.comp_base, PresheafedSpace.of_restrict_base] at this 
      rw [cancel_mono] at this 
      exact this

theorem restrict_top_presheaf (X : PresheafedSpace C) :
  (X.restrict (opens.open_embedding ⊤)).Presheaf = (opens.inclusion_top_iso X.carrier).inv _* X.presheaf :=
  by 
    dsimp 
    rw [opens.inclusion_top_functor X.carrier]
    rfl

theorem of_restrict_top_c (X : PresheafedSpace C) :
  (X.of_restrict (opens.open_embedding ⊤)).c =
    eq_to_hom
      (by 
        rw [restrict_top_presheaf, ←presheaf.pushforward.comp_eq]
        erw [iso.inv_hom_id]
        rw [presheaf.pushforward.id_eq]) :=
  by 
    ext U 
    change X.presheaf.map _ = _ 
    convert eq_to_hom_map _ _ using 1
    congr 
    simpa
    ·
      induction U using Opposite.rec 
      dsimp 
      congr 
      ext 
      exact ⟨fun h => ⟨⟨x, trivialₓ⟩, h, rfl⟩, fun ⟨⟨_, _⟩, h, rfl⟩ => h⟩

/--
The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
def to_restrict_top (X : PresheafedSpace C) : X ⟶ X.restrict (opens.open_embedding ⊤) :=
  { base := (opens.inclusion_top_iso X.carrier).inv, c := eq_to_hom (restrict_top_presheaf X) }

/--
The isomorphism from the restriction to the top subspace.
-/
@[simps]
def restrict_top_iso (X : PresheafedSpace C) : X.restrict (opens.open_embedding ⊤) ≅ X :=
  { Hom := X.of_restrict _, inv := X.to_restrict_top,
    hom_inv_id' :=
      ext _ _ (concrete_category.hom_ext _ _$ fun ⟨x, _⟩ => rfl)$
        by 
          erw [comp_c]
          rw [X.of_restrict_top_c]
          ext 
          simp ,
    inv_hom_id' :=
      ext _ _ rfl$
        by 
          erw [comp_c]
          rw [X.of_restrict_top_c]
          ext 
          simpa [-eq_to_hom_refl] }

end Restrict

/--
The global sections, notated Gamma.
-/
@[simps]
def Γ : PresheafedSpace Cᵒᵖ ⥤ C :=
  { obj := fun X => (unop X).Presheaf.obj (op ⊤), map := fun X Y f => f.unop.c.app (op ⊤) }

theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type u} [category.{v} D]

attribute [local simp] presheaf.pushforward_obj

namespace Functor

/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def map_presheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D :=
  { obj := fun X => { Carrier := X.carrier, Presheaf := X.presheaf ⋙ F },
    map := fun X Y f => { base := f.base, c := whisker_right f.c F } }

@[simp]
theorem map_presheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) : (F.map_presheaf.obj X : Top.{v}) = (X : Top.{v}) :=
  rfl

@[simp]
theorem map_presheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
  (F.map_presheaf.obj X).Presheaf = X.presheaf ⋙ F :=
  rfl

@[simp]
theorem map_presheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) : (F.map_presheaf.map f).base = f.base :=
  rfl

@[simp]
theorem map_presheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
  (F.map_presheaf.map f).c = whisker_right f.c F :=
  rfl

end Functor

namespace NatTrans

/--
A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def on_presheaf {F G : C ⥤ D} (α : F ⟶ G) : G.map_presheaf ⟶ F.map_presheaf :=
  { app := fun X => { base := 𝟙 _, c := whisker_left X.presheaf α ≫ eq_to_hom (presheaf.pushforward.id_eq _).symm } }

end NatTrans

end CategoryTheory

