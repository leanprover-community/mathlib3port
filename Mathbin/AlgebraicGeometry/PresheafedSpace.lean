import Mathbin.Topology.Sheaves.Presheaf

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

variable(C : Type u)[category.{v} C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace where 
  Carrier : Top 
  Presheaf : carrier.presheaf C

variable{C}

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

instance  (X : PresheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
def const (X : Top) (Z : C) : PresheafedSpace C :=
  { Carrier := X, Presheaf := { obj := fun U => Z, map := fun U V f => 𝟙 Z } }

instance  [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (Top.of Pempty) (default C)⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom(X Y : PresheafedSpace C) where 
  base : (X : Top.{v}) ⟶ (Y : Top.{v})
  c : Y.presheaf ⟶ base _* X.presheaf

@[ext]
theorem ext {X Y : PresheafedSpace C} (α β : hom X Y) (w : α.base = β.base)
  (h :
    α.c ≫
        eq_to_hom
          (by 
            rw [w]) =
      β.c) :
  α = β :=
  by 
    cases α 
    cases β 
    dsimp [presheaf.pushforward_obj]  at *
    tidy

-- error in AlgebraicGeometry.PresheafedSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem hext
{X Y : PresheafedSpace C}
(α β : hom X Y)
(w : «expr = »(α.base, β.base))
(h : «expr == »(α.c, β.c)) : «expr = »(α, β) :=
by { cases [expr α] [],
  cases [expr β] [],
  congr,
  exacts ["[", expr w, ",", expr h, "]"] }

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

variable(C)

section 

attribute [local simp] id comp

-- error in AlgebraicGeometry.PresheafedSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
instance category_of_PresheafedSpaces : category (PresheafedSpace C) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g,
  id_comp' := λ X Y f, by { ext1 [] [],
    { rw [expr comp_c] [],
      erw [expr eq_to_hom_map] [],
      simp [] [] [] [] [] [],
      apply [expr comp_id] },
    apply [expr id_comp] },
  comp_id' := λ X Y f, by { ext1 [] [],
    { rw [expr comp_c] [],
      erw [expr congr_hom (presheaf.id_pushforward _) f.c] [],
      simp [] [] [] [] [] [],
      erw [expr eq_to_hom_trans_assoc] [],
      simp [] [] [] [] [] [] },
    apply [expr comp_id] },
  assoc' := λ W X Y Z f g h, by { ext1 [] [],
    repeat { rw [expr comp_c] [] },
    simpa [] [] [] [] [] [],
    refl } }

end 

variable{C}

@[simp]
theorem id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : Top.{v}) :=
  rfl

theorem id_c (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm :=
  rfl

@[simp]
theorem id_c_app (X : PresheafedSpace C) U :
  (𝟙 X : X ⟶ X).c.app U =
    eq_to_hom
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
theorem comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
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

variable(C)

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
@[simps]
def forget : PresheafedSpace C ⥤ Top :=
  { obj := fun X => (X : Top.{v}), map := fun X Y f => f.base }

end 

/--
The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
def restrict {U : Top} (X : PresheafedSpace C) {f : U ⟶ (X : Top.{v})} (h : OpenEmbedding f) : PresheafedSpace C :=
  { Carrier := U, Presheaf := h.is_open_map.functor.op ⋙ X.presheaf }

/--
The map from the restriction of a presheafed space.
-/
def of_restrict {U : Top} (X : PresheafedSpace C) {f : U ⟶ (X : Top.{v})} (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  { base := f,
    c :=
      { app := fun V => X.presheaf.map (h.is_open_map.adjunction.counit.app V.unop).op,
        naturality' :=
          fun U V f =>
            show _ = _ ≫ X.presheaf.map _ by 
              rw [←map_comp, ←map_comp]
              rfl } }

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
          simpa,
    inv_hom_id' :=
      ext _ _ rfl$
        by 
          erw [comp_c]
          rw [X.of_restrict_top_c]
          simpa }

/--
The global sections, notated Gamma.
-/
@[simps]
def Γ : «expr ᵒᵖ» (PresheafedSpace C) ⥤ C :=
  { obj := fun X => (unop X).Presheaf.obj (op ⊤), map := fun X Y f => f.unop.c.app (op ⊤) }

theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable{C}

namespace CategoryTheory

variable{D : Type u}[category.{v} D]

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

