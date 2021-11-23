import Mathbin.AlgebraicGeometry.PresheafedSpace 
import Mathbin.Topology.Sheaves.Sheaf

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/


universe v u

open CategoryTheory

open Top

open TopologicalSpace

open Opposite

open CategoryTheory.Limits

open CategoryTheory.Category CategoryTheory.Functor

variable(C : Type u)[category.{v} C][limits.has_products C]

attribute [local tidy] tactic.op_induction'

namespace AlgebraicGeometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace C where 
  IsSheaf : presheaf.is_sheaf

variable{C}

namespace SheafedSpace

instance coe_carrier : Coe (SheafedSpace C) Top :=
  { coe := fun X => X.carrier }

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : sheaf C (X : Top.{v}) :=
  ⟨X.presheaf, X.is_sheaf⟩

@[simp]
theorem as_coe (X : SheafedSpace C) : X.carrier = (X : Top.{v}) :=
  rfl

@[simp]
theorem mk_coe carrier presheaf h : (({ Carrier, Presheaf, IsSheaf := h } : SheafedSpace.{v} C) : Top.{v}) = carrier :=
  rfl

instance  (X : SheafedSpace.{v} C) : TopologicalSpace X :=
  X.carrier.str

/-- The trivial `punit` valued sheaf on any topological space. -/
def PUnit (X : Top) : SheafedSpace (discrete PUnit) :=
  { @PresheafedSpace.const (discrete PUnit) _ X PUnit.unit with IsSheaf := presheaf.is_sheaf_punit _ }

instance  : Inhabited (SheafedSpace (discrete _root_.punit)) :=
  ⟨PUnit (Top.of Pempty)⟩

instance  : category (SheafedSpace C) :=
  show category (induced_category (PresheafedSpace C) SheafedSpace.to_PresheafedSpace)by 
    infer_instance

-- error in AlgebraicGeometry.SheafedSpace: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
@[derive #["[", expr full, ",", expr faithful, "]"]]
def forget_to_PresheafedSpace : «expr ⥤ »(SheafedSpace C, PresheafedSpace C) :=
induced_functor _

variable{C}

section 

attribute [local simp] id comp

@[simp]
theorem id_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : Top.{v}) :=
  rfl

theorem id_c (X : SheafedSpace C) : (𝟙 X : X ⟶ X).c = eq_to_hom (presheaf.pushforward.id_eq X.presheaf).symm :=
  rfl

@[simp]
theorem id_c_app (X : SheafedSpace C) U :
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
theorem comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) U :
  (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((opens.map β.base).obj (unop U))) :=
  rfl

variable(C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ Top :=
  { obj := fun X => (X : Top.{v}), map := fun X Y f => f.base }

end 

open Top.Presheaf

/--
The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : Top} (X : SheafedSpace C) {f : U ⟶ (X : Top.{v})} (h : OpenEmbedding f) : SheafedSpace C :=
  { X.to_PresheafedSpace.restrict h with
    IsSheaf :=
      fun ι 𝒰 =>
        ⟨is_limit.of_iso_limit ((is_limit.postcompose_inv_equiv _ _).invFun (X.is_sheaf _).some)
            (sheaf_condition_equalizer_products.fork.iso_of_open_embedding h 𝒰).symm⟩ }

/--
The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrict_top_iso (X : SheafedSpace C) : X.restrict (opens.open_embedding ⊤) ≅ X :=
  @preimage_iso _ _ _ _ forget_to_PresheafedSpace _ _ (X.restrict (opens.open_embedding ⊤)) _
    X.to_PresheafedSpace.restrict_top_iso

/--
The global sections, notated Gamma.
-/
def Γ : «expr ᵒᵖ» (SheafedSpace C) ⥤ C :=
  forget_to_PresheafedSpace.op ⋙ PresheafedSpace.Γ

theorem Γ_def : (Γ : _ ⥤ C) = forget_to_PresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : «expr ᵒᵖ» (SheafedSpace C)) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : «expr ᵒᵖ» (SheafedSpace C)} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

end SheafedSpace

end AlgebraicGeometry

