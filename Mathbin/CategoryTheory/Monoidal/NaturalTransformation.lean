import Mathbin.CategoryTheory.Monoidal.Functor 
import Mathbin.CategoryTheory.FullSubcategory

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

(Lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable{C : Type u₁}[category.{v₁} C][monoidal_category.{v₁} C]{D : Type u₂}[category.{v₂} D][monoidal_category.{v₂} D]

/--
A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure monoidal_nat_trans(F G : lax_monoidal_functor C D) extends nat_trans F.to_functor G.to_functor where 
  unit' : F.ε ≫ app (𝟙_ C) = G.ε :=  by 
  runTac 
    obviously 
  tensor' : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ :=  by 
  runTac 
    obviously

restate_axiom monoidal_nat_trans.tensor'

attribute [simp, reassoc] monoidal_nat_trans.tensor

restate_axiom monoidal_nat_trans.unit'

attribute [simp, reassoc] monoidal_nat_trans.unit

namespace MonoidalNatTrans

/--
The identity monoidal natural transformation.
-/
@[simps]
def id (F : lax_monoidal_functor C D) : monoidal_nat_trans F F :=
  { 𝟙 F.to_functor with  }

instance  (F : lax_monoidal_functor C D) : Inhabited (monoidal_nat_trans F F) :=
  ⟨id F⟩

/--
Vertical composition of monoidal natural transformations.
-/
@[simps]
def vcomp {F G H : lax_monoidal_functor C D} (α : monoidal_nat_trans F G) (β : monoidal_nat_trans G H) :
  monoidal_nat_trans F H :=
  { nat_trans.vcomp α.to_nat_trans β.to_nat_trans with  }

instance category_lax_monoidal_functor : category (lax_monoidal_functor C D) :=
  { Hom := monoidal_nat_trans, id := id, comp := fun F G H α β => vcomp α β }

@[simp]
theorem comp_to_nat_trans_lax {F G H : lax_monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).toNatTrans = @category_struct.comp (C ⥤ D) _ _ _ _ α.to_nat_trans β.to_nat_trans :=
  rfl

instance category_monoidal_functor : category (monoidal_functor C D) :=
  induced_category.category monoidal_functor.to_lax_monoidal_functor

@[simp]
theorem comp_to_nat_trans {F G H : monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).toNatTrans = @category_struct.comp (C ⥤ D) _ _ _ _ α.to_nat_trans β.to_nat_trans :=
  rfl

variable{E : Type u₃}[category.{v₃} E][monoidal_category.{v₃} E]

/--
Horizontal composition of monoidal natural transformations.
-/
@[simps]
def hcomp {F G : lax_monoidal_functor C D} {H K : lax_monoidal_functor D E} (α : monoidal_nat_trans F G)
  (β : monoidal_nat_trans H K) : monoidal_nat_trans (F ⊗⋙ H) (G ⊗⋙ K) :=
  { nat_trans.hcomp α.to_nat_trans β.to_nat_trans with
    unit' :=
      by 
        dsimp 
        simp 
        convLHS => rw [←K.to_functor.map_comp, α.unit],
    tensor' :=
      fun X Y =>
        by 
          dsimp 
          simp 
          convLHS => rw [←K.to_functor.map_comp, α.tensor, K.to_functor.map_comp] }

end MonoidalNatTrans

namespace MonoidalNatIso

variable{F G : lax_monoidal_functor C D}

/--
Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction.
-/
def of_components (app : ∀ (X : C), F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).Hom = (app X).Hom ≫ G.map f)
  (unit : F.ε ≫ (app (𝟙_ C)).Hom = G.ε)
  (tensor : ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).Hom = ((app X).Hom ⊗ (app Y).Hom) ≫ G.μ X Y) : F ≅ G :=
  { Hom := { app := fun X => (app X).Hom },
    inv :=
      { (nat_iso.of_components app @naturality).inv with app := fun X => (app X).inv,
        unit' :=
          by 
            dsimp 
            rw [←Unit, assoc, iso.hom_inv_id, comp_id],
        tensor' :=
          fun X Y =>
            by 
              dsimp 
              rw [iso.comp_inv_eq, assoc, tensor, ←tensor_comp_assoc, iso.inv_hom_id, iso.inv_hom_id, tensor_id,
                id_comp] } }

@[simp]
theorem of_components.hom_app (app : ∀ (X : C), F.obj X ≅ G.obj X) naturality unit tensor X :
  (of_components app naturality Unit tensor).Hom.app X = (app X).Hom :=
  rfl

@[simp]
theorem of_components.inv_app (app : ∀ (X : C), F.obj X ≅ G.obj X) naturality unit tensor X :
  (of_components app naturality Unit tensor).inv.app X = (app X).inv :=
  by 
    simp [of_components]

instance is_iso_of_is_iso_app (α : F ⟶ G) [∀ (X : C), is_iso (α.app X)] : is_iso α :=
  ⟨(is_iso.of_iso
        (of_components (fun X => as_iso (α.app X)) (fun X Y f => α.to_nat_trans.naturality f) α.unit α.tensor)).1⟩

end MonoidalNatIso

end CategoryTheory

