import Mathbin.CategoryTheory.ConcreteCategory.Default 
import Mathbin.CategoryTheory.DiscreteCategory 
import Mathbin.CategoryTheory.EqToHom

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

/-- Category of categories. -/
@[nolint check_univs]
def Cat :=
  bundled category.{v, u}

namespace Cat

instance  : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

instance  : CoeSort Cat (Type u) :=
  ⟨bundled.α⟩

instance str (C : Cat.{v, u}) : category.{v, u} C :=
  C.str

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [category.{v} C] : Cat.{v, u} :=
  bundled.of C

/-- Category structure on `Cat` -/
instance category : large_category.{max v u} Cat.{v, u} :=
  { Hom := fun C D => C ⥤ D, id := fun C => 𝟭 C, comp := fun C D E F G => F ⋙ G,
    id_comp' :=
      fun C D F =>
        by 
          cases F <;> rfl,
    comp_id' :=
      fun C D F =>
        by 
          cases F <;> rfl,
    assoc' :=
      by 
        intros  <;> rfl }

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat.{v, u} ⥤ Type u :=
  { obj := fun C => C, map := fun C D F => F.obj }

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equiv_of_iso {C D : Cat} (γ : C ≅ D) : C ≌ D :=
  { Functor := γ.hom, inverse := γ.inv, unitIso := eq_to_iso$ Eq.symm γ.hom_inv_id,
    counitIso := eq_to_iso γ.inv_hom_id }

end Cat

/--
Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
def Type_to_Cat : Type u ⥤ Cat :=
  { obj := fun X => Cat.of (discrete X), map := fun X Y f => discrete.functor f,
    map_id' :=
      fun X =>
        by 
          apply Functor.ext 
          tidy,
    map_comp' :=
      fun X Y Z f g =>
        by 
          apply Functor.ext 
          tidy }

instance  : faithful Type_to_Cat.{u} :=
  {  }

instance  : full Type_to_Cat.{u} :=
  { Preimage := fun X Y F => F.obj,
    witness' :=
      by 
        intro X Y F 
        apply Functor.ext
        ·
          intro x y f 
          dsimp 
          ext
        ·
          intro x 
          rfl }

end CategoryTheory

