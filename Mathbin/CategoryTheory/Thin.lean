import Mathbin.CategoryTheory.FunctorCategory 
import Mathbin.CategoryTheory.Isomorphism

/-!
# Thin categories

A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.

Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.

To construct a category instance one only needs to specify the `category_struct` part,
as the axioms hold for free.

If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable{C : Type u₁}

section 

variable[category_struct.{v₁} C][∀ X Y : C, Subsingleton (X ⟶ Y)]

/-- Construct a category instance from a category_struct, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
def thin_category : category C :=
  {  }

end 

variable[category.{v₁} C]{D : Type u₂}[category.{v₂} D]

variable[∀ X Y : C, Subsingleton (X ⟶ Y)]

/-- If `C` is a thin category, then `D ⥤ C` is a thin category. -/
instance functor_thin (F₁ F₂ : D ⥤ C) : Subsingleton (F₁ ⟶ F₂) :=
  ⟨fun α β => nat_trans.ext α β (funext fun _ => Subsingleton.elimₓ _ _)⟩

/-- To show `X ≅ Y` in a thin category, it suffices to just give any morphism in each direction. -/
def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y :=
  { Hom := f, inv := g }

instance subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y) :=
  ⟨by 
      intro i₁ i₂ 
      ext1 
      apply Subsingleton.elimₓ⟩

end CategoryTheory

