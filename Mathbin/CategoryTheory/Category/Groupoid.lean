import Mathbin.CategoryTheory.SingleObj

/-!
# Category of groupoids

This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.

## Implementation notes

Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/


universe v u

namespace CategoryTheory

/-- Category of groupoids -/
@[nolint check_univs]
def Groupoid :=
  bundled groupoid.{v, u}

namespace Groupoid

instance : Inhabited Groupoid :=
  ⟨bundled.of (single_obj PUnit)⟩

instance str (C : Groupoid.{v, u}) : groupoid.{v, u} C.α :=
  C.str

/-- Construct a bundled `Groupoid` from the underlying type and the typeclass. -/
def of (C : Type u) [groupoid.{v} C] : Groupoid.{v, u} :=
  bundled.of C

/-- Category structure on `Groupoid` -/
instance category : large_category.{max v u} Groupoid.{v, u} where
  Hom := fun C D => C.α ⥤ D.α
  id := fun C => 𝟭 C.α
  comp := fun C D E F G => F ⋙ G
  id_comp' := fun C D F => by
    cases F <;> rfl
  comp_id' := fun C D F => by
    cases F <;> rfl
  assoc' := by
    intros <;> rfl

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Groupoid.{v, u} ⥤ Type u where
  obj := bundled.α
  map := fun C D F => F.obj

/-- Forgetting functor to `Cat` -/
def forget_to_Cat : Groupoid.{v, u} ⥤ Cat.{v, u} where
  obj := fun C => Cat.of C.α
  map := fun C D => id

instance forget_to_Cat_full : full forget_to_Cat where
  Preimage := fun C D => id

instance forget_to_Cat_faithful : faithful forget_to_Cat :=
  {  }

end Groupoid

end CategoryTheory

