import Mathbin.CategoryTheory.Category.Cat 
import Mathbin.CategoryTheory.Groupoid

/-!
# Objects of a category up to an isomorphism

`is_isomorphic X Y := nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/


universe v u

namespace CategoryTheory

section Category

variable{C : Type u}[category.{v} C]

/-- An object `X` is isomorphic to an object `Y`, if `X ≅ Y` is not empty. -/
def is_isomorphic : C → C → Prop :=
  fun X Y => Nonempty (X ≅ Y)

variable(C)

/-- `is_isomorphic` defines a setoid. -/
def is_isomorphic_setoid : Setoidₓ C :=
  { R := is_isomorphic, iseqv := ⟨fun X => ⟨iso.refl X⟩, fun X Y ⟨α⟩ => ⟨α.symm⟩, fun X Y Z ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩ }

end Category

/--
The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
def isomorphism_classes : Cat.{v, u} ⥤ Type u :=
  { obj := fun C => Quotientₓ (is_isomorphic_setoid C.α),
    map := fun C D F => Quot.map F.obj$ fun X Y ⟨f⟩ => ⟨F.map_iso f⟩ }

theorem groupoid.is_isomorphic_iff_nonempty_hom {C : Type u} [groupoid.{v} C] {X Y : C} :
  is_isomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  (groupoid.iso_equiv_hom X Y).nonempty_congr

end CategoryTheory

