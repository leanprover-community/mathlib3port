import Mathbin.CategoryTheory.Closed.Cartesian
import Mathbin.CategoryTheory.Limits.Shapes.Zero
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Conj

/-!
# A cartesian closed category with zero object is trivial

A cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/


universe v u

noncomputable section

namespace CategoryTheory

open Category Limits

variable {C : Type u} [category.{v} C]

variable [has_finite_products C] [cartesian_closed C]

/-- If a cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
def unique_homset_of_initial_iso_terminal [has_initial C] (i : ⊥_ C ≅ ⊤_ C) (X Y : C) : Unique (X ⟶ Y) :=
  Equivₓ.unique $
    calc
      (X ⟶ Y) ≃ (X ⨯ ⊤_ C ⟶ Y) := iso.hom_congr (prod.right_unitor _).symm (iso.refl _)
      _ ≃ (X ⨯ ⊥_ C ⟶ Y) := iso.hom_congr (prod.map_iso (iso.refl _) i.symm) (iso.refl _)
      _ ≃ (⊥_ C ⟶ Y ^^ X) := (exp.adjunction _).homEquiv _ _
      

open_locale ZeroObject

/-- If a cartesian closed category has a zero object, each homset has exactly one element. -/
def unique_homset_of_zero [has_zero_object C] (X Y : C) : Unique (X ⟶ Y) := by
  have : has_initial C := has_zero_object.has_initial
  apply unique_homset_of_initial_iso_terminal _ X Y
  refine' ⟨default, (default : ⊤_ C ⟶ 0) ≫ default, _, _⟩ <;> simp

attribute [local instance] unique_homset_of_zero

/-- A cartesian closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
def equiv_punit [has_zero_object C] : C ≌ discrete PUnit :=
  equivalence.mk (functor.star C) (functor.from_punit 0)
    (nat_iso.of_components (fun X => { Hom := default, inv := default }) fun X Y f => by
      decide)
    (functor.punit_ext _ _)

end CategoryTheory

