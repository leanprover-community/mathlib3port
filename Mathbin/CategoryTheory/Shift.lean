import Mathbin.CategoryTheory.Limits.Shapes.Zero

/-!
# Shift

A `shift` on a category is nothing more than an automorphism of the category. An example to
keep in mind might be the category of complexes ⋯ → C_{n-1} → C_n → C_{n+1} → ⋯ with the shift
operator re-indexing the terms, so the degree `n` term of `shift C` would be the degree `n+1`
term of `C`.

-/


namespace CategoryTheory

universe v u

variable (C : Type u) [category.{v} C]

/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift where 
  shift : C ≌ C

variable [has_shift C]

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shift : C ≌ C :=
  has_shift.shift

notation X "⟦" n "⟧" => (shift _ ^ (n : ℤ)).Functor.obj X

notation f "⟦" n "⟧'" => (shift _ ^ (n : ℤ)).Functor.map f

example {X Y : C} (f : X ⟶ Y) : X⟦1⟧ ⟶ Y⟦1⟧ :=
  f⟦1⟧'

example {X Y : C} (f : X ⟶ Y) : X⟦-2⟧ ⟶ Y⟦-2⟧ :=
  f⟦-2⟧'

open CategoryTheory.Limits

variable [has_zero_morphisms C]

@[simp]
theorem shift_zero_eq_zero (X Y : C) (n : ℤ) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  by 
    apply equivalence_preserves_zero_morphisms

end CategoryTheory

