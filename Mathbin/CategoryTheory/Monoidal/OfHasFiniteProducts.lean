import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way
is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## Implementation
We had previously chosen to rely on `has_terminal` and `has_binary_products` instead of
`has_finite_products`, because we were later relying on the definitional form of the tensor product.
Now that `has_limit` has been refactored to be a `Prop`,
this issue is irrelevant and we could simplify the construction here.

See `category_theory.monoidal.of_chosen_finite_products` for a variant of this construction
which allows specifying a particular choice of terminal object and binary products.
-/


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

attribute [local tidy] tactic.case_bash

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_has_finite_products [has_terminal C] [has_binary_products C] : monoidal_category C where
  tensorUnit := ⊤_ C
  tensorObj := fun X Y => X ⨯ Y
  tensorHom := fun _ _ _ _ f g => limits.prod.map f g
  associator := prod.associator
  leftUnitor := fun P => prod.left_unitor P
  rightUnitor := fun P => prod.right_unitor P
  pentagon' := prod.pentagon
  triangle' := prod.triangle
  associator_naturality' := @prod.associator_naturality _ _ _

end

section

attribute [local instance] monoidal_of_has_finite_products

open MonoidalCategory

/-- The monoidal structure coming from finite products is symmetric.
-/
@[simps]
def symmetric_of_has_finite_products [has_terminal C] [has_binary_products C] : symmetric_category C where
  braiding := fun X Y => limits.prod.braiding X Y
  braiding_naturality' := fun X X' Y Y' f g => by
    dsimp [tensor_hom]
    simp
  hexagon_forward' := fun X Y Z => by
    dsimp [monoidal_of_has_finite_products]
    simp
  hexagon_reverse' := fun X Y Z => by
    dsimp [monoidal_of_has_finite_products]
    simp
  symmetry' := fun X Y => by
    dsimp
    simp
    rfl

end

namespace MonoidalOfHasFiniteProducts

variable [has_terminal C] [has_binary_products C]

attribute [local instance] monoidal_of_has_finite_products

@[simp]
theorem tensor_obj (X Y : C) : X ⊗ Y = (X ⨯ Y) :=
  rfl

@[simp]
theorem tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.prod.map f g :=
  rfl

@[simp]
theorem left_unitor_hom (X : C) : (λ_ X).Hom = limits.prod.snd :=
  rfl

@[simp]
theorem left_unitor_inv (X : C) : (λ_ X).inv = prod.lift (terminal.from X) (𝟙 _) :=
  rfl

@[simp]
theorem right_unitor_hom (X : C) : (ρ_ X).Hom = limits.prod.fst :=
  rfl

@[simp]
theorem right_unitor_inv (X : C) : (ρ_ X).inv = prod.lift (𝟙 _) (terminal.from X) :=
  rfl

theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).Hom =
      prod.lift (limits.prod.fst ≫ limits.prod.fst) (prod.lift (limits.prod.fst ≫ limits.prod.snd) limits.prod.snd) :=
  rfl

end MonoidalOfHasFiniteProducts

section

attribute [local tidy] tactic.case_bash

/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidal_of_has_finite_coproducts [has_initial C] [has_binary_coproducts C] : monoidal_category C where
  tensorUnit := ⊥_ C
  tensorObj := fun X Y => X ⨿ Y
  tensorHom := fun _ _ _ _ f g => limits.coprod.map f g
  associator := coprod.associator
  leftUnitor := coprod.left_unitor
  rightUnitor := coprod.right_unitor
  pentagon' := coprod.pentagon
  triangle' := coprod.triangle
  associator_naturality' := @coprod.associator_naturality _ _ _

end

section

attribute [local instance] monoidal_of_has_finite_coproducts

open MonoidalCategory

/-- The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps]
def symmetric_of_has_finite_coproducts [has_initial C] [has_binary_coproducts C] : symmetric_category C where
  braiding := limits.coprod.braiding
  braiding_naturality' := fun X X' Y Y' f g => by
    dsimp [tensor_hom]
    simp
  hexagon_forward' := fun X Y Z => by
    dsimp [monoidal_of_has_finite_coproducts]
    simp
  hexagon_reverse' := fun X Y Z => by
    dsimp [monoidal_of_has_finite_coproducts]
    simp
  symmetry' := fun X Y => by
    dsimp
    simp
    rfl

end

namespace MonoidalOfHasFiniteCoproducts

variable [has_initial C] [has_binary_coproducts C]

attribute [local instance] monoidal_of_has_finite_coproducts

@[simp]
theorem tensor_obj (X Y : C) : X ⊗ Y = (X ⨿ Y) :=
  rfl

@[simp]
theorem tensor_hom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.coprod.map f g :=
  rfl

@[simp]
theorem left_unitor_hom (X : C) : (λ_ X).Hom = coprod.desc (initial.to X) (𝟙 _) :=
  rfl

@[simp]
theorem right_unitor_hom (X : C) : (ρ_ X).Hom = coprod.desc (𝟙 _) (initial.to X) :=
  rfl

@[simp]
theorem left_unitor_inv (X : C) : (λ_ X).inv = limits.coprod.inr :=
  rfl

@[simp]
theorem right_unitor_inv (X : C) : (ρ_ X).inv = limits.coprod.inl :=
  rfl

theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).Hom = coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr) :=
  rfl

end MonoidalOfHasFiniteCoproducts

end CategoryTheory

