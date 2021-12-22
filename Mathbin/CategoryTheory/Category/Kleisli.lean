import Mathbin.CategoryTheory.Category.Basic

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`category_theory/monad/kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with category_theory.monad
-/


universe u v

namespace CategoryTheory

/--  The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unused_arguments]
def Kleisli (m : Type u → Type v) :=
  Type u

/--  Construct an object of the Kleisli category from a type. -/
def Kleisli.mk m (α : Type u) : Kleisli m :=
  α

-- failed to format: format: uncaught backtrack exception
instance
  Kleisli.category_struct
  { m } [ Monadₓ .{ u , v } m ] : category_struct ( Kleisli m )
  where Hom α β := α → m β id α x := pure x comp X Y Z f g := f >=> g

instance Kleisli.category {m} [Monadₓ.{u, v} m] [IsLawfulMonad m] : category (Kleisli m) := by
  refine' { id_comp' := _, comp_id' := _, assoc' := _ } <;>
    intros <;> ext <;> unfold_projs <;> simp' only [· >=> ·] with functor_norm

@[simp]
theorem Kleisli.id_def {m} [Monadₓ m] (α : Kleisli m) : 𝟙 α = @pure m _ α :=
  rfl

theorem Kleisli.comp_def {m} [Monadₓ m] (α β γ : Kleisli m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    (xs ≫ ys) a = xs a >>= ys :=
  rfl

instance : Inhabited (Kleisli id) :=
  ⟨PUnit⟩

instance {α : Type u} [Inhabited α] : Inhabited (Kleisli.mk id α) :=
  ⟨(default α : _)⟩

end CategoryTheory

