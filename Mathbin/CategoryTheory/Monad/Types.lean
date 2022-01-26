import Mathbin.CategoryTheory.Monad.Basic
import Mathbin.CategoryTheory.Monad.Kleisli
import Mathbin.CategoryTheory.Category.Kleisli
import Mathbin.CategoryTheory.Types

/-!

# Convert from `monad` (i.e. Lean's `Type`-based monads) to `category_theory.monad`

This allows us to use these monads in category theory.

-/


namespace CategoryTheory

section

universe u

variable (m : Type u → Type u) [_root_.monad m] [IsLawfulMonad m]

/-- A lawful `control.monad` gives a category theory `monad` on the category of types.
-/
@[simps]
def of_type_monad : Monadₓ (Type u) where
  toFunctor := of_type_functor m
  η' := ⟨@pure m _, fun α β f => (IsLawfulApplicative.map_comp_pure f).symm⟩
  μ' := ⟨@mjoin m _, fun α β f : α → β => funext fun a => mjoin_map_map f a⟩
  assoc' := fun α => funext fun a => mjoin_map_mjoin a
  left_unit' := fun α => funext fun a => mjoin_pure a
  right_unit' := fun α => funext fun a => mjoin_map_pure a

/-- The `Kleisli` category of a `control.monad` is equivalent to the `kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simps]
def Eq : Kleisli m ≌ kleisli (of_type_monad m) where
  Functor :=
    { obj := fun X => X, map := fun X Y f => f, map_id' := fun X => rfl,
      map_comp' := fun X Y Z f g => by
        unfold_projs
        ext
        dsimp
        simp [mjoin, seq_bind_eq] }
  inverse :=
    { obj := fun X => X, map := fun X Y f => f, map_id' := fun X => rfl,
      map_comp' := fun X Y Z f g => by
        unfold_projs
        ext
        dsimp
        simp [mjoin, seq_bind_eq] }
  unitIso := by
    refine' nat_iso.of_components (fun X => iso.refl X) fun X Y f => _
    change f >=> pure = pure >=> f
    simp' with functor_norm
  counitIso :=
    nat_iso.of_components (fun X => iso.refl X) fun X Y f => by
      tidy

end

end CategoryTheory

