import Mathbin.CategoryTheory.Monoidal.Functor
import Mathbin.CategoryTheory.Functorial

/-!
# Unbundled lax monoidal functors

## Design considerations
The essential problem I've encountered that requires unbundled functors is
having an existing (non-monoidal) functor `F : C ⥤ D` between monoidal categories,
and wanting to assert that it has an extension to a lax monoidal functor.

The two options seem to be
1. Construct a separate `F' : lax_monoidal_functor C D`,
   and assert `F'.to_functor ≅ F`.
2. Introduce unbundled functors and unbundled lax monoidal functors,
   and construct `lax_monoidal F.obj`, then construct `F' := lax_monoidal_functor.of F.obj`.

Both have costs, but as for option 2. the cost is in library design,
while in option 1. the cost is users having to carry around additional isomorphisms forever,
I wanted to introduce unbundled functors.

TODO:
later, we may want to do this for strong monoidal functors as well,
but the immediate application, for enriched categories, only requires this notion.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

/-- An unbundled description of lax monoidal functors. -/
class lax_monoidal (F : C → D) [Functorial.{v₁, v₂} F] where
  ε {} : 𝟙_ D ⟶ F (𝟙_ C)
  μ {} : ∀ X Y : C, F X ⊗ F Y ⟶ F (X ⊗ Y)
  μ_natural' : ∀ {X Y X' Y' : C} f : X ⟶ Y g : X' ⟶ Y', (map F f ⊗ map F g) ≫ μ Y Y' = μ X X' ≫ map F (f ⊗ g) := by
    run_tac
      obviously
  associativity' :
    ∀ X Y Z : C,
      (μ X Y ⊗ 𝟙 (F Z)) ≫ μ (X ⊗ Y) Z ≫ map F (α_ X Y Z).Hom =
        (α_ (F X) (F Y) (F Z)).Hom ≫ (𝟙 (F X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) := by
    run_tac
      obviously
  left_unitality' : ∀ X : C, (λ_ (F X)).Hom = (ε ⊗ 𝟙 (F X)) ≫ μ (𝟙_ C) X ≫ map F (λ_ X).Hom := by
    run_tac
      obviously
  right_unitality' : ∀ X : C, (ρ_ (F X)).Hom = (𝟙 (F X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ map F (ρ_ X).Hom := by
    run_tac
      obviously

restate_axiom lax_monoidal.μ_natural'

attribute [simp] lax_monoidal.μ_natural

restate_axiom lax_monoidal.left_unitality'

restate_axiom lax_monoidal.right_unitality'

restate_axiom lax_monoidal.associativity'

attribute [simp] lax_monoidal.associativity

namespace LaxMonoidalFunctor

/-- Construct a bundled `lax_monoidal_functor` from the object level function
and `functorial` and `lax_monoidal` typeclasses.
-/
@[simps]
def of (F : C → D) [I₁ : Functorial.{v₁, v₂} F] [I₂ : LaxMonoidal.{v₁, v₂} F] : LaxMonoidalFunctor.{v₁, v₂} C D :=
  { I₁, I₂ with obj := F }

end LaxMonoidalFunctor

instance (F : LaxMonoidalFunctor.{v₁, v₂} C D) : LaxMonoidal.{v₁, v₂} F.obj :=
  { F with }

section

instance lax_monoidal_id : LaxMonoidal.{v₁, v₁} (id : C → C) where
  ε := 𝟙 _
  μ := fun X Y => 𝟙 _

end

end CategoryTheory

