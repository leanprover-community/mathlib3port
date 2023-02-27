/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.functorial
! leanprover-community/mathlib commit 73dd4b5411ec8fafb18a9d77c9c826907730af80
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Functor
import Mathbin.CategoryTheory.Functor.Functorial

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

#print CategoryTheory.LaxMonoidal /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`ε] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`μ] [] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- Perhaps in the future we'll redefine `lax_monoidal_functor` in terms of this,
-- but that isn't the immediate plan.
/-- An unbundled description of lax monoidal functors. -/
class LaxMonoidal (F : C → D) [Functorial.{v₁, v₂} F] where
  -- unit morphism
  ε : 𝟙_ D ⟶ F (𝟙_ C)
  -- tensorator
  μ : ∀ X Y : C, F X ⊗ F Y ⟶ F (X ⊗ Y)
  μ_natural' :
    ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
      (map F f ⊗ map F g) ≫ μ Y Y' = μ X X' ≫ map F (f ⊗ g) := by
    obviously
  -- associativity of the tensorator
  associativity' :
    ∀ X Y Z : C,
      (μ X Y ⊗ 𝟙 (F Z)) ≫ μ (X ⊗ Y) Z ≫ map F (α_ X Y Z).Hom =
        (α_ (F X) (F Y) (F Z)).Hom ≫ (𝟙 (F X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) := by
    obviously
  -- unitality
  left_unitality' : ∀ X : C, (λ_ (F X)).Hom = (ε ⊗ 𝟙 (F X)) ≫ μ (𝟙_ C) X ≫ map F (λ_ X).Hom := by
    obviously
  right_unitality' : ∀ X : C, (ρ_ (F X)).Hom = (𝟙 (F X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ map F (ρ_ X).Hom := by
    obviously
#align category_theory.lax_monoidal CategoryTheory.LaxMonoidal
-/

restate_axiom lax_monoidal.μ_natural'

attribute [simp] lax_monoidal.μ_natural

restate_axiom lax_monoidal.left_unitality'

restate_axiom lax_monoidal.right_unitality'

-- The unitality axioms cannot be used as simp lemmas because they require
-- higher-order matching to figure out the `F` and `X` from `F X`.
restate_axiom lax_monoidal.associativity'

attribute [simp] lax_monoidal.associativity

namespace LaxMonoidalFunctor

#print CategoryTheory.LaxMonoidalFunctor.of /-
/-- Construct a bundled `lax_monoidal_functor` from the object level function
and `functorial` and `lax_monoidal` typeclasses.
-/
@[simps]
def of (F : C → D) [I₁ : Functorial.{v₁, v₂} F] [I₂ : LaxMonoidal.{v₁, v₂} F] :
    LaxMonoidalFunctor.{v₁, v₂} C D :=
  { I₁, I₂ with obj := F }
#align category_theory.lax_monoidal_functor.of CategoryTheory.LaxMonoidalFunctor.of
-/

end LaxMonoidalFunctor

instance (F : LaxMonoidalFunctor.{v₁, v₂} C D) : LaxMonoidal.{v₁, v₂} F.obj :=
  { F with }

section

#print CategoryTheory.laxMonoidalId /-
instance laxMonoidalId : LaxMonoidal.{v₁, v₁} (id : C → C)
    where
  ε := 𝟙 _
  μ X Y := 𝟙 _
#align category_theory.lax_monoidal_id CategoryTheory.laxMonoidalId
-/

end

-- TODO instances for composition, as required
-- TODO `strong_monoidal`, as well as `lax_monoidal`
end CategoryTheory

