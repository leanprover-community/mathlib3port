import Mathbin.CategoryTheory.Adjunction.Basic 
import Mathbin.CategoryTheory.Adjunction.Comma 
import Mathbin.CategoryTheory.Limits.Constructions.WeaklyInitial 
import Mathbin.CategoryTheory.Limits.Preserves.Basic 
import Mathbin.CategoryTheory.Limits.Creates 
import Mathbin.CategoryTheory.Limits.Comma 
import Mathbin.CategoryTheory.Punit

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint: `is_right_adjoint_of_preserves_limits_of_solution_set_condition`.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition, see `solution_set_condition_of_is_right_adjoint`
(the file `category_theory/adjunction/limits` already shows it preserves limits).

We define the *solution set condition* for the functor `G : D ⥤ C` to mean, for every object
`A : C`, there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X`
factors through one of the `f_i`.

-/


universe v u

namespace CategoryTheory

open Limits

variable{J : Type v}

variable{C : Type u}[category.{v} C]

/--
The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
def solution_set_condition {D : Type u} [category.{v} D] (G : D ⥤ C) : Prop :=
  ∀ A : C,
    ∃ (ι : Type v)(B : ι → D)(f : ∀ i : ι, A ⟶ G.obj (B i)),
      ∀ X h : A ⟶ G.obj X, ∃ (i : ι)(g : B i ⟶ X), f i ≫ G.map g = h

variable{D : Type u}[category.{v} D]

section GeneralAdjointFunctorTheorem

variable(G : D ⥤ C)

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition.  -/
theorem solution_set_condition_of_is_right_adjoint [is_right_adjoint G] : solution_set_condition G :=
  by 
    intro A 
    refine' ⟨PUnit, fun _ => (left_adjoint G).obj A, fun _ => (adjunction.of_right_adjoint G).Unit.app A, _⟩
    intro B h 
    refine' ⟨PUnit.unit, ((adjunction.of_right_adjoint G).homEquiv _ _).symm h, _⟩
    rw [←adjunction.hom_equiv_unit, Equiv.apply_symm_apply]

-- error in CategoryTheory.Adjunction.AdjointFunctorTheorems: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
if `G` satisfies the solution set condition then `G` is a right adjoint.
-/
noncomputable
def is_right_adjoint_of_preserves_limits_of_solution_set_condition
[has_limits D]
[preserves_limits G]
(hG : solution_set_condition G) : is_right_adjoint G :=
begin
  apply [expr is_right_adjoint_of_structured_arrow_initials _],
  intro [ident A],
  specialize [expr hG A],
  choose [] [ident ι] [ident B, ident f, ident g] ["using", expr hG],
  let [ident B'] [":", expr ι → structured_arrow A G] [":=", expr λ i, structured_arrow.mk (f i)],
  have [ident hB'] [":", expr ∀ A' : structured_arrow A G, «expr∃ , »((i), nonempty «expr ⟶ »(B' i, A'))] [],
  { intros [ident A'],
    obtain ["⟨", ident i, ",", "_", ",", ident t, "⟩", ":=", expr g _ A'.hom],
    exact [expr ⟨i, ⟨structured_arrow.hom_mk _ t⟩⟩] },
  obtain ["⟨", ident T, ",", ident hT, "⟩", ":=", expr has_weakly_initial_of_weakly_initial_set_and_has_products hB'],
  apply [expr has_initial_of_weakly_initial_and_has_wide_equalizers hT]
end

end GeneralAdjointFunctorTheorem

end CategoryTheory

