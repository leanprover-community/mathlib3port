import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts 
import Mathbin.CategoryTheory.Limits.Shapes.Terminal 
import Mathbin.CategoryTheory.Subobject.MonoOver

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally cartesian closed category, every subobject lattice
  is cartesian closed (equivalently, a Heyting algebra).

-/


universe v₁ v₂ u₁ u₂

noncomputable theory

namespace CategoryTheory

open Limits Category

variable{C : Type u₁}[category.{v₁} C]{A : C}

/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
def is_subterminal (A : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g

theorem is_subterminal.def : is_subterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g :=
  Iff.rfl

/--
If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_is_terminal_from`.
-/
theorem is_subterminal.mono_is_terminal_from (hA : is_subterminal A) {T : C} (hT : is_terminal T) : mono (hT.from A) :=
  { right_cancellation := fun Z g h _ => hA _ _ }

/--
If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `is_subterminal_of_mono_terminal_from`.
-/
theorem is_subterminal.mono_terminal_from [has_terminal C] (hA : is_subterminal A) : mono (terminal.from A) :=
  hA.mono_is_terminal_from terminal_is_terminal

/--
If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_is_terminal_from`.
-/
theorem is_subterminal_of_mono_is_terminal_from {T : C} (hT : is_terminal T) [mono (hT.from A)] : is_subterminal A :=
  fun Z f g =>
    by 
      rw [←cancel_mono (hT.from A)]
      apply hT.hom_ext

/--
If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `is_subterminal.mono_terminal_from`.
-/
theorem is_subterminal_of_mono_terminal_from [has_terminal C] [mono (terminal.from A)] : is_subterminal A :=
  fun Z f g =>
    by 
      rw [←cancel_mono (terminal.from A)]
      apply Subsingleton.elimₓ

theorem is_subterminal_of_is_terminal {T : C} (hT : is_terminal T) : is_subterminal T :=
  fun Z f g => hT.hom_ext _ _

theorem is_subterminal_of_terminal [has_terminal C] : is_subterminal (⊤_ C) :=
  fun Z f g => Subsingleton.elimₓ _ _

/--
If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `is_subterminal_of_is_iso_diag`.
-/
theorem is_subterminal.is_iso_diag (hA : is_subterminal A) [has_binary_product A A] : is_iso (diag A) :=
  ⟨⟨limits.prod.fst,
      ⟨by 
          simp ,
        by 
          rw [is_subterminal.def] at hA 
          tidy⟩⟩⟩

-- error in CategoryTheory.Subterminal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `is_subterminal.is_iso_diag`.
-/ theorem is_subterminal_of_is_iso_diag [has_binary_product A A] [is_iso (diag A)] : is_subterminal A :=
λ Z f g, begin
  have [] [":", expr «expr = »((limits.prod.fst : «expr ⟶ »(«expr ⨯ »(A, A), _)), limits.prod.snd)] [],
  { simp [] [] [] ["[", "<-", expr cancel_epi (diag A), "]"] [] [] },
  rw ["[", "<-", expr prod.lift_fst f g, ",", expr this, ",", expr prod.lift_snd, "]"] []
end

-- error in CategoryTheory.Subterminal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps #[]]
def is_subterminal.iso_diag (hA : is_subterminal A) [has_binary_product A A] : «expr ≅ »(«expr ⨯ »(A, A), A) :=
begin
  letI [] [] [":=", expr is_subterminal.is_iso_diag hA],
  apply [expr (as_iso (diag A)).symm]
end

variable(C)

-- error in CategoryTheory.Subterminal: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/--
The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/ @[derive #[expr category]] def subterminals (C : Type u₁) [category.{v₁} C] :=
{A : C // is_subterminal A}

instance  [has_terminal C] : Inhabited (subterminals C) :=
  ⟨⟨⊤_ C, is_subterminal_of_terminal⟩⟩

-- error in CategoryTheory.Subterminal: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler full
/-- The inclusion of the subterminal objects into the original category. -/
@[derive #["[", expr full, ",", expr faithful, "]"], simps #[]]
def subterminal_inclusion : «expr ⥤ »(subterminals C, C) :=
full_subcategory_inclusion _

instance subterminals_thin (X Y : subterminals C) : Subsingleton (X ⟶ Y) :=
  ⟨fun f g => Y.2 f g⟩

/--
The category of subterminal objects is equivalent to the category of monomorphisms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
@[simps]
def subterminals_equiv_mono_over_terminal [has_terminal C] : subterminals C ≌ mono_over (⊤_ C) :=
  { Functor :=
      { obj := fun X => ⟨over.mk (terminal.from X.1), X.2.mono_terminal_from⟩,
        map :=
          fun X Y f =>
            mono_over.hom_mk f
              (by 
                ext1 ⟨⟩) },
    inverse :=
      { obj :=
          fun X =>
            ⟨X.val.left,
              fun Z f g =>
                by 
                  rw [←cancel_mono X.arrow]
                  apply Subsingleton.elimₓ⟩,
        map := fun X Y f => f.1 },
    unitIso := { Hom := { app := fun X => 𝟙 _ }, inv := { app := fun X => 𝟙 _ } },
    counitIso := { Hom := { app := fun X => over.hom_mk (𝟙 _) }, inv := { app := fun X => over.hom_mk (𝟙 _) } } }

@[simp]
theorem subterminals_to_mono_over_terminal_comp_forget [has_terminal C] :
  (subterminals_equiv_mono_over_terminal C).Functor ⋙ mono_over.forget _ ⋙ over.forget _ = subterminal_inclusion C :=
  rfl

@[simp]
theorem mono_over_terminal_to_subterminals_comp [has_terminal C] :
  (subterminals_equiv_mono_over_terminal C).inverse ⋙ subterminal_inclusion C = mono_over.forget _ ⋙ over.forget _ :=
  rfl

end CategoryTheory

