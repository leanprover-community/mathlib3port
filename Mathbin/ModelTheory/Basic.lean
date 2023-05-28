/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn

! This file was ported from Lean 3 source module model_theory.basic
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.VecNotation
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Basics on First-Order Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.elementary_embedding`, denoted `M ↪ₑ[L] N`, is an embedding from the
  `L`-structure `M` to the `L`-structure `N` that commutes with the realizations of all formulas.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## TODO

Use `[countable L.symbols]` instead of `[L.countable]`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v u' v' w w'

open Cardinal

open Cardinal

namespace FirstOrder

/-! ### Languages and Structures -/


#print FirstOrder.Language /-
-- intended to be used with explicit universe parameters
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint check_univs]
structure Language where
  Functions : ℕ → Type u
  Relations : ℕ → Type v
#align first_order.language FirstOrder.Language
-/

#print FirstOrder.Sequence₂ /-
/-- Used to define `first_order.language₂`. -/
@[simp]
def Sequence₂ (a₀ a₁ a₂ : Type u) : ℕ → Type u
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | _ => PEmpty
#align first_order.sequence₂ FirstOrder.Sequence₂
-/

namespace Sequence₂

variable (a₀ a₁ a₂ : Type u)

#print FirstOrder.Sequence₂.inhabited₀ /-
instance inhabited₀ [h : Inhabited a₀] : Inhabited (Sequence₂ a₀ a₁ a₂ 0) :=
  h
#align first_order.sequence₂.inhabited₀ FirstOrder.Sequence₂.inhabited₀
-/

#print FirstOrder.Sequence₂.inhabited₁ /-
instance inhabited₁ [h : Inhabited a₁] : Inhabited (Sequence₂ a₀ a₁ a₂ 1) :=
  h
#align first_order.sequence₂.inhabited₁ FirstOrder.Sequence₂.inhabited₁
-/

#print FirstOrder.Sequence₂.inhabited₂ /-
instance inhabited₂ [h : Inhabited a₂] : Inhabited (Sequence₂ a₀ a₁ a₂ 2) :=
  h
#align first_order.sequence₂.inhabited₂ FirstOrder.Sequence₂.inhabited₂
-/

instance {n : ℕ} : IsEmpty (Sequence₂ a₀ a₁ a₂ (n + 3)) :=
  PEmpty.isEmpty

#print FirstOrder.Sequence₂.lift_mk /-
@[simp]
theorem lift_mk {i : ℕ} :
    Cardinal.lift (#Sequence₂ a₀ a₁ a₂ i) = (#Sequence₂ (ULift a₀) (ULift a₁) (ULift a₂) i) := by
  rcases i with (_ | _ | _ | i) <;>
    simp only [sequence₂, mk_ulift, mk_fintype, Fintype.card_of_isEmpty, Nat.cast_zero, lift_zero]
#align first_order.sequence₂.lift_mk FirstOrder.Sequence₂.lift_mk
-/

/- warning: first_order.sequence₂.sum_card -> FirstOrder.Sequence₂.sum_card is a dubious translation:
lean 3 declaration is
  forall (a₀ : Type.{u1}) (a₁ : Type.{u1}) (a₂ : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.sum.{0, u1} Nat (fun (i : Nat) => Cardinal.mk.{u1} (FirstOrder.Sequence₂.{u1} a₀ a₁ a₂ i))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} a₀) (Cardinal.mk.{u1} a₁)) (Cardinal.mk.{u1} a₂))
but is expected to have type
  forall (a₀ : Type.{u1}) (a₁ : Type.{u1}) (a₂ : Type.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.sum.{0, u1} Nat (fun (i : Nat) => Cardinal.mk.{u1} (FirstOrder.Sequence₂.{u1} a₀ a₁ a₂ i))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} a₀) (Cardinal.mk.{u1} a₁)) (Cardinal.mk.{u1} a₂))
Case conversion may be inaccurate. Consider using '#align first_order.sequence₂.sum_card FirstOrder.Sequence₂.sum_cardₓ'. -/
@[simp]
theorem sum_card : (Cardinal.sum fun i => #Sequence₂ a₀ a₁ a₂ i) = (#a₀) + (#a₁) + (#a₂) :=
  by
  rw [sum_nat_eq_add_sum_succ, sum_nat_eq_add_sum_succ, sum_nat_eq_add_sum_succ]
  simp [add_assoc]
#align first_order.sequence₂.sum_card FirstOrder.Sequence₂.sum_card

end Sequence₂

namespace Language

#print FirstOrder.Language.mk₂ /-
/-- A constructor for languages with only constants, unary and binary functions, and
unary and binary relations. -/
@[simps]
protected def mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) : Language :=
  ⟨Sequence₂ c f₁ f₂, Sequence₂ PEmpty r₁ r₂⟩
#align first_order.language.mk₂ FirstOrder.Language.mk₂
-/

#print FirstOrder.Language.empty /-
/-- The empty language has no symbols. -/
protected def empty : Language :=
  ⟨fun _ => Empty, fun _ => Empty⟩
#align first_order.language.empty FirstOrder.Language.empty
-/

instance : Inhabited Language :=
  ⟨Language.empty⟩

#print FirstOrder.Language.sum /-
/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum (L : Language.{u, v}) (L' : Language.{u', v'}) : Language :=
  ⟨fun n => Sum (L.Functions n) (L'.Functions n), fun n => Sum (L.Relations n) (L'.Relations n)⟩
#align first_order.language.sum FirstOrder.Language.sum
-/

variable (L : Language.{u, v})

#print FirstOrder.Language.Constants /-
/-- The type of constants in a given language. -/
@[nolint has_nonempty_instance]
protected def Constants :=
  L.Functions 0
#align first_order.language.constants FirstOrder.Language.Constants
-/

#print FirstOrder.Language.constants_mk₂ /-
@[simp]
theorem constants_mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).Constants = c :=
  rfl
#align first_order.language.constants_mk₂ FirstOrder.Language.constants_mk₂
-/

#print FirstOrder.Language.Symbols /-
/-- The type of symbols in a given language. -/
@[nolint has_nonempty_instance]
def Symbols :=
  Sum (Σl, L.Functions l) (Σl, L.Relations l)
#align first_order.language.symbols FirstOrder.Language.Symbols
-/

#print FirstOrder.Language.card /-
/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : Cardinal :=
  #L.Symbols
#align first_order.language.card FirstOrder.Language.card
-/

#print FirstOrder.Language.IsRelational /-
/-- A language is relational when it has no function symbols. -/
class IsRelational : Prop where
  empty_functions : ∀ n, IsEmpty (L.Functions n)
#align first_order.language.is_relational FirstOrder.Language.IsRelational
-/

#print FirstOrder.Language.IsAlgebraic /-
/-- A language is algebraic when it has no relation symbols. -/
class IsAlgebraic : Prop where
  empty_relations : ∀ n, IsEmpty (L.Relations n)
#align first_order.language.is_algebraic FirstOrder.Language.IsAlgebraic
-/

variable {L} {L' : Language.{u', v'}}

/- warning: first_order.language.card_eq_card_functions_add_card_relations -> FirstOrder.Language.card_eq_card_functions_add_card_relations is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}}, Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (FirstOrder.Language.card.{u1, u2} L) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.sum.{0, max u1 u2} Nat (fun (l : Nat) => Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} (FirstOrder.Language.Functions.{u1, u2} L l)))) (Cardinal.sum.{0, max u2 u1} Nat (fun (l : Nat) => Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} (FirstOrder.Language.Relations.{u1, u2} L l)))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}}, Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (FirstOrder.Language.card.{u1, u2} L) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.{max u1 u2} Cardinal.{max u2 u1} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.sum.{0, max u2 u1} Nat (fun (l : Nat) => Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} (FirstOrder.Language.Functions.{u1, u2} L l)))) (Cardinal.sum.{0, max u1 u2} Nat (fun (l : Nat) => Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} (FirstOrder.Language.Relations.{u1, u2} L l)))))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_eq_card_functions_add_card_relations FirstOrder.Language.card_eq_card_functions_add_card_relationsₓ'. -/
theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} (#L.Functions l)) +
        Cardinal.sum fun l => Cardinal.lift.{u} (#L.Relations l) :=
  by simp [card, symbols]
#align first_order.language.card_eq_card_functions_add_card_relations FirstOrder.Language.card_eq_card_functions_add_card_relations

instance [L.IsRelational] {n : ℕ} : IsEmpty (L.Functions n) :=
  IsRelational.empty_functions n

instance [L.IsAlgebraic] {n : ℕ} : IsEmpty (L.Relations n) :=
  IsAlgebraic.empty_relations n

#print FirstOrder.Language.isRelational_of_empty_functions /-
instance isRelational_of_empty_functions {symb : ℕ → Type _} :
    IsRelational ⟨fun _ => Empty, symb⟩ :=
  ⟨fun _ => Empty.isEmpty⟩
#align first_order.language.is_relational_of_empty_functions FirstOrder.Language.isRelational_of_empty_functions
-/

#print FirstOrder.Language.isAlgebraic_of_empty_relations /-
instance isAlgebraic_of_empty_relations {symb : ℕ → Type _} : IsAlgebraic ⟨symb, fun _ => Empty⟩ :=
  ⟨fun _ => Empty.isEmpty⟩
#align first_order.language.is_algebraic_of_empty_relations FirstOrder.Language.isAlgebraic_of_empty_relations
-/

#print FirstOrder.Language.isRelational_empty /-
instance isRelational_empty : IsRelational Language.empty :=
  Language.isRelational_of_empty_functions
#align first_order.language.is_relational_empty FirstOrder.Language.isRelational_empty
-/

#print FirstOrder.Language.isAlgebraic_empty /-
instance isAlgebraic_empty : IsAlgebraic Language.empty :=
  Language.isAlgebraic_of_empty_relations
#align first_order.language.is_algebraic_empty FirstOrder.Language.isAlgebraic_empty
-/

#print FirstOrder.Language.isRelational_sum /-
instance isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.Sum L') :=
  ⟨fun n => Sum.isEmpty⟩
#align first_order.language.is_relational_sum FirstOrder.Language.isRelational_sum
-/

#print FirstOrder.Language.isAlgebraic_sum /-
instance isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.Sum L') :=
  ⟨fun n => Sum.isEmpty⟩
#align first_order.language.is_algebraic_sum FirstOrder.Language.isAlgebraic_sum
-/

#print FirstOrder.Language.isRelational_mk₂ /-
instance isRelational_mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h0 : IsEmpty c] [h1 : IsEmpty f₁]
    [h2 : IsEmpty f₂] : IsRelational (Language.mk₂ c f₁ f₂ r₁ r₂) :=
  ⟨fun n =>
    Nat.casesOn n h0 fun n => Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => PEmpty.isEmpty⟩
#align first_order.language.is_relational_mk₂ FirstOrder.Language.isRelational_mk₂
-/

#print FirstOrder.Language.isAlgebraic_mk₂ /-
instance isAlgebraic_mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h1 : IsEmpty r₁] [h2 : IsEmpty r₂] :
    IsAlgebraic (Language.mk₂ c f₁ f₂ r₁ r₂) :=
  ⟨fun n =>
    Nat.casesOn n PEmpty.isEmpty fun n =>
      Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun _ => PEmpty.isEmpty⟩
#align first_order.language.is_algebraic_mk₂ FirstOrder.Language.isAlgebraic_mk₂
-/

#print FirstOrder.Language.subsingleton_mk₂_functions /-
instance subsingleton_mk₂_functions {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h0 : Subsingleton c]
    [h1 : Subsingleton f₁] [h2 : Subsingleton f₂] {n : ℕ} :
    Subsingleton ((Language.mk₂ c f₁ f₂ r₁ r₂).Functions n) :=
  Nat.casesOn n h0 fun n =>
    Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun n => ⟨fun x => PEmpty.elim x⟩
#align first_order.language.subsingleton_mk₂_functions FirstOrder.Language.subsingleton_mk₂_functions
-/

#print FirstOrder.Language.subsingleton_mk₂_relations /-
instance subsingleton_mk₂_relations {c f₁ f₂ : Type u} {r₁ r₂ : Type v} [h1 : Subsingleton r₁]
    [h2 : Subsingleton r₂] {n : ℕ} : Subsingleton ((Language.mk₂ c f₁ f₂ r₁ r₂).Relations n) :=
  Nat.casesOn n ⟨fun x => PEmpty.elim x⟩ fun n =>
    Nat.casesOn n h1 fun n => Nat.casesOn n h2 fun n => ⟨fun x => PEmpty.elim x⟩
#align first_order.language.subsingleton_mk₂_relations FirstOrder.Language.subsingleton_mk₂_relations
-/

#print FirstOrder.Language.empty_card /-
@[simp]
theorem empty_card : Language.empty.card = 0 := by simp [card_eq_card_functions_add_card_relations]
#align first_order.language.empty_card FirstOrder.Language.empty_card
-/

#print FirstOrder.Language.isEmpty_empty /-
instance isEmpty_empty : IsEmpty Language.empty.Symbols :=
  by
  simp only [language.symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩
#align first_order.language.is_empty_empty FirstOrder.Language.isEmpty_empty
-/

#print FirstOrder.Language.Countable.countable_functions /-
instance Countable.countable_functions [h : Countable L.Symbols] : Countable (Σl, L.Functions l) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective
#align first_order.language.countable.countable_functions FirstOrder.Language.Countable.countable_functions
-/

/- warning: first_order.language.card_functions_sum -> FirstOrder.Language.card_functions_sum is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (i : Nat), Eq.{succ (succ (max u1 u3))} Cardinal.{max u1 u3} (Cardinal.mk.{max u1 u3} (FirstOrder.Language.Functions.{max u1 u3, max u2 u4} (FirstOrder.Language.sum.{u1, u2, u3, u4} L L') i)) (HAdd.hAdd.{succ (max u1 u3), succ (max u1 u3), succ (max u1 u3)} Cardinal.{max u1 u3} Cardinal.{max u1 u3} Cardinal.{max u1 u3} (instHAdd.{succ (max u1 u3)} Cardinal.{max u1 u3} Cardinal.hasAdd.{max u1 u3}) (Cardinal.lift.{u3, u1} (Cardinal.mk.{u1} (FirstOrder.Language.Functions.{u1, u2} L i))) (Cardinal.lift.{u1, u3} (Cardinal.mk.{u3} (FirstOrder.Language.Functions.{u3, u4} L' i))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (i : Nat), Eq.{max (succ (succ u1)) (succ (succ u3))} Cardinal.{max u1 u3} (Cardinal.mk.{max u1 u3} (FirstOrder.Language.Functions.{max u1 u3, max u2 u4} (FirstOrder.Language.sum.{u1, u2, u3, u4} L L') i)) (HAdd.hAdd.{max (succ u1) (succ u3), max (succ u1) (succ u3), max (succ u1) (succ u3)} Cardinal.{max u1 u3} Cardinal.{max u3 u1} Cardinal.{max u1 u3} (instHAdd.{max (succ u1) (succ u3)} Cardinal.{max u1 u3} Cardinal.instAddCardinal.{max u1 u3}) (Cardinal.lift.{u3, u1} (Cardinal.mk.{u1} (FirstOrder.Language.Functions.{u1, u2} L i))) (Cardinal.lift.{u1, u3} (Cardinal.mk.{u3} (FirstOrder.Language.Functions.{u3, u4} L' i))))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_functions_sum FirstOrder.Language.card_functions_sumₓ'. -/
@[simp]
theorem card_functions_sum (i : ℕ) :
    (#(L.Sum L').Functions i) = (#L.Functions i).lift + Cardinal.lift.{u} (#L'.Functions i) := by
  simp [language.sum]
#align first_order.language.card_functions_sum FirstOrder.Language.card_functions_sum

/- warning: first_order.language.card_relations_sum -> FirstOrder.Language.card_relations_sum is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (i : Nat), Eq.{succ (succ (max u2 u4))} Cardinal.{max u2 u4} (Cardinal.mk.{max u2 u4} (FirstOrder.Language.Relations.{max u1 u3, max u2 u4} (FirstOrder.Language.sum.{u1, u2, u3, u4} L L') i)) (HAdd.hAdd.{succ (max u2 u4), succ (max u2 u4), succ (max u2 u4)} Cardinal.{max u2 u4} Cardinal.{max u2 u4} Cardinal.{max u2 u4} (instHAdd.{succ (max u2 u4)} Cardinal.{max u2 u4} Cardinal.hasAdd.{max u2 u4}) (Cardinal.lift.{u4, u2} (Cardinal.mk.{u2} (FirstOrder.Language.Relations.{u1, u2} L i))) (Cardinal.lift.{u2, u4} (Cardinal.mk.{u4} (FirstOrder.Language.Relations.{u3, u4} L' i))))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}} (i : Nat), Eq.{max (succ (succ u2)) (succ (succ u4))} Cardinal.{max u2 u4} (Cardinal.mk.{max u2 u4} (FirstOrder.Language.Relations.{max u1 u3, max u2 u4} (FirstOrder.Language.sum.{u1, u2, u3, u4} L L') i)) (HAdd.hAdd.{max (succ u2) (succ u4), max (succ u2) (succ u4), max (succ u2) (succ u4)} Cardinal.{max u2 u4} Cardinal.{max u4 u2} Cardinal.{max u2 u4} (instHAdd.{max (succ u2) (succ u4)} Cardinal.{max u2 u4} Cardinal.instAddCardinal.{max u2 u4}) (Cardinal.lift.{u4, u2} (Cardinal.mk.{u2} (FirstOrder.Language.Relations.{u1, u2} L i))) (Cardinal.lift.{u2, u4} (Cardinal.mk.{u4} (FirstOrder.Language.Relations.{u3, u4} L' i))))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_relations_sum FirstOrder.Language.card_relations_sumₓ'. -/
@[simp]
theorem card_relations_sum (i : ℕ) :
    (#(L.Sum L').Relations i) = (#L.Relations i).lift + Cardinal.lift.{v} (#L'.Relations i) := by
  simp [language.sum]
#align first_order.language.card_relations_sum FirstOrder.Language.card_relations_sum

/- warning: first_order.language.card_sum -> FirstOrder.Language.card_sum is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}}, Eq.{succ (succ (max (max u1 u3) u2 u4))} Cardinal.{max (max u1 u3) u2 u4} (FirstOrder.Language.card.{max u1 u3, max u2 u4} (FirstOrder.Language.sum.{u1, u2, u3, u4} L L')) (HAdd.hAdd.{succ (max (max u1 u3) u2 u4), succ (max (max u1 u3) u2 u4), succ (max (max u1 u3) u2 u4)} Cardinal.{max (max u1 u3) u2 u4} Cardinal.{max (max u1 u3) u2 u4} Cardinal.{max (max u1 u3) u2 u4} (instHAdd.{succ (max (max u1 u3) u2 u4)} Cardinal.{max (max u1 u3) u2 u4} Cardinal.hasAdd.{max (max u1 u3) u2 u4}) (Cardinal.lift.{max u3 u4, max u1 u2} (FirstOrder.Language.card.{u1, u2} L)) (Cardinal.lift.{max u1 u2, max u3 u4} (FirstOrder.Language.card.{u3, u4} L')))
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {L' : FirstOrder.Language.{u3, u4}}, Eq.{max (max (max (succ (succ u1)) (succ (succ u3))) (succ (succ u2))) (succ (succ u4))} Cardinal.{max (max u1 u3) u2 u4} (FirstOrder.Language.card.{max u1 u3, max u2 u4} (FirstOrder.Language.sum.{u1, u2, u3, u4} L L')) (HAdd.hAdd.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4), max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4), max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} Cardinal.{max (max u1 u2) u3 u4} Cardinal.{max (max u3 u4) u1 u2} Cardinal.{max (max u1 u2) u3 u4} (instHAdd.{max (max (max (succ u1) (succ u3)) (succ u2)) (succ u4)} Cardinal.{max (max u1 u2) u3 u4} Cardinal.instAddCardinal.{max (max (max u1 u3) u2) u4}) (Cardinal.lift.{max u3 u4, max u1 u2} (FirstOrder.Language.card.{u1, u2} L)) (Cardinal.lift.{max u1 u2, max u3 u4} (FirstOrder.Language.card.{u3, u4} L')))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_sum FirstOrder.Language.card_sumₓ'. -/
@[simp]
theorem card_sum :
    (L.Sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card :=
  by
  simp only [card_eq_card_functions_add_card_relations, card_functions_sum, card_relations_sum,
    sum_add_distrib', lift_add, lift_sum, lift_lift]
  rw [add_assoc, ← add_assoc (Cardinal.sum fun i => (#L'.functions i).lift),
    add_comm (Cardinal.sum fun i => (#L'.functions i).lift), add_assoc, add_assoc]
#align first_order.language.card_sum FirstOrder.Language.card_sum

/- warning: first_order.language.card_mk₂ -> FirstOrder.Language.card_mk₂ is a dubious translation:
lean 3 declaration is
  forall (c : Type.{u1}) (f₁ : Type.{u1}) (f₂ : Type.{u1}) (r₁ : Type.{u2}) (r₂ : Type.{u2}), Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (FirstOrder.Language.card.{u1, u2} (FirstOrder.Language.mk₂.{u1, u2} c f₁ f₂ r₁ r₂)) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (HAdd.hAdd.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} c)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} f₁))) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} f₂))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} r₁))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} r₂)))
but is expected to have type
  forall (c : Type.{u1}) (f₁ : Type.{u1}) (f₂ : Type.{u1}) (r₁ : Type.{u2}) (r₂ : Type.{u2}), Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (FirstOrder.Language.card.{u1, u2} (FirstOrder.Language.mk₂.{u1, u2} c f₁ f₂ r₁ r₂)) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u2 u1} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (HAdd.hAdd.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHAdd.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instAddCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} c)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} f₁))) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} f₂))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} r₁))) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} r₂)))
Case conversion may be inaccurate. Consider using '#align first_order.language.card_mk₂ FirstOrder.Language.card_mk₂ₓ'. -/
@[simp]
theorem card_mk₂ (c f₁ f₂ : Type u) (r₁ r₂ : Type v) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).card =
      Cardinal.lift.{v} (#c) + Cardinal.lift.{v} (#f₁) + Cardinal.lift.{v} (#f₂) +
          Cardinal.lift.{u} (#r₁) +
        Cardinal.lift.{u} (#r₂) :=
  by simp [card_eq_card_functions_add_card_relations, add_assoc]
#align first_order.language.card_mk₂ FirstOrder.Language.card_mk₂

variable (L) (M : Type w)

#print FirstOrder.Language.Structure /-
/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
@[ext]
class Structure where
  funMap : ∀ {n}, L.Functions n → (Fin n → M) → M
  rel_map : ∀ {n}, L.Relations n → (Fin n → M) → Prop
#align first_order.language.Structure FirstOrder.Language.Structure
-/

variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

#print FirstOrder.Language.Inhabited.trivialStructure /-
/-- Used for defining `first_order.language.Theory.Model.inhabited`. -/
def Inhabited.trivialStructure {α : Type _} [Inhabited α] : L.Structure α :=
  ⟨default, default⟩
#align first_order.language.inhabited.trivial_structure FirstOrder.Language.Inhabited.trivialStructure
-/

/-! ### Maps -/


#print FirstOrder.Language.Hom /-
/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  toFun : M → N
  map_fun' : ∀ {n} (f : L.Functions n) (x), to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    obviously
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r x → RelMap r (to_fun ∘ x) := by obviously
#align first_order.language.hom FirstOrder.Language.Hom
-/

-- mathport name: language.hom
scoped[FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

#print FirstOrder.Language.Embedding /-
/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    obviously
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (to_fun ∘ x) ↔ RelMap r x := by obviously
#align first_order.language.embedding FirstOrder.Language.Embedding
-/

-- mathport name: language.embedding
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

#print FirstOrder.Language.Equiv /-
/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    obviously
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (to_fun ∘ x) ↔ RelMap r x := by obviously
#align first_order.language.equiv FirstOrder.Language.Equiv
-/

-- mathport name: language.equiv
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {L M N} {P : Type _} [L.Structure P] {Q : Type _} [L.Structure Q]

instance : CoeTC L.Constants M :=
  ⟨fun c => funMap c default⟩

/- warning: first_order.language.fun_map_eq_coe_constants -> FirstOrder.Language.funMap_eq_coe_constants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {c : FirstOrder.Language.Constants.{u1, u2} L} {x : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> M}, Eq.{succ u3} M (FirstOrder.Language.Structure.funMap.{u1, u2, u3} L M _inst_1 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) c x) ((fun (a : Type.{u1}) (b : Type.{u3}) [self : HasLiftT.{succ u1, succ u3} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) M (HasLiftT.mk.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (CoeTCₓ.coe.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (FirstOrder.Language.hasCoeT.{u1, u2, u3} L M _inst_1))) c)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] {c : FirstOrder.Language.Constants.{u1, u2} L} {x : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> M}, Eq.{succ u3} M (FirstOrder.Language.Structure.funMap.{u1, u2, u3} L M _inst_1 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) c x) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)
Case conversion may be inaccurate. Consider using '#align first_order.language.fun_map_eq_coe_constants FirstOrder.Language.funMap_eq_coe_constantsₓ'. -/
theorem funMap_eq_coe_constants {c : L.Constants} {x : Fin 0 → M} : funMap c x = c :=
  congr rfl (funext Fin.elim0)
#align first_order.language.fun_map_eq_coe_constants FirstOrder.Language.funMap_eq_coe_constants

#print FirstOrder.Language.nonempty_of_nonempty_constants /-
/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map coe
#align first_order.language.nonempty_of_nonempty_constants FirstOrder.Language.nonempty_of_nonempty_constants
-/

#print FirstOrder.Language.funMap₂ /-
/-- The function map for `first_order.language.Structure₂`. -/
def funMap₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (c' : c → M) (f₁' : f₁ → M → M)
    (f₂' : f₂ → M → M → M) : ∀ {n}, (Language.mk₂ c f₁ f₂ r₁ r₂).Functions n → (Fin n → M) → M
  | 0, f, _ => c' f
  | 1, f, x => f₁' f (x 0)
  | 2, f, x => f₂' f (x 0) (x 1)
  | n + 3, f, _ => PEmpty.elim f
#align first_order.language.fun_map₂ FirstOrder.Language.funMap₂
-/

#print FirstOrder.Language.RelMap₂ /-
/-- The relation map for `first_order.language.Structure₂`. -/
def RelMap₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (r₁' : r₁ → Set M) (r₂' : r₂ → M → M → Prop) :
    ∀ {n}, (Language.mk₂ c f₁ f₂ r₁ r₂).Relations n → (Fin n → M) → Prop
  | 0, r, _ => PEmpty.elim r
  | 1, r, x => x 0 ∈ r₁' r
  | 2, r, x => r₂' r (x 0) (x 1)
  | n + 3, r, _ => PEmpty.elim r
#align first_order.language.rel_map₂ FirstOrder.Language.RelMap₂
-/

#print FirstOrder.Language.Structure.mk₂ /-
/-- A structure constructor to match `first_order.language₂`. -/
protected def Structure.mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (c' : c → M) (f₁' : f₁ → M → M)
    (f₂' : f₂ → M → M → M) (r₁' : r₁ → Set M) (r₂' : r₂ → M → M → Prop) :
    (Language.mk₂ c f₁ f₂ r₁ r₂).Structure M :=
  ⟨fun _ => funMap₂ c' f₁' f₂', fun _ => RelMap₂ r₁' r₂'⟩
#align first_order.language.Structure.mk₂ FirstOrder.Language.Structure.mk₂
-/

namespace Structure

variable {c f₁ f₂ : Type u} {r₁ r₂ : Type v}

variable {c' : c → M} {f₁' : f₁ → M → M} {f₂' : f₂ → M → M → M}

variable {r₁' : r₁ → Set M} {r₂' : r₂ → M → M → Prop}

#print FirstOrder.Language.Structure.funMap_apply₀ /-
@[simp]
theorem funMap_apply₀ (c₀ : c) {x : Fin 0 → M} :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 0 c₀ x = c' c₀ :=
  rfl
#align first_order.language.Structure.fun_map_apply₀ FirstOrder.Language.Structure.funMap_apply₀
-/

#print FirstOrder.Language.Structure.funMap_apply₁ /-
@[simp]
theorem funMap_apply₁ (f : f₁) (x : M) :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 1 f ![x] = f₁' f x :=
  rfl
#align first_order.language.Structure.fun_map_apply₁ FirstOrder.Language.Structure.funMap_apply₁
-/

#print FirstOrder.Language.Structure.funMap_apply₂ /-
@[simp]
theorem funMap_apply₂ (f : f₂) (x y : M) :
    @Structure.funMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 2 f ![x, y] = f₂' f x y :=
  rfl
#align first_order.language.Structure.fun_map_apply₂ FirstOrder.Language.Structure.funMap_apply₂
-/

#print FirstOrder.Language.Structure.relMap_apply₁ /-
@[simp]
theorem relMap_apply₁ (r : r₁) (x : M) :
    @Structure.RelMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 1 r ![x] = (x ∈ r₁' r) :=
  rfl
#align first_order.language.Structure.rel_map_apply₁ FirstOrder.Language.Structure.relMap_apply₁
-/

#print FirstOrder.Language.Structure.relMap_apply₂ /-
@[simp]
theorem relMap_apply₂ (r : r₂) (x y : M) :
    @Structure.RelMap _ M (Structure.mk₂ c' f₁' f₂' r₁' r₂') 2 r ![x, y] = r₂' r x y :=
  rfl
#align first_order.language.Structure.rel_map_apply₂ FirstOrder.Language.Structure.relMap_apply₂
-/

end Structure

/- warning: first_order.language.hom_class -> FirstOrder.Language.HomClass is a dubious translation:
lean 3 declaration is
  forall (L : outParam.{max (succ (succ u1)) (succ (succ u2))} FirstOrder.Language.{u1, u2}) (F : Type.{u3}) (M : outParam.{succ (succ u4)} Type.{u4}) (N : outParam.{succ (succ u5)} Type.{u5}) [_inst_5 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_7 : FirstOrder.Language.Structure.{u1, u2, u5} L N], Type
but is expected to have type
  forall (L : outParam.{max (succ (succ u1)) (succ (succ u2))} FirstOrder.Language.{u2, u1}) (F : Type.{u3}) (M : outParam.{succ (succ u4)} Type.{u4}) (N : outParam.{succ (succ u5)} Type.{u5}) [_inst_5 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_6 : FirstOrder.Language.Structure.{u2, u1, u4} L M] [_inst_7 : FirstOrder.Language.Structure.{u2, u1, u5} L N], Type
Case conversion may be inaccurate. Consider using '#align first_order.language.hom_class FirstOrder.Language.HomClassₓ'. -/
/-- `hom_class L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `first_order.language.hom`. -/
class HomClass (L : outParam Language) (F : Type _) (M N : outParam <| Type _)
  [FunLike F M fun _ => N] [L.Structure M] [L.Structure N] where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r x → RelMap r (φ ∘ x)
#align first_order.language.hom_class FirstOrder.Language.HomClass

/- warning: first_order.language.strong_hom_class -> FirstOrder.Language.StrongHomClass is a dubious translation:
lean 3 declaration is
  forall (L : outParam.{max (succ (succ u1)) (succ (succ u2))} FirstOrder.Language.{u1, u2}) (F : Type.{u3}) (M : outParam.{succ (succ u4)} Type.{u4}) (N : outParam.{succ (succ u5)} Type.{u5}) [_inst_5 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_7 : FirstOrder.Language.Structure.{u1, u2, u5} L N], Type
but is expected to have type
  forall (L : outParam.{max (succ (succ u1)) (succ (succ u2))} FirstOrder.Language.{u2, u1}) (F : Type.{u3}) (M : outParam.{succ (succ u4)} Type.{u4}) (N : outParam.{succ (succ u5)} Type.{u5}) [_inst_5 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_6 : FirstOrder.Language.Structure.{u2, u1, u4} L M] [_inst_7 : FirstOrder.Language.Structure.{u2, u1, u5} L N], Type
Case conversion may be inaccurate. Consider using '#align first_order.language.strong_hom_class FirstOrder.Language.StrongHomClassₓ'. -/
/-- `strong_hom_class L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
class StrongHomClass (L : outParam Language) (F : Type _) (M N : outParam <| Type _)
  [FunLike F M fun _ => N] [L.Structure M] [L.Structure N] where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x
#align first_order.language.strong_hom_class FirstOrder.Language.StrongHomClass

/- warning: first_order.language.strong_hom_class.hom_class -> FirstOrder.Language.StrongHomClass.homClass is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_8 : FirstOrder.Language.StrongHomClass.{u1, u2, u3, u4, u5} L F M N _inst_7 _inst_5 _inst_6], FirstOrder.Language.HomClass.{u1, u2, u3, u4, u5} L F M N _inst_7 _inst_5 _inst_6
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u3} L F] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_7 : FunLike.{succ u5, succ u3, succ u4} N F (fun (_x : F) => M)] [_inst_8 : FirstOrder.Language.StrongHomClass.{u2, u1, u5, u3, u4} L N F M _inst_7 _inst_5 _inst_6], FirstOrder.Language.HomClass.{u2, u1, u5, u3, u4} L N F M _inst_7 _inst_5 _inst_6
Case conversion may be inaccurate. Consider using '#align first_order.language.strong_hom_class.hom_class FirstOrder.Language.StrongHomClass.homClassₓ'. -/
instance (priority := 100) StrongHomClass.homClass {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M fun _ => N] [StrongHomClass L F M N] : HomClass L F M N
    where
  map_fun := StrongHomClass.map_fun
  map_rel φ n R x := (StrongHomClass.map_rel φ R x).2
#align first_order.language.strong_hom_class.hom_class FirstOrder.Language.StrongHomClass.homClass

/- warning: first_order.language.hom_class.strong_hom_class_of_is_algebraic -> FirstOrder.Language.HomClass.strongHomClassOfIsAlgebraic is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} [_inst_5 : FirstOrder.Language.IsAlgebraic.{u1, u2} L] {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_7 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_8 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_9 : FirstOrder.Language.HomClass.{u1, u2, u3, u4, u5} L F M N _inst_8 _inst_6 _inst_7], FirstOrder.Language.StrongHomClass.{u1, u2, u3, u4, u5} L F M N _inst_8 _inst_6 _inst_7
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} [_inst_5 : FirstOrder.Language.IsAlgebraic.{u1, u2} L] {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_7 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_8 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_9 : FirstOrder.Language.HomClass.{u2, u1, u3, u4, u5} L F M N _inst_8 _inst_6 _inst_7], FirstOrder.Language.StrongHomClass.{u2, u1, u3, u4, u5} L F M N _inst_8 _inst_6 _inst_7
Case conversion may be inaccurate. Consider using '#align first_order.language.hom_class.strong_hom_class_of_is_algebraic FirstOrder.Language.HomClass.strongHomClassOfIsAlgebraicₓ'. -/
/-- Not an instance to avoid a loop. -/
def HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M fun _ => N] [HomClass L F M N] : StrongHomClass L F M N
    where
  map_fun := HomClass.map_fun
  map_rel φ n R x := (IsAlgebraic.empty_relations n).elim R
#align first_order.language.hom_class.strong_hom_class_of_is_algebraic FirstOrder.Language.HomClass.strongHomClassOfIsAlgebraic

/- warning: first_order.language.hom_class.map_constants -> FirstOrder.Language.HomClass.map_constants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_8 : FirstOrder.Language.HomClass.{u1, u2, u3, u4, u5} L F M N _inst_7 _inst_5 _inst_6] (φ : F) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u5} N (coeFn.{succ u3, max (succ u4) (succ u5)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N) _inst_7) φ ((fun (a : Type.{u1}) (b : Type.{u4}) [self : HasLiftT.{succ u1, succ u4} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) M (HasLiftT.mk.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) M (CoeTCₓ.coe.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) M (FirstOrder.Language.hasCoeT.{u1, u2, u4} L M _inst_5))) c)) ((fun (a : Type.{u1}) (b : Type.{u5}) [self : HasLiftT.{succ u1, succ u5} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) N (HasLiftT.mk.{succ u1, succ u5} (FirstOrder.Language.Constants.{u1, u2} L) N (CoeTCₓ.coe.{succ u1, succ u5} (FirstOrder.Language.Constants.{u1, u2} L) N (FirstOrder.Language.hasCoeT.{u1, u2, u5} L N _inst_6))) c)
but is expected to have type
  forall {L : FirstOrder.Language.{u4, u5}} {F : Type.{u3}} {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : FirstOrder.Language.Structure.{u4, u5, u2} L M] [_inst_6 : FirstOrder.Language.Structure.{u4, u5, u1} L N] [_inst_7 : FunLike.{succ u3, succ u2, succ u1} F M (fun (_x : M) => N)] [_inst_8 : FirstOrder.Language.HomClass.{u5, u4, u3, u2, u1} L F M N _inst_7 _inst_5 _inst_6] (φ : F) (c : FirstOrder.Language.Constants.{u4, u5} L), Eq.{succ u1} ((fun (x._@.Mathlib.ModelTheory.Basic._hyg.5516 : M) => N) (FirstOrder.Language.constantMap.{u4, u5, u2} L M _inst_5 c)) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.ModelTheory.Basic._hyg.5516 : M) => N) _x) _inst_7 φ (FirstOrder.Language.constantMap.{u4, u5, u2} L M _inst_5 c)) (FirstOrder.Language.constantMap.{u4, u5, u1} L ((fun (x._@.Mathlib.ModelTheory.Basic._hyg.5516 : M) => N) (FirstOrder.Language.constantMap.{u4, u5, u2} L M _inst_5 c)) _inst_6 c)
Case conversion may be inaccurate. Consider using '#align first_order.language.hom_class.map_constants FirstOrder.Language.HomClass.map_constantsₓ'. -/
theorem HomClass.map_constants {F M N} [L.Structure M] [L.Structure N] [FunLike F M fun _ => N]
    [HomClass L F M N] (φ : F) (c : L.Constants) : φ c = c :=
  (HomClass.map_fun φ c default).trans (congr rfl (funext default))
#align first_order.language.hom_class.map_constants FirstOrder.Language.HomClass.map_constants

namespace Hom

#print FirstOrder.Language.Hom.funLike /-
instance funLike : FunLike (M →[L] N) M fun _ => N
    where
  coe := Hom.toFun
  coe_injective' f g h := by cases f; cases g; cases h; rfl
#align first_order.language.hom.fun_like FirstOrder.Language.Hom.funLike
-/

/- warning: first_order.language.hom.hom_class -> FirstOrder.Language.Hom.homClass is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], FirstOrder.Language.HomClass.{u1, u2, max u3 u4, u3, u4} L (FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Hom.funLike.{u1, u2, u3, u4} L M N _inst_1 _inst_2) _inst_1 _inst_2
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], FirstOrder.Language.HomClass.{u2, u1, max u4 u3, u3, u4} L (FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Hom.funLike.{u1, u2, u3, u4} L M N _inst_1 _inst_2) _inst_1 _inst_2
Case conversion may be inaccurate. Consider using '#align first_order.language.hom.hom_class FirstOrder.Language.Hom.homClassₓ'. -/
instance homClass : HomClass L (M →[L] N) M N
    where
  map_fun := map_fun'
  map_rel := map_rel'
#align first_order.language.hom.hom_class FirstOrder.Language.Hom.homClass

instance [L.IsAlgebraic] : StrongHomClass L (M →[L] N) M N :=
  HomClass.strongHomClassOfIsAlgebraic

#print FirstOrder.Language.Hom.hasCoeToFun /-
instance hasCoeToFun : CoeFun (M →[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun
#align first_order.language.hom.has_coe_to_fun FirstOrder.Language.Hom.hasCoeToFun
-/

#print FirstOrder.Language.Hom.toFun_eq_coe /-
@[simp]
theorem toFun_eq_coe {f : M →[L] N} : f.toFun = (f : M → N) :=
  rfl
#align first_order.language.hom.to_fun_eq_coe FirstOrder.Language.Hom.toFun_eq_coe
-/

#print FirstOrder.Language.Hom.ext /-
@[ext]
theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align first_order.language.hom.ext FirstOrder.Language.Hom.ext
-/

#print FirstOrder.Language.Hom.ext_iff /-
theorem ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align first_order.language.hom.ext_iff FirstOrder.Language.Hom.ext_iff
-/

#print FirstOrder.Language.Hom.map_fun /-
@[simp]
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x
#align first_order.language.hom.map_fun FirstOrder.Language.Hom.map_fun
-/

/- warning: first_order.language.hom.map_constants -> FirstOrder.Language.Hom.map_constants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] (φ : FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u4} N (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Hom.hasCoeToFun.{u1, u2, u3, u4} L M N _inst_1 _inst_2) φ ((fun (a : Type.{u1}) (b : Type.{u3}) [self : HasLiftT.{succ u1, succ u3} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) M (HasLiftT.mk.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (CoeTCₓ.coe.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (FirstOrder.Language.hasCoeT.{u1, u2, u3} L M _inst_1))) c)) ((fun (a : Type.{u1}) (b : Type.{u4}) [self : HasLiftT.{succ u1, succ u4} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) N (HasLiftT.mk.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) N (CoeTCₓ.coe.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) N (FirstOrder.Language.hasCoeT.{u1, u2, u4} L N _inst_2))) c)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] (φ : FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u4} ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => N) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => N) _x) (FirstOrder.Language.Hom.funLike.{u1, u2, u3, u4} L M N _inst_1 _inst_2) φ (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) (FirstOrder.Language.constantMap.{u1, u2, u4} L ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => N) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) _inst_2 c)
Case conversion may be inaccurate. Consider using '#align first_order.language.hom.map_constants FirstOrder.Language.Hom.map_constantsₓ'. -/
@[simp]
theorem map_constants (φ : M →[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.hom.map_constants FirstOrder.Language.Hom.map_constants

#print FirstOrder.Language.Hom.map_rel /-
@[simp]
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r x → RelMap r (φ ∘ x) :=
  HomClass.map_rel φ r x
#align first_order.language.hom.map_rel FirstOrder.Language.Hom.map_rel
-/

variable (L) (M)

#print FirstOrder.Language.Hom.id /-
/-- The identity map from a structure to itself -/
@[refl]
def id : M →[L] M where toFun := id
#align first_order.language.hom.id FirstOrder.Language.Hom.id
-/

variable {L} {M}

instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

#print FirstOrder.Language.Hom.id_apply /-
@[simp]
theorem id_apply (x : M) : id L M x = x :=
  rfl
#align first_order.language.hom.id_apply FirstOrder.Language.Hom.id_apply
-/

#print FirstOrder.Language.Hom.comp /-
/-- Composition of first-order homomorphisms -/
@[trans]
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P
    where
  toFun := hnp ∘ hmn
  map_rel' _ _ _ h := by simp [h]
#align first_order.language.hom.comp FirstOrder.Language.Hom.comp
-/

/- warning: first_order.language.hom.comp_apply -> FirstOrder.Language.Hom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] (g : FirstOrder.Language.Hom.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (f : FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (x : M), Eq.{succ u5} P (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Hom.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (fun (_x : FirstOrder.Language.Hom.{u1, u2, u3, u5} L M P _inst_1 _inst_3) => M -> P) (FirstOrder.Language.Hom.hasCoeToFun.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (FirstOrder.Language.Hom.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 g f) x) (coeFn.{max (succ u4) (succ u5), max (succ u4) (succ u5)} (FirstOrder.Language.Hom.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (fun (_x : FirstOrder.Language.Hom.{u1, u2, u4, u5} L N P _inst_2 _inst_3) => N -> P) (FirstOrder.Language.Hom.hasCoeToFun.{u1, u2, u4, u5} L N P _inst_2 _inst_3) g (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Hom.hasCoeToFun.{u1, u2, u3, u4} L M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u5} L N] {P : Type.{u1}} [_inst_3 : FirstOrder.Language.Structure.{u2, u3, u1} L P] (g : FirstOrder.Language.Hom.{u2, u3, u5, u1} L N P _inst_2 _inst_3) (f : FirstOrder.Language.Hom.{u2, u3, u4, u5} L M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => P) x) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Hom.{u2, u3, u4, u1} L M P _inst_1 _inst_3) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => P) _x) (FirstOrder.Language.Hom.funLike.{u2, u3, u4, u1} L M P _inst_1 _inst_3) (FirstOrder.Language.Hom.comp.{u2, u3, u4, u5, u1} L M N _inst_1 _inst_2 P _inst_3 g f) x) (FunLike.coe.{max (succ u5) (succ u1), succ u5, succ u1} (FirstOrder.Language.Hom.{u2, u3, u5, u1} L N P _inst_2 _inst_3) N (fun (_x : N) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : N) => P) _x) (FirstOrder.Language.Hom.funLike.{u2, u3, u5, u1} L N P _inst_2 _inst_3) g (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (FirstOrder.Language.Hom.{u2, u3, u4, u5} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.5742 : M) => N) _x) (FirstOrder.Language.Hom.funLike.{u2, u3, u4, u5} L M N _inst_1 _inst_2) f x))
Case conversion may be inaccurate. Consider using '#align first_order.language.hom.comp_apply FirstOrder.Language.Hom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.hom.comp_apply FirstOrder.Language.Hom.comp_apply

/- warning: first_order.language.hom.comp_assoc -> FirstOrder.Language.Hom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] {Q : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u1, u2, u6} L Q] (f : FirstOrder.Language.Hom.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (g : FirstOrder.Language.Hom.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (h : FirstOrder.Language.Hom.{u1, u2, u5, u6} L P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u6)} (FirstOrder.Language.Hom.{u1, u2, u3, u6} L M Q _inst_1 _inst_4) (FirstOrder.Language.Hom.comp.{u1, u2, u3, u4, u6} L M N _inst_1 _inst_2 Q _inst_4 (FirstOrder.Language.Hom.comp.{u1, u2, u4, u5, u6} L N P _inst_2 _inst_3 Q _inst_4 h g) f) (FirstOrder.Language.Hom.comp.{u1, u2, u3, u5, u6} L M P _inst_1 _inst_3 Q _inst_4 h (FirstOrder.Language.Hom.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 g f))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {M : Type.{u5}} {N : Type.{u6}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] [_inst_2 : FirstOrder.Language.Structure.{u3, u4, u6} L N] {P : Type.{u2}} [_inst_3 : FirstOrder.Language.Structure.{u3, u4, u2} L P] {Q : Type.{u1}} [_inst_4 : FirstOrder.Language.Structure.{u3, u4, u1} L Q] (f : FirstOrder.Language.Hom.{u3, u4, u5, u6} L M N _inst_1 _inst_2) (g : FirstOrder.Language.Hom.{u3, u4, u6, u2} L N P _inst_2 _inst_3) (h : FirstOrder.Language.Hom.{u3, u4, u2, u1} L P Q _inst_3 _inst_4), Eq.{max (succ u5) (succ u1)} (FirstOrder.Language.Hom.{u3, u4, u5, u1} L M Q _inst_1 _inst_4) (FirstOrder.Language.Hom.comp.{u3, u4, u5, u6, u1} L M N _inst_1 _inst_2 Q _inst_4 (FirstOrder.Language.Hom.comp.{u3, u4, u6, u2, u1} L N P _inst_2 _inst_3 Q _inst_4 h g) f) (FirstOrder.Language.Hom.comp.{u3, u4, u5, u2, u1} L M P _inst_1 _inst_3 Q _inst_4 h (FirstOrder.Language.Hom.comp.{u3, u4, u5, u6, u2} L M N _inst_1 _inst_2 P _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align first_order.language.hom.comp_assoc FirstOrder.Language.Hom.comp_assocₓ'. -/
/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.hom.comp_assoc FirstOrder.Language.Hom.comp_assoc

end Hom

/- warning: first_order.language.hom_class.to_hom -> FirstOrder.Language.HomClass.toHom is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_8 : FirstOrder.Language.HomClass.{u1, u2, u3, u4, u5} L F M N _inst_7 _inst_5 _inst_6], F -> (FirstOrder.Language.Hom.{u1, u2, u4, u5} L M N _inst_5 _inst_6)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : FunLike.{succ u3, succ u4, succ u5} F M (fun (_x : M) => N)] [_inst_8 : FirstOrder.Language.HomClass.{u2, u1, u3, u4, u5} L F M N _inst_7 _inst_5 _inst_6], F -> (FirstOrder.Language.Hom.{u1, u2, u4, u5} L M N _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align first_order.language.hom_class.to_hom FirstOrder.Language.HomClass.toHomₓ'. -/
/-- Any element of a `hom_class` can be realized as a first_order homomorphism. -/
def HomClass.toHom {F M N} [L.Structure M] [L.Structure N] [FunLike F M fun _ => N]
    [HomClass L F M N] : F → M →[L] N := fun φ =>
  ⟨φ, fun _ => HomClass.map_fun φ, fun _ => HomClass.map_rel φ⟩
#align first_order.language.hom_class.to_hom FirstOrder.Language.HomClass.toHom

namespace Embedding

#print FirstOrder.Language.Embedding.embeddingLike /-
instance embeddingLike : EmbeddingLike (M ↪[L] N) M N
    where
  coe f := f.toFun
  injective' f := f.toEmbedding.Injective
  coe_injective' f g h := by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iff.1 h x
#align first_order.language.embedding.embedding_like FirstOrder.Language.Embedding.embeddingLike
-/

/- warning: first_order.language.embedding.strong_hom_class -> FirstOrder.Language.Embedding.strongHomClass is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], FirstOrder.Language.StrongHomClass.{u1, u2, max u3 u4, u3, u4} L (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (EmbeddingLike.toFunLike.{succ (max u3 u4), succ u3, succ u4} (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Embedding.embeddingLike.{u1, u2, u3, u4} L M N _inst_1 _inst_2)) _inst_1 _inst_2
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N], FirstOrder.Language.StrongHomClass.{u2, u1, max u4 u3, u3, u4} L (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Embedding.embeddingLike.{u1, u2, u3, u4} L M N _inst_1 _inst_2)) _inst_1 _inst_2
Case conversion may be inaccurate. Consider using '#align first_order.language.embedding.strong_hom_class FirstOrder.Language.Embedding.strongHomClassₓ'. -/
instance strongHomClass : StrongHomClass L (M ↪[L] N) M N
    where
  map_fun := map_fun'
  map_rel := map_rel'
#align first_order.language.embedding.strong_hom_class FirstOrder.Language.Embedding.strongHomClass

#print FirstOrder.Language.Embedding.hasCoeToFun /-
instance hasCoeToFun : CoeFun (M ↪[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun
#align first_order.language.embedding.has_coe_to_fun FirstOrder.Language.Embedding.hasCoeToFun
-/

#print FirstOrder.Language.Embedding.map_fun /-
@[simp]
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x
#align first_order.language.embedding.map_fun FirstOrder.Language.Embedding.map_fun
-/

/- warning: first_order.language.embedding.map_constants -> FirstOrder.Language.Embedding.map_constants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] (φ : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u4} N (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Embedding.hasCoeToFun.{u1, u2, u3, u4} L M N _inst_1 _inst_2) φ ((fun (a : Type.{u1}) (b : Type.{u3}) [self : HasLiftT.{succ u1, succ u3} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) M (HasLiftT.mk.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (CoeTCₓ.coe.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (FirstOrder.Language.hasCoeT.{u1, u2, u3} L M _inst_1))) c)) ((fun (a : Type.{u1}) (b : Type.{u4}) [self : HasLiftT.{succ u1, succ u4} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) N (HasLiftT.mk.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) N (CoeTCₓ.coe.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) N (FirstOrder.Language.hasCoeT.{u1, u2, u4} L N _inst_2))) c)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] (φ : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u4} ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => N) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Embedding.embeddingLike.{u1, u2, u3, u4} L M N _inst_1 _inst_2)) φ (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) (FirstOrder.Language.constantMap.{u1, u2, u4} L ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => N) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) _inst_2 c)
Case conversion may be inaccurate. Consider using '#align first_order.language.embedding.map_constants FirstOrder.Language.Embedding.map_constantsₓ'. -/
@[simp]
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.embedding.map_constants FirstOrder.Language.Embedding.map_constants

#print FirstOrder.Language.Embedding.map_rel /-
@[simp]
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x
#align first_order.language.embedding.map_rel FirstOrder.Language.Embedding.map_rel
-/

#print FirstOrder.Language.Embedding.toHom /-
/-- A first-order embedding is also a first-order homomorphism. -/
def toHom : (M ↪[L] N) → M →[L] N :=
  HomClass.toHom
#align first_order.language.embedding.to_hom FirstOrder.Language.Embedding.toHom
-/

#print FirstOrder.Language.Embedding.coe_toHom /-
@[simp]
theorem coe_toHom {f : M ↪[L] N} : (f.toHom : M → N) = f :=
  rfl
#align first_order.language.embedding.coe_to_hom FirstOrder.Language.Embedding.coe_toHom
-/

#print FirstOrder.Language.Embedding.coe_injective /-
theorem coe_injective : @Function.Injective (M ↪[L] N) (M → N) coeFn
  | f, g, h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iff.1 h x
#align first_order.language.embedding.coe_injective FirstOrder.Language.Embedding.coe_injective
-/

#print FirstOrder.Language.Embedding.ext /-
@[ext]
theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
#align first_order.language.embedding.ext FirstOrder.Language.Embedding.ext
-/

#print FirstOrder.Language.Embedding.ext_iff /-
theorem ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩
#align first_order.language.embedding.ext_iff FirstOrder.Language.Embedding.ext_iff
-/

#print FirstOrder.Language.Embedding.injective /-
theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.Injective
#align first_order.language.embedding.injective FirstOrder.Language.Embedding.injective
-/

#print FirstOrder.Language.Embedding.ofInjective /-
/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps]
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with
    inj' := hf
    map_rel' := fun n r x => StrongHomClass.map_rel f r x }
#align first_order.language.embedding.of_injective FirstOrder.Language.Embedding.ofInjective
-/

#print FirstOrder.Language.Embedding.coeFn_ofInjective /-
@[simp]
theorem coeFn_ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf : M → N) = f :=
  rfl
#align first_order.language.embedding.coe_fn_of_injective FirstOrder.Language.Embedding.coeFn_ofInjective
-/

#print FirstOrder.Language.Embedding.ofInjective_toHom /-
@[simp]
theorem ofInjective_toHom [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf).toHom = f := by ext; simp
#align first_order.language.embedding.of_injective_to_hom FirstOrder.Language.Embedding.ofInjective_toHom
-/

variable (L) (M)

#print FirstOrder.Language.Embedding.refl /-
/-- The identity embedding from a structure to itself -/
@[refl]
def refl : M ↪[L] M where toEmbedding := Function.Embedding.refl M
#align first_order.language.embedding.refl FirstOrder.Language.Embedding.refl
-/

variable {L} {M}

instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

#print FirstOrder.Language.Embedding.refl_apply /-
@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl
#align first_order.language.embedding.refl_apply FirstOrder.Language.Embedding.refl_apply
-/

#print FirstOrder.Language.Embedding.comp /-
/-- Composition of first-order embeddings -/
@[trans]
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P
    where
  toFun := hnp ∘ hmn
  inj' := hnp.Injective.comp hmn.Injective
#align first_order.language.embedding.comp FirstOrder.Language.Embedding.comp
-/

/- warning: first_order.language.embedding.comp_apply -> FirstOrder.Language.Embedding.comp_apply is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] (g : FirstOrder.Language.Embedding.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (f : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (x : M), Eq.{succ u5} P (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (fun (_x : FirstOrder.Language.Embedding.{u1, u2, u3, u5} L M P _inst_1 _inst_3) => M -> P) (FirstOrder.Language.Embedding.hasCoeToFun.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (FirstOrder.Language.Embedding.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 g f) x) (coeFn.{max (succ u4) (succ u5), max (succ u4) (succ u5)} (FirstOrder.Language.Embedding.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (fun (_x : FirstOrder.Language.Embedding.{u1, u2, u4, u5} L N P _inst_2 _inst_3) => N -> P) (FirstOrder.Language.Embedding.hasCoeToFun.{u1, u2, u4, u5} L N P _inst_2 _inst_3) g (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Embedding.hasCoeToFun.{u1, u2, u3, u4} L M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u5} L N] {P : Type.{u1}} [_inst_3 : FirstOrder.Language.Structure.{u2, u3, u1} L P] (g : FirstOrder.Language.Embedding.{u2, u3, u5, u1} L N P _inst_2 _inst_3) (f : FirstOrder.Language.Embedding.{u2, u3, u4, u5} L M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => P) x) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M P _inst_1 _inst_3) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => P) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u4, u1} L M P _inst_1 _inst_3) M P (FirstOrder.Language.Embedding.embeddingLike.{u2, u3, u4, u1} L M P _inst_1 _inst_3)) (FirstOrder.Language.Embedding.comp.{u2, u3, u4, u5, u1} L M N _inst_1 _inst_2 P _inst_3 g f) x) (FunLike.coe.{max (succ u5) (succ u1), succ u5, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u5, u1} L N P _inst_2 _inst_3) N (fun (_x : N) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : N) => P) _x) (EmbeddingLike.toFunLike.{max (succ u5) (succ u1), succ u5, succ u1} (FirstOrder.Language.Embedding.{u2, u3, u5, u1} L N P _inst_2 _inst_3) N P (FirstOrder.Language.Embedding.embeddingLike.{u2, u3, u5, u1} L N P _inst_2 _inst_3)) g (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (FirstOrder.Language.Embedding.{u2, u3, u4, u5} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.6670 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u5), succ u4, succ u5} (FirstOrder.Language.Embedding.{u2, u3, u4, u5} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Embedding.embeddingLike.{u2, u3, u4, u5} L M N _inst_1 _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align first_order.language.embedding.comp_apply FirstOrder.Language.Embedding.comp_applyₓ'. -/
@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.embedding.comp_apply FirstOrder.Language.Embedding.comp_apply

/- warning: first_order.language.embedding.comp_assoc -> FirstOrder.Language.Embedding.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] {Q : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u1, u2, u6} L Q] (f : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (g : FirstOrder.Language.Embedding.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (h : FirstOrder.Language.Embedding.{u1, u2, u5, u6} L P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u6)} (FirstOrder.Language.Embedding.{u1, u2, u3, u6} L M Q _inst_1 _inst_4) (FirstOrder.Language.Embedding.comp.{u1, u2, u3, u4, u6} L M N _inst_1 _inst_2 Q _inst_4 (FirstOrder.Language.Embedding.comp.{u1, u2, u4, u5, u6} L N P _inst_2 _inst_3 Q _inst_4 h g) f) (FirstOrder.Language.Embedding.comp.{u1, u2, u3, u5, u6} L M P _inst_1 _inst_3 Q _inst_4 h (FirstOrder.Language.Embedding.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 g f))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {M : Type.{u5}} {N : Type.{u6}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] [_inst_2 : FirstOrder.Language.Structure.{u3, u4, u6} L N] {P : Type.{u2}} [_inst_3 : FirstOrder.Language.Structure.{u3, u4, u2} L P] {Q : Type.{u1}} [_inst_4 : FirstOrder.Language.Structure.{u3, u4, u1} L Q] (f : FirstOrder.Language.Embedding.{u3, u4, u5, u6} L M N _inst_1 _inst_2) (g : FirstOrder.Language.Embedding.{u3, u4, u6, u2} L N P _inst_2 _inst_3) (h : FirstOrder.Language.Embedding.{u3, u4, u2, u1} L P Q _inst_3 _inst_4), Eq.{max (succ u5) (succ u1)} (FirstOrder.Language.Embedding.{u3, u4, u5, u1} L M Q _inst_1 _inst_4) (FirstOrder.Language.Embedding.comp.{u3, u4, u5, u6, u1} L M N _inst_1 _inst_2 Q _inst_4 (FirstOrder.Language.Embedding.comp.{u3, u4, u6, u2, u1} L N P _inst_2 _inst_3 Q _inst_4 h g) f) (FirstOrder.Language.Embedding.comp.{u3, u4, u5, u2, u1} L M P _inst_1 _inst_3 Q _inst_4 h (FirstOrder.Language.Embedding.comp.{u3, u4, u5, u6, u2} L M N _inst_1 _inst_2 P _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align first_order.language.embedding.comp_assoc FirstOrder.Language.Embedding.comp_assocₓ'. -/
/-- Composition of first-order embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.embedding.comp_assoc FirstOrder.Language.Embedding.comp_assoc

/- warning: first_order.language.embedding.comp_to_hom -> FirstOrder.Language.Embedding.comp_toHom is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] (hnp : FirstOrder.Language.Embedding.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (hmn : FirstOrder.Language.Embedding.{u1, u2, u3, u4} L M N _inst_1 _inst_2), Eq.{max (succ u3) (succ u5)} (FirstOrder.Language.Hom.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (FirstOrder.Language.Embedding.toHom.{u1, u2, u3, u5} L M P _inst_1 _inst_3 (FirstOrder.Language.Embedding.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 hnp hmn)) (FirstOrder.Language.Hom.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 (FirstOrder.Language.Embedding.toHom.{u1, u2, u4, u5} L N P _inst_2 _inst_3 hnp) (FirstOrder.Language.Embedding.toHom.{u1, u2, u3, u4} L M N _inst_1 _inst_2 hmn))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u5} L N] {P : Type.{u1}} [_inst_3 : FirstOrder.Language.Structure.{u2, u3, u1} L P] (hnp : FirstOrder.Language.Embedding.{u2, u3, u5, u1} L N P _inst_2 _inst_3) (hmn : FirstOrder.Language.Embedding.{u2, u3, u4, u5} L M N _inst_1 _inst_2), Eq.{max (succ u4) (succ u1)} (FirstOrder.Language.Hom.{u2, u3, u4, u1} L M P _inst_1 _inst_3) (FirstOrder.Language.Embedding.toHom.{u2, u3, u4, u1} L M P _inst_1 _inst_3 (FirstOrder.Language.Embedding.comp.{u2, u3, u4, u5, u1} L M N _inst_1 _inst_2 P _inst_3 hnp hmn)) (FirstOrder.Language.Hom.comp.{u2, u3, u4, u5, u1} L M N _inst_1 _inst_2 P _inst_3 (FirstOrder.Language.Embedding.toHom.{u2, u3, u5, u1} L N P _inst_2 _inst_3 hnp) (FirstOrder.Language.Embedding.toHom.{u2, u3, u4, u5} L M N _inst_1 _inst_2 hmn))
Case conversion may be inaccurate. Consider using '#align first_order.language.embedding.comp_to_hom FirstOrder.Language.Embedding.comp_toHomₓ'. -/
@[simp]
theorem comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom := by ext;
  simp only [coe_to_hom, comp_apply, hom.comp_apply]
#align first_order.language.embedding.comp_to_hom FirstOrder.Language.Embedding.comp_toHom

end Embedding

/- warning: first_order.language.strong_hom_class.to_embedding -> FirstOrder.Language.StrongHomClass.toEmbedding is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : EmbeddingLike.{succ u3, succ u4, succ u5} F M N] [_inst_8 : FirstOrder.Language.StrongHomClass.{u1, u2, u3, u4, u5} L F M N (EmbeddingLike.toFunLike.{succ u3, succ u4, succ u5} F M N _inst_7) _inst_5 _inst_6], F -> (FirstOrder.Language.Embedding.{u1, u2, u4, u5} L M N _inst_5 _inst_6)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : EmbeddingLike.{succ u3, succ u4, succ u5} F M N] [_inst_8 : FirstOrder.Language.StrongHomClass.{u2, u1, u3, u4, u5} L F M N (EmbeddingLike.toFunLike.{succ u3, succ u4, succ u5} F M N _inst_7) _inst_5 _inst_6], F -> (FirstOrder.Language.Embedding.{u1, u2, u4, u5} L M N _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align first_order.language.strong_hom_class.to_embedding FirstOrder.Language.StrongHomClass.toEmbeddingₓ'. -/
/-- Any element of an injective `strong_hom_class` can be realized as a first_order embedding. -/
def StrongHomClass.toEmbedding {F M N} [L.Structure M] [L.Structure N] [EmbeddingLike F M N]
    [StrongHomClass L F M N] : F → M ↪[L] N := fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, fun _ => StrongHomClass.map_fun φ, fun _ =>
    StrongHomClass.map_rel φ⟩
#align first_order.language.strong_hom_class.to_embedding FirstOrder.Language.StrongHomClass.toEmbedding

namespace Equiv

instance : EquivLike (M ≃[L] N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iff.1 h₁ x

instance : StrongHomClass L (M ≃[L] N) M N
    where
  map_fun := map_fun'
  map_rel := map_rel'

#print FirstOrder.Language.Equiv.symm /-
/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (f : M ≃[L] N) : N ≃[L] M :=
  {
    f.toEquiv.symm with
    map_fun' := fun n f' x => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine' Eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm
      rw [← Function.comp.assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.comp.left_id]
    map_rel' := fun n r x => by
      simp only [Equiv.toFun_as_coe]
      refine' (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _
      rw [← Function.comp.assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.comp.left_id] }
#align first_order.language.equiv.symm FirstOrder.Language.Equiv.symm
-/

#print FirstOrder.Language.Equiv.hasCoeToFun /-
instance hasCoeToFun : CoeFun (M ≃[L] N) fun _ => M → N :=
  FunLike.hasCoeToFun
#align first_order.language.equiv.has_coe_to_fun FirstOrder.Language.Equiv.hasCoeToFun
-/

#print FirstOrder.Language.Equiv.apply_symm_apply /-
@[simp]
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a
#align first_order.language.equiv.apply_symm_apply FirstOrder.Language.Equiv.apply_symm_apply
-/

#print FirstOrder.Language.Equiv.symm_apply_apply /-
@[simp]
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a
#align first_order.language.equiv.symm_apply_apply FirstOrder.Language.Equiv.symm_apply_apply
-/

#print FirstOrder.Language.Equiv.map_fun /-
@[simp]
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x
#align first_order.language.equiv.map_fun FirstOrder.Language.Equiv.map_fun
-/

/- warning: first_order.language.equiv.map_constants -> FirstOrder.Language.Equiv.map_constants is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] (φ : FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u4} N (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u4} L M N _inst_1 _inst_2) φ ((fun (a : Type.{u1}) (b : Type.{u3}) [self : HasLiftT.{succ u1, succ u3} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) M (HasLiftT.mk.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (CoeTCₓ.coe.{succ u1, succ u3} (FirstOrder.Language.Constants.{u1, u2} L) M (FirstOrder.Language.hasCoeT.{u1, u2, u3} L M _inst_1))) c)) ((fun (a : Type.{u1}) (b : Type.{u4}) [self : HasLiftT.{succ u1, succ u4} a b] => self.0) (FirstOrder.Language.Constants.{u1, u2} L) N (HasLiftT.mk.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) N (CoeTCₓ.coe.{succ u1, succ u4} (FirstOrder.Language.Constants.{u1, u2} L) N (FirstOrder.Language.hasCoeT.{u1, u2, u4} L N _inst_2))) c)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] (φ : FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (c : FirstOrder.Language.Constants.{u1, u2} L), Eq.{succ u4} ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u3) (succ u4), succ u3, succ u4} (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2))) φ (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) (FirstOrder.Language.constantMap.{u1, u2, u4} L ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) (FirstOrder.Language.constantMap.{u1, u2, u3} L M _inst_1 c)) _inst_2 c)
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.map_constants FirstOrder.Language.Equiv.map_constantsₓ'. -/
@[simp]
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.equiv.map_constants FirstOrder.Language.Equiv.map_constants

#print FirstOrder.Language.Equiv.map_rel /-
@[simp]
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x
#align first_order.language.equiv.map_rel FirstOrder.Language.Equiv.map_rel
-/

#print FirstOrder.Language.Equiv.toEmbedding /-
/-- A first-order equivalence is also a first-order embedding. -/
def toEmbedding : (M ≃[L] N) → M ↪[L] N :=
  StrongHomClass.toEmbedding
#align first_order.language.equiv.to_embedding FirstOrder.Language.Equiv.toEmbedding
-/

#print FirstOrder.Language.Equiv.toHom /-
/-- A first-order equivalence is also a first-order homomorphism. -/
def toHom : (M ≃[L] N) → M →[L] N :=
  HomClass.toHom
#align first_order.language.equiv.to_hom FirstOrder.Language.Equiv.toHom
-/

#print FirstOrder.Language.Equiv.toEmbedding_toHom /-
@[simp]
theorem toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl
#align first_order.language.equiv.to_embedding_to_hom FirstOrder.Language.Equiv.toEmbedding_toHom
-/

#print FirstOrder.Language.Equiv.coe_toHom /-
@[simp]
theorem coe_toHom {f : M ≃[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl
#align first_order.language.equiv.coe_to_hom FirstOrder.Language.Equiv.coe_toHom
-/

#print FirstOrder.Language.Equiv.coe_toEmbedding /-
@[simp]
theorem coe_toEmbedding (f : M ≃[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl
#align first_order.language.equiv.coe_to_embedding FirstOrder.Language.Equiv.coe_toEmbedding
-/

#print FirstOrder.Language.Equiv.coe_injective /-
theorem coe_injective : @Function.Injective (M ≃[L] N) (M → N) coeFn :=
  FunLike.coe_injective
#align first_order.language.equiv.coe_injective FirstOrder.Language.Equiv.coe_injective
-/

#print FirstOrder.Language.Equiv.ext /-
@[ext]
theorem ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
#align first_order.language.equiv.ext FirstOrder.Language.Equiv.ext
-/

#print FirstOrder.Language.Equiv.ext_iff /-
theorem ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩
#align first_order.language.equiv.ext_iff FirstOrder.Language.Equiv.ext_iff
-/

#print FirstOrder.Language.Equiv.bijective /-
theorem bijective (f : M ≃[L] N) : Function.Bijective f :=
  EquivLike.bijective f
#align first_order.language.equiv.bijective FirstOrder.Language.Equiv.bijective
-/

#print FirstOrder.Language.Equiv.injective /-
theorem injective (f : M ≃[L] N) : Function.Injective f :=
  EquivLike.injective f
#align first_order.language.equiv.injective FirstOrder.Language.Equiv.injective
-/

#print FirstOrder.Language.Equiv.surjective /-
theorem surjective (f : M ≃[L] N) : Function.Surjective f :=
  EquivLike.surjective f
#align first_order.language.equiv.surjective FirstOrder.Language.Equiv.surjective
-/

variable (L) (M)

#print FirstOrder.Language.Equiv.refl /-
/-- The identity equivalence from a structure to itself -/
@[refl]
def refl : M ≃[L] M where toEquiv := Equiv.refl M
#align first_order.language.equiv.refl FirstOrder.Language.Equiv.refl
-/

variable {L} {M}

instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

#print FirstOrder.Language.Equiv.refl_apply /-
@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl
#align first_order.language.equiv.refl_apply FirstOrder.Language.Equiv.refl_apply
-/

#print FirstOrder.Language.Equiv.comp /-
/-- Composition of first-order equivalences -/
@[trans]
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with toFun := hnp ∘ hmn }
#align first_order.language.equiv.comp FirstOrder.Language.Equiv.comp
-/

/- warning: first_order.language.equiv.comp_apply -> FirstOrder.Language.Equiv.comp_apply is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] (g : FirstOrder.Language.Equiv.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (f : FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (x : M), Eq.{succ u5} P (coeFn.{max (succ u3) (succ u5), max (succ u3) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u5} L M P _inst_1 _inst_3) => M -> P) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u5} L M P _inst_1 _inst_3) (FirstOrder.Language.Equiv.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 g f) x) (coeFn.{max (succ u4) (succ u5), max (succ u4) (succ u5)} (FirstOrder.Language.Equiv.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u4, u5} L N P _inst_2 _inst_3) => N -> P) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u4, u5} L N P _inst_2 _inst_3) g (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (fun (_x : FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) => M -> N) (FirstOrder.Language.Equiv.hasCoeToFun.{u1, u2, u3, u4} L M N _inst_1 _inst_2) f x))
but is expected to have type
  forall {L : FirstOrder.Language.{u2, u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_1 : FirstOrder.Language.Structure.{u2, u3, u4} L M] [_inst_2 : FirstOrder.Language.Structure.{u2, u3, u5} L N] {P : Type.{u1}} [_inst_3 : FirstOrder.Language.Structure.{u2, u3, u1} L P] (g : FirstOrder.Language.Equiv.{u2, u3, u5, u1} L N P _inst_2 _inst_3) (f : FirstOrder.Language.Equiv.{u2, u3, u4, u5} L M N _inst_1 _inst_2) (x : M), Eq.{succ u1} ((fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => P) x) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M P _inst_1 _inst_3) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => P) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M P _inst_1 _inst_3) M P (EquivLike.toEmbeddingLike.{max (succ u4) (succ u1), succ u4, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u4, u1} L M P _inst_1 _inst_3) M P (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u1} L M P _inst_1 _inst_3))) (FirstOrder.Language.Equiv.comp.{u2, u3, u4, u5, u1} L M N _inst_1 _inst_2 P _inst_3 g f) x) (FunLike.coe.{max (succ u5) (succ u1), succ u5, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u5, u1} L N P _inst_2 _inst_3) N (fun (_x : N) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : N) => P) _x) (EmbeddingLike.toFunLike.{max (succ u5) (succ u1), succ u5, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u5, u1} L N P _inst_2 _inst_3) N P (EquivLike.toEmbeddingLike.{max (succ u5) (succ u1), succ u5, succ u1} (FirstOrder.Language.Equiv.{u2, u3, u5, u1} L N P _inst_2 _inst_3) N P (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u5, u1} L N P _inst_2 _inst_3))) g (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (FirstOrder.Language.Equiv.{u2, u3, u4, u5} L M N _inst_1 _inst_2) M (fun (_x : M) => (fun (a._@.Mathlib.ModelTheory.Basic._hyg.8209 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u5), succ u4, succ u5} (FirstOrder.Language.Equiv.{u2, u3, u4, u5} L M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u4) (succ u5), succ u4, succ u5} (FirstOrder.Language.Equiv.{u2, u3, u4, u5} L M N _inst_1 _inst_2) M N (FirstOrder.Language.Equiv.instEquivLikeEquiv.{u2, u3, u4, u5} L M N _inst_1 _inst_2))) f x))
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.comp_apply FirstOrder.Language.Equiv.comp_applyₓ'. -/
@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.equiv.comp_apply FirstOrder.Language.Equiv.comp_apply

/- warning: first_order.language.equiv.comp_assoc -> FirstOrder.Language.Equiv.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {M : Type.{u3}} {N : Type.{u4}} [_inst_1 : FirstOrder.Language.Structure.{u1, u2, u3} L M] [_inst_2 : FirstOrder.Language.Structure.{u1, u2, u4} L N] {P : Type.{u5}} [_inst_3 : FirstOrder.Language.Structure.{u1, u2, u5} L P] {Q : Type.{u6}} [_inst_4 : FirstOrder.Language.Structure.{u1, u2, u6} L Q] (f : FirstOrder.Language.Equiv.{u1, u2, u3, u4} L M N _inst_1 _inst_2) (g : FirstOrder.Language.Equiv.{u1, u2, u4, u5} L N P _inst_2 _inst_3) (h : FirstOrder.Language.Equiv.{u1, u2, u5, u6} L P Q _inst_3 _inst_4), Eq.{max (succ u3) (succ u6)} (FirstOrder.Language.Equiv.{u1, u2, u3, u6} L M Q _inst_1 _inst_4) (FirstOrder.Language.Equiv.comp.{u1, u2, u3, u4, u6} L M N _inst_1 _inst_2 Q _inst_4 (FirstOrder.Language.Equiv.comp.{u1, u2, u4, u5, u6} L N P _inst_2 _inst_3 Q _inst_4 h g) f) (FirstOrder.Language.Equiv.comp.{u1, u2, u3, u5, u6} L M P _inst_1 _inst_3 Q _inst_4 h (FirstOrder.Language.Equiv.comp.{u1, u2, u3, u4, u5} L M N _inst_1 _inst_2 P _inst_3 g f))
but is expected to have type
  forall {L : FirstOrder.Language.{u3, u4}} {M : Type.{u5}} {N : Type.{u6}} [_inst_1 : FirstOrder.Language.Structure.{u3, u4, u5} L M] [_inst_2 : FirstOrder.Language.Structure.{u3, u4, u6} L N] {P : Type.{u2}} [_inst_3 : FirstOrder.Language.Structure.{u3, u4, u2} L P] {Q : Type.{u1}} [_inst_4 : FirstOrder.Language.Structure.{u3, u4, u1} L Q] (f : FirstOrder.Language.Equiv.{u3, u4, u5, u6} L M N _inst_1 _inst_2) (g : FirstOrder.Language.Equiv.{u3, u4, u6, u2} L N P _inst_2 _inst_3) (h : FirstOrder.Language.Equiv.{u3, u4, u2, u1} L P Q _inst_3 _inst_4), Eq.{max (succ u5) (succ u1)} (FirstOrder.Language.Equiv.{u3, u4, u5, u1} L M Q _inst_1 _inst_4) (FirstOrder.Language.Equiv.comp.{u3, u4, u5, u6, u1} L M N _inst_1 _inst_2 Q _inst_4 (FirstOrder.Language.Equiv.comp.{u3, u4, u6, u2, u1} L N P _inst_2 _inst_3 Q _inst_4 h g) f) (FirstOrder.Language.Equiv.comp.{u3, u4, u5, u2, u1} L M P _inst_1 _inst_3 Q _inst_4 h (FirstOrder.Language.Equiv.comp.{u3, u4, u5, u6, u2} L M N _inst_1 _inst_2 P _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align first_order.language.equiv.comp_assoc FirstOrder.Language.Equiv.comp_assocₓ'. -/
/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.equiv.comp_assoc FirstOrder.Language.Equiv.comp_assoc

end Equiv

/- warning: first_order.language.strong_hom_class.to_equiv -> FirstOrder.Language.StrongHomClass.toEquiv is a dubious translation:
lean 3 declaration is
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : EquivLike.{succ u3, succ u4, succ u5} F M N] [_inst_8 : FirstOrder.Language.StrongHomClass.{u1, u2, u3, u4, u5} L F M N (EmbeddingLike.toFunLike.{succ u3, succ u4, succ u5} F M N (EquivLike.toEmbeddingLike.{succ u3, succ u4, succ u5} F M N _inst_7)) _inst_5 _inst_6], F -> (FirstOrder.Language.Equiv.{u1, u2, u4, u5} L M N _inst_5 _inst_6)
but is expected to have type
  forall {L : FirstOrder.Language.{u1, u2}} {F : Type.{u3}} {M : Type.{u4}} {N : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u4} L M] [_inst_6 : FirstOrder.Language.Structure.{u1, u2, u5} L N] [_inst_7 : EquivLike.{succ u3, succ u4, succ u5} F M N] [_inst_8 : FirstOrder.Language.StrongHomClass.{u2, u1, u3, u4, u5} L F M N (EmbeddingLike.toFunLike.{succ u3, succ u4, succ u5} F M N (EquivLike.toEmbeddingLike.{succ u3, succ u4, succ u5} F M N _inst_7)) _inst_5 _inst_6], F -> (FirstOrder.Language.Equiv.{u1, u2, u4, u5} L M N _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align first_order.language.strong_hom_class.to_equiv FirstOrder.Language.StrongHomClass.toEquivₓ'. -/
/-- Any element of a bijective `strong_hom_class` can be realized as a first_order isomorphism. -/
def StrongHomClass.toEquiv {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N]
    [StrongHomClass L F M N] : F → M ≃[L] N := fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, fun _ => HomClass.map_fun φ,
    fun _ => StrongHomClass.map_rel φ⟩
#align first_order.language.strong_hom_class.to_equiv FirstOrder.Language.StrongHomClass.toEquiv

section SumStructure

variable (L₁ L₂ : Language) (S : Type _) [L₁.Structure S] [L₂.Structure S]

#print FirstOrder.Language.sumStructure /-
instance sumStructure : (L₁.Sum L₂).Structure S
    where
  funMap n := Sum.elim funMap funMap
  rel_map n := Sum.elim RelMap RelMap
#align first_order.language.sum_Structure FirstOrder.Language.sumStructure
-/

variable {L₁ L₂ S}

/- warning: first_order.language.fun_map_sum_inl -> FirstOrder.Language.funMap_sum_inl is a dubious translation:
lean 3 declaration is
  forall {L₁ : FirstOrder.Language.{u1, u2}} {L₂ : FirstOrder.Language.{u3, u4}} {S : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u5} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u3, u4, u5} L₂ S] {n : Nat} (f : FirstOrder.Language.Functions.{u1, u2} L₁ n), Eq.{succ u5} (((Fin n) -> S) -> S) (FirstOrder.Language.Structure.funMap.{max u1 u3, max u2 u4, u5} (FirstOrder.Language.sum.{u1, u2, u3, u4} L₁ L₂) S (FirstOrder.Language.sumStructure.{u1, u2, u3, u4, u5} L₁ L₂ S _inst_5 _inst_6) n (Sum.inl.{u1, u3} (FirstOrder.Language.Functions.{u1, u2} L₁ n) (FirstOrder.Language.Functions.{u3, u4} L₂ n) f)) (FirstOrder.Language.Structure.funMap.{u1, u2, u5} L₁ S _inst_5 n f)
but is expected to have type
  forall {L₁ : FirstOrder.Language.{u5, u4}} {L₂ : FirstOrder.Language.{u2, u1}} {S : Type.{u3}} [_inst_5 : FirstOrder.Language.Structure.{u5, u4, u3} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u2, u1, u3} L₂ S] {n : Nat} (f : FirstOrder.Language.Functions.{u5, u4} L₁ n), Eq.{succ u3} (((Fin n) -> S) -> S) (FirstOrder.Language.Structure.funMap.{max u2 u5, max u1 u4, u3} (FirstOrder.Language.sum.{u5, u4, u2, u1} L₁ L₂) S (FirstOrder.Language.sumStructure.{u5, u4, u2, u1, u3} L₁ L₂ S _inst_5 _inst_6) n (Sum.inl.{u5, u2} (FirstOrder.Language.Functions.{u5, u4} L₁ n) (FirstOrder.Language.Functions.{u2, u1} L₂ n) f)) (FirstOrder.Language.Structure.funMap.{u5, u4, u3} L₁ S _inst_5 n f)
Case conversion may be inaccurate. Consider using '#align first_order.language.fun_map_sum_inl FirstOrder.Language.funMap_sum_inlₓ'. -/
@[simp]
theorem funMap_sum_inl {n : ℕ} (f : L₁.Functions n) :
    @funMap (L₁.Sum L₂) S _ n (Sum.inl f) = funMap f :=
  rfl
#align first_order.language.fun_map_sum_inl FirstOrder.Language.funMap_sum_inl

/- warning: first_order.language.fun_map_sum_inr -> FirstOrder.Language.funMap_sum_inr is a dubious translation:
lean 3 declaration is
  forall {L₁ : FirstOrder.Language.{u1, u2}} {L₂ : FirstOrder.Language.{u3, u4}} {S : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u5} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u3, u4, u5} L₂ S] {n : Nat} (f : FirstOrder.Language.Functions.{u3, u4} L₂ n), Eq.{succ u5} (((Fin n) -> S) -> S) (FirstOrder.Language.Structure.funMap.{max u1 u3, max u2 u4, u5} (FirstOrder.Language.sum.{u1, u2, u3, u4} L₁ L₂) S (FirstOrder.Language.sumStructure.{u1, u2, u3, u4, u5} L₁ L₂ S _inst_5 _inst_6) n (Sum.inr.{u1, u3} (FirstOrder.Language.Functions.{u1, u2} L₁ n) (FirstOrder.Language.Functions.{u3, u4} L₂ n) f)) (FirstOrder.Language.Structure.funMap.{u3, u4, u5} L₂ S _inst_6 n f)
but is expected to have type
  forall {L₁ : FirstOrder.Language.{u2, u1}} {L₂ : FirstOrder.Language.{u5, u4}} {S : Type.{u3}} [_inst_5 : FirstOrder.Language.Structure.{u2, u1, u3} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u5, u4, u3} L₂ S] {n : Nat} (f : FirstOrder.Language.Functions.{u5, u4} L₂ n), Eq.{succ u3} (((Fin n) -> S) -> S) (FirstOrder.Language.Structure.funMap.{max u5 u2, max u4 u1, u3} (FirstOrder.Language.sum.{u2, u1, u5, u4} L₁ L₂) S (FirstOrder.Language.sumStructure.{u2, u1, u5, u4, u3} L₁ L₂ S _inst_5 _inst_6) n (Sum.inr.{u2, u5} (FirstOrder.Language.Functions.{u2, u1} L₁ n) (FirstOrder.Language.Functions.{u5, u4} L₂ n) f)) (FirstOrder.Language.Structure.funMap.{u5, u4, u3} L₂ S _inst_6 n f)
Case conversion may be inaccurate. Consider using '#align first_order.language.fun_map_sum_inr FirstOrder.Language.funMap_sum_inrₓ'. -/
@[simp]
theorem funMap_sum_inr {n : ℕ} (f : L₂.Functions n) :
    @funMap (L₁.Sum L₂) S _ n (Sum.inr f) = funMap f :=
  rfl
#align first_order.language.fun_map_sum_inr FirstOrder.Language.funMap_sum_inr

/- warning: first_order.language.rel_map_sum_inl -> FirstOrder.Language.relMap_sum_inl is a dubious translation:
lean 3 declaration is
  forall {L₁ : FirstOrder.Language.{u1, u2}} {L₂ : FirstOrder.Language.{u3, u4}} {S : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u5} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u3, u4, u5} L₂ S] {n : Nat} (R : FirstOrder.Language.Relations.{u1, u2} L₁ n), Eq.{succ u5} (((Fin n) -> S) -> Prop) (FirstOrder.Language.Structure.RelMap.{max u1 u3, max u2 u4, u5} (FirstOrder.Language.sum.{u1, u2, u3, u4} L₁ L₂) S (FirstOrder.Language.sumStructure.{u1, u2, u3, u4, u5} L₁ L₂ S _inst_5 _inst_6) n (Sum.inl.{u2, u4} (FirstOrder.Language.Relations.{u1, u2} L₁ n) (FirstOrder.Language.Relations.{u3, u4} L₂ n) R)) (FirstOrder.Language.Structure.RelMap.{u1, u2, u5} L₁ S _inst_5 n R)
but is expected to have type
  forall {L₁ : FirstOrder.Language.{u5, u4}} {L₂ : FirstOrder.Language.{u2, u1}} {S : Type.{u3}} [_inst_5 : FirstOrder.Language.Structure.{u5, u4, u3} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u2, u1, u3} L₂ S] {n : Nat} (R : FirstOrder.Language.Relations.{u5, u4} L₁ n), Eq.{succ u3} (((Fin n) -> S) -> Prop) (FirstOrder.Language.Structure.RelMap.{max u2 u5, max u1 u4, u3} (FirstOrder.Language.sum.{u5, u4, u2, u1} L₁ L₂) S (FirstOrder.Language.sumStructure.{u5, u4, u2, u1, u3} L₁ L₂ S _inst_5 _inst_6) n (Sum.inl.{u4, u1} (FirstOrder.Language.Relations.{u5, u4} L₁ n) (FirstOrder.Language.Relations.{u2, u1} L₂ n) R)) (FirstOrder.Language.Structure.RelMap.{u5, u4, u3} L₁ S _inst_5 n R)
Case conversion may be inaccurate. Consider using '#align first_order.language.rel_map_sum_inl FirstOrder.Language.relMap_sum_inlₓ'. -/
@[simp]
theorem relMap_sum_inl {n : ℕ} (R : L₁.Relations n) :
    @RelMap (L₁.Sum L₂) S _ n (Sum.inl R) = RelMap R :=
  rfl
#align first_order.language.rel_map_sum_inl FirstOrder.Language.relMap_sum_inl

/- warning: first_order.language.rel_map_sum_inr -> FirstOrder.Language.relMap_sum_inr is a dubious translation:
lean 3 declaration is
  forall {L₁ : FirstOrder.Language.{u1, u2}} {L₂ : FirstOrder.Language.{u3, u4}} {S : Type.{u5}} [_inst_5 : FirstOrder.Language.Structure.{u1, u2, u5} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u3, u4, u5} L₂ S] {n : Nat} (R : FirstOrder.Language.Relations.{u3, u4} L₂ n), Eq.{succ u5} (((Fin n) -> S) -> Prop) (FirstOrder.Language.Structure.RelMap.{max u1 u3, max u2 u4, u5} (FirstOrder.Language.sum.{u1, u2, u3, u4} L₁ L₂) S (FirstOrder.Language.sumStructure.{u1, u2, u3, u4, u5} L₁ L₂ S _inst_5 _inst_6) n (Sum.inr.{u2, u4} (FirstOrder.Language.Relations.{u1, u2} L₁ n) (FirstOrder.Language.Relations.{u3, u4} L₂ n) R)) (FirstOrder.Language.Structure.RelMap.{u3, u4, u5} L₂ S _inst_6 n R)
but is expected to have type
  forall {L₁ : FirstOrder.Language.{u2, u1}} {L₂ : FirstOrder.Language.{u5, u4}} {S : Type.{u3}} [_inst_5 : FirstOrder.Language.Structure.{u2, u1, u3} L₁ S] [_inst_6 : FirstOrder.Language.Structure.{u5, u4, u3} L₂ S] {n : Nat} (R : FirstOrder.Language.Relations.{u5, u4} L₂ n), Eq.{succ u3} (((Fin n) -> S) -> Prop) (FirstOrder.Language.Structure.RelMap.{max u5 u2, max u4 u1, u3} (FirstOrder.Language.sum.{u2, u1, u5, u4} L₁ L₂) S (FirstOrder.Language.sumStructure.{u2, u1, u5, u4, u3} L₁ L₂ S _inst_5 _inst_6) n (Sum.inr.{u1, u4} (FirstOrder.Language.Relations.{u2, u1} L₁ n) (FirstOrder.Language.Relations.{u5, u4} L₂ n) R)) (FirstOrder.Language.Structure.RelMap.{u5, u4, u3} L₂ S _inst_6 n R)
Case conversion may be inaccurate. Consider using '#align first_order.language.rel_map_sum_inr FirstOrder.Language.relMap_sum_inrₓ'. -/
@[simp]
theorem relMap_sum_inr {n : ℕ} (R : L₂.Relations n) :
    @RelMap (L₁.Sum L₂) S _ n (Sum.inr R) = RelMap R :=
  rfl
#align first_order.language.rel_map_sum_inr FirstOrder.Language.relMap_sum_inr

end SumStructure

section Empty

section

variable [Language.empty.Structure M] [Language.empty.Structure N]

#print FirstOrder.Language.empty.nonempty_embedding_iff /-
@[simp]
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[Language.empty] N) ↔ Cardinal.lift.{w'} (#M) ≤ Cardinal.lift.{w} (#N) :=
  trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map fun f => { toEmbedding := f }⟩
    Cardinal.lift_mk_le'.symm
#align first_order.language.empty.nonempty_embedding_iff FirstOrder.Language.empty.nonempty_embedding_iff
-/

#print FirstOrder.Language.empty.nonempty_equiv_iff /-
@[simp]
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[Language.empty] N) ↔ Cardinal.lift.{w'} (#M) = Cardinal.lift.{w} (#N) :=
  trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm
#align first_order.language.empty.nonempty_equiv_iff FirstOrder.Language.empty.nonempty_equiv_iff
-/

end

#print FirstOrder.Language.emptyStructure /-
instance emptyStructure : Language.empty.Structure M :=
  ⟨fun _ => Empty.elim, fun _ => Empty.elim⟩
#align first_order.language.empty_Structure FirstOrder.Language.emptyStructure
-/

instance : Unique (Language.empty.Structure M) :=
  ⟨⟨Language.emptyStructure⟩, fun a => by
    ext (n f)
    · exact Empty.elim f
    · exact Subsingleton.elim _ _⟩

#print FirstOrder.Language.strongHomClassEmpty /-
instance (priority := 100) strongHomClassEmpty {F M N} [FunLike F M fun _ => N] :
    StrongHomClass Language.empty F M N :=
  ⟨fun _ _ f => Empty.elim f, fun _ _ r => Empty.elim r⟩
#align first_order.language.strong_hom_class_empty FirstOrder.Language.strongHomClassEmpty
-/

#print Function.emptyHom /-
/-- Makes a `language.empty.hom` out of any function. -/
@[simps]
def Function.emptyHom (f : M → N) : M →[Language.empty] N where toFun := f
#align function.empty_hom Function.emptyHom
-/

#print Embedding.empty /-
/-- Makes a `language.empty.embedding` out of any function. -/
@[simps]
def Embedding.empty (f : M ↪ N) : M ↪[Language.empty] N where toEmbedding := f
#align embedding.empty Embedding.empty
-/

#print Equiv.empty /-
/-- Makes a `language.empty.equiv` out of any function. -/
@[simps]
def Equiv.empty (f : M ≃ N) : M ≃[Language.empty] N where toEquiv := f
#align equiv.empty Equiv.empty
-/

end Empty

end Language

end FirstOrder

namespace Equiv

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

open FirstOrder

variable {L : Language} {M : Type _} {N : Type _} [L.Structure M]

#print Equiv.inducedStructure /-
/-- A structure induced by a bijection. -/
@[simps]
def inducedStructure (e : M ≃ N) : L.Structure N :=
  ⟨fun n f x => e (funMap f (e.symm ∘ x)), fun n r x => RelMap r (e.symm ∘ x)⟩
#align equiv.induced_Structure Equiv.inducedStructure
-/

#print Equiv.inducedStructureEquiv /-
/-- A bijection as a first-order isomorphism with the induced structure on the codomain. -/
@[simps]
def inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStructure e) :=
  { e with
    map_fun' := fun n f x => by simp [← Function.comp.assoc e.symm e x]
    map_rel' := fun n r x => by simp [← Function.comp.assoc e.symm e x] }
#align equiv.induced_Structure_equiv Equiv.inducedStructureEquiv
-/

end Equiv

