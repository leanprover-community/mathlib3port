/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.order
! leanprover-community/mathlib commit 6cf5900728239efa287df7761ec2a1ac9cf39b29
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Semantics

/-!
# Ordered First-Ordered Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.ordered_structure` indicates that the `≤` symbol in an ordered language
is interpreted as the actual relation `≤` in a particular structure.
* `first_order.language.linear_order_theory` and similar define the theories of preorders,
partial orders, and linear orders.
* `first_order.language.DLO` defines the theory of dense linear orders without endpoints, a
particularly useful example in model theory.

## Main Results
* `partial_order`s model the theory of partial orders, `linear_order`s model the theory of
linear orders, and dense linear orders without endpoints model `Theory.DLO`.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

#print FirstOrder.Language.order /-
/-- The language consisting of a single relation representing `≤`. -/
protected def order : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit
#align first_order.language.order FirstOrder.Language.order
-/

#print FirstOrder.Language.orderStructure /-
instance orderStructure [LE M] : Language.order.Structure M :=
  Structure.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => (· ≤ ·)
#align first_order.language.order_Structure FirstOrder.Language.orderStructure
-/

namespace Order

instance : IsRelational Language.order :=
  Language.isRelational_mk₂

instance : Subsingleton (Language.order.Relations n) :=
  Language.subsingleton_mk₂_relations

end Order

#print FirstOrder.Language.IsOrdered /-
/-- A language is ordered if it has a symbol representing `≤`. -/
class IsOrdered (L : Language.{u, v}) where
  leSymb : L.Relations 2
#align first_order.language.is_ordered FirstOrder.Language.IsOrdered
-/

export IsOrdered (leSymb)

section IsOrdered

variable [IsOrdered L]

#print FirstOrder.Language.Term.le /-
/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def Term.le (t₁ t₂ : L.term (Sum α (Fin n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂
#align first_order.language.term.le FirstOrder.Language.Term.le
-/

#print FirstOrder.Language.Term.lt /-
/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
def Term.lt (t₁ t₂ : L.term (Sum α (Fin n))) : L.BoundedFormula α n :=
  t₁.le t₂ ⊓ ∼(t₂.le t₁)
#align first_order.language.term.lt FirstOrder.Language.Term.lt
-/

variable (L)

#print FirstOrder.Language.orderLHom /-
/-- The language homomorphism sending the unique symbol `≤` of `language.order` to `≤` in an ordered
 language. -/
def orderLHom : Language.order →ᴸ L :=
  LHom.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => leSymb
#align first_order.language.order_Lhom FirstOrder.Language.orderLHom
-/

end IsOrdered

instance : IsOrdered Language.order :=
  ⟨Unit.unit⟩

#print FirstOrder.Language.orderLHom_leSymb /-
@[simp]
theorem orderLHom_leSymb [L.IsOrdered] :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl
#align first_order.language.order_Lhom_le_symb FirstOrder.Language.orderLHom_leSymb
-/

#print FirstOrder.Language.orderLHom_order /-
@[simp]
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
#align first_order.language.order_Lhom_order FirstOrder.Language.orderLHom_order
-/

instance : IsOrdered (L.Sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

section

variable (L) [IsOrdered L]

#print FirstOrder.Language.preorderTheory /-
/-- The theory of preorders. -/
def preorderTheory : L.Theory :=
  {leSymb.Reflexive, leSymb.Transitive}
#align first_order.language.preorder_theory FirstOrder.Language.preorderTheory
-/

#print FirstOrder.Language.partialOrderTheory /-
/-- The theory of partial orders. -/
def partialOrderTheory : L.Theory :=
  {leSymb.Reflexive, leSymb.antisymmetric, leSymb.Transitive}
#align first_order.language.partial_order_theory FirstOrder.Language.partialOrderTheory
-/

#print FirstOrder.Language.linearOrderTheory /-
/-- The theory of linear orders. -/
def linearOrderTheory : L.Theory :=
  {leSymb.Reflexive, leSymb.antisymmetric, leSymb.Transitive, leSymb.Total}
#align first_order.language.linear_order_theory FirstOrder.Language.linearOrderTheory
-/

#print FirstOrder.Language.noTopOrderSentence /-
/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.   -/
def noTopOrderSentence : L.Sentence :=
  ∀'∃'∼((&1).le &0)
#align first_order.language.no_top_order_sentence FirstOrder.Language.noTopOrderSentence
-/

#print FirstOrder.Language.noBotOrderSentence /-
/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
def noBotOrderSentence : L.Sentence :=
  ∀'∃'∼((&0).le &1)
#align first_order.language.no_bot_order_sentence FirstOrder.Language.noBotOrderSentence
-/

#print FirstOrder.Language.denselyOrderedSentence /-
/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
def denselyOrderedSentence : L.Sentence :=
  ∀'∀'((&0).lt &1 ⟹ ∃'((&0).lt &2 ⊓ (&2).lt &1))
#align first_order.language.densely_ordered_sentence FirstOrder.Language.denselyOrderedSentence
-/

#print FirstOrder.Language.dlo /-
/-- The theory of dense linear orders without endpoints. -/
def dlo : L.Theory :=
  L.linearOrderTheory ∪ {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}
#align first_order.language.DLO FirstOrder.Language.dlo
-/

end

variable (L M)

#print FirstOrder.Language.OrderedStructure /-
/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
abbrev OrderedStructure [IsOrdered L] [LE M] [L.Structure M] : Prop :=
  LHom.IsExpansionOn (orderLHom L) M
#align first_order.language.ordered_structure FirstOrder.Language.OrderedStructure
-/

variable {L M}

#print FirstOrder.Language.orderedStructure_iff /-
@[simp]
theorem orderedStructure_iff [IsOrdered L] [LE M] [L.Structure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  Iff.rfl
#align first_order.language.ordered_structure_iff FirstOrder.Language.orderedStructure_iff
-/

#print FirstOrder.Language.orderedStructure_LE /-
instance orderedStructure_LE [LE M] : OrderedStructure Language.order M :=
  by
  rw [ordered_structure_iff, order_Lhom_order]
  exact Lhom.id_is_expansion_on M
#align first_order.language.ordered_structure_has_le FirstOrder.Language.orderedStructure_LE
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_preorder [Preorder M] : M ⊨ Language.order.preorderTheory :=
  by
  simp only [preorder_theory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, forall_eq,
    relations.realize_transitive]
  exact ⟨le_refl, fun _ _ _ => le_trans⟩
#align first_order.language.model_preorder FirstOrder.Language.model_preorder

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_partialOrder [PartialOrder M] : M ⊨ Language.order.partialOrderTheory :=
  by
  simp only [partial_order_theory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    forall_eq, relations.realize_transitive]
  exact ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans⟩
#align first_order.language.model_partial_order FirstOrder.Language.model_partialOrder

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_linearOrder [LinearOrder M] : M ⊨ Language.order.linearOrderTheory :=
  by
  simp only [linear_order_theory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    relations.realize_transitive, forall_eq, relations.realize_total]
  exact ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans, le_total⟩
#align first_order.language.model_linear_order FirstOrder.Language.model_linearOrder

section OrderedStructure

variable [IsOrdered L] [L.Structure M]

#print FirstOrder.Language.relMap_leSymb /-
@[simp]
theorem relMap_leSymb [LE M] [L.OrderedStructure M] {a b : M} :
    RelMap (leSymb : L.Relations 2) ![a, b] ↔ a ≤ b :=
  by
  rw [← order_Lhom_le_symb, Lhom.map_on_relation]
  rfl
#align first_order.language.rel_map_le_symb FirstOrder.Language.relMap_leSymb
-/

#print FirstOrder.Language.Term.realize_le /-
@[simp]
theorem Term.realize_le [LE M] [L.OrderedStructure M] {t₁ t₂ : L.term (Sum α (Fin n))} {v : α → M}
    {xs : Fin n → M} :
    (t₁.le t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [term.le]
#align first_order.language.term.realize_le FirstOrder.Language.Term.realize_le
-/

@[simp]
theorem Term.realize_lt [Preorder M] [L.OrderedStructure M] {t₁ t₂ : L.term (Sum α (Fin n))}
    {v : α → M} {xs : Fin n → M} :
    (t₁.lt t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [term.lt, lt_iff_le_not_le]
#align first_order.language.term.realize_lt FirstOrder.Language.Term.realize_lt

end OrderedStructure

section LE

variable [LE M]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.realize_noTopOrder_iff /-
theorem realize_noTopOrder_iff : M ⊨ Language.order.noTopOrderSentence ↔ NoTopOrder M :=
  by
  simp only [no_top_order_sentence, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le, Sum.elim_inr]
  refine' ⟨fun h => ⟨fun a => h a⟩, _⟩
  intro h a
  exact exists_not_le a
#align first_order.language.realize_no_top_order_iff FirstOrder.Language.realize_noTopOrder_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.realize_noTopOrder /-
@[simp]
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ Language.order.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h
#align first_order.language.realize_no_top_order FirstOrder.Language.realize_noTopOrder
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.realize_noBotOrder_iff /-
theorem realize_noBotOrder_iff : M ⊨ Language.order.noBotOrderSentence ↔ NoBotOrder M :=
  by
  simp only [no_bot_order_sentence, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le, Sum.elim_inr]
  refine' ⟨fun h => ⟨fun a => h a⟩, _⟩
  intro h a
  exact exists_not_ge a
#align first_order.language.realize_no_bot_order_iff FirstOrder.Language.realize_noBotOrder_iff
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FirstOrder.Language.realize_noBotOrder /-
@[simp]
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ Language.order.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h
#align first_order.language.realize_no_bot_order FirstOrder.Language.realize_noBotOrder
-/

end LE

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_denselyOrdered_iff [Preorder M] :
    M ⊨ Language.order.denselyOrderedSentence ↔ DenselyOrdered M :=
  by
  simp only [densely_ordered_sentence, sentence.realize, formula.realize,
    bounded_formula.realize_imp, bounded_formula.realize_all, realize, term.realize_lt,
    Sum.elim_inr, bounded_formula.realize_ex, bounded_formula.realize_inf]
  refine' ⟨fun h => ⟨fun a b ab => h a b ab⟩, _⟩
  intro h a b ab
  exact exists_between ab
#align first_order.language.realize_densely_ordered_iff FirstOrder.Language.realize_denselyOrdered_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem realize_denselyOrdered [Preorder M] [h : DenselyOrdered M] :
    M ⊨ Language.order.denselyOrderedSentence :=
  realize_denselyOrdered_iff.2 h
#align first_order.language.realize_densely_ordered FirstOrder.Language.realize_denselyOrdered

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_dlo [LinearOrder M] [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] :
    M ⊨ Language.order.dlo :=
  by
  simp only [DLO, Set.union_insert, Set.union_singleton, Theory.model_iff, Set.mem_insert_iff,
    forall_eq_or_imp, realize_no_top_order, realize_no_bot_order, realize_densely_ordered,
    true_and_iff]
  rw [← Theory.model_iff]
  infer_instance
#align first_order.language.model_DLO FirstOrder.Language.model_dlo

end Language

end FirstOrder

