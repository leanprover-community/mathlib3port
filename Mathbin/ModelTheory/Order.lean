/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.Semantics

/-!
# Ordered First-Ordered Structures
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.is_ordered_structure` indicates that a structure over a
* `first_order.language.Theory.linear_order` and similar define the theories of preorders,
partial orders, and linear orders.
* `first_order.language.Theory.DLO` defines the theory of dense linear orders without endpoints, a
particularly useful example in model theory.


## Main Results
* `partial_order`s model the theory of partial orders, `linear_order`s model the theory of
linear orders, and dense linear orders without endpoints model `Theory.DLO`.

-/


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder

open StructureCat

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The language consisting of a single relation representing `≤`. -/
protected def order : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit
#align first_order.language.order FirstOrder.Language.order

namespace Order

instance structure [LE M] : Language.order.StructureCat M :=
  StructureCat.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => (· ≤ ·)
#align first_order.language.order.Structure FirstOrder.Language.order.structure

instance : IsRelational Language.order :=
  language.is_relational_mk₂

instance : Subsingleton (Language.order.Relations n) :=
  language.subsingleton_mk₂_relations

end Order

/-- A language is ordered if it has a symbol representing `≤`. -/
class IsOrdered (L : Language.{u, v}) where
  leSymb : L.Relations 2
#align first_order.language.is_ordered FirstOrder.Language.IsOrdered

export IsOrdered (leSymb)

section IsOrdered

variable [IsOrdered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def Term.le (t₁ t₂ : L.term (Sum α (Fin n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂
#align first_order.language.term.le FirstOrder.Language.Term.le

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
def Term.lt (t₁ t₂ : L.term (Sum α (Fin n))) : L.BoundedFormula α n :=
  t₁.le t₂ ⊓ ∼(t₂.le t₁)
#align first_order.language.term.lt FirstOrder.Language.Term.lt

variable (L)

/-- The language homomorphism sending the unique symbol `≤` of `language.order` to `≤` in an ordered
 language. -/
def orderLhom : language.order →ᴸ L :=
  LhomCat.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => leSymb
#align first_order.language.order_Lhom FirstOrder.Language.orderLhom

end IsOrdered

instance : IsOrdered Language.order :=
  ⟨Unit.unit⟩

@[simp]
theorem order_Lhom_le_symb [L.IsOrdered] : (orderLhom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl
#align first_order.language.order_Lhom_le_symb FirstOrder.Language.order_Lhom_le_symb

@[simp]
theorem order_Lhom_order : orderLhom Language.order = LhomCat.id Language.order :=
  LhomCat.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
#align first_order.language.order_Lhom_order FirstOrder.Language.order_Lhom_order

instance : IsOrdered (L.Sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

/-- The theory of preorders. -/
protected def TheoryCat.Preorder : Language.order.TheoryCat :=
  {leSymb.Reflexive, leSymb.Transitive}
#align first_order.language.Theory.preorder FirstOrder.Language.TheoryCat.Preorder

/-- The theory of partial orders. -/
protected def TheoryCat.PartialOrder : Language.order.TheoryCat :=
  {leSymb.Reflexive, leSymb.antisymmetric, leSymb.Transitive}
#align first_order.language.Theory.partial_order FirstOrder.Language.TheoryCat.PartialOrder

/-- The theory of linear orders. -/
protected def TheoryCat.LinearOrder : Language.order.TheoryCat :=
  {leSymb.Reflexive, leSymb.antisymmetric, leSymb.Transitive, leSymb.Total}
#align first_order.language.Theory.linear_order FirstOrder.Language.TheoryCat.LinearOrder

/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.   -/
protected def Sentence.noTopOrder : Language.order.Sentence :=
  ∀'∃'∼((&1).le &0)
#align first_order.language.sentence.no_top_order FirstOrder.Language.Sentence.noTopOrder

/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
protected def Sentence.noBotOrder : Language.order.Sentence :=
  ∀'∃'∼((&0).le &1)
#align first_order.language.sentence.no_bot_order FirstOrder.Language.Sentence.noBotOrder

/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
protected def Sentence.denselyOrdered : Language.order.Sentence :=
  ∀'∀'((&0).lt &1 ⟹ ∃'((&0).lt &2 ⊓ (&2).lt &1))
#align first_order.language.sentence.densely_ordered FirstOrder.Language.Sentence.denselyOrdered

/-- The theory of dense linear orders without endpoints. -/
protected def TheoryCat.DLO : Language.order.TheoryCat :=
  Theory.linear_order ∪ {Sentence.noTopOrder, Sentence.noBotOrder, Sentence.denselyOrdered}
#align first_order.language.Theory.DLO FirstOrder.Language.TheoryCat.DLO

variable (L M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
abbrev IsOrderedStructure [IsOrdered L] [LE M] [L.StructureCat M] : Prop :=
  LhomCat.IsExpansionOn (orderLhom L) M
#align first_order.language.is_ordered_structure FirstOrder.Language.IsOrderedStructure

variable {L M}

@[simp]
theorem is_ordered_structure_iff [IsOrdered L] [LE M] [L.StructureCat M] :
    L.IsOrderedStructure M ↔ LhomCat.IsExpansionOn (orderLhom L) M :=
  Iff.rfl
#align first_order.language.is_ordered_structure_iff FirstOrder.Language.is_ordered_structure_iff

instance is_ordered_structure_has_le [LE M] : IsOrderedStructure Language.order M := by
  rw [is_ordered_structure_iff, order_Lhom_order]
  exact Lhom.id_is_expansion_on M
#align first_order.language.is_ordered_structure_has_le FirstOrder.Language.is_ordered_structure_has_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_preorder [Preorder M] : M ⊨ Theory.preorder := by
  simp only [Theory.preorder, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    relations.realize_reflexive, rel_map_apply₂, forall_eq, relations.realize_transitive]
  exact ⟨le_refl, fun _ _ _ => le_trans⟩
#align first_order.language.model_preorder FirstOrder.Language.model_preorder

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_partial_order [PartialOrder M] : M ⊨ Theory.partial_order := by
  simp only [Theory.partial_order, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric, forall_eq,
    relations.realize_transitive]
  exact ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans⟩
#align first_order.language.model_partial_order FirstOrder.Language.model_partial_order

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_linear_order [LinearOrder M] : M ⊨ Theory.linear_order := by
  simp only [Theory.linear_order, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric, relations.realize_transitive,
    forall_eq, relations.realize_total]
  exact ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans, le_total⟩
#align first_order.language.model_linear_order FirstOrder.Language.model_linear_order

section IsOrderedStructure

variable [IsOrdered L] [L.StructureCat M]

@[simp]
theorem rel_map_le_symb [LE M] [L.IsOrderedStructure M] {a b : M} : RelMap (leSymb : L.Relations 2) ![a, b] ↔ a ≤ b :=
  by
  rw [← order_Lhom_le_symb, Lhom.map_on_relation]
  rfl
#align first_order.language.rel_map_le_symb FirstOrder.Language.rel_map_le_symb

@[simp]
theorem Term.realize_le [LE M] [L.IsOrderedStructure M] {t₁ t₂ : L.term (Sum α (Fin n))} {v : α → M} {xs : Fin n → M} :
    (t₁.le t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by simp [term.le]
#align first_order.language.term.realize_le FirstOrder.Language.Term.realize_le

@[simp]
theorem Term.realize_lt [Preorder M] [L.IsOrderedStructure M] {t₁ t₂ : L.term (Sum α (Fin n))} {v : α → M}
    {xs : Fin n → M} : (t₁.lt t₂).realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [term.lt, lt_iff_le_not_le]
#align first_order.language.term.realize_lt FirstOrder.Language.Term.realize_lt

end IsOrderedStructure

section LE

variable [LE M]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_no_top_order_iff : M ⊨ sentence.no_top_order ↔ NoTopOrder M := by
  simp only [sentence.no_top_order, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le, Sum.elim_inr]
  refine' ⟨fun h => ⟨fun a => h a⟩, _⟩
  intro h a
  exact exists_not_le a
#align first_order.language.realize_no_top_order_iff FirstOrder.Language.realize_no_top_order_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem realize_no_top_order [h : NoTopOrder M] : M ⊨ sentence.no_top_order :=
  realize_no_top_order_iff.2 h
#align first_order.language.realize_no_top_order FirstOrder.Language.realize_no_top_order

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_no_bot_order_iff : M ⊨ sentence.no_bot_order ↔ NoBotOrder M := by
  simp only [sentence.no_bot_order, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le, Sum.elim_inr]
  refine' ⟨fun h => ⟨fun a => h a⟩, _⟩
  intro h a
  exact exists_not_ge a
#align first_order.language.realize_no_bot_order_iff FirstOrder.Language.realize_no_bot_order_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem realize_no_bot_order [h : NoBotOrder M] : M ⊨ sentence.no_bot_order :=
  realize_no_bot_order_iff.2 h
#align first_order.language.realize_no_bot_order FirstOrder.Language.realize_no_bot_order

end LE

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem realize_densely_ordered_iff [Preorder M] : M ⊨ sentence.densely_ordered ↔ DenselyOrdered M := by
  simp only [sentence.densely_ordered, sentence.realize, formula.realize, bounded_formula.realize_imp,
    bounded_formula.realize_all, realize, term.realize_lt, Sum.elim_inr, bounded_formula.realize_ex,
    bounded_formula.realize_inf]
  refine' ⟨fun h => ⟨fun a b ab => h a b ab⟩, _⟩
  intro h a b ab
  exact exists_between ab
#align first_order.language.realize_densely_ordered_iff FirstOrder.Language.realize_densely_ordered_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem realize_densely_ordered [Preorder M] [h : DenselyOrdered M] : M ⊨ sentence.densely_ordered :=
  realize_densely_ordered_iff.2 h
#align first_order.language.realize_densely_ordered FirstOrder.Language.realize_densely_ordered

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance model_DLO [LinearOrder M] [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] : M ⊨ Theory.DLO := by
  simp only [Theory.DLO, Set.union_insert, Set.union_singleton, Theory.model_iff, Set.mem_insert_iff, forall_eq_or_imp,
    realize_no_top_order, realize_no_bot_order, realize_densely_ordered, true_and_iff]
  rw [← Theory.model_iff]
  infer_instance
#align first_order.language.model_DLO FirstOrder.Language.model_DLO

end Language

end FirstOrder

