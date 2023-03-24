/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.density
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Order.Partition.Finpartition
import Mathbin.Tactic.Positivity

/-!
# Edge density

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the number and density of edges of a relation/graph.

## Main declarations

Between two finsets of vertices,
* `rel.interedges`: Finset of edges of a relation.
* `rel.edge_density`: Edge density of a relation.
* `simple_graph.interedges`: Finset of edges of a graph.
* `simple_graph.edge_density`: Edge density of a graph.
-/


open Finset

open BigOperators

variable {𝕜 ι κ α β : Type _}

/-! ### Density of a relation -/


namespace Rel

section Asymmetric

variable [LinearOrderedField 𝕜] (r : α → β → Prop) [∀ a, DecidablePred (r a)] {s s₁ s₂ : Finset α}
  {t t₁ t₂ : Finset β} {a : α} {b : β} {δ : 𝕜}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Rel.interedges /-
/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s : Finset α) (t : Finset β) : Finset (α × β) :=
  (s ×ˢ t).filterₓ fun e => r e.1 e.2
#align rel.interedges Rel.interedges
-/

#print Rel.edgeDensity /-
/-- Edge density of a relation between two finsets of vertices. -/
def edgeDensity (s : Finset α) (t : Finset β) : ℚ :=
  (interedges r s t).card / (s.card * t.card)
#align rel.edge_density Rel.edgeDensity
-/

variable {r}

/- warning: rel.mem_interedges_iff -> Rel.mem_interedges_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s : Finset.{u1} α} {t : Finset.{u2} β} {x : Prod.{u1, u2} α β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) x (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Prod.fst.{u1, u2} α β x) s) (And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (Prod.snd.{u1, u2} α β x) t) (r (Prod.fst.{u1, u2} α β x) (Prod.snd.{u1, u2} α β x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s : Finset.{u2} α} {t : Finset.{u1} β} {x : Prod.{u2, u1} α β}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} α β) (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instMembershipFinset.{max u2 u1} (Prod.{u2, u1} α β)) x (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Prod.fst.{u2, u1} α β x) s) (And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (Prod.snd.{u2, u1} α β x) t) (r (Prod.fst.{u2, u1} α β x) (Prod.snd.{u2, u1} α β x))))
Case conversion may be inaccurate. Consider using '#align rel.mem_interedges_iff Rel.mem_interedges_iffₓ'. -/
theorem mem_interedges_iff {x : α × β} : x ∈ interedges r s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ r x.1 x.2 := by
  simp only [interedges, and_assoc', mem_filter, Finset.mem_product]
#align rel.mem_interedges_iff Rel.mem_interedges_iff

#print Rel.mk_mem_interedges_iff /-
theorem mk_mem_interedges_iff : (a, b) ∈ interedges r s t ↔ a ∈ s ∧ b ∈ t ∧ r a b :=
  mem_interedges_iff
#align rel.mk_mem_interedges_iff Rel.mk_mem_interedges_iff
-/

#print Rel.interedges_empty_left /-
@[simp]
theorem interedges_empty_left (t : Finset β) : interedges r ∅ t = ∅ := by
  rw [interedges, Finset.empty_product, filter_empty]
#align rel.interedges_empty_left Rel.interedges_empty_left
-/

/- warning: rel.interedges_mono -> Rel.interedges_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₂ t₁) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₂ t₁) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instHasSubsetFinset.{max u2 u1} (Prod.{u2, u1} α β)) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁))
Case conversion may be inaccurate. Consider using '#align rel.interedges_mono Rel.interedges_monoₓ'. -/
theorem interedges_mono (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) : interedges r s₂ t₂ ⊆ interedges r s₁ t₁ :=
  fun x => by
  simp_rw [mem_interedges_iff]
  exact fun h => ⟨hs h.1, ht h.2.1, h.2.2⟩
#align rel.interedges_mono Rel.interedges_mono

variable (r)

/- warning: rel.card_interedges_add_card_interedges_compl -> Rel.card_interedges_add_card_interedges_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β (fun (x : α) (y : β) => Not (r x y)) (fun (a : α) (a_1 : β) => Not.decidable (r a a_1) (_inst_2 a a_1)) s t))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β (fun (x : α) (y : β) => Not (r x y)) (fun (a : α) (a_1 : β) => instDecidableNot (r a a_1) (_inst_2 a a_1)) s t))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α s) (Finset.card.{u1} β t))
Case conversion may be inaccurate. Consider using '#align rel.card_interedges_add_card_interedges_compl Rel.card_interedges_add_card_interedges_complₓ'. -/
theorem card_interedges_add_card_interedges_compl (s : Finset α) (t : Finset β) :
    (interedges r s t).card + (interedges (fun x y => ¬r x y) s t).card = s.card * t.card := by
  classical
    rw [← card_product, interedges, interedges, ← card_union_eq, filter_union_filter_neg_eq]
    convert disjoint_filter.2 fun x _ => Classical.not_not.2
#align rel.card_interedges_add_card_interedges_compl Rel.card_interedges_add_card_interedges_compl

/- warning: rel.interedges_disjoint_left -> Rel.interedges_disjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s : Finset.{u1} α} {s' : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s') -> (forall (t : Finset.{u2} β), Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Prod.{u1, u2} α β)) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s' t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s : Finset.{u2} α} {s' : Finset.{u2} α}, (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s s') -> (forall (t : Finset.{u1} β), Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.partialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s' t))
Case conversion may be inaccurate. Consider using '#align rel.interedges_disjoint_left Rel.interedges_disjoint_leftₓ'. -/
theorem interedges_disjoint_left {s s' : Finset α} (hs : Disjoint s s') (t : Finset β) :
    Disjoint (interedges r s t) (interedges r s' t) :=
  by
  rw [Finset.disjoint_left] at hs⊢
  rintro x hx hy
  rw [mem_interedges_iff] at hx hy
  exact hs hx.1 hy.1
#align rel.interedges_disjoint_left Rel.interedges_disjoint_left

/- warning: rel.interedges_disjoint_right -> Rel.interedges_disjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] (s : Finset.{u1} α) {t : Finset.{u2} β} {t' : Finset.{u2} β}, (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t') -> (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Prod.{u1, u2} α β)) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] (s : Finset.{u2} α) {t : Finset.{u1} β} {t' : Finset.{u1} β}, (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t t') -> (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.partialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t'))
Case conversion may be inaccurate. Consider using '#align rel.interedges_disjoint_right Rel.interedges_disjoint_rightₓ'. -/
theorem interedges_disjoint_right (s : Finset α) {t t' : Finset β} (ht : Disjoint t t') :
    Disjoint (interedges r s t) (interedges r s t') :=
  by
  rw [Finset.disjoint_left] at ht⊢
  rintro x hx hy
  rw [mem_interedges_iff] at hx hy
  exact ht hx.2.1 hy.2.1
#align rel.interedges_disjoint_right Rel.interedges_disjoint_right

section DecidableEq

variable [DecidableEq α] [DecidableEq β]

/- warning: rel.interedges_bUnion_left -> Rel.interedges_bunionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u3} β (r a)] [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableEq.{succ u3} β] (s : Finset.{u1} ι) (t : Finset.{u3} β) (f : ι -> (Finset.{u2} α)), Eq.{succ (max u2 u3)} (Finset.{max u2 u3} (Prod.{u2, u3} α β)) (Rel.interedges.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (Finset.bunionᵢ.{u1, u2} ι α (fun (a : α) (b : α) => _inst_3 a b) s f) t) (Finset.bunionᵢ.{u1, max u2 u3} ι (Prod.{u2, u3} α β) (fun (a : Prod.{u2, u3} α β) (b : Prod.{u2, u3} α β) => Prod.Lex.decidableEq.{u2, u3} α β (fun (a : α) (b : α) => _inst_3 a b) (fun (a : β) (b : β) => _inst_4 a b) a b) s (fun (a : ι) => Rel.interedges.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (f a) t))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidableEq.{succ u2} β] (s : Finset.{u3} ι) (t : Finset.{u2} β) (f : ι -> (Finset.{u1} α)), Eq.{max (succ u1) (succ u2)} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (Finset.bunionᵢ.{u3, u1} ι α (fun (a : α) (b : α) => _inst_3 a b) s f) t) (Finset.bunionᵢ.{u3, max u2 u1} ι (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => instDecidableEqProd.{u1, u2} α β (fun (a : α) (b : α) => _inst_3 a b) (fun (a : β) (b : β) => _inst_4 a b) a b) s (fun (a : ι) => Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (f a) t))
Case conversion may be inaccurate. Consider using '#align rel.interedges_bUnion_left Rel.interedges_bunionᵢ_leftₓ'. -/
theorem interedges_bunionᵢ_left (s : Finset ι) (t : Finset β) (f : ι → Finset α) :
    interedges r (s.bunionᵢ f) t = s.bunionᵢ fun a => interedges r (f a) t :=
  ext fun a => by simp only [mem_bUnion, mem_interedges_iff, exists_and_right]
#align rel.interedges_bUnion_left Rel.interedges_bunionᵢ_left

/- warning: rel.interedges_bUnion_right -> Rel.interedges_bunionᵢ_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u3} β (r a)] [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableEq.{succ u3} β] (s : Finset.{u2} α) (t : Finset.{u1} ι) (f : ι -> (Finset.{u3} β)), Eq.{succ (max u2 u3)} (Finset.{max u2 u3} (Prod.{u2, u3} α β)) (Rel.interedges.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s (Finset.bunionᵢ.{u1, u3} ι β (fun (a : β) (b : β) => _inst_4 a b) t f)) (Finset.bunionᵢ.{u1, max u2 u3} ι (Prod.{u2, u3} α β) (fun (a : Prod.{u2, u3} α β) (b : Prod.{u2, u3} α β) => Prod.Lex.decidableEq.{u2, u3} α β (fun (a : α) (b : α) => _inst_3 a b) (fun (a : β) (b : β) => _inst_4 a b) a b) t (fun (b : ι) => Rel.interedges.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s (f b)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] [_inst_3 : DecidableEq.{succ u3} α] [_inst_4 : DecidableEq.{succ u1} β] (s : Finset.{u3} α) (t : Finset.{u2} ι) (f : ι -> (Finset.{u1} β)), Eq.{max (succ u3) (succ u1)} (Finset.{max u1 u3} (Prod.{u3, u1} α β)) (Rel.interedges.{u3, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s (Finset.bunionᵢ.{u2, u1} ι β (fun (a : β) (b : β) => _inst_4 a b) t f)) (Finset.bunionᵢ.{u2, max u1 u3} ι (Prod.{u3, u1} α β) (fun (a : Prod.{u3, u1} α β) (b : Prod.{u3, u1} α β) => instDecidableEqProd.{u3, u1} α β (fun (a : α) (b : α) => _inst_3 a b) (fun (a : β) (b : β) => _inst_4 a b) a b) t (fun (b : ι) => Rel.interedges.{u3, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s (f b)))
Case conversion may be inaccurate. Consider using '#align rel.interedges_bUnion_right Rel.interedges_bunionᵢ_rightₓ'. -/
theorem interedges_bunionᵢ_right (s : Finset α) (t : Finset ι) (f : ι → Finset β) :
    interedges r s (t.bunionᵢ f) = t.bunionᵢ fun b => interedges r s (f b) :=
  ext fun a => by simp only [mem_interedges_iff, mem_bUnion, ← exists_and_left, ← exists_and_right]
#align rel.interedges_bUnion_right Rel.interedges_bunionᵢ_right

/- warning: rel.interedges_bUnion -> Rel.interedges_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} {β : Type.{u4}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u4} β (r a)] [_inst_3 : DecidableEq.{succ u3} α] [_inst_4 : DecidableEq.{succ u4} β] (s : Finset.{u1} ι) (t : Finset.{u2} κ) (f : ι -> (Finset.{u3} α)) (g : κ -> (Finset.{u4} β)), Eq.{succ (max u3 u4)} (Finset.{max u3 u4} (Prod.{u3, u4} α β)) (Rel.interedges.{u3, u4} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (Finset.bunionᵢ.{u1, u3} ι α (fun (a : α) (b : α) => _inst_3 a b) s f) (Finset.bunionᵢ.{u2, u4} κ β (fun (a : β) (b : β) => _inst_4 a b) t g)) (Finset.bunionᵢ.{max u1 u2, max u3 u4} (Prod.{u1, u2} ι κ) (Prod.{u3, u4} α β) (fun (a : Prod.{u3, u4} α β) (b : Prod.{u3, u4} α β) => Prod.Lex.decidableEq.{u3, u4} α β (fun (a : α) (b : α) => _inst_3 a b) (fun (a : β) (b : β) => _inst_4 a b) a b) (Finset.product.{u1, u2} ι κ s t) (fun (ab : Prod.{u1, u2} ι κ) => Rel.interedges.{u3, u4} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (f (Prod.fst.{u1, u2} ι κ ab)) (g (Prod.snd.{u1, u2} ι κ ab))))
but is expected to have type
  forall {ι : Type.{u4}} {κ : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableEq.{succ u1} β] (s : Finset.{u4} ι) (t : Finset.{u3} κ) (f : ι -> (Finset.{u2} α)) (g : κ -> (Finset.{u1} β)), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (Finset.bunionᵢ.{u4, u2} ι α (fun (a : α) (b : α) => _inst_3 a b) s f) (Finset.bunionᵢ.{u3, u1} κ β (fun (a : β) (b : β) => _inst_4 a b) t g)) (Finset.bunionᵢ.{max u4 u3, max u1 u2} (Prod.{u4, u3} ι κ) (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_3 a b) (fun (a : β) (b : β) => _inst_4 a b) a b) (Finset.product.{u4, u3} ι κ s t) (fun (ab : Prod.{u4, u3} ι κ) => Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (f (Prod.fst.{u4, u3} ι κ ab)) (g (Prod.snd.{u4, u3} ι κ ab))))
Case conversion may be inaccurate. Consider using '#align rel.interedges_bUnion Rel.interedges_bunionᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interedges_bunionᵢ (s : Finset ι) (t : Finset κ) (f : ι → Finset α) (g : κ → Finset β) :
    interedges r (s.bunionᵢ f) (t.bunionᵢ g) =
      (s ×ˢ t).bunionᵢ fun ab => interedges r (f ab.1) (g ab.2) :=
  by simp_rw [product_bUnion, interedges_bUnion_left, interedges_bUnion_right]
#align rel.interedges_bUnion Rel.interedges_bunionᵢ

end DecidableEq

/- warning: rel.card_interedges_le_mul -> Rel.card_interedges_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] (s : Finset.{u1} α) (t : Finset.{u2} β), LE.le.{0} Nat Nat.hasLe (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] (s : Finset.{u2} α) (t : Finset.{u1} β), LE.le.{0} Nat instLENat (Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α s) (Finset.card.{u1} β t))
Case conversion may be inaccurate. Consider using '#align rel.card_interedges_le_mul Rel.card_interedges_le_mulₓ'. -/
theorem card_interedges_le_mul (s : Finset α) (t : Finset β) :
    (interedges r s t).card ≤ s.card * t.card :=
  (card_filter_le _ _).trans (card_product _ _).le
#align rel.card_interedges_le_mul Rel.card_interedges_le_mul

/- warning: rel.edge_density_nonneg -> Rel.edgeDensity_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] (s : Finset.{u1} α) (t : Finset.{u2} β), LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] (s : Finset.{u2} α) (t : Finset.{u1} β), LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)
Case conversion may be inaccurate. Consider using '#align rel.edge_density_nonneg Rel.edgeDensity_nonnegₓ'. -/
theorem edgeDensity_nonneg (s : Finset α) (t : Finset β) : 0 ≤ edgeDensity r s t := by
  apply div_nonneg <;> exact_mod_cast Nat.zero_le _
#align rel.edge_density_nonneg Rel.edgeDensity_nonneg

/- warning: rel.edge_density_le_one -> Rel.edgeDensity_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] (s : Finset.{u1} α) (t : Finset.{u2} β), LE.le.{0} Rat Rat.hasLe (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] (s : Finset.{u2} α) (t : Finset.{u1} β), LE.le.{0} Rat Rat.instLERat (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align rel.edge_density_le_one Rel.edgeDensity_le_oneₓ'. -/
theorem edgeDensity_le_one (s : Finset α) (t : Finset β) : edgeDensity r s t ≤ 1 :=
  div_le_one_of_le (by exact_mod_cast card_interedges_le_mul _ _ _) <| by
    exact_mod_cast Nat.zero_le _
#align rel.edge_density_le_one Rel.edgeDensity_le_one

/- warning: rel.edge_density_add_edge_density_compl -> Rel.edgeDensity_add_edgeDensity_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u1} α s) -> (Finset.Nonempty.{u2} β t) -> (Eq.{1} Rat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (Rel.edgeDensity.{u1, u2} α β (fun (x : α) (y : β) => Not (r x y)) (fun (a : α) (a_1 : β) => Not.decidable (r a a_1) (_inst_2 a a_1)) s t)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{u2} α s) -> (Finset.Nonempty.{u1} β t) -> (Eq.{1} Rat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t) (Rel.edgeDensity.{u2, u1} α β (fun (x : α) (y : β) => Not (r x y)) (fun (a : α) (a_1 : β) => instDecidableNot (r a a_1) (_inst_2 a a_1)) s t)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)))
Case conversion may be inaccurate. Consider using '#align rel.edge_density_add_edge_density_compl Rel.edgeDensity_add_edgeDensity_complₓ'. -/
theorem edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) :
    edgeDensity r s t + edgeDensity (fun x y => ¬r x y) s t = 1 :=
  by
  rw [edge_density, edge_density, div_add_div_same, div_eq_one_iff_eq]
  · exact_mod_cast card_interedges_add_card_interedges_compl r s t
  · exact_mod_cast (mul_pos hs.card_pos ht.card_pos).ne'
#align rel.edge_density_add_edge_density_compl Rel.edgeDensity_add_edgeDensity_compl

#print Rel.edgeDensity_empty_left /-
@[simp]
theorem edgeDensity_empty_left (t : Finset β) : edgeDensity r ∅ t = 0 := by
  rw [edge_density, Finset.card_empty, Nat.cast_zero, MulZeroClass.zero_mul, div_zero]
#align rel.edge_density_empty_left Rel.edgeDensity_empty_left
-/

/- warning: rel.edge_density_empty_right -> Rel.edgeDensity_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] (s : Finset.{u1} α), Eq.{1} Rat (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] (s : Finset.{u2} α), Eq.{1} Rat (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))) (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))
Case conversion may be inaccurate. Consider using '#align rel.edge_density_empty_right Rel.edgeDensity_empty_rightₓ'. -/
@[simp]
theorem edgeDensity_empty_right (s : Finset α) : edgeDensity r s ∅ = 0 := by
  rw [edge_density, Finset.card_empty, Nat.cast_zero, MulZeroClass.mul_zero, div_zero]
#align rel.edge_density_empty_right Rel.edgeDensity_empty_right

/- warning: rel.card_interedges_finpartition_left -> Rel.card_interedges_finpartition_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s : Finset.{u1} α} [_inst_3 : DecidableEq.{succ u1} α] (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.orderBot.{u1} α) s) (t : Finset.{u2} β), Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.sum.{0, u1} Nat (Finset.{u1} α) Nat.addCommMonoid (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.orderBot.{u1} α) s P) (fun (a : Finset.{u1} α) => Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) a t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s : Finset.{u2} α} [_inst_3 : DecidableEq.{succ u2} α] (P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s) (t : Finset.{u1} β), Eq.{1} Nat (Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.sum.{0, u2} Nat (Finset.{u2} α) Nat.addCommMonoid (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s P) (fun (a : Finset.{u2} α) => Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) a t)))
Case conversion may be inaccurate. Consider using '#align rel.card_interedges_finpartition_left Rel.card_interedges_finpartition_leftₓ'. -/
theorem card_interedges_finpartition_left [DecidableEq α] (P : Finpartition s) (t : Finset β) :
    (interedges r s t).card = ∑ a in P.parts, (interedges r a t).card := by
  classical
    simp_rw [← P.bUnion_parts, interedges_bUnion_left, id.def]
    rw [card_bUnion]
    exact fun x hx y hy h => interedges_disjoint_left r (P.disjoint hx hy h) _
#align rel.card_interedges_finpartition_left Rel.card_interedges_finpartition_left

/- warning: rel.card_interedges_finpartition_right -> Rel.card_interedges_finpartition_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (P : Finpartition.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) (Finset.orderBot.{u2} β) t), Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.sum.{0, u2} Nat (Finset.{u2} β) Nat.addCommMonoid (Finpartition.parts.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) (Finset.orderBot.{u2} β) t P) (fun (b : Finset.{u2} β) => Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (P : Finpartition.{u2} (Finset.{u2} β) (Finset.instLatticeFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) t), Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.sum.{0, u2} Nat (Finset.{u2} β) Nat.addCommMonoid (Finpartition.parts.{u2} (Finset.{u2} β) (Finset.instLatticeFinset.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) t P) (fun (b : Finset.{u2} β) => Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s b)))
Case conversion may be inaccurate. Consider using '#align rel.card_interedges_finpartition_right Rel.card_interedges_finpartition_rightₓ'. -/
theorem card_interedges_finpartition_right [DecidableEq β] (s : Finset α) (P : Finpartition t) :
    (interedges r s t).card = ∑ b in P.parts, (interedges r s b).card := by
  classical
    simp_rw [← P.bUnion_parts, interedges_bUnion_right, id]
    rw [card_bUnion]
    exact fun x hx y hy h => interedges_disjoint_right r _ (P.disjoint hx hy h)
#align rel.card_interedges_finpartition_right Rel.card_interedges_finpartition_right

/- warning: rel.card_interedges_finpartition -> Rel.card_interedges_finpartition is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s : Finset.{u1} α} {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidableEq.{succ u2} β] (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.orderBot.{u1} α) s) (Q : Finpartition.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_4 a b)) (Finset.orderBot.{u2} β) t), Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.sum.{0, max u1 u2} Nat (Prod.{u1, u2} (Finset.{u1} α) (Finset.{u2} β)) Nat.addCommMonoid (Finset.product.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.orderBot.{u1} α) s P) (Finpartition.parts.{u2} (Finset.{u2} β) (Finset.lattice.{u2} β (fun (a : β) (b : β) => _inst_4 a b)) (Finset.orderBot.{u2} β) t Q)) (fun (ab : Prod.{u1, u2} (Finset.{u1} α) (Finset.{u2} β)) => Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Rel.interedges.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (Prod.fst.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) ab) (Prod.snd.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) ab))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s : Finset.{u2} α} {t : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableEq.{succ u1} β] (P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s) (Q : Finpartition.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => _inst_4 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t), Eq.{1} Nat (Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s t)) (Finset.sum.{0, max u1 u2} Nat (Prod.{u2, u1} (Finset.{u2} α) (Finset.{u1} β)) Nat.addCommMonoid (Finset.product.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s P) (Finpartition.parts.{u1} (Finset.{u1} β) (Finset.instLatticeFinset.{u1} β (fun (a : β) (b : β) => _inst_4 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t Q)) (fun (ab : Prod.{u2, u1} (Finset.{u2} α) (Finset.{u1} β)) => Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Rel.interedges.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) (Prod.fst.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) ab) (Prod.snd.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) ab))))
Case conversion may be inaccurate. Consider using '#align rel.card_interedges_finpartition Rel.card_interedges_finpartitionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem card_interedges_finpartition [DecidableEq α] [DecidableEq β] (P : Finpartition s)
    (Q : Finpartition t) :
    (interedges r s t).card = ∑ ab in P.parts ×ˢ Q.parts, (interedges r ab.1 ab.2).card := by
  simp_rw [card_interedges_finpartition_left _ P, card_interedges_finpartition_right _ _ Q,
    sum_product]
#align rel.card_interedges_finpartition Rel.card_interedges_finpartition

/- warning: rel.mul_edge_density_le_edge_density -> Rel.mul_edgeDensity_le_edgeDensity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₂ t₁) -> (Finset.Nonempty.{u1} α s₂) -> (Finset.Nonempty.{u2} β t₂) -> (LE.le.{0} Rat Rat.hasLe (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s₂)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s₁))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u2} β t₂)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u2} β t₁)))) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂)) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₂ t₁) -> (Finset.Nonempty.{u2} α s₂) -> (Finset.Nonempty.{u1} β t₂) -> (LE.le.{0} Rat Rat.instLERat (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u2} α s₂)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u2} α s₁))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} β t₂)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} β t₁)))) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂)) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁))
Case conversion may be inaccurate. Consider using '#align rel.mul_edge_density_le_edge_density Rel.mul_edgeDensity_le_edgeDensityₓ'. -/
theorem mul_edgeDensity_le_edgeDensity (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    (s₂.card : ℚ) / s₁.card * (t₂.card / t₁.card) * edgeDensity r s₂ t₂ ≤ edgeDensity r s₁ t₁ :=
  by
  have hst : (s₂.card : ℚ) * t₂.card ≠ 0 := by simp [hs₂.ne_empty, ht₂.ne_empty]
  rw [edge_density, edge_density, div_mul_div_comm, mul_comm, div_mul_div_cancel _ hst]
  refine' div_le_div_of_le (by exact_mod_cast (s₁.card * t₁.card).zero_le) _
  exact_mod_cast card_le_of_subset (interedges_mono hs ht)
#align rel.mul_edge_density_le_edge_density Rel.mul_edgeDensity_le_edgeDensity

/- warning: rel.edge_density_sub_edge_density_le_one_sub_mul -> Rel.edgeDensity_sub_edgeDensity_le_one_sub_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₂ t₁) -> (Finset.Nonempty.{u1} α s₂) -> (Finset.Nonempty.{u2} β t₂) -> (LE.le.{0} Rat Rat.hasLe (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁)) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s₂)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s₁))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u2} β t₂)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u2} β t₁))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₂ t₁) -> (Finset.Nonempty.{u2} α s₂) -> (Finset.Nonempty.{u1} β t₂) -> (LE.le.{0} Rat Rat.instLERat (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁)) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u2} α s₂)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u2} α s₁))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} β t₂)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} β t₁))))))
Case conversion may be inaccurate. Consider using '#align rel.edge_density_sub_edge_density_le_one_sub_mul Rel.edgeDensity_sub_edgeDensity_le_one_sub_mulₓ'. -/
theorem edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁ ≤ 1 - s₂.card / s₁.card * (t₂.card / t₁.card) :=
  by
  refine' (sub_le_sub_left (mul_edge_density_le_edge_density r hs ht hs₂ ht₂) _).trans _
  refine' le_trans _ (mul_le_of_le_one_right _ (edge_density_le_one r s₂ t₂))
  · rw [sub_mul, one_mul]
  refine' sub_nonneg_of_le (mul_le_one _ (by positivity) _) <;>
    exact div_le_one_of_le (Nat.cast_le.2 (card_le_of_subset ‹_›)) (Nat.cast_nonneg _)
#align rel.edge_density_sub_edge_density_le_one_sub_mul Rel.edgeDensity_sub_edgeDensity_le_one_sub_mul

/- warning: rel.abs_edge_density_sub_edge_density_le_one_sub_mul -> Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₂ t₁) -> (Finset.Nonempty.{u1} α s₂) -> (Finset.Nonempty.{u2} β t₂) -> (LE.le.{0} Rat Rat.hasLe (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂) (Rel.edgeDensity.{u1, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁))) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s₂)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s₁))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u2} β t₂)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u2} β t₁))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u1} β (r a)] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₂ t₁) -> (Finset.Nonempty.{u2} α s₂) -> (Finset.Nonempty.{u1} β t₂) -> (LE.le.{0} Rat Rat.instLERat (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂) (Rel.edgeDensity.{u2, u1} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁))) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u2} α s₂)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u2} α s₁))) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} β t₂)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} β t₁))))))
Case conversion may be inaccurate. Consider using '#align rel.abs_edge_density_sub_edge_density_le_one_sub_mul Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mulₓ'. -/
theorem abs_edgeDensity_sub_edgeDensity_le_one_sub_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁)
    (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) :
    |edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁| ≤ 1 - s₂.card / s₁.card * (t₂.card / t₁.card) :=
  by
  have habs : abs (edge_density r s₂ t₂ - edge_density r s₁ t₁) ≤ 1 :=
    by
    rw [abs_sub_le_iff, ← sub_zero (1 : ℚ)]
    constructor <;> exact sub_le_sub (edge_density_le_one r _ _) (edge_density_nonneg r _ _)
  refine' abs_sub_le_iff.2 ⟨edge_density_sub_edge_density_le_one_sub_mul r hs ht hs₂ ht₂, _⟩
  rw [← add_sub_cancel (edge_density r s₁ t₁) (edge_density (fun x y => ¬r x y) s₁ t₁), ←
    add_sub_cancel (edge_density r s₂ t₂) (edge_density (fun x y => ¬r x y) s₂ t₂),
    edge_density_add_edge_density_compl _ (hs₂.mono hs) (ht₂.mono ht),
    edge_density_add_edge_density_compl _ hs₂ ht₂, sub_sub_sub_cancel_left]
  exact edge_density_sub_edge_density_le_one_sub_mul _ hs ht hs₂ ht₂
#align rel.abs_edge_density_sub_edge_density_le_one_sub_mul Rel.abs_edgeDensity_sub_edgeDensity_le_one_sub_mul

/- warning: rel.abs_edge_density_sub_edge_density_le_two_mul_sub_sq -> Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u3} β (r a)] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u3} β} {t₂ : Finset.{u3} β} {δ : 𝕜}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u3} (Finset.{u3} β) (Finset.hasSubset.{u3} β) t₂ t₁) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))))) δ) -> (LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) δ (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) δ) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} α s₁))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} α s₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) δ) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u3} β t₁))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u3} β t₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (Abs.abs.{u1} 𝕜 (Neg.toHasAbs.{u1} 𝕜 (SubNegMonoid.toHasNeg.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (SemilatticeSup.toHasSup.{u1} 𝕜 (Lattice.toSemilatticeSup.{u1} 𝕜 (LinearOrder.toLattice.{u1} 𝕜 (LinearOrderedRing.toLinearOrder.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u1} Rat 𝕜 (CoeTCₓ.coe.{1, succ u1} Rat 𝕜 (Rat.castCoe.{u1} 𝕜 (DivisionRing.toHasRatCast.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (Rel.edgeDensity.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u1} Rat 𝕜 (CoeTCₓ.coe.{1, succ u1} Rat 𝕜 (Rat.castCoe.{u1} 𝕜 (DivisionRing.toHasRatCast.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (Rel.edgeDensity.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁)))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 2 (OfNat.mk.{u1} 𝕜 2 (bit0.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))))) δ) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) δ (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s₁ : Finset.{u3} α} {s₂ : Finset.{u3} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β} {δ : 𝕜}, (HasSubset.Subset.{u3} (Finset.{u3} α) (Finset.instHasSubsetFinset.{u3} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) t₂ t₁) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))) δ) -> (LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) δ (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) δ) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u3} α s₁))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u3} α s₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) δ) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} β t₁))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} β t₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Abs.abs.{u1} 𝕜 (Neg.toHasAbs.{u1} 𝕜 (Ring.toNeg.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) (SemilatticeSup.toSup.{u1} 𝕜 (Lattice.toSemilatticeSup.{u1} 𝕜 (DistribLattice.toLattice.{u1} 𝕜 (instDistribLattice.{u1} 𝕜 (LinearOrderedRing.toLinearOrder.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Rel.edgeDensity.{u3, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂)) (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Rel.edgeDensity.{u3, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁)))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (OfNat.ofNat.{u1} 𝕜 2 (instOfNat.{u1} 𝕜 2 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) δ) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))))) δ (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align rel.abs_edge_density_sub_edge_density_le_two_mul_sub_sq Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sqₓ'. -/
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hs₂ : (1 - δ) * s₁.card ≤ s₂.card)
    (ht₂ : (1 - δ) * t₁.card ≤ t₂.card) :
    |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| ≤ 2 * δ - δ ^ 2 :=
  by
  have hδ' : 0 ≤ 2 * δ - δ ^ 2 := by
    rw [sub_nonneg, sq]
    exact mul_le_mul_of_nonneg_right (hδ₁.le.trans (by norm_num)) hδ₀
  rw [← sub_pos] at hδ₁
  obtain rfl | hs₂' := s₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at hs₂
    simpa [edge_density, (nonpos_of_mul_nonpos_right hs₂ hδ₁).antisymm (Nat.cast_nonneg _)] using
      hδ'
  obtain rfl | ht₂' := t₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zero] at ht₂
    simpa [edge_density, (nonpos_of_mul_nonpos_right ht₂ hδ₁).antisymm (Nat.cast_nonneg _)] using
      hδ'
  rw [show 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ) by ring]
  norm_cast
  refine'
    (Rat.cast_le.2 <| abs_edge_density_sub_edge_density_le_one_sub_mul r hs ht hs₂' ht₂').trans _
  push_cast
  have := hs₂'.mono hs
  have := ht₂'.mono ht
  refine' sub_le_sub_left (mul_le_mul ((le_div_iff _).2 hs₂) ((le_div_iff _).2 ht₂) hδ₁.le _) _ <;>
    positivity
#align rel.abs_edge_density_sub_edge_density_le_two_mul_sub_sq Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul_sub_sq

/- warning: rel.abs_edge_density_sub_edge_density_le_two_mul -> Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u3} β (r a)] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u3} β} {t₂ : Finset.{u3} β} {δ : 𝕜}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α) s₂ s₁) -> (HasSubset.Subset.{u3} (Finset.{u3} β) (Finset.hasSubset.{u3} β) t₂ t₁) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))))) δ) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) δ) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} α s₁))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u2} α s₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) δ) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u3} β t₁))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u1} Nat 𝕜 (CoeTCₓ.coe.{1, succ u1} Nat 𝕜 (Nat.castCoe.{u1} 𝕜 (AddMonoidWithOne.toNatCast.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))) (Finset.card.{u3} β t₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (Abs.abs.{u1} 𝕜 (Neg.toHasAbs.{u1} 𝕜 (SubNegMonoid.toHasNeg.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (SemilatticeSup.toHasSup.{u1} 𝕜 (Lattice.toSemilatticeSup.{u1} 𝕜 (LinearOrder.toLattice.{u1} 𝕜 (LinearOrderedRing.toLinearOrder.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (AddGroupWithOne.toAddGroup.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u1} Rat 𝕜 (CoeTCₓ.coe.{1, succ u1} Rat 𝕜 (Rat.castCoe.{u1} 𝕜 (DivisionRing.toHasRatCast.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (Rel.edgeDensity.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u1} Rat 𝕜 (CoeTCₓ.coe.{1, succ u1} Rat 𝕜 (Rat.castCoe.{u1} 𝕜 (DivisionRing.toHasRatCast.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (Rel.edgeDensity.{u2, u3} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁)))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 2 (OfNat.mk.{u1} 𝕜 2 (bit0.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (NonAssocRing.toAddGroupWithOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))))))) δ))
but is expected to have type
  forall {𝕜 : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (r : α -> β -> Prop) [_inst_2 : forall (a : α), DecidablePred.{succ u2} β (r a)] {s₁ : Finset.{u3} α} {s₂ : Finset.{u3} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β} {δ : 𝕜}, (HasSubset.Subset.{u3} (Finset.{u3} α) (Finset.instHasSubsetFinset.{u3} α) s₂ s₁) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) t₂ t₁) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))) δ) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) δ) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u3} α s₁))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u3} α s₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) δ) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} β t₁))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} β t₂))) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Abs.abs.{u1} 𝕜 (Neg.toHasAbs.{u1} 𝕜 (Ring.toNeg.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) (SemilatticeSup.toSup.{u1} 𝕜 (Lattice.toSemilatticeSup.{u1} 𝕜 (DistribLattice.toLattice.{u1} 𝕜 (instDistribLattice.{u1} 𝕜 (LinearOrderedRing.toLinearOrder.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (Ring.toSub.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Rel.edgeDensity.{u3, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₂ t₂)) (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Rel.edgeDensity.{u3, u2} α β r (fun (a : α) (a_1 : β) => _inst_2 a a_1) s₁ t₁)))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (OfNat.ofNat.{u1} 𝕜 2 (instOfNat.{u1} 𝕜 2 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) δ))
Case conversion may be inaccurate. Consider using '#align rel.abs_edge_density_sub_edge_density_le_two_mul Rel.abs_edgeDensity_sub_edgeDensity_le_two_mulₓ'. -/
/-- If `s₂ ⊆ s₁`, `t₂ ⊆ t₁` and they take up all but a `δ`-proportion, then the difference in edge
densities is at most `2 * δ`. -/
theorem abs_edgeDensity_sub_edgeDensity_le_two_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hδ : 0 ≤ δ)
    (hscard : (1 - δ) * s₁.card ≤ s₂.card) (htcard : (1 - δ) * t₁.card ≤ t₂.card) :
    |(edgeDensity r s₂ t₂ : 𝕜) - edgeDensity r s₁ t₁| ≤ 2 * δ :=
  by
  cases lt_or_le δ 1
  ·
    exact
      (abs_edge_density_sub_edge_density_le_two_mul_sub_sq r hs ht hδ h hscard htcard).trans
        ((sub_le_self_iff _).2 <| sq_nonneg δ)
  rw [two_mul]
  refine' (abs_sub _ _).trans (add_le_add (le_trans _ h) (le_trans _ h)) <;>
    · rw [abs_of_nonneg]
      exact_mod_cast edge_density_le_one r _ _
      exact_mod_cast edge_density_nonneg r _ _
#align rel.abs_edge_density_sub_edge_density_le_two_mul Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul

end Asymmetric

section Symmetric

variable (r : α → α → Prop) [DecidableRel r] {s s₁ s₂ t t₁ t₂ : Finset α} {a b : α}

variable {r} (hr : Symmetric r)

include hr

#print Rel.swap_mem_interedges_iff /-
@[simp]
theorem swap_mem_interedges_iff {x : α × α} : x.symm ∈ interedges r s t ↔ x ∈ interedges r t s :=
  by
  rw [mem_interedges_iff, mem_interedges_iff, hr.iff]
  exact and_left_comm
#align rel.swap_mem_interedges_iff Rel.swap_mem_interedges_iff
-/

#print Rel.mk_mem_interedges_comm /-
theorem mk_mem_interedges_comm : (a, b) ∈ interedges r s t ↔ (b, a) ∈ interedges r t s :=
  @swap_mem_interedges_iff _ _ _ _ _ hr (b, a)
#align rel.mk_mem_interedges_comm Rel.mk_mem_interedges_comm
-/

#print Rel.card_interedges_comm /-
theorem card_interedges_comm (s t : Finset α) : (interedges r s t).card = (interedges r t s).card :=
  Finset.card_congr (fun (x : α × α) _ => x.symm) (fun x => (swap_mem_interedges_iff hr).2)
    (fun _ _ _ _ h => Prod.swap_injective h) fun x h =>
    ⟨x.symm, (swap_mem_interedges_iff hr).2 h, x.swap_swap⟩
#align rel.card_interedges_comm Rel.card_interedges_comm
-/

#print Rel.edgeDensity_comm /-
theorem edgeDensity_comm (s t : Finset α) : edgeDensity r s t = edgeDensity r t s := by
  rw [edge_density, mul_comm, card_interedges_comm hr, edge_density]
#align rel.edge_density_comm Rel.edgeDensity_comm
-/

end Symmetric

end Rel

open Rel

/-! ### Density of a graph -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] {s s₁ s₂ t t₁ t₂ : Finset α} {a b : α}

#print SimpleGraph.interedges /-
/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s t : Finset α) : Finset (α × α) :=
  interedges G.Adj s t
#align simple_graph.interedges SimpleGraph.interedges
-/

#print SimpleGraph.edgeDensity /-
/-- Density of edges of a graph between two finsets of vertices. -/
def edgeDensity : Finset α → Finset α → ℚ :=
  edgeDensity G.Adj
#align simple_graph.edge_density SimpleGraph.edgeDensity
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print SimpleGraph.interedges_def /-
theorem interedges_def (s t : Finset α) :
    G.interedges s t = (s ×ˢ t).filterₓ fun e => G.Adj e.1 e.2 :=
  rfl
#align simple_graph.interedges_def SimpleGraph.interedges_def
-/

/- warning: simple_graph.edge_density_def -> SimpleGraph.edgeDensity_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{1} Rat (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α t))))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{1} Rat (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} α s)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} α t))))
Case conversion may be inaccurate. Consider using '#align simple_graph.edge_density_def SimpleGraph.edgeDensity_defₓ'. -/
theorem edgeDensity_def (s t : Finset α) :
    G.edgeDensity s t = (G.interedges s t).card / (s.card * t.card) :=
  rfl
#align simple_graph.edge_density_def SimpleGraph.edgeDensity_def

/- warning: simple_graph.card_interedges_div_card -> SimpleGraph.card_interedges_div_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{1} Rat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α s)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))))) (Finset.card.{u1} α t)))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t)
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{1} Rat (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} α s)) (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing))) (Finset.card.{u1} α t)))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t)
Case conversion may be inaccurate. Consider using '#align simple_graph.card_interedges_div_card SimpleGraph.card_interedges_div_cardₓ'. -/
@[simp]
theorem card_interedges_div_card (s t : Finset α) :
    ((G.interedges s t).card : ℚ) / (s.card * t.card) = G.edgeDensity s t :=
  rfl
#align simple_graph.card_interedges_div_card SimpleGraph.card_interedges_div_card

#print SimpleGraph.mem_interedges_iff /-
theorem mem_interedges_iff {x : α × α} : x ∈ G.interedges s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ G.Adj x.1 x.2 :=
  mem_interedges_iff
#align simple_graph.mem_interedges_iff SimpleGraph.mem_interedges_iff
-/

#print SimpleGraph.mk_mem_interedges_iff /-
theorem mk_mem_interedges_iff : (a, b) ∈ G.interedges s t ↔ a ∈ s ∧ b ∈ t ∧ G.Adj a b :=
  mk_mem_interedges_iff
#align simple_graph.mk_mem_interedges_iff SimpleGraph.mk_mem_interedges_iff
-/

#print SimpleGraph.interedges_empty_left /-
@[simp]
theorem interedges_empty_left (t : Finset α) : G.interedges ∅ t = ∅ :=
  interedges_empty_left _
#align simple_graph.interedges_empty_left SimpleGraph.interedges_empty_left
-/

#print SimpleGraph.interedges_mono /-
theorem interedges_mono : s₂ ⊆ s₁ → t₂ ⊆ t₁ → G.interedges s₂ t₂ ⊆ G.interedges s₁ t₁ :=
  interedges_mono
#align simple_graph.interedges_mono SimpleGraph.interedges_mono
-/

/- warning: simple_graph.interedges_disjoint_left -> SimpleGraph.interedges_disjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s₁ s₂) -> (forall (t : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.partialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.orderBot.{u1} (Prod.{u1, u1} α α)) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s₁ t) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s₁ s₂) -> (forall (t : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.partialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} (Prod.{u1, u1} α α)) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s₁ t) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s₂ t))
Case conversion may be inaccurate. Consider using '#align simple_graph.interedges_disjoint_left SimpleGraph.interedges_disjoint_leftₓ'. -/
theorem interedges_disjoint_left (hs : Disjoint s₁ s₂) (t : Finset α) :
    Disjoint (G.interedges s₁ t) (G.interedges s₂ t) :=
  interedges_disjoint_left _ hs _
#align simple_graph.interedges_disjoint_left SimpleGraph.interedges_disjoint_left

/- warning: simple_graph.interedges_disjoint_right -> SimpleGraph.interedges_disjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {t₁ : Finset.{u1} α} {t₂ : Finset.{u1} α} (s : Finset.{u1} α), (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) t₁ t₂) -> (Disjoint.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.partialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.orderBot.{u1} (Prod.{u1, u1} α α)) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t₁) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t₂))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {t₁ : Finset.{u1} α} {t₂ : Finset.{u1} α} (s : Finset.{u1} α), (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) t₁ t₂) -> (Disjoint.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.partialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} (Prod.{u1, u1} α α)) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t₁) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t₂))
Case conversion may be inaccurate. Consider using '#align simple_graph.interedges_disjoint_right SimpleGraph.interedges_disjoint_rightₓ'. -/
theorem interedges_disjoint_right (s : Finset α) (ht : Disjoint t₁ t₂) :
    Disjoint (G.interedges s t₁) (G.interedges s t₂) :=
  interedges_disjoint_right _ _ ht
#align simple_graph.interedges_disjoint_right SimpleGraph.interedges_disjoint_right

section DecidableEq

variable [DecidableEq α]

/- warning: simple_graph.interedges_bUnion_left -> SimpleGraph.interedges_bunionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u1} ι) (t : Finset.{u2} α) (f : ι -> (Finset.{u2} α)), Eq.{succ u2} (Finset.{u2} (Prod.{u2, u2} α α)) (SimpleGraph.interedges.{u2} α G (fun (a : α) (b : α) => _inst_1 a b) (Finset.bunionᵢ.{u1, u2} ι α (fun (a : α) (b : α) => _inst_2 a b) s f) t) (Finset.bunionᵢ.{u1, u2} ι (Prod.{u2, u2} α α) (fun (a : Prod.{u2, u2} α α) (b : Prod.{u2, u2} α α) => Prod.Lex.decidableEq.{u2, u2} α α (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) s (fun (a : ι) => SimpleGraph.interedges.{u2} α G (fun (a : α) (b : α) => _inst_1 a b) (f a) t))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u2} ι) (t : Finset.{u1} α) (f : ι -> (Finset.{u1} α)), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (Finset.bunionᵢ.{u2, u1} ι α (fun (a : α) (b : α) => _inst_2 a b) s f) t) (Finset.bunionᵢ.{u2, u1} ι (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) s (fun (a : ι) => SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (f a) t))
Case conversion may be inaccurate. Consider using '#align simple_graph.interedges_bUnion_left SimpleGraph.interedges_bunionᵢ_leftₓ'. -/
theorem interedges_bunionᵢ_left (s : Finset ι) (t : Finset α) (f : ι → Finset α) :
    G.interedges (s.bunionᵢ f) t = s.bunionᵢ fun a => G.interedges (f a) t :=
  interedges_bunionᵢ_left _ _ _ _
#align simple_graph.interedges_bUnion_left SimpleGraph.interedges_bunionᵢ_left

#print SimpleGraph.interedges_bunionᵢ_right /-
theorem interedges_bunionᵢ_right (s : Finset α) (t : Finset ι) (f : ι → Finset α) :
    G.interedges s (t.bunionᵢ f) = t.bunionᵢ fun b => G.interedges s (f b) :=
  interedges_bunionᵢ_right _ _ _ _
#align simple_graph.interedges_bUnion_right SimpleGraph.interedges_bunionᵢ_right
-/

/- warning: simple_graph.interedges_bUnion -> SimpleGraph.interedges_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} (G : SimpleGraph.{u3} α) [_inst_1 : DecidableRel.{succ u3} α (SimpleGraph.Adj.{u3} α G)] [_inst_2 : DecidableEq.{succ u3} α] (s : Finset.{u1} ι) (t : Finset.{u2} κ) (f : ι -> (Finset.{u3} α)) (g : κ -> (Finset.{u3} α)), Eq.{succ u3} (Finset.{u3} (Prod.{u3, u3} α α)) (SimpleGraph.interedges.{u3} α G (fun (a : α) (b : α) => _inst_1 a b) (Finset.bunionᵢ.{u1, u3} ι α (fun (a : α) (b : α) => _inst_2 a b) s f) (Finset.bunionᵢ.{u2, u3} κ α (fun (a : α) (b : α) => _inst_2 a b) t g)) (Finset.bunionᵢ.{max u1 u2, u3} (Prod.{u1, u2} ι κ) (Prod.{u3, u3} α α) (fun (a : Prod.{u3, u3} α α) (b : Prod.{u3, u3} α α) => Prod.Lex.decidableEq.{u3, u3} α α (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) (Finset.product.{u1, u2} ι κ s t) (fun (ab : Prod.{u1, u2} ι κ) => SimpleGraph.interedges.{u3} α G (fun (a : α) (b : α) => _inst_1 a b) (f (Prod.fst.{u1, u2} ι κ ab)) (g (Prod.snd.{u1, u2} ι κ ab))))
but is expected to have type
  forall {ι : Type.{u3}} {κ : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u3} ι) (t : Finset.{u2} κ) (f : ι -> (Finset.{u1} α)) (g : κ -> (Finset.{u1} α)), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (Finset.bunionᵢ.{u3, u1} ι α (fun (a : α) (b : α) => _inst_2 a b) s f) (Finset.bunionᵢ.{u2, u1} κ α (fun (a : α) (b : α) => _inst_2 a b) t g)) (Finset.bunionᵢ.{max u3 u2, u1} (Prod.{u3, u2} ι κ) (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) (Finset.product.{u3, u2} ι κ s t) (fun (ab : Prod.{u3, u2} ι κ) => SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (f (Prod.fst.{u3, u2} ι κ ab)) (g (Prod.snd.{u3, u2} ι κ ab))))
Case conversion may be inaccurate. Consider using '#align simple_graph.interedges_bUnion SimpleGraph.interedges_bunionᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem interedges_bunionᵢ (s : Finset ι) (t : Finset κ) (f : ι → Finset α) (g : κ → Finset α) :
    G.interedges (s.bunionᵢ f) (t.bunionᵢ g) =
      (s ×ˢ t).bunionᵢ fun ab => G.interedges (f ab.1) (g ab.2) :=
  interedges_bunionᵢ _ _ _ _ _
#align simple_graph.interedges_bUnion SimpleGraph.interedges_bunionᵢ

/- warning: simple_graph.card_interedges_add_card_interedges_compl -> SimpleGraph.card_interedges_add_card_interedges_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t)) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α (HasCompl.compl.{u1} (SimpleGraph.{u1} α) (SimpleGraph.hasCompl.{u1} α) G) (fun (a : α) (b : α) => SimpleGraph.Compl.adjDecidable.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) s t))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u1} α t)))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t)) (Finset.card.{u1} (Prod.{u1, u1} α α) (SimpleGraph.interedges.{u1} α (HasCompl.compl.{u1} (SimpleGraph.{u1} α) (SimpleGraph.instHasComplSimpleGraph.{u1} α) G) (fun (a : α) (b : α) => SimpleGraph.Compl.adjDecidable.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) s t))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} α s) (Finset.card.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align simple_graph.card_interedges_add_card_interedges_compl SimpleGraph.card_interedges_add_card_interedges_complₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem card_interedges_add_card_interedges_compl (h : Disjoint s t) :
    (G.interedges s t).card + (Gᶜ.interedges s t).card = s.card * t.card :=
  by
  rw [← card_product, interedges_def, interedges_def]
  have : ((s ×ˢ t).filterₓ fun e => Gᶜ.Adj e.1 e.2) = (s ×ˢ t).filterₓ fun e => ¬G.adj e.1 e.2 :=
    by
    refine' filter_congr fun x hx => _
    rw [mem_product] at hx
    rw [compl_adj, and_iff_right (h.forall_ne_finset hx.1 hx.2)]
  rw [this, ← card_union_eq, filter_union_filter_neg_eq]
  exact disjoint_filter.2 fun x _ => Classical.not_not.2
#align simple_graph.card_interedges_add_card_interedges_compl SimpleGraph.card_interedges_add_card_interedges_compl

/- warning: simple_graph.edge_density_add_edge_density_compl -> SimpleGraph.edgeDensity_add_edgeDensity_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α], (Finset.Nonempty.{u1} α s) -> (Finset.Nonempty.{u1} α t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{1} Rat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t) (SimpleGraph.edgeDensity.{u1} α (HasCompl.compl.{u1} (SimpleGraph.{u1} α) (SimpleGraph.hasCompl.{u1} α) G) (fun (a : α) (b : α) => SimpleGraph.Compl.adjDecidable.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) s t)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α], (Finset.Nonempty.{u1} α s) -> (Finset.Nonempty.{u1} α t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{1} Rat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t) (SimpleGraph.edgeDensity.{u1} α (HasCompl.compl.{u1} (SimpleGraph.{u1} α) (SimpleGraph.instHasComplSimpleGraph.{u1} α) G) (fun (a : α) (b : α) => SimpleGraph.Compl.adjDecidable.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_2 a b) a b) s t)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)))
Case conversion may be inaccurate. Consider using '#align simple_graph.edge_density_add_edge_density_compl SimpleGraph.edgeDensity_add_edgeDensity_complₓ'. -/
theorem edgeDensity_add_edgeDensity_compl (hs : s.Nonempty) (ht : t.Nonempty) (h : Disjoint s t) :
    G.edgeDensity s t + Gᶜ.edgeDensity s t = 1 :=
  by
  rw [edge_density_def, edge_density_def, div_add_div_same, div_eq_one_iff_eq]
  · exact_mod_cast card_interedges_add_card_interedges_compl _ h
  · positivity
#align simple_graph.edge_density_add_edge_density_compl SimpleGraph.edgeDensity_add_edgeDensity_compl

end DecidableEq

#print SimpleGraph.card_interedges_le_mul /-
theorem card_interedges_le_mul (s t : Finset α) : (G.interedges s t).card ≤ s.card * t.card :=
  card_interedges_le_mul _ _ _
#align simple_graph.card_interedges_le_mul SimpleGraph.card_interedges_le_mul
-/

/- warning: simple_graph.edge_density_nonneg -> SimpleGraph.edgeDensity_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t)
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t)
Case conversion may be inaccurate. Consider using '#align simple_graph.edge_density_nonneg SimpleGraph.edgeDensity_nonnegₓ'. -/
theorem edgeDensity_nonneg (s t : Finset α) : 0 ≤ G.edgeDensity s t :=
  edgeDensity_nonneg _ _ _
#align simple_graph.edge_density_nonneg SimpleGraph.edgeDensity_nonneg

/- warning: simple_graph.edge_density_le_one -> SimpleGraph.edgeDensity_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), LE.le.{0} Rat Rat.hasLe (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (s : Finset.{u1} α) (t : Finset.{u1} α), LE.le.{0} Rat Rat.instLERat (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_1 a b) s t) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align simple_graph.edge_density_le_one SimpleGraph.edgeDensity_le_oneₓ'. -/
theorem edgeDensity_le_one (s t : Finset α) : G.edgeDensity s t ≤ 1 :=
  edgeDensity_le_one _ _ _
#align simple_graph.edge_density_le_one SimpleGraph.edgeDensity_le_one

#print SimpleGraph.edgeDensity_empty_left /-
@[simp]
theorem edgeDensity_empty_left (t : Finset α) : G.edgeDensity ∅ t = 0 :=
  edgeDensity_empty_left _ _
#align simple_graph.edge_density_empty_left SimpleGraph.edgeDensity_empty_left
-/

#print SimpleGraph.edgeDensity_empty_right /-
@[simp]
theorem edgeDensity_empty_right (s : Finset α) : G.edgeDensity s ∅ = 0 :=
  edgeDensity_empty_right _ _
#align simple_graph.edge_density_empty_right SimpleGraph.edgeDensity_empty_right
-/

#print SimpleGraph.swap_mem_interedges_iff /-
@[simp]
theorem swap_mem_interedges_iff {x : α × α} : x.symm ∈ G.interedges s t ↔ x ∈ G.interedges t s :=
  swap_mem_interedges_iff G.symm
#align simple_graph.swap_mem_interedges_iff SimpleGraph.swap_mem_interedges_iff
-/

#print SimpleGraph.mk_mem_interedges_comm /-
theorem mk_mem_interedges_comm : (a, b) ∈ G.interedges s t ↔ (b, a) ∈ G.interedges t s :=
  mk_mem_interedges_comm G.symm
#align simple_graph.mk_mem_interedges_comm SimpleGraph.mk_mem_interedges_comm
-/

#print SimpleGraph.edgeDensity_comm /-
theorem edgeDensity_comm (s t : Finset α) : G.edgeDensity s t = G.edgeDensity t s :=
  edgeDensity_comm G.symm s t
#align simple_graph.edge_density_comm SimpleGraph.edgeDensity_comm
-/

end SimpleGraph

namespace Tactic

open Positivity

/-- Extension for the `positivity` tactic: `rel.edge_density` and `simple_graph.edge_density` are
always nonnegative. -/
@[positivity]
unsafe def positivity_edge_density : expr → tactic strictness
  | q(Rel.edgeDensity $(r) $(s) $(t)) =>
    nonnegative <$> mk_mapp `` Rel.edgeDensity_nonneg [none, none, r, none, s, t]
  | q(SimpleGraph.edgeDensity $(G) $(s) $(t)) =>
    nonnegative <$> mk_mapp `` SimpleGraph.edgeDensity_nonneg [none, G, none, s, t]
  | e =>
    pp e >>=
      fail ∘
        format.bracket "The expression `"
          "` isn't of the form `rel.edge_density r s t` nor `simple_graph.edge_density G s t`"
#align tactic.positivity_edge_density tactic.positivity_edge_density

end Tactic

