/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.zorn
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Chain

/-!
# Zorn's lemmas

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves several formulations of Zorn's Lemma.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_partial_order`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices : ∃ m, ∀ a, m ≺ a → a ≺ m, { ... },`
  (or whatever you actually need) followed by a `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement :=
begin
  let s : set α := {x | whatever x},
  suffices : ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x, -- or with another operator
  { exact proof_post_zorn },
  apply zorn_subset, -- or another variant
  rintro c hcs hc,
  obtain rfl | hcnemp := c.eq_empty_or_nonempty, -- you might need to disjunct on c empty or not
  { exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩ },
  exact ⟨construction,
    proof_that_construction_respects_whatever,
    proof_that_construction_contains_all_stuff_in_c⟩,
end
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/


open Classical Set

variable {α β : Type _} {r : α → α → Prop} {c : Set α}

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => r

#print exists_maximal_of_chains_bounded /-
/-- **Zorn's lemma**

If every chain has an upper bound, then there exists a maximal element. -/
theorem exists_maximal_of_chains_bounded (h : ∀ c, IsChain r c → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  have : ∃ ub, ∀ a ∈ maxChain r, a ≺ ub := h _ <| maxChain_spec.left
  let ⟨ub, (hub : ∀ a ∈ maxChain r, a ≺ ub)⟩ := this
  ⟨ub, fun a ha =>
    have : IsChain r (insert a <| maxChain r) :=
      maxChain_spec.1.insert fun b hb _ => Or.inr <| trans (hub b hb) ha
    hub a <| by
      rw [max_chain_spec.right this (subset_insert _ _)]
      exact mem_insert _ _⟩
#align exists_maximal_of_chains_bounded exists_maximal_of_chains_bounded
-/

#print exists_maximal_of_nonempty_chains_bounded /-
/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [Nonempty α]
    (h : ∀ c, IsChain r c → c.Nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
    (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) : ∃ m, ∀ a, m ≺ a → a ≺ m :=
  exists_maximal_of_chains_bounded
    (fun c hc =>
      (eq_empty_or_nonempty c).elim
        (fun h => ⟨Classical.arbitrary α, fun x hx => (h ▸ hx : x ∈ (∅ : Set α)).elim⟩) (h c hc))
    fun a b c => trans
#align exists_maximal_of_nonempty_chains_bounded exists_maximal_of_nonempty_chains_bounded
-/

section Preorder

variable [Preorder α]

#print zorn_preorder /-
theorem zorn_preorder (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a ≤ m :=
  exists_maximal_of_chains_bounded h fun a b c => le_trans
#align zorn_preorder zorn_preorder
-/

#print zorn_nonempty_preorder /-
theorem zorn_nonempty_preorder [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, ∀ a, m ≤ a → a ≤ m :=
  exists_maximal_of_nonempty_chains_bounded h fun a b c => le_trans
#align zorn_nonempty_preorder zorn_nonempty_preorder
-/

/- warning: zorn_preorder₀ -> zorn_preorder₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) c s) -> (IsChain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) c) -> (Exists.{succ u1} α (fun (ub : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) => forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z ub))))) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) => forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m z) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z m))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) c s) -> (IsChain.{u1} α (fun (x._@.Mathlib.Order.Zorn._hyg.862 : α) (x._@.Mathlib.Order.Zorn._hyg.864 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Zorn._hyg.862 x._@.Mathlib.Order.Zorn._hyg.864) c) -> (Exists.{succ u1} α (fun (ub : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) ub s) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z ub))))) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m z) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z m))))
Case conversion may be inaccurate. Consider using '#align zorn_preorder₀ zorn_preorder₀ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » s) -/
theorem zorn_preorder₀ (s : Set α)
    (ih : ∀ (c) (_ : c ⊆ s), IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z ≤ m :=
  let ⟨⟨m, hms⟩, h⟩ :=
    @zorn_preorder s _ fun c hc =>
      let ⟨ub, hubs, hub⟩ :=
        ih (Subtype.val '' c) (fun _ ⟨⟨x, hx⟩, _, h⟩ => h ▸ hx)
          (by
            rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq <;>
              refine' hc hpc hqc fun t => hpq (Subtype.ext_iff.1 t))
      ⟨⟨ub, hubs⟩, fun ⟨y, hy⟩ hc => hub _ ⟨_, hc, rfl⟩⟩
  ⟨m, hms, fun z hzs hmz => h ⟨z, hzs⟩ hmz⟩
#align zorn_preorder₀ zorn_preorder₀

/- warning: zorn_nonempty_preorder₀ -> zorn_nonempty_preorder₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) c s) -> (IsChain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) c) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y c) -> (Exists.{succ u1} α (fun (ub : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) => forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z ub)))))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) => And (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x m) (forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m z) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z m))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) c s) -> (IsChain.{u1} α (fun (x._@.Mathlib.Order.Zorn._hyg.1178 : α) (x._@.Mathlib.Order.Zorn._hyg.1180 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Zorn._hyg.1178 x._@.Mathlib.Order.Zorn._hyg.1180) c) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y c) -> (Exists.{succ u1} α (fun (ub : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) ub s) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z ub)))))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) (And (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x m) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) m z) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) z m))))))
Case conversion may be inaccurate. Consider using '#align zorn_nonempty_preorder₀ zorn_nonempty_preorder₀ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » s) -/
theorem zorn_nonempty_preorder₀ (s : Set α)
    (ih : ∀ (c) (_ : c ⊆ s), IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α)
    (hxs : x ∈ s) : ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z ≤ m :=
  by
  rcases zorn_preorder₀ ({ y ∈ s | x ≤ y }) fun c hcs hc => _ with ⟨m, ⟨hms, hxm⟩, hm⟩
  · exact ⟨m, hms, hxm, fun z hzs hmz => hm _ ⟨hzs, hxm.trans hmz⟩ hmz⟩
  · rcases c.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
    · exact ⟨x, ⟨hxs, le_rfl⟩, fun z => False.elim⟩
    · rcases ih c (fun z hz => (hcs hz).1) hc y hy with ⟨z, hzs, hz⟩
      exact ⟨z, ⟨hzs, (hcs hy).2.trans <| hz _ hy⟩, hz⟩
#align zorn_nonempty_preorder₀ zorn_nonempty_preorder₀

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » Ici[set.Ici] a) -/
#print zorn_nonempty_Ici₀ /-
theorem zorn_nonempty_Ici₀ (a : α)
    (ih : ∀ (c) (_ : c ⊆ Ici a), IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub, a ≤ ub ∧ ∀ z ∈ c, z ≤ ub)
    (x : α) (hax : a ≤ x) : ∃ m, x ≤ m ∧ ∀ z, m ≤ z → z ≤ m :=
  let ⟨m, hma, hxm, hm⟩ := zorn_nonempty_preorder₀ (Ici a) (by simpa using ih) x hax
  ⟨m, hxm, fun z hmz => hm _ (hax.trans <| hxm.trans hmz) hmz⟩
#align zorn_nonempty_Ici₀ zorn_nonempty_Ici₀
-/

end Preorder

section PartialOrder

variable [PartialOrder α]

#print zorn_partialOrder /-
theorem zorn_partialOrder (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a = m :=
  let ⟨m, hm⟩ := zorn_preorder h
  ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩
#align zorn_partial_order zorn_partialOrder
-/

#print zorn_nonempty_partialOrder /-
theorem zorn_nonempty_partialOrder [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) : ∃ m : α, ∀ a, m ≤ a → a = m :=
  let ⟨m, hm⟩ := zorn_nonempty_preorder h
  ⟨m, fun a ha => le_antisymm (hm a ha) ha⟩
#align zorn_nonempty_partial_order zorn_nonempty_partialOrder
-/

/- warning: zorn_partial_order₀ -> zorn_partialOrder₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) c s) -> (IsChain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) c) -> (Exists.{succ u1} α (fun (ub : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) => forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) z ub))))) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) => forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m z) -> (Eq.{succ u1} α z m))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) c s) -> (IsChain.{u1} α (fun (x._@.Mathlib.Order.Zorn._hyg.1874 : α) (x._@.Mathlib.Order.Zorn._hyg.1876 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Order.Zorn._hyg.1874 x._@.Mathlib.Order.Zorn._hyg.1876) c) -> (Exists.{succ u1} α (fun (ub : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) ub s) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) z ub))))) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m z) -> (Eq.{succ u1} α z m))))
Case conversion may be inaccurate. Consider using '#align zorn_partial_order₀ zorn_partialOrder₀ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » s) -/
theorem zorn_partialOrder₀ (s : Set α)
    (ih : ∀ (c) (_ : c ⊆ s), IsChain (· ≤ ·) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
    ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z = m :=
  let ⟨m, hms, hm⟩ := zorn_preorder₀ s ih
  ⟨m, hms, fun z hzs hmz => (hm z hzs hmz).antisymm hmz⟩
#align zorn_partial_order₀ zorn_partialOrder₀

/- warning: zorn_nonempty_partial_order₀ -> zorn_nonempty_partialOrder₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) c s) -> (IsChain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) c) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y c) -> (Exists.{succ u1} α (fun (ub : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) ub s) => forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) z ub)))))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) => And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x m) (forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m z) -> (Eq.{succ u1} α z m))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : Set.{u1} α), (forall (c : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) c s) -> (IsChain.{u1} α (fun (x._@.Mathlib.Order.Zorn._hyg.2042 : α) (x._@.Mathlib.Order.Zorn._hyg.2044 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Order.Zorn._hyg.2042 x._@.Mathlib.Order.Zorn._hyg.2044) c) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y c) -> (Exists.{succ u1} α (fun (ub : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) ub s) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) z ub)))))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x m) (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m z) -> (Eq.{succ u1} α z m))))))
Case conversion may be inaccurate. Consider using '#align zorn_nonempty_partial_order₀ zorn_nonempty_partialOrder₀ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » s) -/
theorem zorn_nonempty_partialOrder₀ (s : Set α)
    (ih : ∀ (c) (_ : c ⊆ s), IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α)
    (hxs : x ∈ s) : ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z = m :=
  let ⟨m, hms, hxm, hm⟩ := zorn_nonempty_preorder₀ s ih x hxs
  ⟨m, hms, hxm, fun z hzs hmz => (hm z hzs hmz).antisymm hmz⟩
#align zorn_nonempty_partial_order₀ zorn_nonempty_partialOrder₀

end PartialOrder

/- warning: zorn_subset -> zorn_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (ub : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) ub S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) ub S) => forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s ub))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) => forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) m a) -> (Eq.{succ u1} (Set.{u1} α) a m))))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Order.Zorn._hyg.2249 : Set.{u1} α) (x._@.Mathlib.Order.Zorn._hyg.2251 : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) x._@.Mathlib.Order.Zorn._hyg.2249 x._@.Mathlib.Order.Zorn._hyg.2251) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (ub : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) ub S) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s ub))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) m S) (forall (a : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) m a) -> (Eq.{succ u1} (Set.{u1} α) a m))))
Case conversion may be inaccurate. Consider using '#align zorn_subset zorn_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » S) -/
theorem zorn_subset (S : Set (Set α))
    (h : ∀ (c) (_ : c ⊆ S), IsChain (· ⊆ ·) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
    ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m :=
  zorn_partialOrder₀ S h
#align zorn_subset zorn_subset

/- warning: zorn_subset_nonempty -> zorn_subset_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) c) -> (Set.Nonempty.{u1} (Set.{u1} α) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (ub : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) ub S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) ub S) => forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s ub))))) -> (forall (x : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x S) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) x m) (forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) m a) -> (Eq.{succ u1} (Set.{u1} α) a m))))))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Order.Zorn._hyg.2373 : Set.{u1} α) (x._@.Mathlib.Order.Zorn._hyg.2375 : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) x._@.Mathlib.Order.Zorn._hyg.2373 x._@.Mathlib.Order.Zorn._hyg.2375) c) -> (Set.Nonempty.{u1} (Set.{u1} α) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (ub : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) ub S) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s ub))))) -> (forall (x : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) x S) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) m S) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) x m) (forall (a : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) m a) -> (Eq.{succ u1} (Set.{u1} α) a m))))))
Case conversion may be inaccurate. Consider using '#align zorn_subset_nonempty zorn_subset_nonemptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » S) -/
theorem zorn_subset_nonempty (S : Set (Set α))
    (H : ∀ (c) (_ : c ⊆ S), IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x)
    (hx : x ∈ S) : ∃ m ∈ S, x ⊆ m ∧ ∀ a ∈ S, m ⊆ a → a = m :=
  zorn_nonempty_partialOrder₀ _ (fun c cS hc y yc => H _ cS hc ⟨y, yc⟩) _ hx
#align zorn_subset_nonempty zorn_subset_nonempty

/- warning: zorn_superset -> zorn_superset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (lb : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) lb S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) lb S) => forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) lb s))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) => forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a m) -> (Eq.{succ u1} (Set.{u1} α) a m))))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Order.Zorn._hyg.2532 : Set.{u1} α) (x._@.Mathlib.Order.Zorn._hyg.2534 : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) x._@.Mathlib.Order.Zorn._hyg.2532 x._@.Mathlib.Order.Zorn._hyg.2534) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (lb : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) lb S) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) lb s))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) m S) (forall (a : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a m) -> (Eq.{succ u1} (Set.{u1} α) a m))))
Case conversion may be inaccurate. Consider using '#align zorn_superset zorn_supersetₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » S) -/
theorem zorn_superset (S : Set (Set α))
    (h : ∀ (c) (_ : c ⊆ S), IsChain (· ⊆ ·) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
    ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m :=
  @zorn_partialOrder₀ (Set α)ᵒᵈ _ S fun c cS hc => h c cS hc.symm
#align zorn_superset zorn_superset

/- warning: zorn_superset_nonempty -> zorn_superset_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasSubset.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) c) -> (Set.Nonempty.{u1} (Set.{u1} α) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (lb : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) lb S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) lb S) => forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) lb s))))) -> (forall (x : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) x S) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) m S) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) m x) (forall (a : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a m) -> (Eq.{succ u1} (Set.{u1} α) a m))))))
but is expected to have type
  forall {α : Type.{u1}} (S : Set.{u1} (Set.{u1} α)), (forall (c : Set.{u1} (Set.{u1} α)), (HasSubset.Subset.{u1} (Set.{u1} (Set.{u1} α)) (Set.instHasSubsetSet.{u1} (Set.{u1} α)) c S) -> (IsChain.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Order.Zorn._hyg.2674 : Set.{u1} α) (x._@.Mathlib.Order.Zorn._hyg.2676 : Set.{u1} α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) x._@.Mathlib.Order.Zorn._hyg.2674 x._@.Mathlib.Order.Zorn._hyg.2676) c) -> (Set.Nonempty.{u1} (Set.{u1} α) c) -> (Exists.{succ u1} (Set.{u1} α) (fun (lb : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) lb S) (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s c) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) lb s))))) -> (forall (x : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) x S) -> (Exists.{succ u1} (Set.{u1} α) (fun (m : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) m S) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) m x) (forall (a : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) a S) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a m) -> (Eq.{succ u1} (Set.{u1} α) a m))))))
Case conversion may be inaccurate. Consider using '#align zorn_superset_nonempty zorn_superset_nonemptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (c «expr ⊆ » S) -/
theorem zorn_superset_nonempty (S : Set (Set α))
    (H : ∀ (c) (_ : c ⊆ S), IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x)
    (hx : x ∈ S) : ∃ m ∈ S, m ⊆ x ∧ ∀ a ∈ S, a ⊆ m → a = m :=
  @zorn_nonempty_partialOrder₀ (Set α)ᵒᵈ _ S (fun c cS hc y yc => H _ cS hc.symm ⟨y, yc⟩) _ hx
#align zorn_superset_nonempty zorn_superset_nonempty

#print IsChain.exists_maxChain /-
/-- Every chain is contained in a maximal chain. This generalizes Hausdorff's maximality principle.
-/
theorem IsChain.exists_maxChain (hc : IsChain r c) : ∃ M, @IsMaxChain _ r M ∧ c ⊆ M :=
  by
  obtain ⟨M, ⟨_, hM₀⟩, hM₁, hM₂⟩ :=
    zorn_subset_nonempty { s | c ⊆ s ∧ IsChain r s } _ c ⟨subset.rfl, hc⟩
  · exact ⟨M, ⟨hM₀, fun d hd hMd => (hM₂ _ ⟨hM₁.trans hMd, hd⟩ hMd).symm⟩, hM₁⟩
  rintro cs hcs₀ hcs₁ ⟨s, hs⟩
  refine'
    ⟨⋃₀ cs, ⟨fun _ ha => Set.mem_unionₛ_of_mem ((hcs₀ hs).left ha) hs, _⟩, fun _ =>
      Set.subset_unionₛ_of_mem⟩
  rintro y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz
  obtain rfl | hsseq := eq_or_ne sy sz
  · exact (hcs₀ hsy).right hysy hzsz hyz
  cases' hcs₁ hsy hsz hsseq with h h
  · exact (hcs₀ hsz).right (h hysy) hzsz hyz
  · exact (hcs₀ hsy).right hysy (h hzsz) hyz
#align is_chain.exists_max_chain IsChain.exists_maxChain
-/

