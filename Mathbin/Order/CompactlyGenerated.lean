/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module order.compactly_generated
! leanprover-community/mathlib commit c813ed7de0f5115f956239124e9b30f3a621966f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Atoms
import Mathbin.Order.OrderIsoNat
import Mathbin.Order.RelIso.Set
import Mathbin.Order.SupIndep
import Mathbin.Order.Zorn
import Mathbin.Data.Finset.Order
import Mathbin.Data.Set.Intervals.OrderIso
import Mathbin.Data.Finite.Set
import Mathbin.Tactic.Tfae

/-!
# Compactness properties for complete lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `complete_lattice.is_compact_element`
 * `complete_lattice.is_compactly_generated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
 * `well_founded (>)`
 * `complete_lattice.is_sup_closed_compact`
 * `complete_lattice.is_Sup_finite_compact`
 * `∀ k, complete_lattice.is_compact_element k`

This is demonstrated by means of the following four lemmas:
 * `complete_lattice.well_founded.is_Sup_finite_compact`
 * `complete_lattice.is_Sup_finite_compact.is_sup_closed_compact`
 * `complete_lattice.is_sup_closed_compact.well_founded`
 * `complete_lattice.is_Sup_finite_compact_iff_all_elements_compact`

 We also show well-founded lattices are compactly generated
 (`complete_lattice.compactly_generated_of_well_founded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/


alias directedOn_range ↔ Directed.directedOn_range _
#align directed.directed_on_range Directed.directedOn_range

attribute [protected] Directed.directedOn_range

variable {ι : Sort _} {α : Type _} [CompleteLattice α] {f : ι → α}

namespace CompleteLattice

variable (α)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a b «expr ∈ » s) -/
#print CompleteLattice.IsSupClosedCompact /-
/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `Sup`. -/
def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (h : s.Nonempty), (∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊔ b ∈ s) → sSup s ∈ s
#align complete_lattice.is_sup_closed_compact CompleteLattice.IsSupClosedCompact
-/

#print CompleteLattice.IsSupFiniteCompact /-
/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `Sup`. -/
def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sSup s = t.sup id
#align complete_lattice.is_Sup_finite_compact CompleteLattice.IsSupFiniteCompact
-/

#print CompleteLattice.IsCompactElement /-
/-- An element `k` of a complete lattice is said to be compact if any set with `Sup`
above `k` has a finite subset with `Sup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def IsCompactElement {α : Type _} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ sSup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id
#align complete_lattice.is_compact_element CompleteLattice.IsCompactElement
-/

/- warning: complete_lattice.is_compact_element_iff -> CompleteLattice.isCompactElement_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CompleteLattice.{u1} α] (k : α), Iff (CompleteLattice.IsCompactElement.{u1} α _inst_2 k) (forall (ι : Type.{u1}) (s : ι -> α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) k (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) ι s)) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) k (Finset.sup.{u1, u1} α ι (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_2)) t s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CompleteLattice.{u1} α] (k : α), Iff (CompleteLattice.IsCompactElement.{u1} α _inst_2 k) (forall (ι : Type.{u1}) (s : ι -> α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) k (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) ι s)) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (t : Finset.{u1} ι) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) k (Finset.sup.{u1, u1} α ι (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_2)) t s))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.is_compact_element_iff CompleteLattice.isCompactElement_iffₓ'. -/
theorem isCompactElement_iff.{u} {α : Type u} [CompleteLattice α] (k : α) :
    CompleteLattice.IsCompactElement k ↔
      ∀ (ι : Type u) (s : ι → α), k ≤ iSup s → ∃ t : Finset ι, k ≤ t.sup s :=
  by
  classical
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : ∀ x : t, ∃ i, s i = x := fun x => ht x.Prop
      choose f hf using this
      refine' ⟨finset.univ.image f, ht'.trans _⟩
      · rw [Finset.sup_le_iff]
        intro b hb
        rw [← show s (f ⟨b, hb⟩) = id b from hf _]
        exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ ⟨b, hb⟩)
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s coe
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine' ⟨t.image coe, by simp, ht.trans _⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem coe hx)
#align complete_lattice.is_compact_element_iff CompleteLattice.isCompactElement_iff

/- warning: complete_lattice.is_compact_element_iff_le_of_directed_Sup_le -> CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α] (k : α), Iff (CompleteLattice.IsCompactElement.{u1} α _inst_1 k) (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) k (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) k x))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α] (k : α), Iff (CompleteLattice.IsCompactElement.{u1} α _inst_1 k) (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.541 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.543 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.541 x._@.Mathlib.Order.CompactlyGenerated._hyg.543) s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) k (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) k x))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.is_compact_element_iff_le_of_directed_Sup_le CompleteLattice.isCompactElement_iff_le_of_directed_sSup_leₓ'. -/
/-- An element `k` is compact if and only if any directed set with `Sup` above
`k` already got above `k` at some point in the set. -/
theorem isCompactElement_iff_le_of_directed_sSup_le (k : α) :
    IsCompactElement k ↔
      ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ sSup s → ∃ x : α, x ∈ s ∧ k ≤ x :=
  by
  classical
    constructor
    · intro hk s hne hdir hsup
      obtain ⟨t, ht⟩ := hk s hsup
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : ∀ x ∈ t, ∃ y ∈ s, x ≤ y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· ≤ ·) S :=
        by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c ∪ d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : Sup s ≤ Sup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true_iff, id.def, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.nonempty := by
        suffices : ⊥ ∈ S
        exact Set.nonempty_of_mem this
        use ∅
        simp only [Set.empty_subset, Finset.coe_empty, Finset.sup_empty, eq_self_iff_true,
          and_self_iff]
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩
#align complete_lattice.is_compact_element_iff_le_of_directed_Sup_le CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le

/- warning: complete_lattice.is_compact_element.exists_finset_of_le_supr -> CompleteLattice.IsCompactElement.exists_finset_of_le_iSup is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α] {k : α}, (CompleteLattice.IsCompactElement.{u1} α _inst_1 k) -> (forall {ι : Type.{u2}} (f : ι -> α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) k (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) -> (Exists.{succ u2} (Finset.{u2} ι) (fun (s : Finset.{u2} ι) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) k (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) => f i))))))
but is expected to have type
  forall (α : Type.{u2}) [_inst_1 : CompleteLattice.{u2} α] {k : α}, (CompleteLattice.IsCompactElement.{u2} α _inst_1 k) -> (forall {ι : Type.{u1}} (f : ι -> α), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) k (iSup.{u2, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i))) -> (Exists.{succ u1} (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) k (iSup.{u2, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, 0} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) => f i))))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.is_compact_element.exists_finset_of_le_supr CompleteLattice.IsCompactElement.exists_finset_of_le_iSupₓ'. -/
theorem IsCompactElement.exists_finset_of_le_iSup {k : α} (hk : IsCompactElement k) {ι : Type _}
    (f : ι → α) (h : k ≤ ⨆ i, f i) : ∃ s : Finset ι, k ≤ ⨆ i ∈ s, f i := by
  classical
    let g : Finset ι → α := fun s => ⨆ i ∈ s, f i
    have h1 : DirectedOn (· ≤ ·) (Set.range g) :=
      by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩, iSup_le_iSup_of_subset (Finset.subset_union_left s t),
          iSup_le_iSup_of_subset (Finset.subset_union_right s t)⟩
    have h2 : k ≤ Sup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ :=
      (is_compact_element_iff_le_of_directed_Sup_le α k).mp hk (Set.range g) (Set.range_nonempty g)
        h1 h2
    exact ⟨s, hs⟩
#align complete_lattice.is_compact_element.exists_finset_of_le_supr CompleteLattice.IsCompactElement.exists_finset_of_le_iSup

/- warning: complete_lattice.is_compact_element.directed_Sup_lt_of_lt -> CompleteLattice.IsCompactElement.directed_sSup_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CompleteLattice.{u1} α] {k : α}, (CompleteLattice.IsCompactElement.{u1} α _inst_2 k) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2))))) s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) x k)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) s) k))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CompleteLattice.{u1} α] {k : α}, (CompleteLattice.IsCompactElement.{u1} α _inst_2 k) -> (forall {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.1395 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.1397 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.1395 x._@.Mathlib.Order.CompactlyGenerated._hyg.1397) s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) x k)) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_2)))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)) s) k))
Case conversion may be inaccurate. Consider using '#align complete_lattice.is_compact_element.directed_Sup_lt_of_lt CompleteLattice.IsCompactElement.directed_sSup_lt_of_ltₓ'. -/
/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its Sup strictly below `k`. -/
theorem IsCompactElement.directed_sSup_lt_of_lt {α : Type _} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hbelow : ∀ x ∈ s, x < k) : sSup s < k :=
  by
  rw [is_compact_element_iff_le_of_directed_Sup_le] at hk
  by_contra
  have sSup : Sup s ≤ k := sSup_le fun s hs => (hbelow s hs).le
  replace sSup : Sup s = k := eq_iff_le_not_lt.mpr ⟨sSup, h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)
#align complete_lattice.is_compact_element.directed_Sup_lt_of_lt CompleteLattice.IsCompactElement.directed_sSup_lt_of_lt

/- warning: complete_lattice.finset_sup_compact_of_compact -> CompleteLattice.finset_sup_compact_of_compact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CompleteLattice.{u1} α] {f : β -> α} (s : Finset.{u2} β), (forall (x : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) -> (CompleteLattice.IsCompactElement.{u1} α _inst_2 (f x))) -> (CompleteLattice.IsCompactElement.{u1} α _inst_2 (Finset.sup.{u1, u2} α β (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_2)))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_2)) s f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CompleteLattice.{u2} α] {f : β -> α} (s : Finset.{u1} β), (forall (x : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s) -> (CompleteLattice.IsCompactElement.{u2} α _inst_2 (f x))) -> (CompleteLattice.IsCompactElement.{u2} α _inst_2 (Finset.sup.{u2, u1} α β (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_2))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_2)))))) (CompleteLattice.toBoundedOrder.{u2} α _inst_2)) s f))
Case conversion may be inaccurate. Consider using '#align complete_lattice.finset_sup_compact_of_compact CompleteLattice.finset_sup_compact_of_compactₓ'. -/
theorem finset_sup_compact_of_compact {α β : Type _} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀ x ∈ s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
    rw [is_compact_element_iff_le_of_directed_Sup_le]
    intro d hemp hdir hsup
    change f with id ∘ f
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := finset.mem_image.mp hx
    specialize h p hps
    rw [is_compact_element_iff_le_of_directed_Sup_le] at h
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]
#align complete_lattice.finset_sup_compact_of_compact CompleteLattice.finset_sup_compact_of_compact

#print CompleteLattice.WellFounded.isSupFiniteCompact /-
theorem WellFounded.isSupFiniteCompact (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsSupFiniteCompact α := fun s =>
  by
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ :=
    well_founded.well_founded_iff_has_min.mp h { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
      ⟨⊥, ∅, by simp⟩
  refine' ⟨t, ht₁, (sSup_le fun y hy => _).antisymm _⟩
  ·
    classical
      rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
          (hm _ ⟨insert y t, by simp [Set.insert_subset, hy, ht₁]⟩)]
      simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁
#align complete_lattice.well_founded.is_Sup_finite_compact CompleteLattice.WellFounded.isSupFiniteCompact
-/

#print CompleteLattice.IsSupFiniteCompact.isSupClosedCompact /-
theorem IsSupFiniteCompact.isSupClosedCompact (h : IsSupFiniteCompact α) : IsSupClosedCompact α :=
  by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  cases' t.eq_empty_or_nonempty with h h
  · subst h
    rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [eq_singleton_bot_of_sSup_eq_bot_of_nonempty ht₂ hne]
  · rw [ht₂]
    exact t.sup_closed_of_sup_closed h ht₁ hsc
#align complete_lattice.is_Sup_finite_compact.is_sup_closed_compact CompleteLattice.IsSupFiniteCompact.isSupClosedCompact
-/

#print CompleteLattice.IsSupClosedCompact.wellFounded /-
theorem IsSupClosedCompact.wellFounded (h : IsSupClosedCompact α) :
    WellFounded ((· > ·) : α → α → Prop) :=
  by
  refine' rel_embedding.well_founded_iff_no_descending_seq.mpr ⟨fun a => _⟩
  suffices Sup (Set.range a) ∈ Set.range a
    by
    obtain ⟨n, hn⟩ := set.mem_range.mp this
    have h' : Sup (Set.range a) < a (n + 1) :=
      by
      change _ > _
      simp [← hn, a.map_rel_iff]
    apply lt_irrefl (a (n + 1))
    apply lt_of_le_of_lt _ h'
    apply le_sSup
    apply Set.mem_range_self
  apply h (Set.range a)
  · use a 37
    apply Set.mem_range_self
  · rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    use m ⊔ n
    rw [← hm, ← hn]
    apply RelHomClass.map_sup a
#align complete_lattice.is_sup_closed_compact.well_founded CompleteLattice.IsSupClosedCompact.wellFounded
-/

#print CompleteLattice.isSupFiniteCompact_iff_all_elements_compact /-
theorem isSupFiniteCompact_iff_all_elements_compact :
    IsSupFiniteCompact α ↔ ∀ k : α, IsCompactElement k :=
  by
  refine' ⟨fun h k s hs => _, fun h s => _⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (Sup s) s (by rfl)
    have : Sup s = t.sup id :=
      by
      suffices t.sup id ≤ Sup s by apply le_antisymm <;> assumption
      simp only [id.def, Finset.sup_le_iff]
      intro x hx
      exact le_sSup (hts hx)
    use t, hts, this
#align complete_lattice.is_Sup_finite_compact_iff_all_elements_compact CompleteLattice.isSupFiniteCompact_iff_all_elements_compact
-/

#print CompleteLattice.wellFounded_characterisations /-
theorem wellFounded_characterisations :
    TFAE
      [WellFounded ((· > ·) : α → α → Prop), IsSupFiniteCompact α, IsSupClosedCompact α,
        ∀ k : α, IsCompactElement k] :=
  by
  tfae_have 1 → 2; · exact well_founded.is_Sup_finite_compact α
  tfae_have 2 → 3; · exact is_Sup_finite_compact.is_sup_closed_compact α
  tfae_have 3 → 1; · exact is_sup_closed_compact.well_founded α
  tfae_have 2 ↔ 4; · exact is_Sup_finite_compact_iff_all_elements_compact α
  tfae_finish
#align complete_lattice.well_founded_characterisations CompleteLattice.wellFounded_characterisations
-/

#print CompleteLattice.wellFounded_iff_isSupFiniteCompact /-
theorem wellFounded_iff_isSupFiniteCompact :
    WellFounded ((· > ·) : α → α → Prop) ↔ IsSupFiniteCompact α :=
  (wellFounded_characterisations α).out 0 1
#align complete_lattice.well_founded_iff_is_Sup_finite_compact CompleteLattice.wellFounded_iff_isSupFiniteCompact
-/

#print CompleteLattice.isSupFiniteCompact_iff_isSupClosedCompact /-
theorem isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (wellFounded_characterisations α).out 1 2
#align complete_lattice.is_Sup_finite_compact_iff_is_sup_closed_compact CompleteLattice.isSupFiniteCompact_iff_isSupClosedCompact
-/

#print CompleteLattice.isSupClosedCompact_iff_wellFounded /-
theorem isSupClosedCompact_iff_wellFounded :
    IsSupClosedCompact α ↔ WellFounded ((· > ·) : α → α → Prop) :=
  (wellFounded_characterisations α).out 2 0
#align complete_lattice.is_sup_closed_compact_iff_well_founded CompleteLattice.isSupClosedCompact_iff_wellFounded
-/

alias well_founded_iff_is_Sup_finite_compact ↔ _ is_Sup_finite_compact.well_founded
#align complete_lattice.is_Sup_finite_compact.well_founded CompleteLattice.IsSupFiniteCompact.wellFounded

alias is_Sup_finite_compact_iff_is_sup_closed_compact ↔
  _ is_sup_closed_compact.is_Sup_finite_compact
#align complete_lattice.is_sup_closed_compact.is_Sup_finite_compact CompleteLattice.IsSupClosedCompact.isSupFiniteCompact

alias is_sup_closed_compact_iff_well_founded ↔ _ _root_.well_founded.is_sup_closed_compact
#align well_founded.is_sup_closed_compact WellFounded.isSupClosedCompact

variable {α}

#print CompleteLattice.WellFounded.finite_of_setIndependent /-
theorem WellFounded.finite_of_setIndependent (h : WellFounded ((· > ·) : α → α → Prop)) {s : Set α}
    (hs : SetIndependent s) : s.Finite := by
  classical
    refine' set.not_infinite.mp fun contra => _
    obtain ⟨t, ht₁, ht₂⟩ := well_founded.is_Sup_finite_compact α h s
    replace contra : ∃ x : α, x ∈ s ∧ x ≠ ⊥ ∧ x ∉ t
    · have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.diff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ Sup s = ⊥
    · have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s) (by simp : x ∈ _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_Sup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs, eq_comm, inf_eq_left]
    exact le_sSup hx₀
#align complete_lattice.well_founded.finite_of_set_independent CompleteLattice.WellFounded.finite_of_setIndependent
-/

/- warning: complete_lattice.well_founded.finite_of_independent -> CompleteLattice.WellFounded.finite_of_independent is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], (WellFounded.{succ u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) -> (forall {ι : Type.{u2}} {t : ι -> α}, (CompleteLattice.Independent.{succ u2, u1} ι α _inst_1 t) -> (forall (i : ι), Ne.{succ u1} α (t i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) -> (Finite.{succ u2} ι))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : CompleteLattice.{u2} α], (WellFounded.{succ u2} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.6107 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.6109 : α) => GT.gt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.6107 x._@.Mathlib.Order.CompactlyGenerated._hyg.6109)) -> (forall {ι : Type.{u1}} {t : ι -> α}, (CompleteLattice.Independent.{succ u1, u2} ι α _inst_1 t) -> (forall (i : ι), Ne.{succ u2} α (t i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) -> (Finite.{succ u1} ι))
Case conversion may be inaccurate. Consider using '#align complete_lattice.well_founded.finite_of_independent CompleteLattice.WellFounded.finite_of_independentₓ'. -/
theorem WellFounded.finite_of_independent (hwf : WellFounded ((· > ·) : α → α → Prop)) {ι : Type _}
    {t : ι → α} (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (well_founded.finite_of_set_independent hwf ht.set_independent_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)
#align complete_lattice.well_founded.finite_of_independent CompleteLattice.WellFounded.finite_of_independent

end CompleteLattice

#print IsCompactlyGenerated /-
/-- A complete lattice is said to be compactly generated if any
element is the `Sup` of compact elements. -/
class IsCompactlyGenerated (α : Type _) [CompleteLattice α] : Prop where
  exists_sSup_eq : ∀ x : α, ∃ s : Set α, (∀ x ∈ s, CompleteLattice.IsCompactElement x) ∧ sSup s = x
#align is_compactly_generated IsCompactlyGenerated
-/

section

variable {α} [IsCompactlyGenerated α] {a b : α} {s : Set α}

/- warning: Sup_compact_le_eq -> sSup_compact_le_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] (b : α), Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (c : α) => And (CompleteLattice.IsCompactElement.{u1} α _inst_1 c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) c b)))) b
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] (b : α), Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (c : α) => And (CompleteLattice.IsCompactElement.{u1} α _inst_1 c) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) c b)))) b
Case conversion may be inaccurate. Consider using '#align Sup_compact_le_eq sSup_compact_le_eqₓ'. -/
@[simp]
theorem sSup_compact_le_eq (b) : sSup { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } = b :=
  by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)
#align Sup_compact_le_eq sSup_compact_le_eq

/- warning: Sup_compact_eq_top -> sSup_compact_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1], Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => CompleteLattice.IsCompactElement.{u1} α _inst_1 a))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1], Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => CompleteLattice.IsCompactElement.{u1} α _inst_1 a))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_compact_eq_top sSup_compact_eq_topₓ'. -/
@[simp]
theorem sSup_compact_eq_top : sSup { a : α | CompleteLattice.IsCompactElement a } = ⊤ :=
  by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (sSup_compact_le_eq ⊤)
  exact (and_iff_left le_top).symm
#align Sup_compact_eq_top sSup_compact_eq_top

#print le_iff_compact_le_imp /-
theorem le_iff_compact_le_imp {a b : α} :
    a ≤ b ↔ ∀ c : α, CompleteLattice.IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_trans ca ab, fun h =>
    by
    rw [← sSup_compact_le_eq a, ← sSup_compact_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩
#align le_iff_compact_le_imp le_iff_compact_le_imp
-/

/- warning: directed_on.inf_Sup_eq -> DirectedOn.inf_sSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) s) -> (Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.6526 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.6528 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.6526 x._@.Mathlib.Order.CompactlyGenerated._hyg.6528) s) -> (Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) a b))))
Case conversion may be inaccurate. Consider using '#align directed_on.inf_Sup_eq DirectedOn.inf_sSup_eqₓ'. -/
/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem DirectedOn.inf_sSup_eq (h : DirectedOn (· ≤ ·) s) : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      by_cases hs : s.nonempty
      · intro c hc hcinf
        rw [le_inf_iff] at hcinf
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        exact (le_inf hcinf.1 cd).trans (le_iSup₂ d ds)
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [hs])
    iSup_inf_le_inf_sSup
#align directed_on.inf_Sup_eq DirectedOn.inf_sSup_eq

/- warning: directed_on.Sup_inf_eq -> DirectedOn.sSup_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) s) -> (Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s) a) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) b a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.6794 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.6796 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.6794 x._@.Mathlib.Order.CompactlyGenerated._hyg.6796) s) -> (Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s) a) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) b a))))
Case conversion may be inaccurate. Consider using '#align directed_on.Sup_inf_eq DirectedOn.sSup_inf_eqₓ'. -/
/-- This property is sometimes referred to as `α` being upper continuous. -/
protected theorem DirectedOn.sSup_inf_eq (h : DirectedOn (· ≤ ·) s) : sSup s ⊓ a = ⨆ b ∈ s, b ⊓ a :=
  by simp_rw [@inf_comm _ _ _ a, h.inf_Sup_eq]
#align directed_on.Sup_inf_eq DirectedOn.sSup_inf_eq

/- warning: directed.inf_supr_eq -> Directed.inf_iSup_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} [_inst_2 : IsCompactlyGenerated.{u2} α _inst_1] {a : α}, (Directed.{u2, u1} α ι (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) f) -> (Eq.{succ u2} α (Inf.inf.{u2} α (SemilatticeInf.toHasInf.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)))) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toHasSup.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toHasSup.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u2} α (SemilatticeInf.toHasInf.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)))) a (f i))))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} {_inst_1 : ι -> α} [f : CompleteLattice.{u2} α] [_inst_2 : IsCompactlyGenerated.{u2} α f] {a : α}, (Directed.{u2, u1} α ι (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.6885 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.6887 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.6885 x._@.Mathlib.Order.CompactlyGenerated._hyg.6887) _inst_1) -> (Eq.{succ u2} α (Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f))) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f)) ι (fun (i : ι) => _inst_1 i))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f)) ι (fun (i : ι) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f))) a (_inst_1 i))))
Case conversion may be inaccurate. Consider using '#align directed.inf_supr_eq Directed.inf_iSup_eqₓ'. -/
protected theorem Directed.inf_iSup_eq (h : Directed (· ≤ ·) f) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i :=
  by rw [iSup, h.directed_on_range.inf_Sup_eq, iSup_range]
#align directed.inf_supr_eq Directed.inf_iSup_eq

/- warning: directed.supr_inf_eq -> Directed.iSup_inf_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} [_inst_2 : IsCompactlyGenerated.{u2} α _inst_1] {a : α}, (Directed.{u2, u1} α ι (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) f) -> (Eq.{succ u2} α (Inf.inf.{u2} α (SemilatticeInf.toHasInf.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toHasSup.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) a) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toHasSup.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u2} α (SemilatticeInf.toHasInf.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)))) (f i) a)))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} {_inst_1 : ι -> α} [f : CompleteLattice.{u2} α] [_inst_2 : IsCompactlyGenerated.{u2} α f] {a : α}, (Directed.{u2, u1} α ι (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.7000 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.7002 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.7000 x._@.Mathlib.Order.CompactlyGenerated._hyg.7002) _inst_1) -> (Eq.{succ u2} α (Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f))) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f)) ι (fun (i : ι) => _inst_1 i)) a) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f)) ι (fun (i : ι) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f))) (_inst_1 i) a)))
Case conversion may be inaccurate. Consider using '#align directed.supr_inf_eq Directed.iSup_inf_eqₓ'. -/
protected theorem Directed.iSup_inf_eq (h : Directed (· ≤ ·) f) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
  by rw [iSup, h.directed_on_range.Sup_inf_eq, iSup_range]
#align directed.supr_inf_eq Directed.iSup_inf_eq

/- warning: directed_on.disjoint_Sup_right -> DirectedOn.disjoint_sSup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) s) -> (Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (forall {{b : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.7117 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.7119 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.7117 x._@.Mathlib.Order.CompactlyGenerated._hyg.7119) s) -> (Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (forall {{b : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a b)))
Case conversion may be inaccurate. Consider using '#align directed_on.disjoint_Sup_right DirectedOn.disjoint_sSup_rightₓ'. -/
protected theorem DirectedOn.disjoint_sSup_right (h : DirectedOn (· ≤ ·) s) :
    Disjoint a (sSup s) ↔ ∀ ⦃b⦄, b ∈ s → Disjoint a b := by
  simp_rw [disjoint_iff, h.inf_Sup_eq, iSup_eq_bot]
#align directed_on.disjoint_Sup_right DirectedOn.disjoint_sSup_right

/- warning: directed_on.disjoint_Sup_left -> DirectedOn.disjoint_sSup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) s) -> (Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s) a) (forall {{b : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, (DirectedOn.{u1} α (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.7188 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.7190 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.7188 x._@.Mathlib.Order.CompactlyGenerated._hyg.7190) s) -> (Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s) a) (forall {{b : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b a)))
Case conversion may be inaccurate. Consider using '#align directed_on.disjoint_Sup_left DirectedOn.disjoint_sSup_leftₓ'. -/
protected theorem DirectedOn.disjoint_sSup_left (h : DirectedOn (· ≤ ·) s) :
    Disjoint (sSup s) a ↔ ∀ ⦃b⦄, b ∈ s → Disjoint b a := by
  simp_rw [disjoint_iff, h.Sup_inf_eq, iSup_eq_bot]
#align directed_on.disjoint_Sup_left DirectedOn.disjoint_sSup_left

/- warning: directed.disjoint_supr_right -> Directed.disjoint_iSup_right is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} [_inst_2 : IsCompactlyGenerated.{u2} α _inst_1] {a : α}, (Directed.{u2, u1} α ι (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) f) -> (Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toHasSup.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (forall (i : ι), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) a (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} {_inst_1 : ι -> α} [f : CompleteLattice.{u2} α] [_inst_2 : IsCompactlyGenerated.{u2} α f] {a : α}, (Directed.{u2, u1} α ι (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.7259 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.7261 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.7259 x._@.Mathlib.Order.CompactlyGenerated._hyg.7261) _inst_1) -> (Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) (CompleteLattice.toBoundedOrder.{u2} α f)) a (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f)) ι (fun (i : ι) => _inst_1 i))) (forall (i : ι), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) (CompleteLattice.toBoundedOrder.{u2} α f)) a (_inst_1 i)))
Case conversion may be inaccurate. Consider using '#align directed.disjoint_supr_right Directed.disjoint_iSup_rightₓ'. -/
protected theorem Directed.disjoint_iSup_right (h : Directed (· ≤ ·) f) :
    Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simp_rw [disjoint_iff, h.inf_supr_eq, iSup_eq_bot]
#align directed.disjoint_supr_right Directed.disjoint_iSup_right

/- warning: directed.disjoint_supr_left -> Directed.disjoint_iSup_left is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} [_inst_2 : IsCompactlyGenerated.{u2} α _inst_1] {a : α}, (Directed.{u2, u1} α ι (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) f) -> (Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toHasSup.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) a) (forall (i : ι), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u2} α _inst_1)) (f i) a))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u2}} {_inst_1 : ι -> α} [f : CompleteLattice.{u2} α] [_inst_2 : IsCompactlyGenerated.{u2} α f] {a : α}, (Directed.{u2, u1} α ι (fun (x._@.Mathlib.Order.CompactlyGenerated._hyg.7343 : α) (x._@.Mathlib.Order.CompactlyGenerated._hyg.7345 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) x._@.Mathlib.Order.CompactlyGenerated._hyg.7343 x._@.Mathlib.Order.CompactlyGenerated._hyg.7345) _inst_1) -> (Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) (CompleteLattice.toBoundedOrder.{u2} α f)) (iSup.{u2, u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α f)) ι (fun (i : ι) => _inst_1 i)) a) (forall (i : ι), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α f)))) (CompleteLattice.toBoundedOrder.{u2} α f)) (_inst_1 i) a))
Case conversion may be inaccurate. Consider using '#align directed.disjoint_supr_left Directed.disjoint_iSup_leftₓ'. -/
protected theorem Directed.disjoint_iSup_left (h : Directed (· ≤ ·) f) :
    Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp_rw [disjoint_iff, h.supr_inf_eq, iSup_eq_bot]
#align directed.disjoint_supr_left Directed.disjoint_iSup_left

/- warning: inf_Sup_eq_supr_inf_sup_finset -> inf_sSup_eq_iSup_inf_sup_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Finset.{u1} α) (fun (t : Finset.{u1} α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) a (Finset.sup.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) t (id.{succ u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsCompactlyGenerated.{u1} α _inst_1] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Finset.{u1} α) (fun (t : Finset.{u1} α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α t) s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α t) s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) a (Finset.sup.{u1, u1} α α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) t (id.{succ u1} α)))))
Case conversion may be inaccurate. Consider using '#align inf_Sup_eq_supr_inf_sup_finset inf_sSup_eq_iSup_inf_sup_finsetₓ'. -/
/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_sSup_eq_iSup_inf_sup_finset :
    a ⊓ sSup s = ⨆ (t : Finset α) (H : ↑t ⊆ s), a ⊓ t.sup id :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      exact (le_inf hcinf.1 ht2).trans (le_iSup₂ t ht1))
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))
#align inf_Sup_eq_supr_inf_sup_finset inf_sSup_eq_iSup_inf_sup_finset

#print CompleteLattice.setIndependent_iff_finite /-
theorem CompleteLattice.setIndependent_iff_finite {s : Set α} :
    CompleteLattice.SetIndependent s ↔
      ∀ t : Finset α, ↑t ⊆ s → CompleteLattice.SetIndependent (↑t : Set α) :=
  ⟨fun hs t ht => hs.mono ht, fun h a ha =>
    by
    rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot]
    intro t
    rw [iSup_eq_bot, Finset.sup_id_eq_sSup]
    intro ht
    classical
      have h' := (h (insert a t) _ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_diff_self_of_not_mem] at h'
        exact fun con => ((Set.mem_diff a).1 (ht Con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset]
        exact ⟨ha, Set.Subset.trans ht (Set.diff_subset _ _)⟩⟩
#align complete_lattice.set_independent_iff_finite CompleteLattice.setIndependent_iff_finite
-/

#print CompleteLattice.setIndependent_iUnion_of_directed /-
theorem CompleteLattice.setIndependent_iUnion_of_directed {η : Type _} {s : η → Set α}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, CompleteLattice.SetIndependent (s i)) :
    CompleteLattice.SetIndependent (⋃ i, s i) :=
  by
  by_cases hη : Nonempty η
  · skip
    rw [CompleteLattice.setIndependent_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_iUnion t.finite_to_set ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.to_finset
    exact
      (h i).mono
        (Set.Subset.trans hI <| Set.iUnion₂_subset fun j hj => hi j (fi.mem_to_finset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩
#align complete_lattice.set_independent_Union_of_directed CompleteLattice.setIndependent_iUnion_of_directed
-/

#print CompleteLattice.independent_sUnion_of_directed /-
theorem CompleteLattice.independent_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, CompleteLattice.SetIndependent a) : CompleteLattice.SetIndependent (⋃₀ s) := by
  rw [Set.sUnion_eq_iUnion] <;>
    exact CompleteLattice.setIndependent_iUnion_of_directed hs.directed_coe (by simpa using h)
#align complete_lattice.independent_sUnion_of_directed CompleteLattice.independent_sUnion_of_directed
-/

end

namespace CompleteLattice

#print CompleteLattice.isCompactlyGenerated_of_wellFounded /-
theorem isCompactlyGenerated_of_wellFounded (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsCompactlyGenerated α :=
  by
  rw [well_founded_iff_is_Sup_finite_compact, is_Sup_finite_compact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩
#align complete_lattice.compactly_generated_of_well_founded CompleteLattice.isCompactlyGenerated_of_wellFounded
-/

#print CompleteLattice.Iic_coatomic_of_compact_element /-
/-- A compact element `k` has the property that any `b < k` lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) : IsCoatomic (Set.Iic k) :=
  ⟨fun ⟨b, hbk⟩ => by
    by_cases htriv : b = k
    · left
      ext
      simp only [htriv, Set.Iic.coe_top, Subtype.coe_mk]
    right
    obtain ⟨a, a₀, ba, h⟩ := zorn_nonempty_partialOrder₀ (Set.Iio k) _ b (lt_of_le_of_ne hbk htriv)
    · refine' ⟨⟨a, le_of_lt a₀⟩, ⟨ne_of_lt a₀, fun c hck => by_contradiction fun c₀ => _⟩, ba⟩
      cases h c.1 (lt_of_le_of_ne c.2 fun con => c₀ (Subtype.ext Con)) hck.le
      exact lt_irrefl _ hck
    · intro S SC cC I IS
      by_cases hS : S.nonempty
      · exact ⟨Sup S, h.directed_Sup_lt_of_lt hS cC.directed_on SC, fun _ => le_sSup⟩
      exact
        ⟨b, lt_of_le_of_ne hbk htriv, by
          simp only [set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
            forall_prop_of_false, not_false_iff]⟩⟩
#align complete_lattice.Iic_coatomic_of_compact_element CompleteLattice.Iic_coatomic_of_compact_element
-/

/- warning: complete_lattice.coatomic_of_top_compact -> CompleteLattice.coatomic_of_top_compact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], (CompleteLattice.IsCompactElement.{u1} α _inst_1 (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (IsCoatomic.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], (CompleteLattice.IsCompactElement.{u1} α _inst_1 (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (IsCoatomic.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align complete_lattice.coatomic_of_top_compact CompleteLattice.coatomic_of_top_compactₓ'. -/
theorem coatomic_of_top_compact (h : IsCompactElement (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.IicTop α _ _).IsCoatomic_iff.mp (Iic_coatomic_of_compact_element h)
#align complete_lattice.coatomic_of_top_compact CompleteLattice.coatomic_of_top_compact

end CompleteLattice

section

variable [IsModularLattice α] [IsCompactlyGenerated α]

#print isAtomic_of_complementedLattice /-
instance (priority := 100) isAtomic_of_complementedLattice [ComplementedLattice α] : IsAtomic α :=
  ⟨fun b => by
    by_cases h : { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } ⊆ {⊥}
    · left
      rw [← sSup_compact_le_eq b, sSup_eq_bot]
      exact h
    · rcases Set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩
      right
      have hc' := CompleteLattice.Iic_coatomic_of_compact_element hc
      rw [← isAtomic_iff_isCoatomic] at hc'
      haveI := hc'
      obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : Set.Iic c)
      · exfalso
        apply hcbot
        simp only [Subtype.ext_iff, Set.Iic.coe_bot, Subtype.coe_mk] at con
        exact Con
      rw [← Subtype.coe_le_coe, Subtype.coe_mk] at hac
      exact ⟨a, ha.of_is_atom_coe_Iic, hac.trans hcb⟩⟩
#align is_atomic_of_complemented_lattice isAtomic_of_complementedLattice
-/

#print isAtomistic_of_complementedLattice /-
/-- See [Lemma 5.1][calugareanu]. -/
instance (priority := 100) isAtomistic_of_complementedLattice [ComplementedLattice α] :
    IsAtomistic α :=
  ⟨fun b =>
    ⟨{ a | IsAtom a ∧ a ≤ b }, by
      symm
      have hle : Sup { a : α | IsAtom a ∧ a ≤ b } ≤ b := sSup_le fun _ => And.right
      apply (lt_or_eq_of_le hle).resolve_left fun con => _
      obtain ⟨c, hc⟩ := exists_is_compl (⟨Sup { a : α | IsAtom a ∧ a ≤ b }, hle⟩ : Set.Iic b)
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      · exact ne_of_lt Con (Subtype.ext_iff.1 (eq_top_of_isCompl_bot hc))
      · apply ha.1
        rw [eq_bot_iff]
        apply le_trans (le_inf _ hac) hc.disjoint.le_bot
        rw [← Subtype.coe_le_coe, Subtype.coe_mk]
        exact le_sSup ⟨ha.of_is_atom_coe_Iic, a.2⟩, fun _ => And.left⟩⟩
#align is_atomistic_of_complemented_lattice isAtomistic_of_complementedLattice
-/

/-!
Now we will prove that a compactly generated modular atomistic lattice is a complemented lattice.
Most explicitly, every element is the complement of a supremum of indepedendent atoms.
-/


/- warning: exists_set_independent_is_compl_Sup_atoms -> exists_setIndependent_isCompl_sSup_atoms is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))] [_inst_3 : IsCompactlyGenerated.{u1} α _inst_1], (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (forall (b : α), Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (CompleteLattice.SetIndependent.{u1} α _inst_1 s) (And (IsCompl.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteLattice.toBoundedOrder.{u1} α _inst_1) b (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))] [_inst_3 : IsCompactlyGenerated.{u1} α _inst_1], (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (forall (b : α), Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (CompleteLattice.SetIndependent.{u1} α _inst_1 s) (And (IsCompl.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteLattice.toBoundedOrder.{u1} α _inst_1) b (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)) (forall {{a : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a)))))
Case conversion may be inaccurate. Consider using '#align exists_set_independent_is_compl_Sup_atoms exists_setIndependent_isCompl_sSup_atomsₓ'. -/
/-- In an atomic lattice, every element `b` has a complement of the form `Sup s`, where each element
of `s` is an atom. See also `complemented_lattice_of_Sup_atoms_eq_top`. -/
theorem exists_setIndependent_isCompl_sSup_atoms (h : sSup { a : α | IsAtom a } = ⊤) (b : α) :
    ∃ s : Set α, CompleteLattice.SetIndependent s ∧ IsCompl b (sSup s) ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  by
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ :=
    zorn_subset
      { s : Set α | CompleteLattice.SetIndependent s ∧ Disjoint b (Sup s) ∧ ∀ a ∈ s, IsAtom a }
      fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨CompleteLattice.independent_sUnion_of_directed hc2.DirectedOn fun s hs => (hc1 hs).1, _,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  swap
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directed_on.mono fun s t => sSup_le_sSup
  refine' ⟨s, s_ind, ⟨b_inf_Sup_s, _⟩, s_atoms⟩
  rw [codisjoint_iff_le_sup, ← h, sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine' (ha.le_iff.mp inf_le_left).resolve_left fun con => ha.1 _
  rw [← Con, eq_comm, inf_eq_left]
  refine' (le_sSup _).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (Sup s) := con.mono_right le_sup_right
  rw [← s_max (s ∪ {a}) ⟨fun x hx => _, ⟨_, fun x hx => _⟩⟩ (Set.subset_union_left _ _)]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_diff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup <| Set.diff_subset _ _).trans le_sup_right)
    · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} :=
        by
        simp only [Set.union_singleton]
        rw [Set.insert_diff_of_not_mem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h, sSup_union, sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left Con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha
#align exists_set_independent_is_compl_Sup_atoms exists_setIndependent_isCompl_sSup_atoms

/- warning: exists_set_independent_of_Sup_atoms_eq_top -> exists_setIndependent_of_sSup_atoms_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))] [_inst_3 : IsCompactlyGenerated.{u1} α _inst_1], (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (CompleteLattice.SetIndependent.{u1} α _inst_1 s) (And (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))] [_inst_3 : IsCompactlyGenerated.{u1} α _inst_1], (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (CompleteLattice.SetIndependent.{u1} α _inst_1 s) (And (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) (forall {{a : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a)))))
Case conversion may be inaccurate. Consider using '#align exists_set_independent_of_Sup_atoms_eq_top exists_setIndependent_of_sSup_atoms_eq_topₓ'. -/
theorem exists_setIndependent_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ∃ s : Set α, CompleteLattice.SetIndependent s ∧ sSup s = ⊤ ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  let ⟨s, s_ind, s_top, s_atoms⟩ := exists_setIndependent_isCompl_sSup_atoms h ⊥
  ⟨s, s_ind, eq_top_of_isCompl_bot s_top.symm, s_atoms⟩
#align exists_set_independent_of_Sup_atoms_eq_top exists_setIndependent_of_sSup_atoms_eq_top

/- warning: complemented_lattice_of_Sup_atoms_eq_top -> complementedLattice_of_sSup_atoms_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))] [_inst_3 : IsCompactlyGenerated.{u1} α _inst_1], (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (ComplementedLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (CompleteLattice.toBoundedOrder.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsModularLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))] [_inst_3 : IsCompactlyGenerated.{u1} α _inst_1], (Eq.{succ u1} α (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (setOf.{u1} α (fun (a : α) => IsAtom.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) a))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (ComplementedLattice.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (CompleteLattice.toBoundedOrder.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align complemented_lattice_of_Sup_atoms_eq_top complementedLattice_of_sSup_atoms_eq_topₓ'. -/
/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ComplementedLattice α :=
  ⟨fun b =>
    let ⟨s, _, s_top, s_atoms⟩ := exists_setIndependent_isCompl_sSup_atoms h b
    ⟨sSup s, s_top⟩⟩
#align complemented_lattice_of_Sup_atoms_eq_top complementedLattice_of_sSup_atoms_eq_top

#print complementedLattice_of_isAtomistic /-
/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_isAtomistic [IsAtomistic α] : ComplementedLattice α :=
  complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top
#align complemented_lattice_of_is_atomistic complementedLattice_of_isAtomistic
-/

#print complementedLattice_iff_isAtomistic /-
theorem complementedLattice_iff_isAtomistic : ComplementedLattice α ↔ IsAtomistic α :=
  by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic
#align complemented_lattice_iff_is_atomistic complementedLattice_iff_isAtomistic
-/

end

