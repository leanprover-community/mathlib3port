/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.order
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Order.Field
import Mathbin.Topology.Algebra.Order.MonotoneConvergence

/-!
# Infinite sum in an order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides lemmas about the interaction of infinite sums and order operations.
-/


open Finset Filter Function

open BigOperators Classical

variable {ι κ α : Type _}

section Preorder

variable [Preorder α] [AddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] [T2Space α]
  {f : ℕ → α} {c : α}

/- warning: tsum_le_of_sum_range_le -> tsum_le_of_sum_range_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderClosedTopology.{u1} α _inst_3 _inst_1] [_inst_5 : T2Space.{u1} α _inst_3] {f : Nat -> α} {c : α}, (Summable.{u1, 0} α Nat _inst_2 _inst_3 f) -> (forall (n : Nat), LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (Finset.sum.{u1, 0} α Nat _inst_2 (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (tsum.{u1, 0} α _inst_2 _inst_3 Nat (fun (n : Nat) => f n)) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OrderClosedTopology.{u1} α _inst_3 _inst_1] [_inst_5 : T2Space.{u1} α _inst_3] {f : Nat -> α} {c : α}, (Summable.{u1, 0} α Nat _inst_2 _inst_3 f) -> (forall (n : Nat), LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (Finset.sum.{u1, 0} α Nat _inst_2 (Finset.range n) (fun (i : Nat) => f i)) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (tsum.{u1, 0} α _inst_2 _inst_3 Nat (fun (n : Nat) => f n)) c)
Case conversion may be inaccurate. Consider using '#align tsum_le_of_sum_range_le tsum_le_of_sum_range_leₓ'. -/
theorem tsum_le_of_sum_range_le (hf : Summable f) (h : ∀ n, (∑ i in range n, f i) ≤ c) :
    (∑' n, f n) ≤ c :=
  let ⟨l, hl⟩ := hf
  hl.tsum_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h
#align tsum_le_of_sum_range_le tsum_le_of_sum_range_le

end Preorder

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α}
  {a a₁ a₂ : α}

/- warning: has_sum_le -> hasSum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (g i)) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a₂) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (g i)) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a₂) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align has_sum_le hasSum_leₓ'. -/
theorem hasSum_le (h : ∀ i, f i ≤ g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun s => sum_le_sum fun i _ => h i
#align has_sum_le hasSum_le

/- warning: has_sum_mono -> hasSum_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a₂) -> (LE.le.{max u1 u2} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1)))) f g) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a₂) -> (LE.le.{max u1 u2} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1)))) f g) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align has_sum_mono hasSum_monoₓ'. -/
@[mono]
theorem hasSum_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
  hasSum_le h hf hg
#align has_sum_mono hasSum_mono

/- warning: has_sum_le_of_sum_le -> hasSum_le_of_sum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a₂) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a a₂)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a₂) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a a₂)
Case conversion may be inaccurate. Consider using '#align has_sum_le_of_sum_le hasSum_le_of_sum_leₓ'. -/
theorem hasSum_le_of_sum_le (hf : HasSum f a) (h : ∀ s, (∑ i in s, f i) ≤ a₂) : a ≤ a₂ :=
  le_of_tendsto' hf h
#align has_sum_le_of_sum_le hasSum_le_of_sum_le

/- warning: le_has_sum_of_le_sum -> le_hasSum_of_le_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₂ (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₂ a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₂ (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a₂ a)
Case conversion may be inaccurate. Consider using '#align le_has_sum_of_le_sum le_hasSum_of_le_sumₓ'. -/
theorem le_hasSum_of_le_sum (hf : HasSum f a) (h : ∀ s, a₂ ≤ ∑ i in s, f i) : a₂ ≤ a :=
  ge_of_tendsto' hf h
#align le_has_sum_of_le_sum le_hasSum_of_le_sum

/- warning: has_sum_le_inj -> hasSum_le_inj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} [_inst_1 : OrderedAddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : OrderClosedTopology.{u3} α _inst_2 (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))] {f : ι -> α} {a₁ : α} {a₂ : α} {g : κ -> α} (e : ι -> κ), (Function.Injective.{succ u1, succ u2} ι κ e) -> (forall (c : κ), (Not (Membership.Mem.{u2, u2} κ (Set.{u2} κ) (Set.hasMem.{u2} κ) c (Set.range.{u2, succ u1} κ ι e))) -> (LE.le.{u3} α (Preorder.toHasLe.{u3} α (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))) (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (AddZeroClass.toHasZero.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1))))))) (g c))) -> (forall (i : ι), LE.le.{u3} α (Preorder.toHasLe.{u3} α (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))) (f i) (g (e i))) -> (HasSum.{u3, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1) _inst_2 f a₁) -> (HasSum.{u3, u2} α κ (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1) _inst_2 g a₂) -> (LE.le.{u3} α (Preorder.toHasLe.{u3} α (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))) a₁ a₂)
but is expected to have type
  forall {ι : Type.{u3}} {κ : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))] {f : ι -> α} {a₁ : α} {a₂ : α} {g : κ -> α} (e : ι -> κ), (Function.Injective.{succ u3, succ u2} ι κ e) -> (forall (c : κ), (Not (Membership.mem.{u2, u2} κ (Set.{u2} κ) (Set.instMembershipSet.{u2} κ) c (Set.range.{u2, succ u3} κ ι e))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) (g c))) -> (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (f i) (g (e i))) -> (HasSum.{u1, u3} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a₁) -> (HasSum.{u1, u2} α κ (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 g a₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align has_sum_le_inj hasSum_le_injₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∉ » set.range[set.range] e) -/
theorem hasSum_le_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ (c) (_ : c ∉ Set.range e), 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : HasSum f a₁)
    (hg : HasSum g a₂) : a₁ ≤ a₂ :=
  by
  have : HasSum (fun c => (partialInv e c).casesOn' 0 f) a₁ :=
    by
    refine'
      (hasSum_iff_hasSum_of_ne_zero_bij (e ∘ coe) (fun c₁ c₂ hc => he hc) (fun c hc => _) _).2 hf
    · rw [mem_support] at hc
      cases' eq : partial_inv e c with i <;> rw [Eq] at hc
      · contradiction
      · rw [partial_inv_of_injective he] at eq
        exact ⟨⟨i, hc⟩, Eq⟩
    · rintro c
      simp [partial_inv_left he, Option.casesOn']
  refine' hasSum_le (fun c => _) this hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [partial_inv_left he, Option.casesOn']
    exact h _
  · have : partial_inv e c = none := dif_neg h
    rw [this, Option.casesOn']
    exact hs _ h
#align has_sum_le_inj hasSum_le_inj

/- warning: tsum_le_tsum_of_inj -> tsum_le_tsum_of_inj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} [_inst_1 : OrderedAddCommMonoid.{u3} α] [_inst_2 : TopologicalSpace.{u3} α] [_inst_3 : OrderClosedTopology.{u3} α _inst_2 (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))] {f : ι -> α} {g : κ -> α} (e : ι -> κ), (Function.Injective.{succ u1, succ u2} ι κ e) -> (forall (c : κ), (Not (Membership.Mem.{u2, u2} κ (Set.{u2} κ) (Set.hasMem.{u2} κ) c (Set.range.{u2, succ u1} κ ι e))) -> (LE.le.{u3} α (Preorder.toHasLe.{u3} α (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))) (OfNat.ofNat.{u3} α 0 (OfNat.mk.{u3} α 0 (Zero.zero.{u3} α (AddZeroClass.toHasZero.{u3} α (AddMonoid.toAddZeroClass.{u3} α (AddCommMonoid.toAddMonoid.{u3} α (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1))))))) (g c))) -> (forall (i : ι), LE.le.{u3} α (Preorder.toHasLe.{u3} α (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))) (f i) (g (e i))) -> (Summable.{u3, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1) _inst_2 f) -> (Summable.{u3, u2} α κ (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1) _inst_2 g) -> (LE.le.{u3} α (Preorder.toHasLe.{u3} α (PartialOrder.toPreorder.{u3} α (OrderedAddCommMonoid.toPartialOrder.{u3} α _inst_1))) (tsum.{u3, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1) _inst_2 ι f) (tsum.{u3, u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u3} α _inst_1) _inst_2 κ g))
but is expected to have type
  forall {ι : Type.{u3}} {κ : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))] {f : ι -> α} {g : κ -> α} (e : ι -> κ), (Function.Injective.{succ u3, succ u2} ι κ e) -> (forall (c : κ), (Not (Membership.mem.{u2, u2} κ (Set.{u2} κ) (Set.instMembershipSet.{u2} κ) c (Set.range.{u2, succ u3} κ ι e))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) (g c))) -> (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (f i) (g (e i))) -> (Summable.{u1, u3} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (Summable.{u1, u2} α κ (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 g) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (tsum.{u1, u3} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 ι f) (tsum.{u1, u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 κ g))
Case conversion may be inaccurate. Consider using '#align tsum_le_tsum_of_inj tsum_le_tsum_of_injₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (c «expr ∉ » set.range[set.range] e) -/
theorem tsum_le_tsum_of_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ (c) (_ : c ∉ Set.range e), 0 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : Summable f)
    (hg : Summable g) : tsum f ≤ tsum g :=
  hasSum_le_inj _ he hs h hf.HasSum hg.HasSum
#align tsum_le_tsum_of_inj tsum_le_tsum_of_inj

/- warning: sum_le_has_sum -> sum_le_hasSum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α} (s : Finset.{u1} ι), (forall (i : ι), (Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s)) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (f i))) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))] {f : ι -> α} {a : α} (s : Finset.{u2} ι), (forall (i : ι), (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) (f i))) -> (HasSum.{u1, u2} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 f a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (Finset.sum.{u1, u2} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) s (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align sum_le_has_sum sum_le_hasSumₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem sum_le_hasSum (s : Finset ι) (hs : ∀ (i) (_ : i ∉ s), 0 ≤ f i) (hf : HasSum f a) :
    (∑ i in s, f i) ≤ a :=
  ge_of_tendsto hf
    (eventually_atTop.2
      ⟨s, fun t hst => sum_le_sum_of_subset_of_nonneg hst fun i hbt hbs => hs i hbs⟩)
#align sum_le_has_sum sum_le_hasSum

/- warning: is_lub_has_sum -> isLUB_hasSum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (f i)) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1)) (Set.range.{u2, succ u1} α (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (f i)) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1)) (Set.range.{u2, succ u1} α (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) a)
Case conversion may be inaccurate. Consider using '#align is_lub_has_sum isLUB_hasSumₓ'. -/
theorem isLUB_hasSum (h : ∀ i, 0 ≤ f i) (hf : HasSum f a) :
    IsLUB (Set.range fun s => ∑ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.sum_mono_set_of_nonneg h) hf
#align is_lub_has_sum isLUB_hasSum

/- warning: le_has_sum -> le_hasSum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (forall (i : ι), (forall (b' : ι), (Ne.{succ u1} ι b' i) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (f b'))) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) a))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a) -> (forall (i : ι), (forall (b' : ι), (Ne.{succ u1} ι b' i) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (f b'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) a))
Case conversion may be inaccurate. Consider using '#align le_has_sum le_hasSumₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » i) -/
theorem le_hasSum (hf : HasSum f a) (i : ι) (hb : ∀ (b') (_ : b' ≠ i), 0 ≤ f b') : f i ≤ a :=
  calc
    f i = ∑ i in {i}, f i := Finset.sum_singleton.symm
    _ ≤ a :=
      sum_le_hasSum _
        (by
          convert hb
          simp)
        hf
    
#align le_has_sum le_hasSum

/- warning: sum_le_tsum -> sum_le_tsum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} (s : Finset.{u1} ι), (forall (i : ι), (Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s)) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (f i))) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedAddCommMonoid.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderClosedTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))] {f : ι -> α} (s : Finset.{u2} ι), (forall (i : ι), (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1))))) (f i))) -> (Summable.{u1, u2} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 f) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α _inst_1))) (Finset.sum.{u1, u2} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) s (fun (i : ι) => f i)) (tsum.{u1, u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α _inst_1) _inst_2 ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align sum_le_tsum sum_le_tsumₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem sum_le_tsum {f : ι → α} (s : Finset ι) (hs : ∀ (i) (_ : i ∉ s), 0 ≤ f i) (hf : Summable f) :
    (∑ i in s, f i) ≤ ∑' i, f i :=
  sum_le_hasSum s hs hf.HasSum
#align sum_le_tsum sum_le_tsum

/- warning: le_tsum -> le_tsum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (forall (i : ι), (forall (b' : ι), (Ne.{succ u1} ι b' i) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (f b'))) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (forall (i : ι), (forall (b' : ι), (Ne.{succ u1} ι b' i) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (f b'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align le_tsum le_tsumₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (b' «expr ≠ » i) -/
theorem le_tsum (hf : Summable f) (i : ι) (hb : ∀ (b') (_ : b' ≠ i), 0 ≤ f b') : f i ≤ ∑' i, f i :=
  le_hasSum (Summable.hasSum hf) i hb
#align le_tsum le_tsum

/- warning: tsum_le_tsum -> tsum_le_tsum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (g i)) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (g i)) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align tsum_le_tsum tsum_le_tsumₓ'. -/
theorem tsum_le_tsum (h : ∀ i, f i ≤ g i) (hf : Summable f) (hg : Summable g) :
    (∑' i, f i) ≤ ∑' i, g i :=
  hasSum_le h hf.HasSum hg.HasSum
#align tsum_le_tsum tsum_le_tsum

/- warning: tsum_mono -> tsum_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (LE.le.{max u1 u2} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1)))) f g) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (n : ι) => f n)) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (n : ι) => g n)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g) -> (LE.le.{max u1 u2} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1)))) f g) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (n : ι) => f n)) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (n : ι) => g n)))
Case conversion may be inaccurate. Consider using '#align tsum_mono tsum_monoₓ'. -/
@[mono]
theorem tsum_mono (hf : Summable f) (hg : Summable g) (h : f ≤ g) : (∑' n, f n) ≤ ∑' n, g n :=
  tsum_le_tsum h hf hg
#align tsum_mono tsum_mono

/- warning: tsum_le_of_sum_le -> tsum_le_of_sum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a₂ : α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a₂) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a₂)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a₂ : α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a₂) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a₂)
Case conversion may be inaccurate. Consider using '#align tsum_le_of_sum_le tsum_le_of_sum_leₓ'. -/
theorem tsum_le_of_sum_le (hf : Summable f) (h : ∀ s, (∑ i in s, f i) ≤ a₂) : (∑' i, f i) ≤ a₂ :=
  hasSum_le_of_sum_le hf.HasSum h
#align tsum_le_of_sum_le tsum_le_of_sum_le

/- warning: tsum_le_of_sum_le' -> tsum_le_of_sum_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a₂ : α}, (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) a₂) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a₂) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a₂)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {a₂ : α}, (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) a₂) -> (forall (s : Finset.{u1} ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i)) a₂) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a₂)
Case conversion may be inaccurate. Consider using '#align tsum_le_of_sum_le' tsum_le_of_sum_le'ₓ'. -/
theorem tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s, (∑ i in s, f i) ≤ a₂) : (∑' i, f i) ≤ a₂ :=
  by
  by_cases hf : Summable f
  · exact tsum_le_of_sum_le hf h
  · rw [tsum_eq_zero_of_not_summable hf]
    exact ha₂
#align tsum_le_of_sum_le' tsum_le_of_sum_le'

/- warning: has_sum.nonneg -> HasSum.nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {g : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (g i)) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {g : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (g i)) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) a)
Case conversion may be inaccurate. Consider using '#align has_sum.nonneg HasSum.nonnegₓ'. -/
theorem HasSum.nonneg (h : ∀ i, 0 ≤ g i) (ha : HasSum g a) : 0 ≤ a :=
  hasSum_le h hasSum_zero ha
#align has_sum.nonneg HasSum.nonneg

/- warning: has_sum.nonpos -> HasSum.nonpos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {g : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (g i) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1)))))))) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {g : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (g i) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1)))))) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 g a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align has_sum.nonpos HasSum.nonposₓ'. -/
theorem HasSum.nonpos (h : ∀ i, g i ≤ 0) (ha : HasSum g a) : a ≤ 0 :=
  hasSum_le h ha hasSum_zero
#align has_sum.nonpos HasSum.nonpos

/- warning: tsum_nonneg -> tsum_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (g i)) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (g i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align tsum_nonneg tsum_nonnegₓ'. -/
theorem tsum_nonneg (h : ∀ i, 0 ≤ g i) : 0 ≤ ∑' i, g i :=
  by
  by_cases hg : Summable g
  · exact hg.has_sum.nonneg h
  · simp [tsum_eq_zero_of_not_summable hg]
#align tsum_nonneg tsum_nonneg

/- warning: tsum_nonpos -> tsum_nonpos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1)))))))) -> (LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {f : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1)))))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align tsum_nonpos tsum_nonposₓ'. -/
theorem tsum_nonpos (h : ∀ i, f i ≤ 0) : (∑' i, f i) ≤ 0 :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.nonpos h
  · simp [tsum_eq_zero_of_not_summable hf]
#align tsum_nonpos tsum_nonpos

end OrderedAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
  [OrderClosedTopology α] {f g : ι → α} {a₁ a₂ : α} {i : ι}

/- warning: has_sum_lt -> hasSum_lt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α} {i : ι}, (LE.le.{max u1 u2} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1)))) f g) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (f i) (g i)) -> (HasSum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 g a₂) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedAddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α _inst_1))] [_inst_4 : OrderClosedTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α} {i : ι}, (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1)))) f g) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1))) (f i) (g i)) -> (HasSum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} α _inst_1)) _inst_2 f a₁) -> (HasSum.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} α _inst_1)) _inst_2 g a₂) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1))) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align has_sum_lt hasSum_ltₓ'. -/
theorem hasSum_lt (h : f ≤ g) (hi : f i < g i) (hf : HasSum f a₁) (hg : HasSum g a₂) : a₁ < a₂ :=
  by
  have : update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 0 - f i + a₁ ≤ 0 - g i + a₂ := hasSum_le this (hf.update i 0) (hg.update i 0)
  simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this
#align has_sum_lt hasSum_lt

/- warning: has_sum_strict_mono -> hasSum_strict_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α}, (HasSum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 g a₂) -> (LT.lt.{max u1 u2} (ι -> α) (Preorder.toHasLt.{max u1 u2} (ι -> α) (Pi.preorder.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1)))) f g) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {a₁ : α} {a₂ : α}, (HasSum.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 g a₂) -> (LT.lt.{max u1 u2} (ι -> α) (Preorder.toLT.{max u1 u2} (ι -> α) (Pi.preorder.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1)))) f g) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) a₁ a₂)
Case conversion may be inaccurate. Consider using '#align has_sum_strict_mono hasSum_strict_monoₓ'. -/
@[mono]
theorem hasSum_strict_mono (hf : HasSum f a₁) (hg : HasSum g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg
#align has_sum_strict_mono hasSum_strict_mono

/- warning: tsum_lt_tsum -> tsum_lt_tsum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α} {i : ι}, (LE.le.{max u1 u2} (ι -> α) (Pi.hasLe.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1)))) f g) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (f i) (g i)) -> (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 f) -> (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 g) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 ι (fun (n : ι) => f n)) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 ι (fun (n : ι) => g n)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedAddCommGroup.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : TopologicalAddGroup.{u1} α _inst_2 (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α _inst_1))] [_inst_4 : OrderClosedTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1))] {f : ι -> α} {g : ι -> α} {i : ι}, (LE.le.{max u2 u1} (ι -> α) (Pi.hasLe.{u2, u1} ι (fun (ᾰ : ι) => α) (fun (i : ι) => Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1)))) f g) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1))) (f i) (g i)) -> (Summable.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} α _inst_1)) _inst_2 f) -> (Summable.{u1, u2} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} α _inst_1)) _inst_2 g) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α _inst_1))) (tsum.{u1, u2} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} α _inst_1)) _inst_2 ι (fun (n : ι) => f n)) (tsum.{u1, u2} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} α _inst_1)) _inst_2 ι (fun (n : ι) => g n)))
Case conversion may be inaccurate. Consider using '#align tsum_lt_tsum tsum_lt_tsumₓ'. -/
theorem tsum_lt_tsum (h : f ≤ g) (hi : f i < g i) (hf : Summable f) (hg : Summable g) :
    (∑' n, f n) < ∑' n, g n :=
  hasSum_lt h hi hf.HasSum hg.HasSum
#align tsum_lt_tsum tsum_lt_tsum

/- warning: tsum_strict_mono -> tsum_strict_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α}, (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 f) -> (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 g) -> (LT.lt.{max u1 u2} (ι -> α) (Preorder.toHasLt.{max u1 u2} (ι -> α) (Pi.preorder.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1)))) f g) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 ι (fun (n : ι) => f n)) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 ι (fun (n : ι) => g n)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α} {g : ι -> α}, (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 g) -> (LT.lt.{max u1 u2} (ι -> α) (Preorder.toLT.{max u1 u2} (ι -> α) (Pi.preorder.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1)))) f g) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (tsum.{u2, u1} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (n : ι) => f n)) (tsum.{u2, u1} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (n : ι) => g n)))
Case conversion may be inaccurate. Consider using '#align tsum_strict_mono tsum_strict_monoₓ'. -/
@[mono]
theorem tsum_strict_mono (hf : Summable f) (hg : Summable g) (h : f < g) :
    (∑' n, f n) < ∑' n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hf hg
#align tsum_strict_mono tsum_strict_mono

/- warning: tsum_pos -> tsum_pos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {g : ι -> α}, (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 g) -> (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))))))))) (g i)) -> (forall (i : ι), (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))))))))) (g i)) -> (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))))))))) (tsum.{u2, u1} α (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => g i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {g : ι -> α}, (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 g) -> (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)))))))) (g i)) -> (forall (i : ι), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)))))))) (g i)) -> (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)))))))) (tsum.{u2, u1} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align tsum_pos tsum_posₓ'. -/
theorem tsum_pos (hsum : Summable g) (hg : ∀ i, 0 ≤ g i) (i : ι) (hi : 0 < g i) : 0 < ∑' i, g i :=
  by
  rw [← tsum_zero]
  exact tsum_lt_tsum hg hi summable_zero hsum
#align tsum_pos tsum_pos

/- warning: has_sum_zero_iff_of_nonneg -> hasSum_zero_iff_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))] {f : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))))))))) (f i)) -> (Iff (HasSum.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)) _inst_2 f (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1)))))))))) (Eq.{max (succ u1) (succ u2)} (ι -> α) f (OfNat.ofNat.{max u1 u2} (ι -> α) 0 (OfNat.mk.{max u1 u2} (ι -> α) 0 (Zero.zero.{max u1 u2} (ι -> α) (Pi.instZero.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α _inst_1))))))))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))] {_inst_4 : ι -> α}, (forall (ᾰ : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α _inst_1))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (_inst_4 ᾰ)) -> (Iff (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 _inst_4 (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1)))))) (Eq.{max (succ u1) (succ u2)} (ι -> α) _inst_4 (OfNat.ofNat.{max u1 u2} (ι -> α) 0 (Zero.toOfNat0.{max u1 u2} (ι -> α) (Pi.instZero.{u1, u2} ι (fun (a._@.Mathlib.Topology.Algebra.InfiniteSum.Order._hyg.1730 : ι) => α) (fun (i : ι) => AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align has_sum_zero_iff_of_nonneg hasSum_zero_iff_of_nonnegₓ'. -/
theorem hasSum_zero_iff_of_nonneg (hf : ∀ i, 0 ≤ f i) : HasSum f 0 ↔ f = 0 :=
  by
  refine' ⟨fun hf' => _, _⟩
  · ext i
    refine' (hf i).eq_of_not_gt fun hi => _
    simpa using hasSum_lt hf hi hasSum_zero hf'
  · rintro rfl
    exact hasSum_zero
#align has_sum_zero_iff_of_nonneg hasSum_zero_iff_of_nonneg

end OrderedAddCommGroup

section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddMonoid α] [TopologicalSpace α] [OrderClosedTopology α] {f : ι → α}
  {a : α}

/- warning: le_has_sum' -> le_hasSum' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f a) -> (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (f i) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f a) -> (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (f i) a)
Case conversion may be inaccurate. Consider using '#align le_has_sum' le_hasSum'ₓ'. -/
theorem le_hasSum' (hf : HasSum f a) (i : ι) : f i ≤ a :=
  le_hasSum hf i fun _ _ => zero_le _
#align le_has_sum' le_hasSum'

/- warning: le_tsum' -> le_tsum' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (f i) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (f i) (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align le_tsum' le_tsum'ₓ'. -/
theorem le_tsum' (hf : Summable f) (i : ι) : f i ≤ ∑' i, f i :=
  le_tsum hf i fun _ _ => zero_le _
#align le_tsum' le_tsum'

/- warning: has_sum_zero_iff -> hasSum_zero_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, Iff (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))))) (forall (x : ι), Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, Iff (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))) (forall (x : ι), Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align has_sum_zero_iff hasSum_zero_iffₓ'. -/
theorem hasSum_zero_iff : HasSum f 0 ↔ ∀ x, f x = 0 :=
  by
  refine' ⟨_, fun h => _⟩
  · contrapose!
    exact fun ⟨x, hx⟩ h => hx (nonpos_iff_eq_zero.1 <| le_hasSum' h x)
  · convert hasSum_zero
    exact funext h
#align has_sum_zero_iff hasSum_zero_iff

/- warning: tsum_eq_zero_iff -> tsum_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (Iff (Eq.{succ u2} α (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => f i)) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))))) (forall (x : ι), Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (Iff (Eq.{succ u2} α (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => f i)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))) (forall (x : ι), Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align tsum_eq_zero_iff tsum_eq_zero_iffₓ'. -/
theorem tsum_eq_zero_iff (hf : Summable f) : (∑' i, f i) = 0 ↔ ∀ x, f x = 0 := by
  rw [← hasSum_zero_iff, hf.has_sum_iff]
#align tsum_eq_zero_iff tsum_eq_zero_iff

/- warning: tsum_ne_zero_iff -> tsum_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (Iff (Ne.{succ u2} α (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => f i)) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))))) (Exists.{succ u1} ι (fun (x : ι) => Ne.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f) -> (Iff (Ne.{succ u2} α (tsum.{u2, u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 ι (fun (i : ι) => f i)) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))))) (Exists.{succ u1} ι (fun (x : ι) => Ne.{succ u2} α (f x) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align tsum_ne_zero_iff tsum_ne_zero_iffₓ'. -/
theorem tsum_ne_zero_iff (hf : Summable f) : (∑' i, f i) ≠ 0 ↔ ∃ x, f x ≠ 0 := by
  rw [Ne.def, tsum_eq_zero_iff hf, not_forall]
#align tsum_ne_zero_iff tsum_ne_zero_iff

#print isLUB_hasSum' /-
theorem isLUB_hasSum' (hf : HasSum f a) : IsLUB (Set.range fun s => ∑ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.sum_mono_set f) hf
#align is_lub_has_sum' isLUB_hasSum'
-/

end CanonicallyOrderedAddMonoid

section LinearOrder

/-!
For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/


/- warning: has_sum_of_is_lub_of_nonneg -> hasSum_of_isLUB_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α} (i : α), (forall (i : ι), LE.le.{u2} α (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))))) (f i)) -> (IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))) (Set.range.{u2, succ u1} α (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) s (fun (i : ι) => f i))) i) -> (HasSum.{u2, u1} α ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) _inst_2 f i)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommMonoid.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OrderTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] {f : ι -> α} (i : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (LinearOrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1))))) (f i)) -> (IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))) (Set.range.{u2, succ u1} α (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => Finset.sum.{u2, u1} α ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) i) -> (HasSum.{u2, u1} α ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u2} α _inst_1) _inst_2 f i)
Case conversion may be inaccurate. Consider using '#align has_sum_of_is_lub_of_nonneg hasSum_of_isLUB_of_nonnegₓ'. -/
theorem hasSum_of_isLUB_of_nonneg [LinearOrderedAddCommMonoid α] [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h : ∀ i, 0 ≤ f i)
    (hf : IsLUB (Set.range fun s => ∑ i in s, f i) i) : HasSum f i :=
  tendsto_atTop_isLUB (Finset.sum_mono_set_of_nonneg h) hf
#align has_sum_of_is_lub_of_nonneg hasSum_of_isLUB_of_nonneg

#print hasSum_of_isLUB /-
theorem hasSum_of_isLUB [CanonicallyLinearOrderedAddMonoid α] [TopologicalSpace α] [OrderTopology α]
    {f : ι → α} (b : α) (hf : IsLUB (Set.range fun s => ∑ i in s, f i) b) : HasSum f b :=
  tendsto_atTop_isLUB (Finset.sum_mono_set f) hf
#align has_sum_of_is_lub hasSum_of_isLUB
-/

/- warning: summable_abs_iff -> summable_abs_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : CompleteSpace.{u2} α _inst_2] {f : ι -> α}, Iff (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (fun (x : ι) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (SubNegMonoid.toHasNeg.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))) (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (LinearOrder.toLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1))))) (f x))) (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : CompleteSpace.{u2} α _inst_2] {f : ι -> α}, Iff (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (fun (x : ι) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1)))))) (f x))) (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f)
Case conversion may be inaccurate. Consider using '#align summable_abs_iff summable_abs_iffₓ'. -/
theorem summable_abs_iff [LinearOrderedAddCommGroup α] [UniformSpace α] [UniformAddGroup α]
    [CompleteSpace α] {f : ι → α} : (Summable fun x => |f x|) ↔ Summable f :=
  have h1 : ∀ x : { x | 0 ≤ f x }, |f x| = f x := fun x => abs_of_nonneg x.2
  have h2 : ∀ x : { x | 0 ≤ f x }ᶜ, |f x| = -f x := fun x => abs_of_neg (not_le.1 x.2)
  calc
    (Summable fun x => |f x|) ↔
        (Summable fun x : { x | 0 ≤ f x } => |f x|) ∧ Summable fun x : { x | 0 ≤ f x }ᶜ => |f x| :=
      summable_subtype_and_compl.symm
    _ ↔ (Summable fun x : { x | 0 ≤ f x } => f x) ∧ Summable fun x : { x | 0 ≤ f x }ᶜ => -f x := by
      simp only [h1, h2]
    _ ↔ _ := by simp only [summable_neg_iff, summable_subtype_and_compl]
    
#align summable_abs_iff summable_abs_iff

/- warning: summable.of_abs -> Summable.of_abs is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : CompleteSpace.{u2} α _inst_2] {f : ι -> α}, (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (fun (x : ι) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (SubNegMonoid.toHasNeg.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))) (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (LinearOrder.toLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1))))) (f x))) -> (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : CompleteSpace.{u2} α _inst_2] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (fun (x : ι) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1)))))) (f x))) -> (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f)
Case conversion may be inaccurate. Consider using '#align summable.of_abs Summable.of_absₓ'. -/
/- warning: summable.abs -> Summable.abs is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : CompleteSpace.{u2} α _inst_2] {f : ι -> α}, (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (fun (x : ι) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (SubNegMonoid.toHasNeg.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))) (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (LinearOrder.toLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1))))) (f x)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : UniformSpace.{u2} α] [_inst_3 : UniformAddGroup.{u2} α _inst_2 (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : CompleteSpace.{u2} α _inst_2] {f : ι -> α}, (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) f) -> (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) (UniformSpace.toTopologicalSpace.{u2} α _inst_2) (fun (x : ι) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1)))))) (f x)))
Case conversion may be inaccurate. Consider using '#align summable.abs Summable.absₓ'. -/
alias summable_abs_iff ↔ Summable.of_abs Summable.abs
#align summable.of_abs Summable.of_abs
#align summable.abs Summable.abs

/- warning: finite_of_summable_const -> Set.Finite.of_summable_const is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : Archimedean.{u2} α (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} α (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] {b : α}, (LT.lt.{u2} α (Preorder.toHasLt.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α (AddCommGroup.toAddGroup.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))))))))) b) -> (Summable.{u2, u1} α ι (AddCommGroup.toAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))) _inst_2 (fun (i : ι) => b)) -> (Set.Finite.{u1} ι (Set.univ.{u1} ι))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : Archimedean.{u2} α (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1)))] [_inst_4 : OrderClosedTopology.{u2} α _inst_2 (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))] {b : α}, (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))) (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))))))) b) -> (Summable.{u2, u1} α ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} α _inst_1))) _inst_2 (fun (i : ι) => b)) -> (Set.Finite.{u1} ι (Set.univ.{u1} ι))
Case conversion may be inaccurate. Consider using '#align finite_of_summable_const Set.Finite.of_summable_constₓ'. -/
--TODO: Change the conclusion to `finite ι`
theorem Set.Finite.of_summable_const [LinearOrderedAddCommGroup α] [TopologicalSpace α]
    [Archimedean α] [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun i : ι => b) :
    (Set.univ : Set ι).Finite :=
  by
  have H : ∀ s : Finset ι, s.card • b ≤ ∑' i : ι, b :=
    by
    intro s
    simpa using sum_le_hasSum s (fun a ha => hb.le) hf.has_sum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' i : ι, b) hb
  have : ∀ s : Finset ι, s.card ≤ n := by
    intro s
    simpa [nsmul_le_nsmul_iff hb] using (H s).trans hn
  haveI : Fintype ι := fintypeOfFinsetCardLe n this
  exact Set.finite_univ
#align finite_of_summable_const Set.Finite.of_summable_const

end LinearOrder

/- warning: summable.tendsto_top_of_pos -> Summable.tendsto_atTop_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))] {f : Nat -> α}, (Summable.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) _inst_2 (Inv.inv.{u1} (Nat -> α) (Pi.instInv.{0, u1} Nat (fun (ᾰ : Nat) => α) (fun (i : Nat) => DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))) f)) -> (forall (n : Nat), LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (DivisionRing.toRing.{u1} α (Field.toDivisionRing.{u1} α (LinearOrderedField.toField.{u1} α _inst_1))))))))))) (f n)) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (StrictOrderedRing.toOrderedAddCommGroup.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OrderTopology.{u1} α _inst_2 (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))] {f : Nat -> α}, (Summable.{u1, 0} α Nat (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1)))))) _inst_2 (Inv.inv.{u1} (Nat -> α) (Pi.instInv.{0, u1} Nat (fun (ᾰ : Nat) => α) (fun (i : Nat) => LinearOrderedField.toInv.{u1} α _inst_1)) f)) -> (forall (n : Nat), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (LinearOrderedField.toLinearOrderedSemifield.{u1} α _inst_1))))))) (f n)) -> (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedRing.toPartialOrder.{u1} α (LinearOrderedRing.toStrictOrderedRing.{u1} α (LinearOrderedCommRing.toLinearOrderedRing.{u1} α (LinearOrderedField.toLinearOrderedCommRing.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align summable.tendsto_top_of_pos Summable.tendsto_atTop_of_posₓ'. -/
theorem Summable.tendsto_atTop_of_pos [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop :=
  by
  rw [← inv_inv f]
  apply Filter.Tendsto.inv_tendsto_zero
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (Summable.tendsto_atTop_zero hf)
  rw [eventually_iff_exists_mem]
  refine' ⟨Set.Ioi 0, Ioi_mem_at_top _, fun _ _ => _⟩
  rw [Set.mem_Ioi, inv_eq_one_div, one_div, Pi.inv_apply, _root_.inv_pos]
  exact hf' _
#align summable.tendsto_top_of_pos Summable.tendsto_atTop_of_pos

