/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn

! This file was ported from Lean 3 source module order.countable_dense_linear_order
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Ideal
import Mathbin.Data.Finset.Lattice

/-!
# The back and forth method and countable dense linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Results

Suppose `α β` are linear orders, with `α` countable and `β` dense, nontrivial. Then there is an
order embedding `α ↪ β`. If in addition `α` is dense, nonempty, without endpoints and `β` is
countable, without endpoints, then we can upgrade this to an order isomorphism `α ≃ β`.

The idea for both results is to consider "partial isomorphisms", which identify a finite subset of
`α` with a finite subset of `β`, and prove that for any such partial isomorphism `f` and `a : α`, we
can extend `f` to include `a` in its domain.

## References

https://en.wikipedia.org/wiki/Back-and-forth_method

## Tags

back and forth, dense, countable, order
-/


noncomputable section

open Classical

namespace Order

#print Order.exists_between_finsets /-
/-- Suppose `α` is a nonempty dense linear order without endpoints, and
    suppose `lo`, `hi`, are finite subssets with all of `lo` strictly
    before `hi`. Then there is an element of `α` strictly between `lo`
    and `hi`. -/
theorem exists_between_finsets {α : Type _} [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [nonem : Nonempty α] (lo hi : Finset α) (lo_lt_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y) :
    ∃ m : α, (∀ x ∈ lo, x < m) ∧ ∀ y ∈ hi, m < y :=
  if nlo : lo.Nonempty then
    if nhi : hi.Nonempty then
      -- both sets are nonempty, use densely_ordered
        Exists.elim
        (exists_between (lo_lt_hi _ (Finset.max'_mem _ nlo) _ (Finset.min'_mem _ nhi))) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm.1, fun y hy =>
          lt_of_lt_of_le hm.2 (Finset.min'_le hi y hy)⟩
    else-- upper set is empty, use `no_max_order`
        Exists.elim
        (exists_gt (Finset.max' lo nlo)) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm, fun y hy => (nhi ⟨y, hy⟩).elim⟩
  else
    if nhi : hi.Nonempty then
      -- lower set is empty, use `no_min_order`
        Exists.elim
        (exists_lt (Finset.min' hi nhi)) fun m hm =>
        ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => lt_of_lt_of_le hm (Finset.min'_le hi y hy)⟩
    else-- both sets are empty, use nonempty
          nonem.elim
        fun m => ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => (nhi ⟨y, hy⟩).elim⟩
#align order.exists_between_finsets Order.exists_between_finsets
-/

variable (α β : Type _) [LinearOrder α] [LinearOrder β]

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (p q «expr ∈ » f) -/
#print Order.PartialIso /-
/-- The type of partial order isomorphisms between `α` and `β` defined on finite subsets.
    A partial order isomorphism is encoded as a finite subset of `α × β`, consisting
    of pairs which should be identified. -/
def PartialIso : Type _ :=
  { f : Finset (α × β) //
    ∀ (p) (_ : p ∈ f) (q) (_ : q ∈ f),
      cmp (Prod.fst p) (Prod.fst q) = cmp (Prod.snd p) (Prod.snd q) }
#align order.partial_iso Order.PartialIso
-/

namespace PartialIso

instance : Inhabited (PartialIso α β) :=
  ⟨⟨∅, fun p h q => h.elim⟩⟩

instance : Preorder (PartialIso α β) :=
  Subtype.preorder _

variable {α β}

#print Order.PartialIso.exists_across /-
/-- For each `a`, we can find a `b` in the codomain, such that `a`'s relation to
the domain of `f` is `b`'s relation to the image of `f`.

Thus, if `a` is not already in `f`, then we can extend `f` by sending `a` to `b`.
-/
theorem exists_across [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β]
    (f : PartialIso α β) (a : α) : ∃ b : β, ∀ p ∈ f.val, cmp (Prod.fst p) a = cmp (Prod.snd p) b :=
  by
  by_cases h : ∃ b, (a, b) ∈ f.val
  · cases' h with b hb
    exact ⟨b, fun p hp => f.prop _ hp _ hb⟩
  have :
    ∀ x ∈ (f.val.filter fun p : α × β => p.fst < a).image Prod.snd,
      ∀ y ∈ (f.val.filter fun p : α × β => a < p.fst).image Prod.snd, x < y :=
    by
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp1, rfl⟩
    rcases hy with ⟨q, hq1, rfl⟩
    rw [Finset.mem_filter] at hp1 hq1
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp1.1 _ hq1.1)]
    exact lt_trans hp1.right hq1.right
  cases' exists_between_finsets _ _ this with b hb
  use b
  rintro ⟨p1, p2⟩ hp
  have : p1 ≠ a := fun he => h ⟨p2, he ▸ hp⟩
  cases' lt_or_gt_of_ne this with hl hr
  · have : p1 < a ∧ p2 < b :=
      ⟨hl, hb.1 _ (finset.mem_image.mpr ⟨(p1, p2), finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩
    rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff] at this
    cc
  · have : a < p1 ∧ b < p2 :=
      ⟨hr, hb.2 _ (finset.mem_image.mpr ⟨(p1, p2), finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩
    rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff] at this
    cc
#align order.partial_iso.exists_across Order.PartialIso.exists_across
-/

#print Order.PartialIso.comm /-
/-- A partial isomorphism between `α` and `β` is also a partial isomorphism between `β` and `α`. -/
protected def comm : PartialIso α β → PartialIso β α :=
  Subtype.map (Finset.image (Equiv.prodComm _ _)) fun f hf p hp q hq =>
    Eq.symm <|
      hf ((Equiv.prodComm α β).symm p)
        (by
          rw [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage] at hp
          rwa [← Finset.mem_coe])
        ((Equiv.prodComm α β).symm q)
        (by
          rw [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage] at hq
          rwa [← Finset.mem_coe])
#align order.partial_iso.comm Order.PartialIso.comm
-/

variable (β)

/- warning: order.partial_iso.defined_at_left -> Order.PartialIso.definedAtLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_4 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_5 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_6 : Nonempty.{succ u2} β], α -> (Order.Cofinal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u1}} (β : Type.{u2}) [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))] [_inst_4 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))] [_inst_5 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))] [_inst_6 : Nonempty.{succ u2} β], α -> (Order.Cofinal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align order.partial_iso.defined_at_left Order.PartialIso.definedAtLeftₓ'. -/
/-- The set of partial isomorphisms defined at `a : α`, together with a proof that any
    partial isomorphism can be extended to one defined at `a`. -/
def definedAtLeft [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α) :
    Cofinal (PartialIso α β)
    where
  carrier f := ∃ b : β, (a, b) ∈ f.val
  mem_gt f := by
    cases' exists_across f a with b a_b
    refine'
      ⟨⟨insert (a, b) f.val, fun p hp q hq => _⟩, ⟨b, Finset.mem_insert_self _ _⟩,
        Finset.subset_insert _ _⟩
    rw [Finset.mem_insert] at hp hq
    rcases hp with (rfl | pf) <;> rcases hq with (rfl | qf)
    · simp only [cmp_self_eq_eq]
    · rw [cmp_eq_cmp_symm]
      exact a_b _ qf
    · exact a_b _ pf
    · exact f.prop _ pf _ qf
#align order.partial_iso.defined_at_left Order.PartialIso.definedAtLeft

variable (α) {β}

/- warning: order.partial_iso.defined_at_right -> Order.PartialIso.definedAtRight is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_6 : Nonempty.{succ u1} α], β -> (Order.Cofinal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_6 : Nonempty.{succ u1} α], β -> (Order.Cofinal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align order.partial_iso.defined_at_right Order.PartialIso.definedAtRightₓ'. -/
/-- The set of partial isomorphisms defined at `b : β`, together with a proof that any
    partial isomorphism can be extended to include `b`. We prove this by symmetry. -/
def definedAtRight [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β) :
    Cofinal (PartialIso α β) where
  carrier f := ∃ a, (a, b) ∈ f.val
  mem_gt f := by
    rcases(defined_at_left α b).mem_gt f.comm with ⟨f', ⟨a, ha⟩, hl⟩
    refine' ⟨f'.comm, ⟨a, _⟩, _⟩
    · change (a, b) ∈ f'.val.image _
      rwa [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage]
    · change _ ⊆ f'.val.image _
      rw [← Finset.coe_subset, Finset.coe_image, ← Equiv.subset_image]
      change f.val.image _ ⊆ _ at hl
      rwa [← Finset.coe_subset, Finset.coe_image] at hl
#align order.partial_iso.defined_at_right Order.PartialIso.definedAtRight

variable {α}

/- warning: order.partial_iso.fun_of_ideal -> Order.PartialIso.funOfIdeal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_4 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_5 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_6 : Nonempty.{succ u2} β] (a : α) (I : Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))), (Exists.{succ (max u1 u2)} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (fun (f : Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) => And (Membership.Mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Cofinal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)) (Order.Cofinal.hasMem.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)) f (Order.PartialIso.definedAtLeft.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 a)) (Membership.Mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.setLike.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)))) f I))) -> (Subtype.{succ u2} β (fun (b : β) => Exists.{succ (max u1 u2)} (Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) (fun (f : Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.setLike.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)))) f I) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.setLike.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)))) f I) => Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (Subtype.val.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q))))) f)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))] [_inst_4 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))] [_inst_5 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))] [_inst_6 : Nonempty.{succ u2} β] (a : α) (I : Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))), (Exists.{succ (max u1 u2)} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (fun (f : Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) => And (Membership.mem.{max u1 u2, max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Cofinal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)) (Order.Cofinal.instMembershipCofinal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)) f (Order.PartialIso.definedAtLeft.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 a)) (Membership.mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (SetLike.instMembership.{max u1 u2, max u1 u2} (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.instSetLikeIdeal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)))) f I))) -> (Subtype.{succ u2} β (fun (b : β) => Exists.{succ (max u1 u2)} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (fun (f : Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) => And (Membership.mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (SetLike.instMembership.{max u1 u2, max u1 u2} (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.instSetLikeIdeal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)))) f I) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.instMembershipFinset.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (Subtype.val.{succ (max u1 u2)} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u2 u1} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.instMembershipFinset.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.instMembershipFinset.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q))))) f)))))
Case conversion may be inaccurate. Consider using '#align order.partial_iso.fun_of_ideal Order.PartialIso.funOfIdealₓ'. -/
/-- Given an ideal which intersects `defined_at_left β a`, pick `b : β` such that
    some partial function in the ideal maps `a` to `b`. -/
def funOfIdeal [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α)
    (I : Ideal (PartialIso α β)) :
    (∃ f, f ∈ definedAtLeft β a ∧ f ∈ I) → { b // ∃ f ∈ I, (a, b) ∈ Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨b, hb⟩, hf⟩ => ⟨b, f, hf, hb⟩
#align order.partial_iso.fun_of_ideal Order.PartialIso.funOfIdeal

/- warning: order.partial_iso.inv_of_ideal -> Order.PartialIso.invOfIdeal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_6 : Nonempty.{succ u1} α] (b : β) (I : Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))), (Exists.{succ (max u1 u2)} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (fun (f : Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) => And (Membership.Mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Cofinal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)) (Order.Cofinal.hasMem.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)) f (Order.PartialIso.definedAtRight.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 b)) (Membership.Mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.setLike.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)))) f I))) -> (Subtype.{succ u1} α (fun (a : α) => Exists.{succ (max u1 u2)} (Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) (fun (f : Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.setLike.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)))) f I) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Subtype.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q)))))) (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Order.Ideal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.setLike.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.preorder.{u1, u2} α β _inst_1 _inst_2)))) f I) => Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (Subtype.val.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u1 u2} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q))))) f)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_5 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_6 : Nonempty.{succ u1} α] (b : β) (I : Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))), (Exists.{succ (max u1 u2)} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (fun (f : Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) => And (Membership.mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Cofinal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)) (Order.Cofinal.instMembershipCofinal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)) f (Order.PartialIso.definedAtRight.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 b)) (Membership.mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (SetLike.instMembership.{max u1 u2, max u1 u2} (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.instSetLikeIdeal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)))) f I))) -> (Subtype.{succ u1} α (fun (a : α) => Exists.{succ (max u1 u2)} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (fun (f : Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) => And (Membership.mem.{max u1 u2, max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (SetLike.instMembership.{max u1 u2, max u1 u2} (Order.Ideal.{max u2 u1} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2))) (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.Ideal.instSetLikeIdeal.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Preorder.toLE.{max u1 u2} (Order.PartialIso.{u1, u2} α β _inst_1 _inst_2) (Order.PartialIso.instPreorderPartialIso.{u1, u2} α β _inst_1 _inst_2)))) f I) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.instMembershipFinset.{max u2 u1} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (Subtype.val.{succ (max u1 u2)} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (fun (f : Finset.{max u2 u1} (Prod.{u1, u2} α β)) => forall (p : Prod.{u1, u2} α β), (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.instMembershipFinset.{max u1 u2} (Prod.{u1, u2} α β)) p f) -> (forall (q : Prod.{u1, u2} α β), (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.instMembershipFinset.{max u1 u2} (Prod.{u1, u2} α β)) q f) -> (Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_1 a b) (Prod.fst.{u1, u2} α β p) (Prod.fst.{u1, u2} α β q)) (cmp.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u2} β _inst_2 a b) (Prod.snd.{u1, u2} α β p) (Prod.snd.{u1, u2} α β q))))) f)))))
Case conversion may be inaccurate. Consider using '#align order.partial_iso.inv_of_ideal Order.PartialIso.invOfIdealₓ'. -/
/-- Given an ideal which intersects `defined_at_right α b`, pick `a : α` such that
    some partial function in the ideal maps `a` to `b`. -/
def invOfIdeal [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β)
    (I : Ideal (PartialIso α β)) :
    (∃ f, f ∈ definedAtRight α b ∧ f ∈ I) → { a // ∃ f ∈ I, (a, b) ∈ Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨a, ha⟩, hf⟩ => ⟨a, f, hf, ha⟩
#align order.partial_iso.inv_of_ideal Order.PartialIso.invOfIdeal

end PartialIso

open PartialIso

variable (α β)

/- warning: order.embedding_from_countable_to_dense -> Order.embedding_from_countable_to_dense is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Encodable.{u1} α] [_inst_4 : DenselyOrdered.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_5 : Nontrivial.{u2} β], Nonempty.{max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))))
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] [_inst_3 : Encodable.{u2} α] [_inst_4 : DenselyOrdered.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))))] [_inst_5 : Nontrivial.{u1} β], Nonempty.{max (succ u1) (succ u2)} (OrderEmbedding.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align order.embedding_from_countable_to_dense Order.embedding_from_countable_to_denseₓ'. -/
/-- Any countable linear order embeds in any nontrivial dense linear order. -/
theorem embedding_from_countable_to_dense [Encodable α] [DenselyOrdered β] [Nontrivial β] :
    Nonempty (α ↪o β) := by
  rcases exists_pair_lt β with ⟨x, y, hxy⟩
  cases' exists_between hxy with a ha
  haveI : Nonempty (Set.Ioo x y) := ⟨⟨a, ha⟩⟩
  let our_ideal : ideal (partial_iso α _) :=
    ideal_of_cofinals default (defined_at_left (Set.Ioo x y))
  let F a := fun_of_ideal a our_ideal (cofinal_meets_ideal_of_cofinals _ _ a)
  refine'
    ⟨RelEmbedding.trans (OrderEmbedding.ofStrictMono (fun a => (F a).val) fun a₁ a₂ => _)
        (OrderEmbedding.subtype _)⟩
  rcases(F a₁).Prop with ⟨f, hf, ha₁⟩
  rcases(F a₂).Prop with ⟨g, hg, ha₂⟩
  rcases our_ideal.directed _ hf _ hg with ⟨m, hm, fm, gm⟩
  exact (lt_iff_lt_of_cmp_eq_cmp <| m.prop (a₁, _) (fm ha₁) (a₂, _) (gm ha₂)).mp
#align order.embedding_from_countable_to_dense Order.embedding_from_countable_to_dense

/- warning: order.iso_of_countable_dense -> Order.iso_of_countable_dense is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Encodable.{u1} α] [_inst_4 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_5 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_6 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_7 : Nonempty.{succ u1} α] [_inst_8 : Encodable.{u2} β] [_inst_9 : DenselyOrdered.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_10 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_11 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))] [_inst_12 : Nonempty.{succ u2} β], Nonempty.{max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))))
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : LinearOrder.{u2} α] [_inst_2 : LinearOrder.{u1} β] [_inst_3 : Encodable.{u2} α] [_inst_4 : DenselyOrdered.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] [_inst_5 : NoMinOrder.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] [_inst_6 : NoMaxOrder.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1))))))] [_inst_7 : Nonempty.{succ u2} α] [_inst_8 : Encodable.{u1} β] [_inst_9 : DenselyOrdered.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))))] [_inst_10 : NoMinOrder.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))))] [_inst_11 : NoMaxOrder.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))))] [_inst_12 : Nonempty.{succ u1} β], Nonempty.{max (succ u1) (succ u2)} (OrderIso.{u2, u1} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align order.iso_of_countable_dense Order.iso_of_countable_denseₓ'. -/
/-- Any two countable dense, nonempty linear orders without endpoints are order isomorphic. -/
theorem iso_of_countable_dense [Encodable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Encodable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) :=
  let to_cofinal : Sum α β → Cofinal (PartialIso α β) := fun p =>
    Sum.recOn p (definedAtLeft β) (definedAtRight α)
  let our_ideal : Ideal (PartialIso α β) := idealOfCofinals default to_cofinal
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b := invOfIdeal b our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  ⟨OrderIso.ofCmpEqCmp (fun a => (F a).val) (fun b => (G b).val) fun a b =>
      by
      rcases(F a).Prop with ⟨f, hf, ha⟩
      rcases(G b).Prop with ⟨g, hg, hb⟩
      rcases our_ideal.directed _ hf _ hg with ⟨m, hm, fm, gm⟩
      exact m.prop (a, _) (fm ha) (_, b) (gm hb)⟩
#align order.iso_of_countable_dense Order.iso_of_countable_dense

end Order

