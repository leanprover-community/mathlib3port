/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.finset.noncomm_prod
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Algebra.Hom.Commute
import Mathbin.Algebra.BigOperators.Basic

/-!
# Products (respectively, sums) over a finset or a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/


variable {F ι α β γ : Type _} (f : α → β → β) (op : α → α → α)

namespace Multiset

#print Multiset.noncommFoldr /-
/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncommFoldr (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise fun x y => ∀ b, f x (f y b) = f y (f x b)) (b : β) : β :=
  s.attach.foldr (f ∘ Subtype.val)
    (fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      haveI : IsRefl α fun x y => ∀ b, f x (f y b) = f y (f x b) := ⟨fun x b => rfl⟩
      comm.of_refl hx hy)
    b
#align multiset.noncomm_foldr Multiset.noncommFoldr
-/

/- warning: multiset.noncomm_foldr_coe -> Multiset.noncommFoldr_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (l : List.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l))) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u2} β (f x (f y b)) (f y (f x b)))) (b : β), Eq.{succ u2} β (Multiset.noncommFoldr.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l) comm b) (List.foldr.{u1, u2} α β f b l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (l : List.{u2} α) (comm : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x (Multiset.ofList.{u2} α l))) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u1} β (f x (f y b)) (f y (f x b)))) (b : β), Eq.{succ u1} β (Multiset.noncommFoldr.{u2, u1} α β f (Multiset.ofList.{u2} α l) comm b) (List.foldr.{u2, u1} α β f b l)
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_foldr_coe Multiset.noncommFoldr_coeₓ'. -/
@[simp]
theorem noncommFoldr_coe (l : List α) (comm) (b : β) :
    noncommFoldr f (l : Multiset α) comm b = l.foldr f b :=
  by
  simp only [noncomm_foldr, coe_foldr, coe_attach, List.attach]
  rw [← List.foldr_map]
  simp [List.map_pmap, List.pmap_eq_map]
#align multiset.noncomm_foldr_coe Multiset.noncommFoldr_coe

/- warning: multiset.noncomm_foldr_empty -> Multiset.noncommFoldr_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (h : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u2} β (f x (f y b)) (f y (f x b)))) (b : β), Eq.{succ u2} β (Multiset.noncommFoldr.{u1, u2} α β f (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) h b) b
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (h : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))))) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u1} β (f x (f y b)) (f y (f x b)))) (b : β), Eq.{succ u1} β (Multiset.noncommFoldr.{u2, u1} α β f (OfNat.ofNat.{u2} (Multiset.{u2} α) 0 (Zero.toOfNat0.{u2} (Multiset.{u2} α) (Multiset.instZeroMultiset.{u2} α))) h b) b
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_foldr_empty Multiset.noncommFoldr_emptyₓ'. -/
@[simp]
theorem noncommFoldr_empty (h) (b : β) : noncommFoldr f (0 : Multiset α) h b = b :=
  rfl
#align multiset.noncomm_foldr_empty Multiset.noncommFoldr_empty

/- warning: multiset.noncomm_foldr_cons -> Multiset.noncommFoldr_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (s : Multiset.{u1} α) (a : α) (h : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (Multiset.cons.{u1} α a s))) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u2} β (f x (f y b)) (f y (f x b)))) (h' : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u2} β (f x (f y b)) (f y (f x b)))) (b : β), Eq.{succ u2} β (Multiset.noncommFoldr.{u1, u2} α β f (Multiset.cons.{u1} α a s) h b) (f a (Multiset.noncommFoldr.{u1, u2} α β f s h' b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (s : Multiset.{u2} α) (a : α) (h : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x (Multiset.cons.{u2} α a s))) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u1} β (f x (f y b)) (f y (f x b)))) (h' : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) (fun (x : α) (y : α) => forall (b : β), Eq.{succ u1} β (f x (f y b)) (f y (f x b)))) (b : β), Eq.{succ u1} β (Multiset.noncommFoldr.{u2, u1} α β f (Multiset.cons.{u2} α a s) h b) (f a (Multiset.noncommFoldr.{u2, u1} α β f s h' b))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_foldr_cons Multiset.noncommFoldr_consₓ'. -/
theorem noncommFoldr_cons (s : Multiset α) (a : α) (h h') (b : β) :
    noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b) :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_foldr_cons Multiset.noncommFoldr_cons

/- warning: multiset.noncomm_foldr_eq_foldr -> Multiset.noncommFoldr_eq_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β -> β) (s : Multiset.{u1} α) (h : LeftCommutative.{u1, u2} α β f) (b : β), Eq.{succ u2} β (Multiset.noncommFoldr.{u1, u2} α β f s (fun (x : α) (_x : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s))) (y : α) (_x : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s))) (_x : Ne.{succ u1} α x y) => h x y) b) (Multiset.foldr.{u1, u2} α β f h b s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β -> β) (s : Multiset.{u2} α) (h : LeftCommutative.{u2, u1} α β f) (b : β), Eq.{succ u1} β (Multiset.noncommFoldr.{u2, u1} α β f s (fun (x : α) (_x : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s))) (y : α) (_x : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s))) (_x : Ne.{succ u2} α x y) => h x y) b) (Multiset.foldr.{u2, u1} α β f h b s)
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_foldr_eq_foldr Multiset.noncommFoldr_eq_foldrₓ'. -/
theorem noncommFoldr_eq_foldr (s : Multiset α) (h : LeftCommutative f) (b : β) :
    noncommFoldr f s (fun x _ y _ _ => h x y) b = foldr f h b s :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_foldr_eq_foldr Multiset.noncommFoldr_eq_foldr

variable [assoc : IsAssociative α op]

include assoc

#print Multiset.noncommFold /-
/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncommFold (s : Multiset α) (comm : { x | x ∈ s }.Pairwise fun x y => op x y = op y x) :
    α → α :=
  noncommFoldr op s fun x hx y hy h b => by rw [← assoc.assoc, comm hx hy h, assoc.assoc]
#align multiset.noncomm_fold Multiset.noncommFold
-/

#print Multiset.noncommFold_coe /-
@[simp]
theorem noncommFold_coe (l : List α) (comm) (a : α) :
    noncommFold op (l : Multiset α) comm a = l.foldr op a := by simp [noncomm_fold]
#align multiset.noncomm_fold_coe Multiset.noncommFold_coe
-/

#print Multiset.noncommFold_empty /-
@[simp]
theorem noncommFold_empty (h) (a : α) : noncommFold op (0 : Multiset α) h a = a :=
  rfl
#align multiset.noncomm_fold_empty Multiset.noncommFold_empty
-/

#print Multiset.noncommFold_cons /-
theorem noncommFold_cons (s : Multiset α) (a : α) (h h') (x : α) :
    noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x) :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_fold_cons Multiset.noncommFold_cons
-/

#print Multiset.noncommFold_eq_fold /-
theorem noncommFold_eq_fold (s : Multiset α) [IsCommutative α op] (a : α) :
    noncommFold op s (fun x _ y _ _ => IsCommutative.comm x y) a = fold op a s :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_fold_eq_fold Multiset.noncommFold_eq_fold
-/

omit assoc

variable [Monoid α] [Monoid β]

/- warning: multiset.noncomm_prod -> Multiset.noncommProd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α), (Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) -> α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α), (Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s)) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) -> α
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod Multiset.noncommProdₓ'. -/
/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes\non all elements `x ∈ s`."]
def noncommProd (s : Multiset α) (comm : { x | x ∈ s }.Pairwise Commute) : α :=
  s.noncommFold (· * ·) comm 1
#align multiset.noncomm_prod Multiset.noncommProd
#align multiset.noncomm_sum Multiset.noncommSum

/- warning: multiset.noncomm_prod_coe -> Multiset.noncommProd_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (l : List.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l))) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l) comm) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) l)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (l : List.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x (Multiset.ofList.{u1} α l))) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (Multiset.ofList.{u1} α l) comm) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) l)
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_coe Multiset.noncommProd_coeₓ'. -/
@[simp, to_additive]
theorem noncommProd_coe (l : List α) (comm) : noncommProd (l : Multiset α) comm = l.Prod :=
  by
  rw [noncomm_prod]
  simp only [noncomm_fold_coe]
  induction' l with hd tl hl
  · simp
  · rw [List.prod_cons, List.foldr, hl]
    intro x hx y hy
    exact comm (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)
#align multiset.noncomm_prod_coe Multiset.noncommProd_coe
#align multiset.noncomm_sum_coe Multiset.noncommSum_coe

/- warning: multiset.noncomm_prod_empty -> Multiset.noncommProd_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (h : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))))) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α)))) h) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (h : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))))) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α))) h) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_empty Multiset.noncommProd_emptyₓ'. -/
@[simp, to_additive]
theorem noncommProd_empty (h) : noncommProd (0 : Multiset α) h = 1 :=
  rfl
#align multiset.noncomm_prod_empty Multiset.noncommProd_empty
#align multiset.noncomm_sum_empty Multiset.noncommSum_empty

/- warning: multiset.noncomm_prod_cons -> Multiset.noncommProd_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (a : α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (Multiset.cons.{u1} α a s))) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (Multiset.cons.{u1} α a s) comm) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (Multiset.noncommProd.{u1} α _inst_1 s (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (Multiset.cons.{u1} α a s))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (fun (_x : α) => Multiset.mem_cons_of_mem.{u1} α _x a s) comm)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (a : α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x (Multiset.cons.{u1} α a s))) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (Multiset.cons.{u1} α a s) comm) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (Multiset.noncommProd.{u1} α _inst_1 s (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (fun (x._@.Mathlib.Data.Finset.NoncommProd._hyg.1019 : α) => Quot.liftOn.{succ u1, 1} (List.{u1} α) Prop (Setoid.r.{succ u1} (List.{u1} α) (List.isSetoid.{u1} α)) (Multiset.cons.{u1} α a s) (fun (l : List.{u1} α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x._@.Mathlib.Data.Finset.NoncommProd._hyg.1019 l) (Multiset.Mem.proof_1.{u1} α x._@.Mathlib.Data.Finset.NoncommProd._hyg.1019)) (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s)) (fun (_x : α) => Multiset.mem_cons_of_mem.{u1} α _x a s) comm)))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_cons Multiset.noncommProd_consₓ'. -/
@[simp, to_additive]
theorem noncommProd_cons (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = a * noncommProd s (comm.mono fun _ => mem_cons_of_mem) :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_prod_cons Multiset.noncommProd_cons
#align multiset.noncomm_sum_cons Multiset.noncommSum_cons

/- warning: multiset.noncomm_prod_cons' -> Multiset.noncommProd_cons' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (a : α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (Multiset.cons.{u1} α a s))) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (Multiset.cons.{u1} α a s) comm) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Multiset.noncommProd.{u1} α _inst_1 s (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (Multiset.cons.{u1} α a s))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (fun (_x : α) => Multiset.mem_cons_of_mem.{u1} α _x a s) comm)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (a : α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x (Multiset.cons.{u1} α a s))) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (Multiset.cons.{u1} α a s) comm) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Multiset.noncommProd.{u1} α _inst_1 s (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (fun (x._@.Mathlib.Data.Finset.NoncommProd._hyg.1077 : α) => Quot.liftOn.{succ u1, 1} (List.{u1} α) Prop (Setoid.r.{succ u1} (List.{u1} α) (List.isSetoid.{u1} α)) (Multiset.cons.{u1} α a s) (fun (l : List.{u1} α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x._@.Mathlib.Data.Finset.NoncommProd._hyg.1077 l) (Multiset.Mem.proof_1.{u1} α x._@.Mathlib.Data.Finset.NoncommProd._hyg.1077)) (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s)) (fun (_x : α) => Multiset.mem_cons_of_mem.{u1} α _x a s) comm)) a)
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_cons' Multiset.noncommProd_cons'ₓ'. -/
@[to_additive]
theorem noncommProd_cons' (s : Multiset α) (a : α) (comm) :
    noncommProd (a ::ₘ s) comm = noncommProd s (comm.mono fun _ => mem_cons_of_mem) * a :=
  by
  induction' s using Quotient.inductionOn with s
  simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, List.prod_cons]
  induction' s with hd tl IH
  · simp
  · rw [List.prod_cons, mul_assoc, ← IH, ← mul_assoc, ← mul_assoc]
    · congr 1
      apply comm.of_refl <;> simp
    · intro x hx y hy
      simp only [quot_mk_to_coe, List.mem_cons, mem_coe, cons_coe] at hx hy
      apply comm
      · cases hx <;> simp [hx]
      · cases hy <;> simp [hy]
#align multiset.noncomm_prod_cons' Multiset.noncommProd_cons'
#align multiset.noncomm_sum_cons' Multiset.noncommSum_cons'

/- warning: multiset.noncomm_prod_add -> Multiset.noncommProd_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t))) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t) comm) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Multiset.noncommProd.{u1} α _inst_1 s (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (Multiset.subset_of_le.{u1} α s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t) (Multiset.le_add_right.{u1} α s t)) comm)) (Multiset.noncommProd.{u1} α _inst_1 t (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t))) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x t)) (Multiset.subset_of_le.{u1} α t (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t) (Multiset.le_add_left.{u1} α t s)) comm)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t))) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))), Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t) comm) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Multiset.noncommProd.{u1} α _inst_1 s (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (fun (a : α) => Quot.liftOn.{succ u1, 1} (List.{u1} α) Prop (Setoid.r.{succ u1} (List.{u1} α) (List.isSetoid.{u1} α)) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t) (fun (l : List.{u1} α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l) (Multiset.Mem.proof_1.{u1} α a)) (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s)) (Multiset.subset_of_le.{u1} α s (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t) (Multiset.le_add_right.{u1} α s t)) comm)) (Multiset.noncommProd.{u1} α _inst_1 t (Set.Pairwise.mono.{u1} α (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (fun (a : α) => Quot.liftOn.{succ u1, 1} (List.{u1} α) Prop (Setoid.r.{succ u1} (List.{u1} α) (List.isSetoid.{u1} α)) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t) (fun (l : List.{u1} α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) a l) (Multiset.Mem.proof_1.{u1} α a)) (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x t)) (Multiset.subset_of_le.{u1} α t (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t) (Multiset.le_add_left.{u1} α t s)) comm)))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_add Multiset.noncommProd_addₓ'. -/
@[to_additive]
theorem noncommProd_add (s t : Multiset α) (comm) :
    noncommProd (s + t) comm =
      noncommProd s (comm.mono <| subset_of_le <| s.le_add_right t) *
        noncommProd t (comm.mono <| subset_of_le <| t.le_add_left s) :=
  by
  rcases s with ⟨⟩
  rcases t with ⟨⟩
  simp
#align multiset.noncomm_prod_add Multiset.noncommProd_add
#align multiset.noncomm_sum_add Multiset.noncommSum_add

/- warning: multiset.noncomm_prod_map_aux -> Multiset.noncommProd_map_aux is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u2} α] [_inst_2 : Monoid.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u3} β _inst_2)] (s : Multiset.{u2} α), (Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Multiset.{u2} α) (Multiset.hasMem.{u2} α) x s)) (Commute.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)))) -> (forall (f : F), Set.Pairwise.{u3} β (setOf.{u3} β (fun (x : β) => Membership.Mem.{u3, u3} β (Multiset.{u3} β) (Multiset.hasMem.{u3} β) x (Multiset.map.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u3} β _inst_2) _inst_3))) f) s))) (Commute.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_2))))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u2} α] [_inst_2 : Monoid.{u1} β] [_inst_3 : MonoidHomClass.{u3, u2, u1} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u1} β _inst_2)] (s : Multiset.{u2} α), (Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) (Commute.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)))) -> (forall (f : F), Set.Pairwise.{u1} β (setOf.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) x (Multiset.map.{u2, u1} α β (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u1} β _inst_2) _inst_3)) f) s))) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_map_aux Multiset.noncommProd_map_auxₓ'. -/
@[protected, to_additive]
theorem noncommProd_map_aux [MonoidHomClass F α β] (s : Multiset α)
    (comm : { x | x ∈ s }.Pairwise Commute) (f : F) : { x | x ∈ s.map f }.Pairwise Commute :=
  by
  simp only [Multiset.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
  exact (comm.of_refl hx hy).map f
#align multiset.noncomm_prod_map_aux Multiset.noncommProd_map_aux
#align multiset.noncomm_sum_map_aux Multiset.noncommSum_map_aux

/- warning: multiset.noncomm_prod_map -> Multiset.noncommProd_map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u2} α] [_inst_2 : Monoid.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u3} β _inst_2)] (s : Multiset.{u2} α) (comm : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Multiset.{u2} α) (Multiset.hasMem.{u2} α) x s)) (Commute.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)))) (f : F), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u3} β _inst_2) _inst_3))) f (Multiset.noncommProd.{u2} α _inst_1 s comm)) (Multiset.noncommProd.{u3} β _inst_2 (Multiset.map.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u3} β _inst_2) _inst_3))) f) s) (Multiset.noncommProd_map_aux.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3 s comm f))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u2} α] [_inst_2 : Monoid.{u1} β] [_inst_3 : MonoidHomClass.{u3, u2, u1} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u1} β _inst_2)] (s : Multiset.{u2} α) (comm : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x s)) (Commute.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)))) (f : F), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) (Multiset.noncommProd.{u2} α _inst_1 s comm)) (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u1} β _inst_2) _inst_3)) f (Multiset.noncommProd.{u2} α _inst_1 s comm)) (Multiset.noncommProd.{u1} β _inst_2 (Multiset.map.{u2, u1} α β (FunLike.coe.{succ u3, succ u2, succ u1} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u3, u2, u1} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α _inst_1)) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F α β (Monoid.toMulOneClass.{u2} α _inst_1) (Monoid.toMulOneClass.{u1} β _inst_2) _inst_3)) f) s) (Multiset.noncommProd_map_aux.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3 s comm f))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_map Multiset.noncommProd_mapₓ'. -/
@[to_additive]
theorem noncommProd_map [MonoidHomClass F α β] (s : Multiset α) (comm) (f : F) :
    f (s.noncommProd comm) = (s.map f).noncommProd (noncommProd_map_aux s comm f) :=
  by
  induction s using Quotient.inductionOn
  simpa using map_list_prod f _
#align multiset.noncomm_prod_map Multiset.noncommProd_map
#align multiset.noncomm_sum_map Multiset.noncommSum_map

/- warning: multiset.noncomm_prod_eq_pow_card -> Multiset.noncommProd_eq_pow_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (m : α), (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (Eq.{succ u1} α x m)) -> (Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 s comm) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) m (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s)) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (m : α), (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (Eq.{succ u1} α x m)) -> (Eq.{succ u1} α (Multiset.noncommProd.{u1} α _inst_1 s comm) (HPow.hPow.{u1, 0, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) α (instHPow.{u1, 0} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (Monoid.Pow.{u1} α _inst_1)) m (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_eq_pow_card Multiset.noncommProd_eq_pow_cardₓ'. -/
@[to_additive noncomm_sum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Multiset α) (comm) (m : α) (h : ∀ x ∈ s, x = m) :
    s.noncommProd comm = m ^ s.card :=
  by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncomm_prod_coe, coe_card, mem_coe] at *
  exact List.prod_eq_pow_card _ m h
#align multiset.noncomm_prod_eq_pow_card Multiset.noncommProd_eq_pow_card
#align multiset.noncomm_sum_eq_card_nsmul Multiset.noncommSum_eq_card_nsmul

#print Multiset.noncommProd_eq_prod /-
@[to_additive]
theorem noncommProd_eq_prod {α : Type _} [CommMonoid α] (s : Multiset α) :
    (noncommProd s fun _ _ _ _ _ => Commute.all _ _) = prod s :=
  by
  induction s using Quotient.inductionOn
  simp
#align multiset.noncomm_prod_eq_prod Multiset.noncommProd_eq_prod
#align multiset.noncomm_sum_eq_sum Multiset.noncommSum_eq_sum
-/

/- warning: multiset.noncomm_prod_commute -> Multiset.noncommProd_commute is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s)) (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (y : α), (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) y x)) -> (Commute.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) y (Multiset.noncommProd.{u1} α _inst_1 s comm))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (s : Multiset.{u1} α) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s)) (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (y : α), (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) y x)) -> (Commute.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) y (Multiset.noncommProd.{u1} α _inst_1 s comm))
Case conversion may be inaccurate. Consider using '#align multiset.noncomm_prod_commute Multiset.noncommProd_commuteₓ'. -/
@[to_additive noncomm_sum_add_commute]
theorem noncommProd_commute (s : Multiset α) (comm) (y : α) (h : ∀ x ∈ s, Commute y x) :
    Commute y (s.noncommProd comm) :=
  by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, noncomm_prod_coe]
  exact Commute.list_prod_right _ _ h
#align multiset.noncomm_prod_commute Multiset.noncommProd_commute
#align multiset.noncomm_sum_add_commute Multiset.noncommSum_addCommute

end Multiset

namespace Finset

variable [Monoid β] [Monoid γ]

/- warning: finset.noncomm_prod -> Finset.noncommProd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (s : Finset.{u1} α) (f : α -> β), (Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))) -> β
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (s : Finset.{u1} α) (f : α -> β), (Set.Pairwise.{u1} α (Finset.toSet.{u1} α s) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))) -> β
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod Finset.noncommProdₓ'. -/
/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive
      "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,\ngiven a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncommProd (s : Finset α) (f : α → β)
    (comm : (s : Set α).Pairwise fun a b => Commute (f a) (f b)) : β :=
  (s.1.map f).noncommProd <| by
    simp_rw [Multiset.mem_map]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact comm.of_refl ha hb
#align finset.noncomm_prod Finset.noncommProd
#align finset.noncomm_sum Finset.noncommSum

/- warning: finset.noncomm_prod_congr -> Finset.noncommProd_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {f : α -> β} {g : α -> β} (h₁ : Eq.{succ u1} (Finset.{u1} α) s₁ s₂) (h₂ : forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₂) -> (Eq.{succ u2} β (f x) (g x))) (comm : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))), Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 s₁ f comm) (Finset.noncommProd.{u1, u2} α β _inst_1 s₂ g (fun (x : α) (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂)) (y : α) (hy : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂)) (h : Ne.{succ u1} α x y) => Eq.mpr.{0} (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (g y)) (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (g y)) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (g y)) (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (g y))) (Eq.ndrec.{0, succ u2} β (g x) (fun (_a : β) => Eq.{1} Prop (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (g y)) (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) _a (g y))) (rfl.{1} Prop (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (g y))) (f x) (Eq.symm.{succ u2} β (f x) (g x) (h₂ x hx)))) (Eq.mpr.{0} (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (g y)) (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (f y)) (id_tag Tactic.IdTag.rw (Eq.{1} Prop (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (g y)) (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (f y))) (Eq.ndrec.{0, succ u2} β (g y) (fun (_a : β) => Eq.{1} Prop (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (g y)) (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) _a)) (rfl.{1} Prop (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (g y))) (f y) (Eq.symm.{succ u2} β (f y) (g y) (h₂ y hy)))) (Eq.ndrec.{0, succ u1} (Finset.{u1} α) s₁ (fun {s₂ : Finset.{u1} α} => (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₂) -> (Eq.{succ u2} β (f x) (g x))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂)) -> (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (f y))) (fun (h₂ : forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₁) -> (Eq.{succ u2} β (f x) (g x))) (hx : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁)) (hy : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁)) => comm x hx y hy h) s₂ h₁ h₂ hx hy))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} {g : α -> β} (h₁ : Eq.{succ u2} (Finset.{u2} α) s₁ s₂) (h₂ : forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s₂) -> (Eq.{succ u1} β (f x) (g x))) (comm : Set.Pairwise.{u2} α (Finset.toSet.{u2} α s₁) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))), Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 s₁ f comm) (Finset.noncommProd.{u2, u1} α β _inst_1 s₂ g (fun (x : α) (hx : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s₂)) (y : α) (hy : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y (Finset.toSet.{u2} α s₂)) (h : Ne.{succ u2} α x y) => id.{0} ((fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g a) (g b)) x y) (Eq.mpr.{0} (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (g y)) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (g y)) (id.{0} (Eq.{1} Prop (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (g y)) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (g y))) (Eq.ndrec.{0, succ u1} β (g x) (fun (_a : β) => Eq.{1} Prop (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (g y)) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) _a (g y))) (Eq.refl.{1} Prop (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (g y))) (f x) (Eq.symm.{succ u1} β (f x) (g x) (h₂ x hx)))) (Eq.mpr.{0} (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (g y)) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (f y)) (id.{0} (Eq.{1} Prop (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (g y)) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (f y))) (Eq.ndrec.{0, succ u1} β (g y) (fun (_a : β) => Eq.{1} Prop (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (g y)) (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) _a)) (Eq.refl.{1} Prop (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (g y))) (f y) (Eq.symm.{succ u1} β (f y) (g y) (h₂ y hy)))) (Eq.ndrec.{0, succ u2} (Finset.{u2} α) s₁ (fun {s₂ : Finset.{u2} α} => (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s₂) -> (Eq.{succ u1} β (f x) (g x))) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s₂)) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y (Finset.toSet.{u2} α s₂)) -> (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (f y))) (fun (h₂ : forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s₁) -> (Eq.{succ u1} β (f x) (g x))) (hx : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Finset.toSet.{u2} α s₁)) (hy : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) y (Finset.toSet.{u2} α s₁)) => comm x hx y hy h) s₂ h₁ h₂ hx hy)))))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_congr Finset.noncommProd_congrₓ'. -/
@[congr, to_additive]
theorem noncommProd_congr {s₁ s₂ : Finset α} {f g : α → β} (h₁ : s₁ = s₂) (h₂ : ∀ x ∈ s₂, f x = g x)
    (comm) :
    noncommProd s₁ f comm =
      noncommProd s₂ g fun x hx y hy h =>
        by
        rw [← h₂ _ hx, ← h₂ _ hy]
        subst h₁
        exact comm hx hy h :=
  by simp_rw [noncomm_prod, Multiset.map_congr (congr_arg _ h₁) h₂]
#align finset.noncomm_prod_congr Finset.noncommProd_congr
#align finset.noncomm_sum_congr Finset.noncommSum_congr

/- warning: finset.noncomm_prod_to_finset -> Finset.noncommProd_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] [_inst_3 : DecidableEq.{succ u1} α] (l : List.{u1} α) (f : α -> β) (comm : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b) l)) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))), (List.Nodup.{u1} α l) -> (Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b) l) f comm) (List.prod.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (List.map.{u1, u2} α β f l)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] [_inst_3 : DecidableEq.{succ u2} α] (l : List.{u2} α) (f : α -> β) (comm : Set.Pairwise.{u2} α (Finset.toSet.{u2} α (List.toFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b) l)) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))), (List.Nodup.{u2} α l) -> (Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 (List.toFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b) l) f comm) (List.prod.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (Monoid.toOne.{u1} β _inst_1) (List.map.{u2, u1} α β f l)))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_to_finset Finset.noncommProd_toFinsetₓ'. -/
@[simp, to_additive]
theorem noncommProd_toFinset [DecidableEq α] (l : List α) (f : α → β) (comm) (hl : l.Nodup) :
    noncommProd l.toFinset f comm = (l.map f).Prod :=
  by
  rw [← List.dedup_eq_self] at hl
  simp [noncomm_prod, hl]
#align finset.noncomm_prod_to_finset Finset.noncommProd_toFinset
#align finset.noncomm_sum_to_finset Finset.noncommSum_toFinset

/- warning: finset.noncomm_prod_empty -> Finset.noncommProd_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (f : α -> β) (h : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))), Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) f h) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (f : α -> β) (h : Set.Pairwise.{u2} α (Finset.toSet.{u2} α (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))), Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)) f h) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β _inst_1)))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_empty Finset.noncommProd_emptyₓ'. -/
@[simp, to_additive]
theorem noncommProd_empty (f : α → β) (h) : noncommProd (∅ : Finset α) f h = 1 :=
  rfl
#align finset.noncomm_prod_empty Finset.noncommProd_empty
#align finset.noncomm_sum_empty Finset.noncommSum_empty

/- warning: finset.noncomm_prod_insert_of_not_mem -> Finset.noncommProd_insert_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] [_inst_3 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α) (f : α -> β) (comm : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) a s)) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) a s) f comm) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a) (Finset.noncommProd.{u1, u2} α β _inst_1 s f (Set.Pairwise.mono.{u1} α (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) a s)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (_x : α) => Finset.mem_insert_of_mem.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _x a) comm))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] [_inst_3 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (f : α -> β) (comm : Set.Pairwise.{u2} α (Finset.toSet.{u2} α (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) a s)) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))), (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) a s) f comm) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (f a) (Finset.noncommProd.{u2, u1} α β _inst_1 s f (Set.Pairwise.mono.{u2} α (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b)) (fun (x._@.Mathlib.Data.Finset.NoncommProd._hyg.2117 : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x._@.Mathlib.Data.Finset.NoncommProd._hyg.2117 (Finset.val.{u2} α (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) a s))) (Finset.toSet.{u2} α s) (fun (_x : α) => Finset.mem_insert_of_mem.{u2} α (fun (a : α) (b : α) => _inst_3 a b) s _x a) comm))))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_insert_of_not_mem Finset.noncommProd_insert_of_not_memₓ'. -/
@[simp, to_additive]
theorem noncommProd_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      f a * noncommProd s f (comm.mono fun _ => mem_insert_of_mem) :=
  by simp [insert_val_of_not_mem ha, noncomm_prod]
#align finset.noncomm_prod_insert_of_not_mem Finset.noncommProd_insert_of_not_mem
#align finset.noncomm_sum_insert_of_not_mem Finset.noncommSum_insert_of_not_mem

/- warning: finset.noncomm_prod_insert_of_not_mem' -> Finset.noncommProd_insert_of_not_mem' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] [_inst_3 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α) (f : α -> β) (comm : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) a s)) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) a s) f comm) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (Finset.noncommProd.{u1, u2} α β _inst_1 s f (Set.Pairwise.mono.{u1} α (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) a s)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (_x : α) => Finset.mem_insert_of_mem.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s _x a) comm)) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] [_inst_3 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (f : α -> β) (comm : Set.Pairwise.{u2} α (Finset.toSet.{u2} α (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) a s)) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))), (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) a s) f comm) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (Finset.noncommProd.{u2, u1} α β _inst_1 s f (Set.Pairwise.mono.{u2} α (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b)) (fun (x._@.Mathlib.Data.Finset.NoncommProd._hyg.2333 : α) => Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) x._@.Mathlib.Data.Finset.NoncommProd._hyg.2333 (Finset.val.{u2} α (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) a s))) (Finset.toSet.{u2} α s) (fun (_x : α) => Finset.mem_insert_of_mem.{u2} α (fun (a : α) (b : α) => _inst_3 a b) s _x a) comm)) (f a)))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_insert_of_not_mem' Finset.noncommProd_insert_of_not_mem'ₓ'. -/
@[to_additive]
theorem noncommProd_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β) (comm)
    (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      noncommProd s f (comm.mono fun _ => mem_insert_of_mem) * f a :=
  by simp [noncomm_prod, insert_val_of_not_mem ha, Multiset.noncommProd_cons']
#align finset.noncomm_prod_insert_of_not_mem' Finset.noncommProd_insert_of_not_mem'
#align finset.noncomm_sum_insert_of_not_mem' Finset.noncommSum_insert_of_not_mem'

#print Finset.noncommProd_singleton /-
@[simp, to_additive]
theorem noncommProd_singleton (a : α) (f : α → β) :
    noncommProd ({a} : Finset α) f
        (by
          norm_cast
          exact Set.pairwise_singleton _ _) =
      f a :=
  by simp [noncomm_prod, ← Multiset.cons_zero]
#align finset.noncomm_prod_singleton Finset.noncommProd_singleton
#align finset.noncomm_sum_singleton Finset.noncommSum_singleton
-/

/- warning: finset.noncomm_prod_map -> Finset.noncommProd_map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Monoid.{u3} β] [_inst_2 : Monoid.{u4} γ] [_inst_3 : MonoidHomClass.{u1, u3, u4} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u4} γ _inst_2)] (s : Finset.{u2} α) (f : α -> β) (comm : Set.Pairwise.{u2} α ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} α) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (Finset.Set.hasCoeT.{u2} α))) s) (fun (a : α) (b : α) => Commute.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (f a) (f b))) (g : F), Eq.{succ u4} γ (coeFn.{succ u1, max (succ u3) (succ u4)} F (fun (_x : F) => β -> γ) (FunLike.hasCoeToFun.{succ u1, succ u3, succ u4} F β (fun (_x : β) => γ) (MulHomClass.toFunLike.{u1, u3, u4} F β γ (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (MulOneClass.toHasMul.{u4} γ (Monoid.toMulOneClass.{u4} γ _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u4} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u4} γ _inst_2) _inst_3))) g (Finset.noncommProd.{u2, u3} α β _inst_1 s f comm)) (Finset.noncommProd.{u2, u4} α γ _inst_2 s (fun (i : α) => coeFn.{succ u1, max (succ u3) (succ u4)} F (fun (_x : F) => β -> γ) (FunLike.hasCoeToFun.{succ u1, succ u3, succ u4} F β (fun (_x : β) => γ) (MulHomClass.toFunLike.{u1, u3, u4} F β γ (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (MulOneClass.toHasMul.{u4} γ (Monoid.toMulOneClass.{u4} γ _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u4} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u4} γ _inst_2) _inst_3))) g (f i)) (fun (x : α) (hx : Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) x ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} α) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (Finset.Set.hasCoeT.{u2} α))) s)) (y : α) (hy : Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) y ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} α) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (Finset.Set.hasCoeT.{u2} α))) s)) (h : Ne.{succ u2} α x y) => Commute.map.{u1, u3, u4} F β γ (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (MulOneClass.toHasMul.{u4} γ (Monoid.toMulOneClass.{u4} γ _inst_2)) (f x) (f y) (MonoidHomClass.toMulHomClass.{u1, u3, u4} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u4} γ _inst_2) _inst_3) (Set.Pairwise.of_refl.{u2} α (fun (a : α) (b : α) => Commute.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (f a) (f b)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} α) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (Finset.Set.hasCoeT.{u2} α))) s) (Commute.on_isRefl.{u2, u3} α β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (fun (a : α) => f a)) comm x hx y hy) g))
but is expected to have type
  forall {F : Type.{u4}} {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Monoid.{u3} β] [_inst_2 : Monoid.{u2} γ] [_inst_3 : MonoidHomClass.{u4, u3, u2} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u2} γ _inst_2)] (s : Finset.{u1} α) (f : α -> β) (comm : Set.Pairwise.{u1} α (Finset.toSet.{u1} α s) (fun (a : α) (b : α) => Commute.{u3} β (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (f a) (f b))) (g : F), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : β) => γ) (Finset.noncommProd.{u1, u3} α β _inst_1 s f comm)) (FunLike.coe.{succ u4, succ u3, succ u2} F β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : β) => γ) _x) (MulHomClass.toFunLike.{u4, u3, u2} F β γ (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (MulOneClass.toMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_2)) (MonoidHomClass.toMulHomClass.{u4, u3, u2} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u2} γ _inst_2) _inst_3)) g (Finset.noncommProd.{u1, u3} α β _inst_1 s f comm)) (Finset.noncommProd.{u1, u2} α γ _inst_2 s (fun (i : α) => FunLike.coe.{succ u4, succ u3, succ u2} F β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : β) => γ) _x) (MulHomClass.toFunLike.{u4, u3, u2} F β γ (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (MulOneClass.toMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_2)) (MonoidHomClass.toMulHomClass.{u4, u3, u2} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u2} γ _inst_2) _inst_3)) g (f i)) (fun (x : α) (hx : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Finset.toSet.{u1} α s)) (y : α) (hy : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Finset.toSet.{u1} α s)) (h : Ne.{succ u1} α x y) => Commute.map.{u2, u3, u4} F β γ (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (MulOneClass.toMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_2)) (f x) (f y) (MonoidHomClass.toMulHomClass.{u4, u3, u2} F β γ (Monoid.toMulOneClass.{u3} β _inst_1) (Monoid.toMulOneClass.{u2} γ _inst_2) _inst_3) (Set.Pairwise.of_refl.{u1} α (fun (a : α) (b : α) => Commute.{u3} β (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (f a) (f b)) (Finset.toSet.{u1} α s) (Commute.on_isRefl.{u1, u3} α β (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β _inst_1)) (fun (a : α) => f a)) comm x hx y hy) g))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_map Finset.noncommProd_mapₓ'. -/
@[to_additive]
theorem noncommProd_map [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (comm) (g : F) :
    g (s.noncommProd f comm) =
      s.noncommProd (fun i => g (f i)) fun x hx y hy h => (comm.of_refl hx hy).map g :=
  by simp [noncomm_prod, Multiset.noncommProd_map]
#align finset.noncomm_prod_map Finset.noncommProd_map
#align finset.noncomm_sum_map Finset.noncommSum_map

/- warning: finset.noncomm_prod_eq_pow_card -> Finset.noncommProd_eq_pow_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (s : Finset.{u1} α) (f : α -> β) (comm : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))) (m : β), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) m)) -> (Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 s f comm) (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β _inst_1)) m (Finset.card.{u1} α s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (s : Finset.{u2} α) (f : α -> β) (comm : Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))) (m : β), (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Eq.{succ u1} β (f x) m)) -> (Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 s f comm) (HPow.hPow.{u1, 0, u1} β Nat β (instHPow.{u1, 0} β Nat (Monoid.Pow.{u1} β _inst_1)) m (Finset.card.{u2} α s)))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_eq_pow_card Finset.noncommProd_eq_pow_cardₓ'. -/
@[to_additive noncomm_sum_eq_card_nsmul]
theorem noncommProd_eq_pow_card (s : Finset α) (f : α → β) (comm) (m : β) (h : ∀ x ∈ s, f x = m) :
    s.noncommProd f comm = m ^ s.card :=
  by
  rw [noncomm_prod, Multiset.noncommProd_eq_pow_card _ _ m]
  simp only [Finset.card_def, Multiset.card_map]
  simpa using h
#align finset.noncomm_prod_eq_pow_card Finset.noncommProd_eq_pow_card
#align finset.noncomm_sum_eq_card_nsmul Finset.noncommSum_eq_card_nsmul

/- warning: finset.noncomm_prod_commute -> Finset.noncommProd_commute is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (s : Finset.{u1} α) (f : α -> β) (comm : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))) (y : β), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) y (f x))) -> (Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) y (Finset.noncommProd.{u1, u2} α β _inst_1 s f comm))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (s : Finset.{u2} α) (f : α -> β) (comm : Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))) (y : β), (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) y (f x))) -> (Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) y (Finset.noncommProd.{u2, u1} α β _inst_1 s f comm))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_commute Finset.noncommProd_commuteₓ'. -/
@[to_additive noncomm_sum_add_commute]
theorem noncommProd_commute (s : Finset α) (f : α → β) (comm) (y : β)
    (h : ∀ x ∈ s, Commute y (f x)) : Commute y (s.noncommProd f comm) :=
  by
  apply Multiset.noncommProd_commute
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx
#align finset.noncomm_prod_commute Finset.noncommProd_commute
#align finset.noncomm_sum_add_commute Finset.noncommSum_addCommute

#print Finset.noncommProd_eq_prod /-
@[to_additive]
theorem noncommProd_eq_prod {β : Type _} [CommMonoid β] (s : Finset α) (f : α → β) :
    (noncommProd s f fun _ _ _ _ _ => Commute.all _ _) = s.Prod f := by
  classical
    induction' s using Finset.induction_on with a s ha IH
    · simp
    · simp [ha, IH]
#align finset.noncomm_prod_eq_prod Finset.noncommProd_eq_prod
#align finset.noncomm_sum_eq_sum Finset.noncommSum_eq_sum
-/

/- warning: finset.noncomm_prod_union_of_disjoint -> Finset.noncommProd_union_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] [_inst_3 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (forall (f : α -> β) (comm : Set.Pairwise.{u1} α (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b))), Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t) f comm) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (Finset.noncommProd.{u1, u2} α β _inst_1 s f (Set.Pairwise.mono.{u1} α (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b)) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Iff.mpr (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.coe_subset.{u1} α s (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.subset_union_left.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s t)) comm)) (Finset.noncommProd.{u1, u2} α β _inst_1 t f (Set.Pairwise.mono.{u1} α (fun (a : α) (b : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f a) (f b)) (setOf.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) (Iff.mpr (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.coe_subset.{u1} α t (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.subset_union_right.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s t)) comm))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] [_inst_3 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {t : Finset.{u2} α}, (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s t) -> (forall (f : α -> β) (comm : Set.Pairwise.{u2} α (setOf.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b))), Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t) f comm) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (Finset.noncommProd.{u2, u1} α β _inst_1 s f (Set.Pairwise.mono.{u2} α (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b)) (Finset.toSet.{u2} α (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.toSet.{u2} α s) (Iff.mpr (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α s) (Finset.toSet.{u2} α (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.coe_subset.{u2} α s (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.subset_union_left.{u2} α (fun (a : α) (b : α) => _inst_3 a b) s t)) comm)) (Finset.noncommProd.{u2, u1} α β _inst_1 t f (Set.Pairwise.mono.{u2} α (fun (a : α) (b : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f a) (f b)) (Finset.toSet.{u2} α (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.toSet.{u2} α t) (Iff.mpr (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α t) (Finset.toSet.{u2} α (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t))) (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) t (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.coe_subset.{u2} α t (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s t)) (Finset.subset_union_right.{u2} α (fun (a : α) (b : α) => _inst_3 a b) s t)) comm))))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_union_of_disjoint Finset.noncommProd_union_of_disjointₓ'. -/
/-- The non-commutative version of `finset.prod_union` -/
@[to_additive "The non-commutative version of `finset.sum_union`"]
theorem noncommProd_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t)
    (f : α → β) (comm : { x | x ∈ s ∪ t }.Pairwise fun a b => Commute (f a) (f b)) :
    noncommProd (s ∪ t) f comm =
      noncommProd s f (comm.mono <| coe_subset.2 <| subset_union_left _ _) *
        noncommProd t f (comm.mono <| coe_subset.2 <| subset_union_right _ _) :=
  by
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t
  rw [List.disjoint_toFinset_iff_disjoint] at h
  simp [sl', tl', noncomm_prod_to_finset, ← List.prod_append, ← List.toFinset_append,
    sl'.append tl' h]
#align finset.noncomm_prod_union_of_disjoint Finset.noncommProd_union_of_disjoint
#align finset.noncomm_sum_union_of_disjoint Finset.noncommSum_union_of_disjoint

/- warning: finset.noncomm_prod_mul_distrib_aux -> Finset.noncommProd_mul_distrib_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] {s : Finset.{u1} α} {f : α -> β} {g : α -> β}, (Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (f y))) -> (Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (g y))) -> (Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (f y))) -> (Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)))) f g x) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)))) f g y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} {g : α -> β}, (Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (f y))) -> (Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (g y))) -> (Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (f y))) -> (Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)))) f g x) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)))) f g y)))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_mul_distrib_aux Finset.noncommProd_mul_distrib_auxₓ'. -/
@[protected, to_additive]
theorem noncommProd_mul_distrib_aux {s : Finset α} {f : α → β} {g : α → β}
    (comm_ff : (s : Set α).Pairwise fun x y => Commute (f x) (f y))
    (comm_gg : (s : Set α).Pairwise fun x y => Commute (g x) (g y))
    (comm_gf : (s : Set α).Pairwise fun x y => Commute (g x) (f y)) :
    (s : Set α).Pairwise fun x y => Commute ((f * g) x) ((f * g) y) :=
  by
  intro x hx y hy h
  apply Commute.mul_left <;> apply Commute.mul_right
  · exact comm_ff.of_refl hx hy
  · exact (comm_gf hy hx h.symm).symm
  · exact comm_gf hx hy h
  · exact comm_gg.of_refl hx hy
#align finset.noncomm_prod_mul_distrib_aux Finset.noncommProd_mul_distrib_aux
#align finset.noncomm_sum_add_distrib_aux Finset.noncommSum_add_distrib_aux

/- warning: finset.noncomm_prod_mul_distrib -> Finset.noncommProd_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] {s : Finset.{u1} α} (f : α -> β) (g : α -> β) (comm_ff : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (f x) (f y))) (comm_gg : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (g y))) (comm_gf : Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (fun (x : α) (y : α) => Commute.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)) (g x) (f y))), Eq.{succ u2} β (Finset.noncommProd.{u1, u2} α β _inst_1 s (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1)))) f g) (Finset.noncommProd_mul_distrib_aux.{u1, u2} α β _inst_1 s f g comm_ff comm_gg comm_gf)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (Finset.noncommProd.{u1, u2} α β _inst_1 s f comm_ff) (Finset.noncommProd.{u1, u2} α β _inst_1 s g comm_gg))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] {s : Finset.{u2} α} (f : α -> β) (g : α -> β) (comm_ff : Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (f x) (f y))) (comm_gg : Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (g y))) (comm_gf : Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (fun (x : α) (y : α) => Commute.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)) (g x) (f y))), Eq.{succ u1} β (Finset.noncommProd.{u2, u1} α β _inst_1 s (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1)))) f g) (Finset.noncommProd_mul_distrib_aux.{u1, u2} α β _inst_1 s f g comm_ff comm_gg comm_gf)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (Finset.noncommProd.{u2, u1} α β _inst_1 s f comm_ff) (Finset.noncommProd.{u2, u1} α β _inst_1 s g comm_gg))
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_mul_distrib Finset.noncommProd_mul_distribₓ'. -/
/-- The non-commutative version of `finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `finset.sum_add_distrib`"]
theorem noncommProd_mul_distrib {s : Finset α} (f : α → β) (g : α → β) (comm_ff comm_gg comm_gf) :
    noncommProd s (f * g) (noncommProd_mul_distrib_aux comm_ff comm_gg comm_gf) =
      noncommProd s f comm_ff * noncommProd s g comm_gg :=
  by
  classical
    induction' s using Finset.induction_on with x s hnmem ih
    · simp
    simp only [Finset.noncommProd_insert_of_not_mem _ _ _ _ hnmem]
    specialize
      ih (comm_ff.mono fun _ => mem_insert_of_mem) (comm_gg.mono fun _ => mem_insert_of_mem)
        (comm_gf.mono fun _ => mem_insert_of_mem)
    rw [ih, Pi.mul_apply]
    simp only [mul_assoc]
    congr 1
    simp only [← mul_assoc]
    congr 1
    refine' noncomm_prod_commute _ _ _ _ fun y hy => _
    exact comm_gf (mem_insert_self x s) (mem_insert_of_mem hy) (ne_of_mem_of_not_mem hy hnmem).symm
#align finset.noncomm_prod_mul_distrib Finset.noncommProd_mul_distrib
#align finset.noncomm_sum_add_distrib Finset.noncommSum_add_distrib

section FinitePi

variable {M : ι → Type _} [∀ i, Monoid (M i)]

/- warning: finset.noncomm_prod_mul_single -> Finset.noncommProd_mul_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : ι -> Type.{u2}} [_inst_3 : forall (i : ι), Monoid.{u2} (M i)] [_inst_4 : Fintype.{u1} ι] [_inst_5 : DecidableEq.{succ u1} ι] (x : forall (i : ι), M i), Eq.{succ (max u1 u2)} (forall (i : ι), M i) (Finset.noncommProd.{u1, max u1 u2} ι (forall (i : ι), M i) (Pi.monoid.{u1, u2} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_3 i)) (Finset.univ.{u1} ι _inst_4) (fun (i : ι) => Pi.mulSingle.{u1, u2} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => MulOneClass.toHasOne.{u2} (M i) (Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) i (x i)) (fun (i : ι) (_x : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) (Finset.univ.{u1} ι _inst_4))) (j : ι) (_x : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) j ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) (Finset.univ.{u1} ι _inst_4))) (_x : Ne.{succ u1} ι i j) => Pi.mulSingle_apply_commute.{u1, u2} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i)) x i j)) x
but is expected to have type
  forall {ι : Type.{u2}} {M : ι -> Type.{u1}} [_inst_3 : forall (i : ι), Monoid.{u1} (M i)] [_inst_4 : Fintype.{u2} ι] [_inst_5 : DecidableEq.{succ u2} ι] (x : forall (i : ι), M i), Eq.{max (succ u2) (succ u1)} (forall (i : ι), M i) (Finset.noncommProd.{u2, max u1 u2} ι (forall (i : ι), M i) (Pi.monoid.{u2, u1} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_3 i)) (Finset.univ.{u2} ι _inst_4) (fun (i : ι) => Pi.mulSingle.{u2, u1} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => Monoid.toOne.{u1} (M i) (_inst_3 i)) i (x i)) (fun (i : ι) (_x : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i (Finset.toSet.{u2} ι (Finset.univ.{u2} ι _inst_4))) (j : ι) (_x : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) j (Finset.toSet.{u2} ι (Finset.univ.{u2} ι _inst_4))) (_x : Ne.{succ u2} ι i j) => Pi.mulSingle_apply_commute.{u2, u1} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => Monoid.toMulOneClass.{u1} (M i) (_inst_3 i)) x i j)) x
Case conversion may be inaccurate. Consider using '#align finset.noncomm_prod_mul_single Finset.noncommProd_mul_singleₓ'. -/
@[to_additive]
theorem noncommProd_mul_single [Fintype ι] [DecidableEq ι] (x : ∀ i, M i) :
    (univ.noncommProd (fun i => Pi.mulSingle i (x i)) fun i _ j _ _ =>
        Pi.mulSingle_apply_commute x i j) =
      x :=
  by
  ext i
  apply (univ.noncomm_prod_map (fun i => MonoidHom.single M i (x i)) _ (Pi.evalMonoidHom M i)).trans
  rw [← insert_erase (mem_univ i), noncomm_prod_insert_of_not_mem' _ _ _ _ (not_mem_erase _ _),
    noncomm_prod_eq_pow_card, one_pow]
  · simp
  · intro i h
    simp at h
    simp [h]
#align finset.noncomm_prod_mul_single Finset.noncommProd_mul_single
#align finset.noncomm_sum_single Finset.noncommSum_single

/- warning: monoid_hom.pi_ext -> MonoidHom.pi_ext is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {γ : Type.{u2}} [_inst_2 : Monoid.{u2} γ] {M : ι -> Type.{u3}} [_inst_3 : forall (i : ι), Monoid.{u3} (M i)] [_inst_4 : Finite.{succ u1} ι] [_inst_5 : DecidableEq.{succ u1} ι] {f : MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)} {g : MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)}, (forall (i : ι) (x : M i), Eq.{succ u2} γ (coeFn.{max (succ u2) (succ (max u1 u3)), max (succ (max u1 u3)) (succ u2)} (MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) (fun (_x : MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) => (forall (i : ι), M i) -> γ) (MonoidHom.hasCoeToFun.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) f (Pi.mulSingle.{u1, u3} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => MulOneClass.toHasOne.{u3} (M i) (Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) i x)) (coeFn.{max (succ u2) (succ (max u1 u3)), max (succ (max u1 u3)) (succ u2)} (MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) (fun (_x : MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) => (forall (i : ι), M i) -> γ) (MonoidHom.hasCoeToFun.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) g (Pi.mulSingle.{u1, u3} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => MulOneClass.toHasOne.{u3} (M i) (Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) i x))) -> (Eq.{max (succ u2) (succ (max u1 u3))} (MonoidHom.{max u1 u3, u2} (forall (i : ι), M i) γ (Pi.mulOneClass.{u1, u3} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u3} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u2} γ _inst_2)) f g)
but is expected to have type
  forall {ι : Type.{u3}} {γ : Type.{u1}} [_inst_2 : Monoid.{u1} γ] {M : ι -> Type.{u2}} [_inst_3 : forall (i : ι), Monoid.{u2} (M i)] [_inst_4 : Finite.{succ u3} ι] [_inst_5 : DecidableEq.{succ u3} ι] {f : MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)} {g : MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)}, (forall (i : ι) (x : M i), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (i : ι), M i) => γ) (Pi.mulSingle.{u3, u2} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => Monoid.toOne.{u2} (M i) (_inst_3 i)) i x)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u3) (succ u2), succ u1} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) (forall (i : ι), M i) (fun (_x : forall (i : ι), M i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (i : ι), M i) => γ) _x) (MulHomClass.toFunLike.{max (max u3 u1) u2, max u3 u2, u1} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) (forall (i : ι), M i) γ (MulOneClass.toMul.{max u3 u2} (forall (i : ι), M i) (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i)))) (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_2)) (MonoidHomClass.toMulHomClass.{max (max u3 u1) u2, max u3 u2, u1} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2) (MonoidHom.monoidHomClass.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)))) f (Pi.mulSingle.{u3, u2} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => Monoid.toOne.{u2} (M i) (_inst_3 i)) i x)) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), max (succ u3) (succ u2), succ u1} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) (forall (i : ι), M i) (fun (_x : forall (i : ι), M i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (i : ι), M i) => γ) _x) (MulHomClass.toFunLike.{max (max u3 u1) u2, max u3 u2, u1} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) (forall (i : ι), M i) γ (MulOneClass.toMul.{max u3 u2} (forall (i : ι), M i) (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i)))) (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_2)) (MonoidHomClass.toMulHomClass.{max (max u3 u1) u2, max u3 u2, u1} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2) (MonoidHom.monoidHomClass.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)))) g (Pi.mulSingle.{u3, u2} ι (fun (i : ι) => M i) (fun (a : ι) (b : ι) => _inst_5 a b) (fun (i : ι) => Monoid.toOne.{u2} (M i) (_inst_3 i)) i x))) -> (Eq.{max (max (succ u3) (succ u1)) (succ u2)} (MonoidHom.{max u3 u2, u1} (forall (i : ι), M i) γ (Pi.mulOneClass.{u3, u2} ι (fun (i : ι) => M i) (fun (i : ι) => Monoid.toMulOneClass.{u2} (M i) (_inst_3 i))) (Monoid.toMulOneClass.{u1} γ _inst_2)) f g)
Case conversion may be inaccurate. Consider using '#align monoid_hom.pi_ext MonoidHom.pi_extₓ'. -/
@[to_additive]
theorem MonoidHom.pi_ext [Finite ι] [DecidableEq ι] {f g : (∀ i, M i) →* γ}
    (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g :=
  by
  cases nonempty_fintype ι
  ext x
  rw [← noncomm_prod_mul_single x, univ.noncomm_prod_map, univ.noncomm_prod_map]
  congr 1 with i; exact h i (x i)
#align monoid_hom.pi_ext MonoidHom.pi_ext
#align add_monoid_hom.pi_ext AddMonoidHom.pi_ext

end FinitePi

end Finset

