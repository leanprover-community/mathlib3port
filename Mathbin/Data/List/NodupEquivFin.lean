/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module data.list.nodup_equiv_fin
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Data.List.Sort
import Mathbin.Data.List.Duplicate

/-!
# Equivalence between `fin (length l)` and elements of a list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a list `l`,

* if `l` has no duplicates, then `list.nodup.nth_le_equiv` is the equivalence between
  `fin (length l)` and `{x // x ∈ l}` sending `⟨i, hi⟩` to `⟨nth_le l i hi, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨index_of x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `list.nodup.nth_le_equiv_of_forall_mem_list` defines an equivalence between
  `fin (length l)` and `α`;  if `α` does not have decidable equality, then
  there is a bijection `list.nodup.nth_le_bijection_of_forall_mem_list`;

* if `l` is sorted w.r.t. `(<)`, then `list.sorted.nth_le_iso` is the same bijection reinterpreted
  as an `order_iso`.

-/


namespace List

variable {α : Type _}

namespace Nodup

#print List.Nodup.getBijectionOfForallMemList /-
/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
a bijection `fin l.length → α`.  See `list.nodup.nth_le_equiv_of_forall_mem_list`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
def getBijectionOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) :
    { f : Fin l.length → α // Function.Bijective f } :=
  ⟨fun i => l.nthLe i i.property, fun i j h => Fin.ext <| (nd.nthLe_inj_iff _ _).1 h, fun x =>
    let ⟨i, hi, hl⟩ := List.mem_iff_nthLe.1 (h x)
    ⟨⟨i, hi⟩, hl⟩⟩
#align list.nodup.nth_le_bijection_of_forall_mem_list List.Nodup.getBijectionOfForallMemList
-/

variable [DecidableEq α]

#print List.Nodup.getEquiv /-
/-- If `l` has no duplicates, then `list.nth_le` defines an equivalence between `fin (length l)` and
the set of elements of `l`. -/
@[simps]
def getEquiv (l : List α) (H : Nodup l) : Fin (length l) ≃ { x // x ∈ l }
    where
  toFun i := ⟨nthLe l i i.2, nthLe_mem l i i.2⟩
  invFun x := ⟨indexOf (↑x) l, indexOf_lt_length.2 x.2⟩
  left_inv i := by simp [H]
  right_inv x := by simp
#align list.nodup.nth_le_equiv List.Nodup.getEquiv
-/

#print List.Nodup.getEquivOfForallMemList /-
/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
an equivalence between `fin l.length` and `α`.

See `list.nodup.nth_le_bijection_of_forall_mem_list` for a version without
decidable equality. -/
@[simps]
def getEquivOfForallMemList (l : List α) (nd : l.Nodup) (h : ∀ x : α, x ∈ l) : Fin l.length ≃ α
    where
  toFun i := l.nthLe i i.2
  invFun a := ⟨_, indexOf_lt_length.2 (h a)⟩
  left_inv i := by simp [nd]
  right_inv a := by simp
#align list.nodup.nth_le_equiv_of_forall_mem_list List.Nodup.getEquivOfForallMemList
-/

end Nodup

namespace Sorted

variable [Preorder α] {l : List α}

/- warning: list.sorted.nth_le_mono -> List.Sorted.get_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α}, (List.Sorted.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) l) -> (Monotone.{0, u1} (Fin (List.length.{u1} α l)) α (PartialOrder.toPreorder.{0} (Fin (List.length.{u1} α l)) (Fin.partialOrder (List.length.{u1} α l))) _inst_1 (fun (i : Fin (List.length.{u1} α l)) => List.nthLe.{u1} α l ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) i) (Fin.property (List.length.{u1} α l) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α}, (List.Sorted.{u1} α (fun (x._@.Mathlib.Data.List.NodupEquivFin._hyg.263 : α) (x._@.Mathlib.Data.List.NodupEquivFin._hyg.265 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Data.List.NodupEquivFin._hyg.263 x._@.Mathlib.Data.List.NodupEquivFin._hyg.265) l) -> (Monotone.{0, u1} (Fin (List.length.{u1} α l)) α (PartialOrder.toPreorder.{0} (Fin (List.length.{u1} α l)) (Fin.instPartialOrderFin (List.length.{u1} α l))) _inst_1 (List.get.{u1} α l))
Case conversion may be inaccurate. Consider using '#align list.sorted.nth_le_mono List.Sorted.get_monoₓ'. -/
theorem get_mono (h : l.Sorted (· ≤ ·)) : Monotone fun i : Fin l.length => l.nthLe i i.2 :=
  fun i j => h.rel_nthLe_of_le _ _
#align list.sorted.nth_le_mono List.Sorted.get_mono

/- warning: list.sorted.nth_le_strict_mono -> List.Sorted.get_strictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α}, (List.Sorted.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1)) l) -> (StrictMono.{0, u1} (Fin (List.length.{u1} α l)) α (PartialOrder.toPreorder.{0} (Fin (List.length.{u1} α l)) (Fin.partialOrder (List.length.{u1} α l))) _inst_1 (fun (i : Fin (List.length.{u1} α l)) => List.nthLe.{u1} α l ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) i) (Fin.property (List.length.{u1} α l) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α}, (List.Sorted.{u1} α (fun (x._@.Mathlib.Data.List.NodupEquivFin._hyg.298 : α) (x._@.Mathlib.Data.List.NodupEquivFin._hyg.300 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x._@.Mathlib.Data.List.NodupEquivFin._hyg.298 x._@.Mathlib.Data.List.NodupEquivFin._hyg.300) l) -> (StrictMono.{0, u1} (Fin (List.length.{u1} α l)) α (PartialOrder.toPreorder.{0} (Fin (List.length.{u1} α l)) (Fin.instPartialOrderFin (List.length.{u1} α l))) _inst_1 (List.get.{u1} α l))
Case conversion may be inaccurate. Consider using '#align list.sorted.nth_le_strict_mono List.Sorted.get_strictMonoₓ'. -/
theorem get_strictMono (h : l.Sorted (· < ·)) : StrictMono fun i : Fin l.length => l.nthLe i i.2 :=
  fun i j => h.rel_nthLe_of_lt _ _
#align list.sorted.nth_le_strict_mono List.Sorted.get_strictMono

variable [DecidableEq α]

#print List.Sorted.getIso /-
/-- If `l` is a list sorted w.r.t. `(<)`, then `list.nth_le` defines an order isomorphism between
`fin (length l)` and the set of elements of `l`. -/
def getIso (l : List α) (H : Sorted (· < ·) l) : Fin (length l) ≃o { x // x ∈ l }
    where
  toEquiv := H.Nodup.getEquiv l
  map_rel_iff' i j := H.get_strictMono.le_iff_le
#align list.sorted.nth_le_iso List.Sorted.getIso
-/

variable (H : Sorted (· < ·) l) {x : { x // x ∈ l }} {i : Fin l.length}

/- warning: list.sorted.coe_nth_le_iso_apply -> List.Sorted.coe_getIso_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] (H : List.Sorted.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1)) l) {i : Fin (List.length.{u1} α l)}, Eq.{succ u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l))))) (coeFn.{succ u1, succ u1} (OrderIso.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Fin.hasLe (List.length.{u1} α l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l))) (fun (_x : RelIso.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l))) (LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)))) => (Fin (List.length.{u1} α l)) -> (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l))) (RelIso.hasCoeToFun.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l))) (LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)))) (List.Sorted.getIso.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) l H) i)) (List.nthLe.{u1} α l ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) i) (Fin.property (List.length.{u1} α l) i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] (H : List.Sorted.{u1} α (fun (x._@.Mathlib.Data.List.NodupEquivFin._hyg.456 : α) (x._@.Mathlib.Data.List.NodupEquivFin._hyg.458 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x._@.Mathlib.Data.List.NodupEquivFin._hyg.456 x._@.Mathlib.Data.List.NodupEquivFin._hyg.458) l) {i : Fin (List.length.{u1} α l)}, Eq.{succ u1} α (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) (FunLike.coe.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l))) (Fin (List.length.{u1} α l)) (fun (_x : Fin (List.length.{u1} α l)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin (List.length.{u1} α l)) => Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) _x) (EmbeddingLike.toFunLike.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l))) (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Function.instEmbeddingLikeEmbedding.{1, succ u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)))) (RelEmbedding.toEmbedding.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (fun (a : Fin (List.length.{u1} α l)) (b : Fin (List.length.{u1} α l)) => LE.le.{0} (Fin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l)) a b) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) => LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Fin (List.length.{u1} α l)) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Fin (List.length.{u1} α l)) => LE.le.{0} (Fin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) => LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (List.Sorted.getIso.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) l H))) i)) (List.get.{u1} α l i)
Case conversion may be inaccurate. Consider using '#align list.sorted.coe_nth_le_iso_apply List.Sorted.coe_getIso_applyₓ'. -/
@[simp]
theorem coe_getIso_apply : (H.getIso l i : α) = nthLe l i i.2 :=
  rfl
#align list.sorted.coe_nth_le_iso_apply List.Sorted.coe_getIso_apply

/- warning: list.sorted.coe_nth_le_iso_symm_apply -> List.Sorted.coe_getIso_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] (H : List.Sorted.{u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1)) l) {x : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)}, Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) (coeFn.{succ u1, succ u1} (OrderIso.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Fin (List.length.{u1} α l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Fin.hasLe (List.length.{u1} α l))) (fun (_x : RelIso.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Fin (List.length.{u1} α l)) (LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l))) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l)))) => (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) -> (Fin (List.length.{u1} α l))) (RelIso.hasCoeToFun.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Fin (List.length.{u1} α l)) (LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l))) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l)))) (OrderIso.symm.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (Fin.hasLe (List.length.{u1} α l)) (Subtype.hasLe.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) (List.Sorted.getIso.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) l H)) x)) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l))))) x) l)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {l : List.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] (H : List.Sorted.{u1} α (fun (x._@.Mathlib.Data.List.NodupEquivFin._hyg.513 : α) (x._@.Mathlib.Data.List.NodupEquivFin._hyg.515 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_1) x._@.Mathlib.Data.List.NodupEquivFin._hyg.513 x._@.Mathlib.Data.List.NodupEquivFin._hyg.515) l) {x : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)}, Eq.{1} Nat (Fin.val (List.length.{u1} α l) (FunLike.coe.{succ u1, succ u1, 1} (Function.Embedding.{succ u1, 1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Fin (List.length.{u1} α l))) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (fun (_x : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) => Fin (List.length.{u1} α l)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, 1} (Function.Embedding.{succ u1, 1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Fin (List.length.{u1} α l))) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Fin (List.length.{u1} α l)) (Function.instEmbeddingLikeEmbedding.{succ u1, 1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Fin (List.length.{u1} α l)))) (RelEmbedding.toEmbedding.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Fin (List.length.{u1} α l)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) => LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin (List.length.{u1} α l)) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin (List.length.{u1} α l)) => LE.le.{0} (Fin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, 0} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Fin (List.length.{u1} α l)) (fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (b : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) => LE.le.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) a b) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Fin (List.length.{u1} α l)) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Fin (List.length.{u1} α l)) => LE.le.{0} (Fin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (OrderIso.symm.{0, u1} (Fin (List.length.{u1} α l)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (instLEFin (List.length.{u1} α l)) (Subtype.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l)) (List.Sorted.getIso.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) l H)))) x)) (List.indexOf.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) x) l)
Case conversion may be inaccurate. Consider using '#align list.sorted.coe_nth_le_iso_symm_apply List.Sorted.coe_getIso_symm_applyₓ'. -/
@[simp]
theorem coe_getIso_symm_apply : ((H.getIso l).symm x : ℕ) = indexOf (↑x) l :=
  rfl
#align list.sorted.coe_nth_le_iso_symm_apply List.Sorted.coe_getIso_symm_apply

end Sorted

section Sublist

/- warning: list.sublist_of_order_embedding_nth_eq -> List.sublist_of_orderEmbedding_get?_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {l' : List.{u1} α} (f : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe), (forall (ix : Nat), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α l ix) (List.get?.{u1} α l' (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) f ix))) -> (List.Sublist.{u1} α l l')
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {l' : List.{u1} α} (f : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat), (forall (ix : Nat), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α l ix) (List.get?.{u1} α l' (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) f) ix))) -> (List.Sublist.{u1} α l l')
Case conversion may be inaccurate. Consider using '#align list.sublist_of_order_embedding_nth_eq List.sublist_of_orderEmbedding_get?_eqₓ'. -/
/-- If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `sublist l l'`.
-/
theorem sublist_of_orderEmbedding_get?_eq {l l' : List α} (f : ℕ ↪o ℕ)
    (hf : ∀ ix : ℕ, l.get? ix = l'.get? (f ix)) : l <+ l' :=
  by
  induction' l with hd tl IH generalizing l' f
  · simp
  have : some hd = _ := hf 0
  rw [eq_comm, List.get?_eq_some'] at this
  obtain ⟨w, h⟩ := this
  let f' : ℕ ↪o ℕ :=
    OrderEmbedding.ofMapLeIff (fun i => f (i + 1) - (f 0 + 1)) fun a b => by
      simp [tsub_le_tsub_iff_right, Nat.succ_le_iff, Nat.lt_succ_iff]
  have : ∀ ix, tl.nth ix = (l'.drop (f 0 + 1)).get? (f' ix) :=
    by
    intro ix
    simp [List.get?_drop, add_tsub_cancel_of_le, Nat.succ_le_iff, ← hf]
  rw [← List.take_append_drop (f 0 + 1) l', ← List.singleton_append]
  apply List.Sublist.append _ (IH _ this)
  rw [List.singleton_sublist, ← h, l'.nth_le_take _ (Nat.lt_succ_self _)]
  apply List.nthLe_mem
#align list.sublist_of_order_embedding_nth_eq List.sublist_of_orderEmbedding_get?_eq

/- warning: list.sublist_iff_exists_order_embedding_nth_eq -> List.sublist_iff_exists_orderEmbedding_get?_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {l' : List.{u1} α}, Iff (List.Sublist.{u1} α l l') (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (f : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => forall (ix : Nat), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α l ix) (List.get?.{u1} α l' (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) f ix))))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {l' : List.{u1} α}, Iff (List.Sublist.{u1} α l l') (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (f : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => forall (ix : Nat), Eq.{succ u1} (Option.{u1} α) (List.get?.{u1} α l ix) (List.get?.{u1} α l' (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) f) ix))))
Case conversion may be inaccurate. Consider using '#align list.sublist_iff_exists_order_embedding_nth_eq List.sublist_iff_exists_orderEmbedding_get?_eqₓ'. -/
/-- A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_orderEmbedding_get?_eq {l l' : List α} :
    l <+ l' ↔ ∃ f : ℕ ↪o ℕ, ∀ ix : ℕ, l.get? ix = l'.get? (f ix) :=
  by
  constructor
  · intro H
    induction' H with xs ys y H IH xs ys x H IH
    · simp
    · obtain ⟨f, hf⟩ := IH
      refine' ⟨f.trans (OrderEmbedding.ofStrictMono (· + 1) fun _ => by simp), _⟩
      simpa using hf
    · obtain ⟨f, hf⟩ := IH
      refine'
        ⟨OrderEmbedding.ofMapLeIff (fun ix : ℕ => if ix = 0 then 0 else (f ix.pred).succ) _, _⟩
      · rintro ⟨_ | a⟩ ⟨_ | b⟩ <;> simp [Nat.succ_le_succ_iff]
      · rintro ⟨_ | i⟩
        · simp
        · simpa using hf _
  · rintro ⟨f, hf⟩
    exact sublist_of_order_embedding_nth_eq f hf
#align list.sublist_iff_exists_order_embedding_nth_eq List.sublist_iff_exists_orderEmbedding_get?_eq

/- warning: list.sublist_iff_exists_fin_order_embedding_nth_le_eq -> List.sublist_iff_exists_fin_orderEmbedding_get_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α} {l' : List.{u1} α}, Iff (List.Sublist.{u1} α l l') (Exists.{1} (OrderEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l'))) (fun (f : OrderEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l'))) => forall (ix : Fin (List.length.{u1} α l)), Eq.{succ u1} α (List.nthLe.{u1} α l ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) ix) (Fin.is_lt (List.length.{u1} α l) ix)) (List.nthLe.{u1} α l' ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l')) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l')) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l')) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l')) Nat (Fin.coeToNat (List.length.{u1} α l'))))) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l'))) (fun (_x : RelEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l))) (LE.le.{0} (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l')))) => (Fin (List.length.{u1} α l)) -> (Fin (List.length.{u1} α l'))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l))) (LE.le.{0} (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l')))) f ix)) (Fin.is_lt (List.length.{u1} α l') (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l'))) (fun (_x : RelEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l))) (LE.le.{0} (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l')))) => (Fin (List.length.{u1} α l)) -> (Fin (List.length.{u1} α l'))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (LE.le.{0} (Fin (List.length.{u1} α l)) (Fin.hasLe (List.length.{u1} α l))) (LE.le.{0} (Fin (List.length.{u1} α l')) (Fin.hasLe (List.length.{u1} α l')))) f ix)))))
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α} {l' : List.{u1} α}, Iff (List.Sublist.{u1} α l l') (Exists.{1} (OrderEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (instLEFin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l'))) (fun (f : OrderEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (instLEFin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l'))) => forall (ix : Fin (List.length.{u1} α l)), Eq.{succ u1} α (List.get.{u1} α l ix) (List.get.{u1} α l' (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l'))) (Fin (List.length.{u1} α l)) (fun (a : Fin (List.length.{u1} α l)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin (List.length.{u1} α l)) => Fin (List.length.{u1} α l')) a) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l'))) (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')))) (RelEmbedding.toEmbedding.{0, 0} (Fin (List.length.{u1} α l)) (Fin (List.length.{u1} α l')) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin (List.length.{u1} α l)) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin (List.length.{u1} α l)) => LE.le.{0} (Fin (List.length.{u1} α l)) (instLEFin (List.length.{u1} α l)) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (List.length.{u1} α l')) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (List.length.{u1} α l')) => LE.le.{0} (Fin (List.length.{u1} α l')) (instLEFin (List.length.{u1} α l')) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) f) ix))))
Case conversion may be inaccurate. Consider using '#align list.sublist_iff_exists_fin_order_embedding_nth_le_eq List.sublist_iff_exists_fin_orderEmbedding_get_eqₓ'. -/
/-- A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `fin l.length` into `fin l'.length` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
theorem sublist_iff_exists_fin_orderEmbedding_get_eq {l l' : List α} :
    l <+ l' ↔
      ∃ f : Fin l.length ↪o Fin l'.length,
        ∀ ix : Fin l.length, l.nthLe ix ix.is_lt = l'.nthLe (f ix) (f ix).is_lt :=
  by
  rw [sublist_iff_exists_order_embedding_nth_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h : ∀ {i : ℕ} (h : i < l.length), f i < l'.length :=
      by
      intro i hi
      specialize hf i
      rw [nth_le_nth hi, eq_comm, nth_eq_some] at hf
      obtain ⟨h, -⟩ := hf
      exact h
    refine' ⟨OrderEmbedding.ofMapLeIff (fun ix => ⟨f ix, h ix.is_lt⟩) _, _⟩
    · simp
    · intro i
      apply Option.some_injective
      simpa [← nth_le_nth] using hf _
  · rintro ⟨f, hf⟩
    refine'
      ⟨OrderEmbedding.ofStrictMono (fun i => if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length)
          _,
        _⟩
    · intro i j h
      dsimp only
      split_ifs with hi hj hj hi
      · simpa using h
      · rw [add_comm]
        exact lt_add_of_lt_of_pos (Fin.is_lt _) (i.zero_le.trans_lt h)
      · exact absurd (h.trans hj) hi
      · simpa using h
    · intro i
      simp only [OrderEmbedding.coe_ofStrictMono]
      split_ifs with hi
      · rw [nth_le_nth hi, nth_le_nth, ← hf]
        simp
      · rw [nth_len_le, nth_len_le]
        · simp
        · simpa using hi
#align list.sublist_iff_exists_fin_order_embedding_nth_le_eq List.sublist_iff_exists_fin_orderEmbedding_get_eq

#print List.duplicate_iff_exists_distinct_nthLe /-
/-- An element `x : α` of `l : list α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
theorem duplicate_iff_exists_distinct_nthLe {l : List α} {x : α} :
    l.Duplicate x ↔
      ∃ (n : ℕ)(hn : n < l.length)(m : ℕ)(hm : m < l.length)(h : n < m),
        x = l.nthLe n hn ∧ x = l.nthLe m hm :=
  by
  classical
    rw [duplicate_iff_two_le_count, le_count_iff_replicate_sublist,
      sublist_iff_exists_fin_order_embedding_nth_le_eq]
    constructor
    · rintro ⟨f, hf⟩
      refine' ⟨f ⟨0, by simp⟩, Fin.is_lt _, f ⟨1, by simp⟩, Fin.is_lt _, by simp, _, _⟩
      · simpa using hf ⟨0, by simp⟩
      · simpa using hf ⟨1, by simp⟩
    · rintro ⟨n, hn, m, hm, hnm, h, h'⟩
      refine' ⟨OrderEmbedding.ofStrictMono (fun i => if (i : ℕ) = 0 then ⟨n, hn⟩ else ⟨m, hm⟩) _, _⟩
      · rintro ⟨⟨_ | i⟩, hi⟩ ⟨⟨_ | j⟩, hj⟩
        · simp
        · simp [hnm]
        · simp
        · simp only [Nat.lt_succ_iff, Nat.succ_le_succ_iff, replicate, length,
            nonpos_iff_eq_zero] at hi hj
          simp [hi, hj]
      · rintro ⟨⟨_ | i⟩, hi⟩
        · simpa using h
        · simpa using h'
#align list.duplicate_iff_exists_distinct_nth_le List.duplicate_iff_exists_distinct_nthLe
-/

end Sublist

end List

