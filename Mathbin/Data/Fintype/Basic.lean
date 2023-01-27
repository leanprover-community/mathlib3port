/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.basic
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Image

/-!
# Finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a typeclass to state that a type is finite.

## Main declarations

* `fintype α`:  Typeclass saying that a type is finite. It takes as fields a `finset` and a proof
  that all terms of type `α` are in it.
* `finset.univ`: The finset of all elements of a fintype.

See `data.fintype.card` for the cardinality of a fintype,
the equivalence with `fin (fintype.card α)`, and pigeonhole principles.

## Instances

Instances for `fintype` for
* `{x // p x}` are in this file as `fintype.subtype`
* `option α` are in `data.fintype.option`
* `α × β` are in `data.fintype.prod`
* `α ⊕ β` are in `data.fintype.sum`
* `Σ (a : α), β a` are in `data.fintype.sigma`

These files also contain appropriate `infinite` instances for these types.

`infinite` instances for `ℕ`, `ℤ`, `multiset α`, and `list α` are in `data.fintype.lattice`.

Types which have a surjection from/an injection to a `fintype` are themselves fintypes.
See `fintype.of_injective` and `fintype.of_surjective`.
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

#print Fintype /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`elems] [] -/
/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type _) where
  elems : Finset α
  complete : ∀ x : α, x ∈ elems
#align fintype Fintype
-/

namespace Finset

variable [Fintype α] {s t : Finset α}

#print Finset.univ /-
/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : Finset α :=
  Fintype.elems α
#align finset.univ Finset.univ
-/

#print Finset.mem_univ /-
@[simp]
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x
#align finset.mem_univ Finset.mem_univ
-/

#print Finset.mem_univ_val /-
@[simp]
theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 :=
  mem_univ
#align finset.mem_univ_val Finset.mem_univ_val
-/

#print Finset.eq_univ_iff_forall /-
theorem eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by simp [ext_iff]
#align finset.eq_univ_iff_forall Finset.eq_univ_iff_forall
-/

#print Finset.eq_univ_of_forall /-
theorem eq_univ_of_forall : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2
#align finset.eq_univ_of_forall Finset.eq_univ_of_forall
-/

#print Finset.coe_univ /-
@[simp, norm_cast]
theorem coe_univ : ↑(univ : Finset α) = (Set.univ : Set α) := by ext <;> simp
#align finset.coe_univ Finset.coe_univ
-/

#print Finset.coe_eq_univ /-
@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = Set.univ ↔ s = univ := by rw [← coe_univ, coe_inj]
#align finset.coe_eq_univ Finset.coe_eq_univ
-/

#print Finset.Nonempty.eq_univ /-
theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ :=
  by
  rintro ⟨x, hx⟩
  refine' eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
#align finset.nonempty.eq_univ Finset.Nonempty.eq_univ
-/

#print Finset.univ_nonempty_iff /-
theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]
#align finset.univ_nonempty_iff Finset.univ_nonempty_iff
-/

#print Finset.univ_nonempty /-
theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›
#align finset.univ_nonempty Finset.univ_nonempty
-/

#print Finset.univ_eq_empty_iff /-
theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]
#align finset.univ_eq_empty_iff Finset.univ_eq_empty_iff
-/

#print Finset.univ_eq_empty /-
@[simp]
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›
#align finset.univ_eq_empty Finset.univ_eq_empty
-/

#print Finset.univ_unique /-
@[simp]
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
  Finset.ext fun x => iff_of_true (mem_univ _) <| mem_singleton.2 <| Subsingleton.elim x default
#align finset.univ_unique Finset.univ_unique
-/

#print Finset.subset_univ /-
@[simp]
theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a
#align finset.subset_univ Finset.subset_univ
-/

instance : BoundedOrder (Finset α) :=
  { Finset.orderBot with
    top := univ
    le_top := subset_univ }

/- warning: finset.top_eq_univ -> Finset.top_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} α) (Top.top.{u1} (Finset.{u1} α) (OrderTop.toHasTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.boundedOrder.{u1} α _inst_1)))) (Finset.univ.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} α) (Top.top.{u1} (Finset.{u1} α) (OrderTop.toTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.instBoundedOrderFinsetToLEToPreorderPartialOrder.{u1} α _inst_1)))) (Finset.univ.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align finset.top_eq_univ Finset.top_eq_univₓ'. -/
@[simp]
theorem top_eq_univ : (⊤ : Finset α) = univ :=
  rfl
#align finset.top_eq_univ Finset.top_eq_univ

#print Finset.ssubset_univ_iff /-
theorem ssubset_univ_iff {s : Finset α} : s ⊂ univ ↔ s ≠ univ :=
  @lt_top_iff_ne_top _ _ _ s
#align finset.ssubset_univ_iff Finset.ssubset_univ_iff
-/

/- warning: finset.codisjoint_left -> Finset.codisjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Codisjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.boundedOrder.{u1} α _inst_1)) s t) (forall {{a : α}}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Codisjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.instBoundedOrderFinsetToLEToPreorderPartialOrder.{u1} α _inst_1)) s t) (forall {{a : α}}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t))
Case conversion may be inaccurate. Consider using '#align finset.codisjoint_left Finset.codisjoint_leftₓ'. -/
theorem codisjoint_left : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ s → a ∈ t := by
  classical simp [codisjoint_iff, eq_univ_iff_forall, or_iff_not_imp_left]
#align finset.codisjoint_left Finset.codisjoint_left

/- warning: finset.codisjoint_right -> Finset.codisjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Codisjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.boundedOrder.{u1} α _inst_1)) s t) (forall {{a : α}}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t)) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Codisjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.instBoundedOrderFinsetToLEToPreorderPartialOrder.{u1} α _inst_1)) s t) (forall {{a : α}}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t)) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.codisjoint_right Finset.codisjoint_rightₓ'. -/
theorem codisjoint_right : Codisjoint s t ↔ ∀ ⦃a⦄, a ∉ t → a ∈ s :=
  Codisjoint_comm.trans codisjoint_left
#align finset.codisjoint_right Finset.codisjoint_right

section BooleanAlgebra

variable [DecidableEq α] {a : α}

instance : BooleanAlgebra (Finset α) :=
  GeneralizedBooleanAlgebra.toBooleanAlgebra

/- warning: finset.sdiff_eq_inter_compl -> Finset.sdiff_eq_inter_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) t))
Case conversion may be inaccurate. Consider using '#align finset.sdiff_eq_inter_compl Finset.sdiff_eq_inter_complₓ'. -/
theorem sdiff_eq_inter_compl (s t : Finset α) : s \ t = s ∩ tᶜ :=
  sdiff_eq
#align finset.sdiff_eq_inter_compl Finset.sdiff_eq_inter_compl

/- warning: finset.compl_eq_univ_sdiff -> Finset.compl_eq_univ_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.univ.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.univ.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align finset.compl_eq_univ_sdiff Finset.compl_eq_univ_sdiffₓ'. -/
theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl
#align finset.compl_eq_univ_sdiff Finset.compl_eq_univ_sdiff

/- warning: finset.mem_compl -> Finset.mem_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.mem_compl Finset.mem_complₓ'. -/
@[simp]
theorem mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]
#align finset.mem_compl Finset.mem_compl

/- warning: finset.not_mem_compl -> Finset.not_mem_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Iff (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Iff (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align finset.not_mem_compl Finset.not_mem_complₓ'. -/
theorem not_mem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]
#align finset.not_mem_compl Finset.not_mem_compl

/- warning: finset.coe_compl -> Finset.coe_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.coe_compl Finset.coe_complₓ'. -/
@[simp, norm_cast]
theorem coe_compl (s : Finset α) : ↑(sᶜ) = (↑s : Set α)ᶜ :=
  Set.ext fun x => mem_compl
#align finset.coe_compl Finset.coe_compl

/- warning: finset.compl_empty -> Finset.compl_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α], Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Finset.univ.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α], Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (Finset.univ.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align finset.compl_empty Finset.compl_emptyₓ'. -/
@[simp]
theorem compl_empty : (∅ : Finset α)ᶜ = univ :=
  compl_bot
#align finset.compl_empty Finset.compl_empty

/- warning: finset.compl_univ -> Finset.compl_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α], Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Finset.univ.{u1} α _inst_1)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α], Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Finset.univ.{u1} α _inst_1)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.compl_univ Finset.compl_univₓ'. -/
@[simp]
theorem compl_univ : (univ : Finset α)ᶜ = ∅ :=
  compl_top
#align finset.compl_univ Finset.compl_univ

/- warning: finset.compl_eq_empty_iff -> Finset.compl_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Eq.{succ u1} (Finset.{u1} α) s (Finset.univ.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (Eq.{succ u1} (Finset.{u1} α) s (Finset.univ.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align finset.compl_eq_empty_iff Finset.compl_eq_empty_iffₓ'. -/
@[simp]
theorem compl_eq_empty_iff (s : Finset α) : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot
#align finset.compl_eq_empty_iff Finset.compl_eq_empty_iff

/- warning: finset.compl_eq_univ_iff -> Finset.compl_eq_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (Finset.univ.{u1} α _inst_1)) (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (Finset.univ.{u1} α _inst_1)) (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align finset.compl_eq_univ_iff Finset.compl_eq_univ_iffₓ'. -/
@[simp]
theorem compl_eq_univ_iff (s : Finset α) : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top
#align finset.compl_eq_univ_iff Finset.compl_eq_univ_iff

/- warning: finset.union_compl -> Finset.union_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (Finset.univ.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (Finset.univ.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align finset.union_compl Finset.union_complₓ'. -/
@[simp]
theorem union_compl (s : Finset α) : s ∪ sᶜ = univ :=
  sup_compl_eq_top
#align finset.union_compl Finset.union_compl

/- warning: finset.inter_compl -> Finset.inter_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.inter_compl Finset.inter_complₓ'. -/
@[simp]
theorem inter_compl (s : Finset α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot
#align finset.inter_compl Finset.inter_compl

/- warning: finset.compl_union -> Finset.compl_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) t))
Case conversion may be inaccurate. Consider using '#align finset.compl_union Finset.compl_unionₓ'. -/
@[simp]
theorem compl_union (s t : Finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup
#align finset.compl_union Finset.compl_union

/- warning: finset.compl_inter -> Finset.compl_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) t))
Case conversion may be inaccurate. Consider using '#align finset.compl_inter Finset.compl_interₓ'. -/
@[simp]
theorem compl_inter (s t : Finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf
#align finset.compl_inter Finset.compl_inter

/- warning: finset.compl_erase -> Finset.compl_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a)) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a)) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))
Case conversion may be inaccurate. Consider using '#align finset.compl_erase Finset.compl_eraseₓ'. -/
@[simp]
theorem compl_erase : s.erase aᶜ = insert a (sᶜ) :=
  by
  ext
  simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase]
#align finset.compl_erase Finset.compl_erase

/- warning: finset.compl_insert -> Finset.compl_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Finset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) a)
Case conversion may be inaccurate. Consider using '#align finset.compl_insert Finset.compl_insertₓ'. -/
@[simp]
theorem compl_insert : insert a sᶜ = sᶜ.erase a :=
  by
  ext
  simp only [not_or, mem_insert, iff_self_iff, mem_compl, mem_erase]
#align finset.compl_insert Finset.compl_insert

/- warning: finset.insert_compl_self -> Finset.insert_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (x : α), Eq.{succ u1} (Finset.{u1} α) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) x (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) x))) (Finset.univ.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (x : α), Eq.{succ u1} (Finset.{u1} α) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) x (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) x))) (Finset.univ.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align finset.insert_compl_self Finset.insert_compl_selfₓ'. -/
@[simp]
theorem insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ := by
  rw [← compl_erase, erase_singleton, compl_empty]
#align finset.insert_compl_self Finset.insert_compl_self

/- warning: finset.compl_filter -> Finset.compl_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (p : α -> Prop) [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : forall (x : α), Decidable (Not (p x))], Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) (Finset.univ.{u1} α _inst_1))) (Finset.filter.{u1} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_4 a) (Finset.univ.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (p : α -> Prop) [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : forall (x : α), Decidable (Not (p x))], Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) (Finset.univ.{u1} α _inst_1))) (Finset.filter.{u1} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_4 a) (Finset.univ.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align finset.compl_filter Finset.compl_filterₓ'. -/
@[simp]
theorem compl_filter (p : α → Prop) [DecidablePred p] [∀ x, Decidable ¬p x] :
    univ.filter pᶜ = univ.filter fun x => ¬p x :=
  (filter_not _ _).symm
#align finset.compl_filter Finset.compl_filter

/- warning: finset.compl_ne_univ_iff_nonempty -> Finset.compl_ne_univ_iff_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (Ne.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (Finset.univ.{u1} α _inst_1)) (Finset.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Iff (Ne.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) (Finset.univ.{u1} α _inst_1)) (Finset.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.compl_ne_univ_iff_nonempty Finset.compl_ne_univ_iff_nonemptyₓ'. -/
theorem compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ ≠ univ ↔ s.Nonempty := by
  simp [eq_univ_iff_forall, Finset.Nonempty]
#align finset.compl_ne_univ_iff_nonempty Finset.compl_ne_univ_iff_nonempty

/- warning: finset.compl_singleton -> Finset.compl_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (a : α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Finset.univ.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (a : α), Eq.{succ u1} (Finset.{u1} α) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Finset.univ.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align finset.compl_singleton Finset.compl_singletonₓ'. -/
theorem compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a := by
  rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]
#align finset.compl_singleton Finset.compl_singleton

/- warning: finset.insert_inj_on' -> Finset.insert_inj_on' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Set.InjOn.{u1, u1} α (Finset.{u1} α) (fun (a : α) => Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Set.InjOn.{u1, u1} α (Finset.{u1} α) (fun (a : α) => Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (Finset.toSet.{u1} α (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))
Case conversion may be inaccurate. Consider using '#align finset.insert_inj_on' Finset.insert_inj_on'ₓ'. -/
theorem insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Finset α) :=
  by
  rw [coe_compl]
  exact s.insert_inj_on
#align finset.insert_inj_on' Finset.insert_inj_on'

#print Finset.image_univ_of_surjective /-
theorem image_univ_of_surjective [Fintype β] {f : β → α} (hf : Surjective f) :
    univ.image f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_image_of_mem _ <| mem_univ _
#align finset.image_univ_of_surjective Finset.image_univ_of_surjective
-/

end BooleanAlgebra

#print Finset.map_univ_of_surjective /-
theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_map_of_mem _ <| mem_univ _
#align finset.map_univ_of_surjective Finset.map_univ_of_surjective
-/

#print Finset.map_univ_equiv /-
@[simp]
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.Surjective
#align finset.map_univ_equiv Finset.map_univ_equiv
-/

#print Finset.univ_inter /-
@[simp]
theorem univ_inter [DecidableEq α] (s : Finset α) : univ ∩ s = s :=
  ext fun a => by simp
#align finset.univ_inter Finset.univ_inter
-/

#print Finset.inter_univ /-
@[simp]
theorem inter_univ [DecidableEq α] (s : Finset α) : s ∩ univ = s := by rw [inter_comm, univ_inter]
#align finset.inter_univ Finset.inter_univ
-/

/- warning: finset.piecewise_univ -> Finset.piecewise_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Finset.univ.{u1} α _inst_1))] {δ : α -> Sort.{u2}} (f : forall (i : α), δ i) (g : forall (i : α), δ i), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (Finset.univ.{u1} α _inst_1) f g (fun (j : α) => _inst_2 j)) f
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Fintype.{u2} α] [_inst_2 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Finset.univ.{u2} α _inst_1))] {δ : α -> Sort.{u1}} (f : forall (i : α), δ i) (g : forall (i : α), δ i), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (Finset.univ.{u2} α _inst_1) f g (fun (j : α) => _inst_2 j)) f
Case conversion may be inaccurate. Consider using '#align finset.piecewise_univ Finset.piecewise_univₓ'. -/
@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (univ : Finset α))] {δ : α → Sort _}
    (f g : ∀ i, δ i) : univ.piecewise f g = f :=
  by
  ext i
  simp [piecewise]
#align finset.piecewise_univ Finset.piecewise_univ

/- warning: finset.piecewise_compl -> Finset.piecewise_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) [_inst_3 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s)] [_inst_4 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))] {δ : α -> Sort.{u2}} (f : forall (i : α), δ i) (g : forall (i : α), δ i), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) f g (fun (j : α) => _inst_4 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s g f (fun (j : α) => _inst_3 j))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) [_inst_3 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s)] [_inst_4 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.instBooleanAlgebraFinset.{u2} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s))] {δ : α -> Sort.{u1}} (f : forall (i : α), δ i) (g : forall (i : α), δ i), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.instBooleanAlgebraFinset.{u2} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s) f g (fun (j : α) => _inst_4 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s g f (fun (j : α) => _inst_3 j))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_compl Finset.piecewise_complₓ'. -/
theorem piecewise_compl [DecidableEq α] (s : Finset α) [∀ i : α, Decidable (i ∈ s)]
    [∀ i : α, Decidable (i ∈ sᶜ)] {δ : α → Sort _} (f g : ∀ i, δ i) :
    sᶜ.piecewise f g = s.piecewise g f := by
  ext i
  simp [piecewise]
#align finset.piecewise_compl Finset.piecewise_compl

#print Finset.piecewise_erase_univ /-
@[simp]
theorem piecewise_erase_univ {δ : α → Sort _} [DecidableEq α] (a : α) (f g : ∀ a, δ a) :
    (Finset.univ.erase a).piecewise f g = Function.update f a (g a) := by
  rw [← compl_singleton, piecewise_compl, piecewise_singleton]
#align finset.piecewise_erase_univ Finset.piecewise_erase_univ
-/

/- warning: finset.univ_map_equiv_to_embedding -> Finset.univ_map_equiv_to_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Fintype.{u1} α] [_inst_3 : Fintype.{u2} β] (e : Equiv.{succ u1, succ u2} α β), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β (Equiv.toEmbedding.{succ u1, succ u2} α β e) (Finset.univ.{u1} α _inst_2)) (Finset.univ.{u2} β _inst_3)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : Fintype.{u2} α] [_inst_3 : Fintype.{u1} β] (e : Equiv.{succ u2, succ u1} α β), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β (Equiv.toEmbedding.{succ u2, succ u1} α β e) (Finset.univ.{u2} α _inst_2)) (Finset.univ.{u1} β _inst_3)
Case conversion may be inaccurate. Consider using '#align finset.univ_map_equiv_to_embedding Finset.univ_map_equiv_to_embeddingₓ'. -/
theorem univ_map_equiv_to_embedding {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) :
    univ.map e.toEmbedding = univ :=
  eq_univ_iff_forall.mpr fun b => mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩
#align finset.univ_map_equiv_to_embedding Finset.univ_map_equiv_to_embedding

#print Finset.univ_filter_exists /-
@[simp]
theorem univ_filter_exists (f : α → β) [Fintype β] [DecidablePred fun y => ∃ x, f x = y]
    [DecidableEq β] : (Finset.univ.filter fun y => ∃ x, f x = y) = Finset.univ.image f :=
  by
  ext
  simp
#align finset.univ_filter_exists Finset.univ_filter_exists
-/

#print Finset.univ_filter_mem_range /-
/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
theorem univ_filter_mem_range (f : α → β) [Fintype β] [DecidablePred fun y => y ∈ Set.range f]
    [DecidableEq β] : (Finset.univ.filter fun y => y ∈ Set.range f) = Finset.univ.image f :=
  univ_filter_exists f
#align finset.univ_filter_mem_range Finset.univ_filter_mem_range
-/

#print Finset.coe_filter_univ /-
theorem coe_filter_univ (p : α → Prop) [DecidablePred p] : (univ.filter p : Set α) = { x | p x } :=
  by rw [coe_filter, coe_univ, Set.sep_univ]
#align finset.coe_filter_univ Finset.coe_filter_univ
-/

end Finset

open Finset Function

namespace Fintype

#print Fintype.decidablePiFintype /-
instance decidablePiFintype {α} {β : α → Type _} [∀ a, DecidableEq (β a)] [Fintype α] :
    DecidableEq (∀ a, β a) := fun f g =>
  decidable_of_iff (∀ a ∈ Fintype.elems α, f a = g a)
    (by simp [Function.funext_iff, Fintype.complete])
#align fintype.decidable_pi_fintype Fintype.decidablePiFintype
-/

#print Fintype.decidableForallFintype /-
instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∀ a, p a) :=
  decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)
#align fintype.decidable_forall_fintype Fintype.decidableForallFintype
-/

#print Fintype.decidableExistsFintype /-
instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)
#align fintype.decidable_exists_fintype Fintype.decidableExistsFintype
-/

#print Fintype.decidableMemRangeFintype /-
instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α → β) :
    DecidablePred (· ∈ Set.range f) := fun x => Fintype.decidableExistsFintype
#align fintype.decidable_mem_range_fintype Fintype.decidableMemRangeFintype
-/

section BundledHoms

#print Fintype.decidableEqEquivFintype /-
instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidable_of_iff (a.1 = b.1) Equiv.coeFn_injective.eq_iff
#align fintype.decidable_eq_equiv_fintype Fintype.decidableEqEquivFintype
-/

#print Fintype.decidableEqEmbeddingFintype /-
instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff
#align fintype.decidable_eq_embedding_fintype Fintype.decidableEqEmbeddingFintype
-/

#print Fintype.decidableEqOneHomFintype /-
@[to_additive]
instance decidableEqOneHomFintype [DecidableEq β] [Fintype α] [One α] [One β] :
    DecidableEq (OneHom α β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff OneHom.coe_inj)
#align fintype.decidable_eq_one_hom_fintype Fintype.decidableEqOneHomFintype
#align fintype.decidable_eq_zero_hom_fintype Fintype.decidableEqZeroHomFintype
-/

#print Fintype.decidableEqMulHomFintype /-
@[to_additive]
instance decidableEqMulHomFintype [DecidableEq β] [Fintype α] [Mul α] [Mul β] :
    DecidableEq (α →ₙ* β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff MulHom.coe_inj)
#align fintype.decidable_eq_mul_hom_fintype Fintype.decidableEqMulHomFintype
#align fintype.decidable_eq_add_hom_fintype Fintype.decidableEqAddHomFintype
-/

#print Fintype.decidableEqMonoidHomFintype /-
@[to_additive]
instance decidableEqMonoidHomFintype [DecidableEq β] [Fintype α] [MulOneClass α] [MulOneClass β] :
    DecidableEq (α →* β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff MonoidHom.coe_inj)
#align fintype.decidable_eq_monoid_hom_fintype Fintype.decidableEqMonoidHomFintype
#align fintype.decidable_eq_add_monoid_hom_fintype Fintype.decidableEqAddMonoidHomFintype
-/

#print Fintype.decidableEqMonoidWithZeroHomFintype /-
instance decidableEqMonoidWithZeroHomFintype [DecidableEq β] [Fintype α] [MulZeroOneClass α]
    [MulZeroOneClass β] : DecidableEq (α →*₀ β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff MonoidWithZeroHom.coe_inj)
#align fintype.decidable_eq_monoid_with_zero_hom_fintype Fintype.decidableEqMonoidWithZeroHomFintype
-/

#print Fintype.decidableEqRingHomFintype /-
instance decidableEqRingHomFintype [DecidableEq β] [Fintype α] [Semiring α] [Semiring β] :
    DecidableEq (α →+* β) := fun a b =>
  decidable_of_iff ((a : α → β) = b) (Injective.eq_iff RingHom.coe_inj)
#align fintype.decidable_eq_ring_hom_fintype Fintype.decidableEqRingHomFintype
-/

end BundledHoms

#print Fintype.decidableInjectiveFintype /-
instance decidableInjectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α → β) → Prop) := fun x => by unfold injective <;> infer_instance
#align fintype.decidable_injective_fintype Fintype.decidableInjectiveFintype
-/

#print Fintype.decidableSurjectiveFintype /-
instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) := fun x => by unfold surjective <;> infer_instance
#align fintype.decidable_surjective_fintype Fintype.decidableSurjectiveFintype
-/

#print Fintype.decidableBijectiveFintype /-
instance decidableBijectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α → β) → Prop) := fun x => by unfold bijective <;> infer_instance
#align fintype.decidable_bijective_fintype Fintype.decidableBijectiveFintype
-/

#print Fintype.decidableRightInverseFintype /-
instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
    Decidable (Function.RightInverse f g) :=
  show Decidable (∀ x, g (f x) = x) by infer_instance
#align fintype.decidable_right_inverse_fintype Fintype.decidableRightInverseFintype
-/

#print Fintype.decidableLeftInverseFintype /-
instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
    Decidable (Function.LeftInverse f g) :=
  show Decidable (∀ x, f (g x) = x) by infer_instance
#align fintype.decidable_left_inverse_fintype Fintype.decidableLeftInverseFintype
-/

#print Fintype.ofMultiset /-
/-- Construct a proof of `fintype α` from a universal multiset -/
def ofMultiset [DecidableEq α] (s : Multiset α) (H : ∀ x : α, x ∈ s) : Fintype α :=
  ⟨s.toFinset, by simpa using H⟩
#align fintype.of_multiset Fintype.ofMultiset
-/

#print Fintype.ofList /-
/-- Construct a proof of `fintype α` from a universal list -/
def ofList [DecidableEq α] (l : List α) (H : ∀ x : α, x ∈ l) : Fintype α :=
  ⟨l.toFinset, by simpa using H⟩
#align fintype.of_list Fintype.ofList
-/

instance (α : Type _) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by congr <;> simp [Finset.ext_iff, h₁, h₂]⟩

#print Fintype.subtype /-
/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.Nodup.pmap fun a _ b _ => congr_arg Subtype.val⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩
#align fintype.subtype Fintype.subtype
-/

#print Fintype.ofFinset /-
/-- Construct a fintype from a finset with the same elements. -/
def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H
#align fintype.of_finset Fintype.ofFinset
-/

#print Fintype.ofBijective /-
/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def ofBijective [Fintype α] (f : α → β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨a, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩
#align fintype.of_bijective Fintype.ofBijective
-/

#print Fintype.ofSurjective /-
/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def ofSurjective [DecidableEq β] [Fintype α] (f : α → β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.image f, fun b =>
    let ⟨a, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩
#align fintype.of_surjective Fintype.ofSurjective
-/

end Fintype

namespace Finset

variable [Fintype α] [DecidableEq α] {s t : Finset α}

/- warning: finset.decidable_codisjoint -> Finset.decidableCodisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Decidable (Codisjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.boundedOrder.{u1} α _inst_1)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Decidable (Codisjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (BoundedOrder.toOrderTop.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.instBoundedOrderFinsetToLEToPreorderPartialOrder.{u1} α _inst_1)) s t)
Case conversion may be inaccurate. Consider using '#align finset.decidable_codisjoint Finset.decidableCodisjointₓ'. -/
instance decidableCodisjoint : Decidable (Codisjoint s t) :=
  decidable_of_iff _ codisjoint_left.symm
#align finset.decidable_codisjoint Finset.decidableCodisjoint

/- warning: finset.decidable_is_compl -> Finset.decidableIsCompl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Decidable (IsCompl.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.boundedOrder.{u1} α _inst_1) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Decidable (IsCompl.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instBoundedOrderFinsetToLEToPreorderPartialOrder.{u1} α _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align finset.decidable_is_compl Finset.decidableIsComplₓ'. -/
instance decidableIsCompl : Decidable (IsCompl s t) :=
  decidable_of_iff' _ isCompl_iff
#align finset.decidable_is_compl Finset.decidableIsCompl

end Finset

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

#print Function.Injective.invOfMemRange /-
/-- The inverse of an `hf : injective` function `f : α → β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def invOfMemRange : Set.range f → α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.exists_unique_of_mem_range b.property))
#align function.injective.inv_of_mem_range Function.Injective.invOfMemRange
-/

#print Function.Injective.left_inv_of_invOfMemRange /-
theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right
#align function.injective.left_inv_of_inv_of_mem_range Function.Injective.left_inv_of_invOfMemRange
-/

/- warning: function.injective.right_inv_of_inv_of_mem_range -> Function.Injective.right_inv_of_invOfMemRange is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β} (hf : Function.Injective.{succ u1, succ u2} α β f) (a : α), Eq.{succ u1} α (Function.Injective.invOfMemRange.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f hf (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u1} β α f)) (f a) (Set.mem_range_self.{u2, succ u1} β α f a))) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β} (hf : Function.Injective.{succ u2, succ u1} α β f) (a : α), Eq.{succ u2} α (Function.Injective.invOfMemRange.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f hf (Subtype.mk.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α f)) (f a) (Set.mem_range_self.{succ u2, u1} β α f a))) a
Case conversion may be inaccurate. Consider using '#align function.injective.right_inv_of_inv_of_mem_range Function.Injective.right_inv_of_invOfMemRangeₓ'. -/
@[simp]
theorem right_inv_of_invOfMemRange (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right
#align function.injective.right_inv_of_inv_of_mem_range Function.Injective.right_inv_of_invOfMemRange

/- warning: function.injective.inv_fun_restrict -> Function.Injective.invFun_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β} (hf : Function.Injective.{succ u1, succ u2} α β f) [_inst_3 : Nonempty.{succ u1} α], Eq.{max (succ u2) (succ u1)} ((coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α f)) -> α) (Set.restrict.{u2, u1} β (fun (ᾰ : β) => α) (Set.range.{u2, succ u1} β α f) (Function.invFun.{succ u1, succ u2} α β _inst_3 f)) (Function.Injective.invOfMemRange.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β} (hf : Function.Injective.{succ u2, succ u1} α β f) [_inst_3 : Nonempty.{succ u2} α], Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u1} β (Set.range.{u1, succ u2} β α f)) -> α) (Set.restrict.{u1, u2} β (fun (ᾰ : β) => α) (Set.range.{u1, succ u2} β α f) (Function.invFun.{succ u2, succ u1} α β _inst_3 f)) (Function.Injective.invOfMemRange.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f hf)
Case conversion may be inaccurate. Consider using '#align function.injective.inv_fun_restrict Function.Injective.invFun_restrictₓ'. -/
theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = hf.invOfMemRange :=
  by
  ext ⟨b, h⟩
  apply hf
  simp [hf.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
#align function.injective.inv_fun_restrict Function.Injective.invFun_restrict

#print Function.Injective.invOfMemRange_surjective /-
theorem invOfMemRange_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩
#align function.injective.inv_of_mem_range_surjective Function.Injective.invOfMemRange_surjective
-/

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.range f)

#print Function.Embedding.invOfMemRange /-
/-- The inverse of an embedding `f : α ↪ β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def invOfMemRange : α :=
  f.Injective.invOfMemRange b
#align function.embedding.inv_of_mem_range Function.Embedding.invOfMemRange
-/

#print Function.Embedding.left_inv_of_invOfMemRange /-
@[simp]
theorem left_inv_of_invOfMemRange : f (f.invOfMemRange b) = b :=
  f.Injective.left_inv_of_inv_of_mem_range b
#align function.embedding.left_inv_of_inv_of_mem_range Function.Embedding.left_inv_of_invOfMemRange
-/

/- warning: function.embedding.right_inv_of_inv_of_mem_range -> Function.Embedding.right_inv_of_invOfMemRange is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : Function.Embedding.{succ u1, succ u2} α β) (a : α), Eq.{succ u1} α (Function.Embedding.invOfMemRange.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Set.mem_range_self.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) a))) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : Function.Embedding.{succ u2, succ u1} α β) (a : α), Eq.{succ u2} α (Function.Embedding.invOfMemRange.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (Subtype.mk.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Set.mem_range_self.{succ u2, u1} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) a))) a
Case conversion may be inaccurate. Consider using '#align function.embedding.right_inv_of_inv_of_mem_range Function.Embedding.right_inv_of_invOfMemRangeₓ'. -/
@[simp]
theorem right_inv_of_invOfMemRange (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.Injective.right_inv_of_inv_of_mem_range a
#align function.embedding.right_inv_of_inv_of_mem_range Function.Embedding.right_inv_of_invOfMemRange

/- warning: function.embedding.inv_fun_restrict -> Function.Embedding.invFun_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : Function.Embedding.{succ u1, succ u2} α β) [_inst_3 : Nonempty.{succ u1} α], Eq.{max (succ u2) (succ u1)} ((coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) -> α) (Set.restrict.{u2, u1} β (fun (ᾰ : β) => α) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f)) (Function.invFun.{succ u1, succ u2} α β _inst_3 (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) (Function.Embedding.invOfMemRange.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : Function.Embedding.{succ u2, succ u1} α β) [_inst_3 : Nonempty.{succ u2} α], Eq.{max (succ u2) (succ u1)} ((Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) -> α) (Set.restrict.{u1, u2} β (fun (ᾰ : β) => α) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f)) (Function.invFun.{succ u2, succ u1} α β _inst_3 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) (Function.Embedding.invOfMemRange.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f)
Case conversion may be inaccurate. Consider using '#align function.embedding.inv_fun_restrict Function.Embedding.invFun_restrictₓ'. -/
theorem invFun_restrict [Nonempty α] : (Set.range f).restrict (invFun f) = f.invOfMemRange :=
  by
  ext ⟨b, h⟩
  apply f.injective
  simp [f.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
#align function.embedding.inv_fun_restrict Function.Embedding.invFun_restrict

#print Function.Embedding.invOfMemRange_surjective /-
theorem invOfMemRange_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by simp⟩
#align function.embedding.inv_of_mem_range_surjective Function.Embedding.invOfMemRange_surjective
-/

end Embedding

end Function

end Inv

namespace Fintype

#print Fintype.ofInjective /-
/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable def ofInjective [Fintype β] (f : α → β) (H : Function.Injective f) : Fintype α :=
  letI := Classical.dec
  if hα : Nonempty α then
    letI := Classical.inhabited_of_nonempty hα
    of_surjective (inv_fun f) (inv_fun_surjective H)
  else ⟨∅, fun x => (hα ⟨x⟩).elim⟩
#align fintype.of_injective Fintype.ofInjective
-/

#print Fintype.ofEquiv /-
/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def ofEquiv (α : Type _) [Fintype α] (f : α ≃ β) : Fintype β :=
  ofBijective _ f.Bijective
#align fintype.of_equiv Fintype.ofEquiv
-/

#print Fintype.ofSubsingleton /-
/-- Any subsingleton type with a witness is a fintype (with one term). -/
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun b => Finset.mem_singleton.2 (Subsingleton.elim _ _)⟩
#align fintype.of_subsingleton Fintype.ofSubsingleton
-/

#print Fintype.univ_ofSubsingleton /-
@[simp]
theorem univ_ofSubsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl
#align fintype.univ_of_subsingleton Fintype.univ_ofSubsingleton
-/

#print Fintype.ofIsEmpty /-
-- see Note [lower instance priority]
instance (priority := 100) ofIsEmpty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩
#align fintype.of_is_empty Fintype.ofIsEmpty
-/

#print Fintype.univ_of_isEmpty /-
-- no-lint since while `finset.univ_eq_empty` can prove this, it isn't applicable for `dsimp`.
/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `finset.univ_eq_empty`. -/
@[simp, nolint simp_nf]
theorem univ_of_isEmpty [IsEmpty α] : @univ α _ = ∅ :=
  rfl
#align fintype.univ_of_is_empty Fintype.univ_of_isEmpty
-/

end Fintype

namespace Set

variable {s t : Set α}

#print Set.toFinset /-
/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  (@Finset.univ s _).map <| Function.Embedding.subtype _
#align set.to_finset Set.toFinset
-/

#print Set.toFinset_congr /-
@[congr]
theorem toFinset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) :
    toFinset s = toFinset t := by cc
#align set.to_finset_congr Set.toFinset_congr
-/

#print Set.mem_toFinset /-
@[simp]
theorem mem_toFinset {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset ↔ a ∈ s := by simp [to_finset]
#align set.mem_to_finset Set.mem_toFinset
-/

#print Set.toFinset_ofFinset /-
/-- Many `fintype` instances for sets are defined using an extensionally equal `finset`.
Rewriting `s.to_finset` with `set.to_finset_of_finset` replaces the term with such a `finset`. -/
theorem toFinset_ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
    @Set.toFinset _ p (Fintype.ofFinset s H) = s :=
  Finset.ext fun x => by rw [mem_to_finset, H]
#align set.to_finset_of_finset Set.toFinset_ofFinset
-/

#print Set.decidableMemOfFintype /-
/-- Membership of a set with a `fintype` instance is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a ∈ s) :=
  decidable_of_iff _ mem_toFinset
#align set.decidable_mem_of_fintype Set.decidableMemOfFintype
-/

#print Set.coe_toFinset /-
@[simp]
theorem coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_toFinset
#align set.coe_to_finset Set.coe_toFinset
-/

#print Set.toFinset_nonempty /-
@[simp]
theorem toFinset_nonempty {s : Set α} [Fintype s] : s.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, coe_to_finset]
#align set.to_finset_nonempty Set.toFinset_nonempty
-/

#print Set.toFinset_inj /-
@[simp]
theorem toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by rw [← s.coe_to_finset, h, t.coe_to_finset], fun h => by simp [h] <;> congr ⟩
#align set.to_finset_inj Set.toFinset_inj
-/

#print Set.toFinset_subset_toFinset /-
@[mono]
theorem toFinset_subset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp [Finset.subset_iff, Set.subset_def]
#align set.to_finset_subset_to_finset Set.toFinset_subset_toFinset
-/

/- warning: set.to_finset_ssubset -> Set.toFinset_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] {t : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.toFinset.{u1} α s _inst_1) t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] {t : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.toFinset.{u1} α s _inst_1) t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Finset.toSet.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.to_finset_ssubset Set.toFinset_ssubsetₓ'. -/
@[simp]
theorem toFinset_ssubset [Fintype s] {t : Finset α} : s.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_to_finset]
#align set.to_finset_ssubset Set.toFinset_ssubset

#print Set.subset_toFinset /-
@[simp]
theorem subset_toFinset {s : Finset α} [Fintype t] : s ⊆ t.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, coe_to_finset]
#align set.subset_to_finset Set.subset_toFinset
-/

/- warning: set.ssubset_to_finset -> Set.ssubset_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : Set.{u1} α} {s : Finset.{u1} α} [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s (Set.toFinset.{u1} α t _inst_1)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) t)
but is expected to have type
  forall {α : Type.{u1}} {t : Set.{u1} α} {s : Finset.{u1} α} [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α t)], Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s (Set.toFinset.{u1} α t _inst_1)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (Finset.toSet.{u1} α s) t)
Case conversion may be inaccurate. Consider using '#align set.ssubset_to_finset Set.ssubset_toFinsetₓ'. -/
@[simp]
theorem ssubset_toFinset {s : Finset α} [Fintype t] : s ⊂ t.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, coe_to_finset]
#align set.ssubset_to_finset Set.ssubset_toFinset

/- warning: set.to_finset_ssubset_to_finset -> Set.toFinset_ssubset_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u1} α t _inst_2)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α t)], Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u1} α t _inst_2)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.to_finset_ssubset_to_finset Set.toFinset_ssubset_toFinsetₓ'. -/
@[mono]
theorem toFinset_ssubset_toFinset [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [Finset.ssubset_def, to_finset_subset_to_finset, ssubset_def]
#align set.to_finset_ssubset_to_finset Set.toFinset_ssubset_toFinset

#print Set.toFinset_subset /-
@[simp]
theorem toFinset_subset [Fintype s] {t : Finset α} : s.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, coe_to_finset]
#align set.to_finset_subset Set.toFinset_subset
-/

alias to_finset_subset_to_finset ↔ _ to_finset_mono
#align set.to_finset_mono Set.toFinset_mono

/- warning: set.to_finset_strict_mono -> Set.toFinset_strict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u1} α t _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α t)], (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u1} α t _inst_2))
Case conversion may be inaccurate. Consider using '#align set.to_finset_strict_mono Set.toFinset_strict_monoₓ'. -/
alias to_finset_ssubset_to_finset ↔ _ to_finset_strict_mono
#align set.to_finset_strict_mono Set.toFinset_strict_mono

/- warning: set.disjoint_to_finset -> Set.disjoint_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u1} α t _inst_2)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α t)], Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Set.toFinset.{u1} α s _inst_1) (Set.toFinset.{u1} α t _inst_2)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t)
Case conversion may be inaccurate. Consider using '#align set.disjoint_to_finset Set.disjoint_toFinsetₓ'. -/
@[simp]
theorem disjoint_toFinset [Fintype s] [Fintype t] : Disjoint s.toFinset t.toFinset ↔ Disjoint s t :=
  by simp only [← disjoint_coe, coe_to_finset]
#align set.disjoint_to_finset Set.disjoint_toFinset

section DecidableEq

variable [DecidableEq α] (s t) [Fintype s] [Fintype t]

/- warning: set.to_finset_inter -> Set.toFinset_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)] [_inst_4 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) _inst_4) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)] [_inst_4 : Fintype.{u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) _inst_4) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
Case conversion may be inaccurate. Consider using '#align set.to_finset_inter Set.toFinset_interₓ'. -/
@[simp]
theorem toFinset_inter [Fintype ↥(s ∩ t)] : (s ∩ t).toFinset = s.toFinset ∩ t.toFinset :=
  by
  ext
  simp
#align set.to_finset_inter Set.toFinset_inter

/- warning: set.to_finset_union -> Set.toFinset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)] [_inst_4 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) _inst_4) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)] [_inst_4 : Fintype.{u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) _inst_4) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
Case conversion may be inaccurate. Consider using '#align set.to_finset_union Set.toFinset_unionₓ'. -/
@[simp]
theorem toFinset_union [Fintype ↥(s ∪ t)] : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset :=
  by
  ext
  simp
#align set.to_finset_union Set.toFinset_union

/- warning: set.to_finset_diff -> Set.toFinset_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)] [_inst_4 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) _inst_4) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)] [_inst_4 : Fintype.{u1} (Set.Elem.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) _inst_4) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
Case conversion may be inaccurate. Consider using '#align set.to_finset_diff Set.toFinset_diffₓ'. -/
@[simp]
theorem toFinset_diff [Fintype ↥(s \ t)] : (s \ t).toFinset = s.toFinset \ t.toFinset :=
  by
  ext
  simp
#align set.to_finset_diff Set.toFinset_diff

/- warning: set.to_finset_symm_diff -> Set.toFinset_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)] [_inst_4 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) _inst_4) (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)] [_inst_4 : Fintype.{u1} (Set.Elem.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) _inst_4) (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.toFinset.{u1} α s _inst_2) (Set.toFinset.{u1} α t _inst_3))
Case conversion may be inaccurate. Consider using '#align set.to_finset_symm_diff Set.toFinset_symmDiffₓ'. -/
@[simp]
theorem toFinset_symmDiff [Fintype ↥(s ∆ t)] : (s ∆ t).toFinset = s.toFinset ∆ t.toFinset :=
  by
  ext
  simp [mem_symm_diff, Finset.mem_symmDiff]
#align set.to_finset_symm_diff Set.toFinset_symmDiff

/- warning: set.to_finset_compl -> Set.toFinset_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_4 : Fintype.{u1} α] [_inst_5 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) _inst_5) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_4 (fun (a : α) (b : α) => _inst_1 a b))) (Set.toFinset.{u1} α s _inst_2))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_4 : Fintype.{u1} α] [_inst_5 : Fintype.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) _inst_5) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_4 (fun (a : α) (b : α) => _inst_1 a b))) (Set.toFinset.{u1} α s _inst_2))
Case conversion may be inaccurate. Consider using '#align set.to_finset_compl Set.toFinset_complₓ'. -/
@[simp]
theorem toFinset_compl [Fintype α] [Fintype ↥(sᶜ)] : sᶜ.toFinset = s.toFinsetᶜ :=
  by
  ext
  simp
#align set.to_finset_compl Set.toFinset_compl

end DecidableEq

#print Set.toFinset_empty /-
-- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`.
@[simp]
theorem toFinset_empty [Fintype ↥(∅ : Set α)] : (∅ : Set α).toFinset = ∅ :=
  by
  ext
  simp
#align set.to_finset_empty Set.toFinset_empty
-/

#print Set.toFinset_univ /-
/- TODO Without the coercion arrow (`↥`) there is an elaboration bug in the following two;
it essentially infers `fintype.{v} (set.univ.{u} : set α)` with `v` and `u` distinct.
Reported in leanprover-community/lean#672 -/
@[simp]
theorem toFinset_univ [Fintype α] [Fintype ↥(Set.univ : Set α)] :
    (Set.univ : Set α).toFinset = Finset.univ :=
  by
  ext
  simp
#align set.to_finset_univ Set.toFinset_univ
-/

#print Set.toFinset_eq_empty /-
@[simp]
theorem toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  rw [← to_finset_empty, to_finset_inj]
#align set.to_finset_eq_empty Set.toFinset_eq_empty
-/

#print Set.toFinset_eq_univ /-
@[simp]
theorem toFinset_eq_univ [Fintype α] [Fintype s] : s.toFinset = Finset.univ ↔ s = univ := by
  rw [← coe_inj, coe_to_finset, coe_univ]
#align set.to_finset_eq_univ Set.toFinset_eq_univ
-/

#print Set.to_finset_set_of /-
@[simp]
theorem to_finset_set_of [Fintype α] (p : α → Prop) [DecidablePred p] [Fintype { x | p x }] :
    { x | p x }.toFinset = Finset.univ.filter p :=
  by
  ext
  simp
#align set.to_finset_set_of Set.to_finset_set_of
-/

/- warning: set.to_finset_ssubset_univ -> Set.toFinset_ssubset_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Set.{u1} α} [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.toFinset.{u1} α s _inst_2) (Finset.univ.{u1} α _inst_1)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {s : Set.{u1} α} [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)], Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.toFinset.{u1} α s _inst_2) (Finset.univ.{u1} α _inst_1)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.to_finset_ssubset_univ Set.toFinset_ssubset_univₓ'. -/
@[simp]
theorem toFinset_ssubset_univ [Fintype α] {s : Set α} [Fintype s] :
    s.toFinset ⊂ Finset.univ ↔ s ⊂ univ := by rw [← coe_ssubset, coe_to_finset, coe_univ]
#align set.to_finset_ssubset_univ Set.toFinset_ssubset_univ

#print Set.toFinset_image /-
@[simp]
theorem toFinset_image [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] [Fintype (f '' s)] :
    (f '' s).toFinset = s.toFinset.image f :=
  Finset.coe_injective <| by simp
#align set.to_finset_image Set.toFinset_image
-/

/- warning: set.to_finset_range -> Set.toFinset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u2} β] (f : β -> α) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.range.{u1, succ u2} α β f))], Eq.{succ u1} (Finset.{u1} α) (Set.toFinset.{u1} α (Set.range.{u1, succ u2} α β f) _inst_3) (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_1 a b) f (Finset.univ.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u1} β] (f : β -> α) [_inst_3 : Fintype.{u2} (Set.Elem.{u2} α (Set.range.{u2, succ u1} α β f))], Eq.{succ u2} (Finset.{u2} α) (Set.toFinset.{u2} α (Set.range.{u2, succ u1} α β f) _inst_3) (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_1 a b) f (Finset.univ.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align set.to_finset_range Set.toFinset_rangeₓ'. -/
@[simp]
theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.range f)] :
    (Set.range f).toFinset = Finset.univ.image f :=
  by
  ext
  simp
#align set.to_finset_range Set.toFinset_range

#print Set.toFinset_singleton /-
-- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`.
theorem toFinset_singleton (a : α) [Fintype ↥({a} : Set α)] : ({a} : Set α).toFinset = {a} :=
  by
  ext
  simp
#align set.to_finset_singleton Set.toFinset_singleton
-/

#print Set.toFinset_insert /-
-- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`.
@[simp]
theorem toFinset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype ↥(insert a s : Set α)]
    [Fintype s] : (insert a s).toFinset = insert a s.toFinset :=
  by
  ext
  simp
#align set.to_finset_insert Set.toFinset_insert
-/

#print Set.filter_mem_univ_eq_toFinset /-
theorem filter_mem_univ_eq_toFinset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· ∈ s)] :
    Finset.univ.filter (· ∈ s) = s.toFinset := by
  ext
  simp only [mem_filter, Finset.mem_univ, true_and_iff, mem_to_finset]
#align set.filter_mem_univ_eq_to_finset Set.filter_mem_univ_eq_toFinset
-/

end Set

#print Finset.toFinset_coe /-
@[simp]
theorem Finset.toFinset_coe (s : Finset α) [Fintype ↥(s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_toFinset
#align finset.to_finset_coe Finset.toFinset_coe
-/

instance (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

#print Fin.univ_def /-
theorem Fin.univ_def (n : ℕ) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ :=
  rfl
#align fin.univ_def Fin.univ_def
-/

/- warning: fin.image_succ_above_univ -> Fin.image_succAbove_univ is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.booleanAlgebra.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b))) (Singleton.singleton.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasSingleton.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) i))
but is expected to have type
  forall {n : Nat} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) (Fin.succAbove n i))) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.instBooleanAlgebraFinset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b))) (Singleton.singleton.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.instSingletonFinset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) i))
Case conversion may be inaccurate. Consider using '#align fin.image_succ_above_univ Fin.image_succAbove_univₓ'. -/
@[simp]
theorem Fin.image_succAbove_univ {n : ℕ} (i : Fin (n + 1)) : univ.image i.succAbove = {i}ᶜ :=
  by
  ext m
  simp
#align fin.image_succ_above_univ Fin.image_succAbove_univ

/- warning: fin.image_succ_univ -> Fin.image_succ_univ is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (Finset.{0} (Fin (Nat.succ n))) (Finset.image.{0, 0} (Fin n) (Fin (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => Fin.decidableEq (Nat.succ n) a b) (Fin.succ n) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.booleanAlgebra.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => Fin.decidableEq (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))))
but is expected to have type
  forall (n : Nat), Eq.{1} (Finset.{0} (Fin (Nat.succ n))) (Finset.image.{0, 0} (Fin n) (Fin (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b) (Fin.succ n) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.instBooleanAlgebraFinset.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))))
Case conversion may be inaccurate. Consider using '#align fin.image_succ_univ Fin.image_succ_univₓ'. -/
@[simp]
theorem Fin.image_succ_univ (n : ℕ) : (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ := by
  rw [← Fin.succAbove_zero, Fin.image_succAbove_univ]
#align fin.image_succ_univ Fin.image_succ_univ

/- warning: fin.image_cast_succ -> Fin.image_castSucc is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.booleanAlgebra.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b))) (Singleton.singleton.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasSingleton.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Fin.last n)))
but is expected to have type
  forall (n : Nat), Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) (Fin.castSucc n))) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.instBooleanAlgebraFinset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => instDecidableEqFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) a b))) (Singleton.singleton.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.instSingletonFinset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin.last n)))
Case conversion may be inaccurate. Consider using '#align fin.image_cast_succ Fin.image_castSuccₓ'. -/
@[simp]
theorem Fin.image_castSucc (n : ℕ) : (univ : Finset (Fin n)).image Fin.castSucc = {Fin.last n}ᶜ :=
  by rw [← Fin.succAbove_last, Fin.image_succAbove_univ]
#align fin.image_cast_succ Fin.image_castSucc

/- warning: fin.univ_succ -> Fin.univ_succ is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.univ.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.cons.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Eq.mpr.{0} (Not (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Not (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))))) True) (Eq.trans.{1} Prop (Not (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))))) (Not False) True ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) False (Eq.trans.{1} Prop (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) (Not True) False (Eq.trans.{1} Prop (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) (Not (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))))) (Not True) (Eq.trans.{1} Prop (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.booleanAlgebra.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => Fin.decidableEq (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))))) (Not (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))))) ((fun [self : Membership.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))] (ᾰ : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (ᾰ_1 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (e_2 : Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) ᾰ ᾰ_1) (ᾰ_2 : Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (ᾰ_3 : Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (e_3 : Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) ᾰ_2 ᾰ_3) => congr.{1, 1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) Prop (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) self ᾰ) (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) self ᾰ_1) ᾰ_2 ᾰ_3 (congr_arg.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) ((Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) -> Prop) ᾰ ᾰ_1 (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) self) e_2) e_3) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (rfl.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.booleanAlgebra.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => Fin.decidableEq (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))))) (Eq.trans.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.succ n) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.booleanAlgebra.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => Fin.decidableEq (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))))) (Eq.trans.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.map.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) a b) (coeFn.{1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Function.Embedding.hasCoeToFun.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n))) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Fin.succ n) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Finset.map_eq_image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) ((fun [_inst_1 : DecidableEq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))] (f : (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (f_1 : (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (e_2 : Eq.{1} ((Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) f f_1) (s : Finset.{0} (Fin n)) (s_1 : Finset.{0} (Fin n)) (e_3 : Eq.{1} (Finset.{0} (Fin n)) s s_1) => congr.{1, 1} (Finset.{0} (Fin n)) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) _inst_1 f) (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) _inst_1 f_1) s s_1 (congr_arg.{1, 1} ((Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) ((Finset.{0} (Fin n)) -> (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) f f_1 (Finset.image.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) _inst_1) e_2) e_3) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) a b) (coeFn.{1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Function.Embedding.hasCoeToFun.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n))) (Fin.succ n) (Function.Embedding.coeFn_mk.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)) (rfl.{1} (Finset.{0} (Fin n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))))) (Fin.image_succ_univ n))) (propext (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (HasCompl.compl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.booleanAlgebra.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (Nat.succ n) a b) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))))) (Not (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))))) (Finset.mem_compl.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) (fun (a : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => Fin.decidableEq (Nat.succ n) a b) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.hasSingleton.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))))) True (Eq.trans.{1} Prop (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Singleton.singleton.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasSingleton.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))))) (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) True (propext (Membership.Mem.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasMem.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (Singleton.singleton.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.hasSingleton.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))))) (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) (Finset.mem_singleton.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))))) (propext (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))) True (eq_self_iff_true.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (NeZero.succ n)))))))))) (propext (Not True) False not_true))) (propext (Not False) True not_false_iff))) trivial))
but is expected to have type
  forall (n : Nat), Eq.{1} (Finset.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.univ.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.cons.{0} (Fin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (of_eq_true (Not (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))))) (Eq.trans.{1} Prop (Not (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))))) (Not False) True (congrArg.{1, 1} Prop Prop (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) False Not (Eq.trans.{1} Prop (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) (Not True) False (Eq.trans.{1} Prop (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) (Not (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))))) (Not True) (Eq.trans.{1} Prop (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n)))) (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.instBooleanAlgebraFinset.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))))) (Not (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))))) (congrArg.{1, 1} (Finset.{0} (Fin (Nat.succ n))) Prop (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.instBooleanAlgebraFinset.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))) (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (Eq.trans.{1} (Finset.{0} (Fin (Nat.succ n))) (Finset.map.{0, 0} (Fin n) (Fin (Nat.succ n)) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Finset.image.{0, 0} (Fin n) (Fin (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (Nat.succ n))) (Fin n) (fun (a : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (Nat.succ n)) a) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (Nat.succ n))) (Fin n) (Fin (Nat.succ n)) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (Nat.succ n)))) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n))) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (HasCompl.compl.{0} (Finset.{0} (Fin (Nat.succ n))) (BooleanAlgebra.toHasCompl.{0} (Finset.{0} (Fin (Nat.succ n))) (Finset.instBooleanAlgebraFinset.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))) (Finset.map_eq_image.{0, 0} (Fin n) (Fin (Nat.succ n)) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b) (Function.Embedding.mk.{1, 1} (Fin n) (Fin (Nat.succ n)) (Fin.succ n) (Fin.succ_injective n)) (Finset.univ.{0} (Fin n) (Fin.fintype n))) (Fin.image_succ_univ n))) (Mathlib.Data.Fintype.Basic._auxLemma.8.{0} (Fin (Nat.succ n)) (Fin.fintype (Nat.succ n)) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (fun (a : Fin (Nat.succ n)) (b : Fin (Nat.succ n)) => instDecidableEqFin (Nat.succ n) a b) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))) (congrArg.{1, 1} Prop Prop (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))) True Not (Eq.trans.{1} Prop (Membership.mem.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instMembershipFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (Singleton.singleton.{0, 0} (Fin (Nat.succ n)) (Finset.{0} (Fin (Nat.succ n))) (Finset.instSingletonFinset.{0} (Fin (Nat.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))) (Eq.{1} (Fin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) True (Mathlib.Data.Finset.Basic._auxLemma.26.{0} (Fin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (eq_self.{1} (Fin (Nat.succ n)) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))))) Std.Logic._auxLemma.3)) Std.Logic._auxLemma.4)))
Case conversion may be inaccurate. Consider using '#align fin.univ_succ Fin.univ_succₓ'. -/
/- The following three lemmas use `finset.cons` instead of `insert` and `finset.map` instead of
`finset.image` to reduce proof obligations downstream. -/
/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
theorem Fin.univ_succ (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image]) :=
  by simp [map_eq_image]
#align fin.univ_succ Fin.univ_succ

#print Fin.univ_castSucc /-
/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
theorem Fin.univ_castSucc (n : ℕ) :
    (univ : Finset (Fin (n + 1))) =
      cons (Fin.last n) (univ.map Fin.castSucc.toEmbedding) (by simp [map_eq_image]) :=
  by simp [map_eq_image]
#align fin.univ_cast_succ Fin.univ_castSucc
-/

#print Fin.univ_succAbove /-
/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
theorem Fin.univ_succAbove (n : ℕ) (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))) = cons p (univ.map <| (Fin.succAbove p).toEmbedding) (by simp) :=
  by simp [map_eq_image]
#align fin.univ_succ_above Fin.univ_succAbove
-/

#print Unique.fintype /-
@[instance]
def Unique.fintype {α : Type _} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default
#align unique.fintype Unique.fintype
-/

#print Fintype.subtypeEq /-
/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y} (by simp)
#align fintype.subtype_eq Fintype.subtypeEq
-/

#print Fintype.subtypeEq' /-
/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y} (by simp [eq_comm])
#align fintype.subtype_eq' Fintype.subtypeEq'
-/

#print Fintype.univ_empty /-
@[simp]
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl
#align fintype.univ_empty Fintype.univ_empty
-/

#print Fintype.univ_pempty /-
@[simp]
theorem Fintype.univ_pempty : @univ PEmpty _ = ∅ :=
  rfl
#align fintype.univ_pempty Fintype.univ_pempty
-/

instance : Fintype Unit :=
  Fintype.ofSubsingleton ()

/- warning: fintype.univ_unit -> Fintype.univ_unit is a dubious translation:
lean 3 declaration is
  Eq.{1} (Finset.{0} Unit) (Finset.univ.{0} Unit Unit.fintype) (Singleton.singleton.{0, 0} Unit (Finset.{0} Unit) (Finset.hasSingleton.{0} Unit) Unit.unit)
but is expected to have type
  Eq.{1} (Finset.{0} Unit) (Finset.univ.{0} Unit instFintypeUnit) (Singleton.singleton.{0, 0} Unit (Finset.{0} Unit) (Finset.instSingletonFinset.{0} Unit) Unit.unit)
Case conversion may be inaccurate. Consider using '#align fintype.univ_unit Fintype.univ_unitₓ'. -/
theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl
#align fintype.univ_unit Fintype.univ_unit

instance : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit

/- warning: fintype.univ_punit -> Fintype.univ_punit is a dubious translation:
lean 3 declaration is
  Eq.{succ u1} (Finset.{u1} PUnit.{succ u1}) (Finset.univ.{u1} PUnit.{succ u1} PUnit.fintype.{u1}) (Singleton.singleton.{u1, u1} PUnit.{succ u1} (Finset.{u1} PUnit.{succ u1}) (Finset.hasSingleton.{u1} PUnit.{succ u1}) PUnit.unit.{succ u1})
but is expected to have type
  Eq.{succ u1} (Finset.{u1} PUnit.{succ u1}) (Finset.univ.{u1} PUnit.{succ u1} instFintypePUnit.{u1}) (Singleton.singleton.{u1, u1} PUnit.{succ u1} (Finset.{u1} PUnit.{succ u1}) (Finset.instSingletonFinset.{u1} PUnit.{succ u1}) PUnit.unit.{succ u1})
Case conversion may be inaccurate. Consider using '#align fintype.univ_punit Fintype.univ_punitₓ'. -/
@[simp]
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl
#align fintype.univ_punit Fintype.univ_punit

instance : Fintype Bool :=
  ⟨⟨{true, false}, by simp⟩, fun x => by cases x <;> simp⟩

#print Fintype.univ_bool /-
@[simp]
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl
#align fintype.univ_bool Fintype.univ_bool
-/

#print Additive.fintype /-
instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  id
#align additive.fintype Additive.fintype
-/

#print Multiplicative.fintype /-
instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  id
#align multiplicative.fintype Multiplicative.fintype
-/

#print Fintype.prodLeft /-
/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(Fintype.elems (α × β)).image Prod.fst, fun a =>
    by
    let ⟨b⟩ := ‹Nonempty β›
    simp <;> exact ⟨b, Fintype.complete _⟩⟩
#align fintype.prod_left Fintype.prodLeft
-/

#print Fintype.prodRight /-
/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(Fintype.elems (α × β)).image Prod.snd, fun b =>
    by
    let ⟨a⟩ := ‹Nonempty α›
    simp <;> exact ⟨a, Fintype.complete _⟩⟩
#align fintype.prod_right Fintype.prodRight
-/

instance (α : Type _) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm

instance (α : Type _) [Fintype α] : Fintype (PLift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm

instance (α : Type _) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›

instance (α : Type _) [Finite α] : Finite αᵒᵈ :=
  ‹Finite α›

instance (α : Type _) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›

section Finset

/-! ### `fintype (s : finset α)` -/


#print Finset.fintypeCoeSort /-
instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩
#align finset.fintype_coe_sort Finset.fintypeCoeSort
-/

#print Finset.univ_eq_attach /-
@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl
#align finset.univ_eq_attach Finset.univ_eq_attach
-/

end Finset

/- warning: fintype.coe_image_univ -> Fintype.coe_image_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β}, Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) f (Finset.univ.{u1} α _inst_1))) (Set.range.{u2, succ u1} β α f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β}, Eq.{succ u1} (Set.{u1} β) (Finset.toSet.{u1} β (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_2 a b) f (Finset.univ.{u2} α _inst_1))) (Set.range.{u1, succ u2} β α f)
Case conversion may be inaccurate. Consider using '#align fintype.coe_image_univ Fintype.coe_image_univₓ'. -/
theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} :
    ↑(Finset.image f Finset.univ) = Set.range f :=
  by
  ext x
  simp
#align fintype.coe_image_univ Fintype.coe_image_univ

#print List.Subtype.fintype /-
instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach
#align list.subtype.fintype List.Subtype.fintype
-/

#print Multiset.Subtype.fintype /-
instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach
#align multiset.subtype.fintype Multiset.Subtype.fintype
-/

#print Finset.Subtype.fintype /-
instance Finset.Subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩
#align finset.subtype.fintype Finset.Subtype.fintype
-/

#print FinsetCoe.fintype /-
instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.Subtype.fintype s
#align finset_coe.fintype FinsetCoe.fintype
-/

#print Finset.attach_eq_univ /-
theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl
#align finset.attach_eq_univ Finset.attach_eq_univ
-/

#print PLift.fintypeProp /-
instance PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩
#align plift.fintype_Prop PLift.fintypeProp
-/

#print Prop.fintype /-
instance Prop.fintype : Fintype Prop :=
  ⟨⟨{True, False}, by simp [true_ne_false]⟩, Classical.cases (by simp) (by simp)⟩
#align Prop.fintype Prop.fintype
-/

/- warning: fintype.univ_Prop -> Fintype.univ_Prop is a dubious translation:
lean 3 declaration is
  Eq.{1} (Finset.{0} Prop) (Finset.univ.{0} Prop Prop.fintype) (Insert.insert.{0, 0} Prop (Finset.{0} Prop) (Finset.hasInsert.{0} Prop (fun (a : Prop) (b : Prop) => Eq.decidable.{0} Prop Prop.linearOrder a b)) True (Singleton.singleton.{0, 0} Prop (Finset.{0} Prop) (Finset.hasSingleton.{0} Prop) False))
but is expected to have type
  Eq.{1} (Finset.{0} Prop) (Finset.univ.{0} Prop Prop.fintype) (Insert.insert.{0, 0} Prop (Finset.{0} Prop) (Finset.instInsertFinset.{0} Prop (fun (a : Prop) (b : Prop) => instDecidableEq.{0} Prop Prop.linearOrder a b)) True (Singleton.singleton.{0, 0} Prop (Finset.{0} Prop) (Finset.instSingletonFinset.{0} Prop) False))
Case conversion may be inaccurate. Consider using '#align fintype.univ_Prop Fintype.univ_Propₓ'. -/
@[simp]
theorem Fintype.univ_Prop : (Finset.univ : Finset Prop) = {True, False} :=
  Finset.eq_of_veq <| by simp <;> rfl
#align fintype.univ_Prop Fintype.univ_Prop

#print Subtype.fintype /-
instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p) (by simp)
#align subtype.fintype Subtype.fintype
-/

#print setFintype /-
/-- A set on a fintype, when coerced to a type, is a fintype. -/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s
#align set_fintype setFintype
-/

section

variable (α)

/- warning: units_equiv_prod_subtype -> unitsEquivProdSubtype is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], Equiv.{succ u1, succ u1} (Units.{u1} α _inst_1) (Subtype.{succ u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => And (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Prod.snd.{u1, u1} α α p) (Prod.fst.{u1, u1} α α p)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], Equiv.{succ u1, succ u1} (Units.{u1} α _inst_1) (Subtype.{succ u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => And (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Prod.snd.{u1, u1} α α p) (Prod.fst.{u1, u1} α α p)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align units_equiv_prod_subtype unitsEquivProdSubtypeₓ'. -/
/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def unitsEquivProdSubtype [Monoid α] : αˣ ≃ { p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 }
    where
  toFun u := ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun p := Units.mk (p : α × α).1 (p : α × α).2 p.Prop.1 p.Prop.2
  left_inv u := Units.ext rfl
  right_inv p := Subtype.ext <| Prod.ext rfl rfl
#align units_equiv_prod_subtype unitsEquivProdSubtype

/- warning: units_equiv_ne_zero -> unitsEquivNeZero is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : GroupWithZero.{u1} α], Equiv.{succ u1, succ u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))) (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : GroupWithZero.{u1} α], Equiv.{succ u1, succ u1} (Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))) (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align units_equiv_ne_zero unitsEquivNeZeroₓ'. -/
/-- In a `group_with_zero` `α`, the unit group `αˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps]
def unitsEquivNeZero [GroupWithZero α] : αˣ ≃ { a : α // a ≠ 0 } :=
  ⟨fun a => ⟨a, a.NeZero⟩, fun a => Units.mk0 _ a.Prop, fun _ => Units.ext rfl, fun _ =>
    Subtype.ext rfl⟩
#align units_equiv_ne_zero unitsEquivNeZero

end

namespace Fintype

#print Fintype.finsetEquivSet /-
/-- Given `fintype α`, `finset_equiv_set` is the equiv between `finset α` and `set α`. (All
sets on a finite type are finite.) -/
noncomputable def finsetEquivSet [Fintype α] : Finset α ≃ Set α
    where
  toFun := coe
  invFun := by classical exact fun s => s.toFinset
  left_inv s := by convert Finset.toFinset_coe s
  right_inv s := by classical exact s.coe_to_finset
#align fintype.finset_equiv_set Fintype.finsetEquivSet
-/

#print Fintype.finsetEquivSet_apply /-
@[simp]
theorem finsetEquivSet_apply [Fintype α] (s : Finset α) : finsetEquivSet s = s :=
  rfl
#align fintype.finset_equiv_set_apply Fintype.finsetEquivSet_apply
-/

#print Fintype.finsetEquivSet_symm_apply /-
@[simp]
theorem finsetEquivSet_symm_apply [Fintype α] (s : Set α) [Fintype s] :
    finsetEquivSet.symm s = s.toFinset := by convert rfl
#align fintype.finset_equiv_set_symm_apply Fintype.finsetEquivSet_symm_apply
-/

end Fintype

#print Quotient.fintype /-
instance Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    Fintype (Quotient s) :=
  Fintype.ofSurjective Quotient.mk' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩
#align quotient.fintype Quotient.fintype
-/

#print PSigma.fintypePropLeft /-
instance PSigma.fintypePropLeft {α : Prop} {β : α → Type _} [Decidable α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => h x.1⟩
#align psigma.fintype_prop_left PSigma.fintypePropLeft
-/

#print PSigma.fintypePropRight /-
instance PSigma.fintypePropRight {α : Type _} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => rfl, fun ⟨x, y⟩ => rfl⟩
#align psigma.fintype_prop_right PSigma.fintypePropRight
-/

#print PSigma.fintypePropProp /-
instance PSigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    Fintype (Σ'a, β a) :=
  if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ => h ⟨x, y⟩⟩
#align psigma.fintype_prop_prop PSigma.fintypePropProp
-/

#print pfunFintype /-
instance pfunFintype (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, Fintype (α hp)] :
    Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, by simp [hp, Function.funext_iff]⟩
#align pfun_fintype pfunFintype
-/

/- warning: mem_image_univ_iff_mem_range -> mem_image_univ_iff_mem_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) f (Finset.univ.{u1} α _inst_1))) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β} {b : β}, Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_2 a b) f (Finset.univ.{u2} α _inst_1))) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align mem_image_univ_iff_mem_range mem_image_univ_iff_mem_rangeₓ'. -/
theorem mem_image_univ_iff_mem_range {α β : Type _} [Fintype α] [DecidableEq β] {f : α → β}
    {b : β} : b ∈ univ.image f ↔ b ∈ Set.range f := by simp
#align mem_image_univ_iff_mem_range mem_image_univ_iff_mem_range

#print Quotient.finChoiceAux /-
/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def Quotient.finChoiceAux {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoid (α i)] :
    ∀ l : List ι, (∀ i ∈ l, Quotient (S i)) → @Quotient (∀ i ∈ l, α i) (by infer_instance)
  | [], f => ⟦fun i => False.elim⟧
  | i :: l, f =>
    by
    refine'
      Quotient.liftOn₂ (f i (List.mem_cons_self _ _))
        (Quotient.finChoiceAux l fun j h => f j (List.mem_cons_of_mem _ h)) _ _
    exact fun a l =>
      ⟦fun j h => if e : j = i then by rw [e] <;> exact a else l _ (h.resolve_left e)⟧
    refine' fun a₁ l₁ a₂ l₂ h₁ h₂ => Quotient.sound fun j h => _
    by_cases e : j = i <;> simp [e]
    · subst j
      exact h₁
    · exact h₂ _ _
#align quotient.fin_choice_aux Quotient.finChoiceAux
-/

/- warning: quotient.fin_choice_aux_eq -> Quotient.finChoiceAux_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} ι] {α : ι -> Type.{u2}} [S : forall (i : ι), Setoid.{succ u2} (α i)] (l : List.{u1} ι) (f : forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)), Eq.{max (succ u1) (succ u2)} (Quotient.{max (succ u1) (succ u2)} (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u2} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => α i) (fun (i_1 : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => S i)))) (Quotient.finChoiceAux.{u1, u2} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => α i) (fun (i : ι) => S i) l (fun (i : ι) (h : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => Quotient.mk'.{succ u2} (α i) (S i) (f i h))) (Quotient.mk'.{max (succ u1) (succ u2)} (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u2} (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) (fun (H : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => α i) (fun (i_1 : Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) => S i))) f)
but is expected to have type
  forall {ι : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} ι] {α : ι -> Type.{u1}} [S : forall (i : ι), Setoid.{succ u1} (α i)] (l : List.{u2} ι) (f : forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i))) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u1} (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) (fun (a._@.Mathlib.Data.Fintype.Basic._hyg.8431 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => α i) (fun (i_1 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => (fun (i : ι) => S i) i))))) (Quotient.finChoiceAux.{u2, u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => α i) (fun (i : ι) => S i) l (fun (i : ι) (h : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => Quotient.mk.{succ u1} (α i) (S i) (f i h))) (Quotient.mk.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i))) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (α i)) (fun (i : ι) => piSetoid.{0, succ u1} (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) (fun (a._@.Mathlib.Data.Fintype.Basic._hyg.8431 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => α i) (fun (i_1 : Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) => (fun (i : ι) => S i) i)))) f)
Case conversion may be inaccurate. Consider using '#align quotient.fin_choice_aux_eq Quotient.finChoiceAux_eqₓ'. -/
theorem Quotient.finChoiceAux_eq {ι : Type _} [DecidableEq ι] {α : ι → Type _}
    [S : ∀ i, Setoid (α i)] :
    ∀ (l : List ι) (f : ∀ i ∈ l, α i), (Quotient.finChoiceAux l fun i h => ⟦f i h⟧) = ⟦f⟧
  | [], f => Quotient.sound fun i h => h.elim
  | i :: l, f => by
    simp [Quotient.finChoiceAux, Quotient.finChoiceAux_eq l]
    refine' Quotient.sound fun j h => _
    by_cases e : j = i <;> simp [e]
    subst j; rfl
#align quotient.fin_choice_aux_eq Quotient.finChoiceAux_eq

#print Quotient.finChoice /-
/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def Quotient.finChoice {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _}
    [S : ∀ i, Setoid (α i)] (f : ∀ i, Quotient (S i)) : @Quotient (∀ i, α i) (by infer_instance) :=
  Quotient.liftOn
    (@Quotient.recOn _ _ (fun l : Multiset ι => @Quotient (∀ i ∈ l, α i) (by infer_instance))
      Finset.univ.1 (fun l => Quotient.finChoiceAux l fun i _ => f i) fun a b h =>
      by
      have := fun a => Quotient.finChoiceAux_eq a fun i h => Quotient.out (f i)
      simp [Quotient.out_eq] at this
      simp [this]
      let g := fun a : Multiset ι => ⟦fun (i : ι) (h : i ∈ a) => Quotient.out (f i)⟧
      refine' eq_of_hEq ((eq_rec_hEq _ _).trans (_ : HEq (g a) (g b)))
      congr 1; exact Quotient.sound h)
    (fun f => ⟦fun i => f i (Finset.mem_univ _)⟧) fun a b h => Quotient.sound fun i => h _ _
#align quotient.fin_choice Quotient.finChoice
-/

/- warning: quotient.fin_choice_eq -> Quotient.finChoice_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] {α : ι -> Type.{u2}} [_inst_3 : forall (i : ι), Setoid.{succ u2} (α i)] (f : forall (i : ι), α i), Eq.{max (succ u1) (succ u2)} (Quotient.{max (succ u1) (succ u2)} (forall (i : ι), α i) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i))) (Quotient.finChoice.{u1, u2} ι (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => Quotient.mk'.{succ u2} (α i) (_inst_3 i) (f i))) (Quotient.mk'.{max (succ u1) (succ u2)} (forall (i : ι), α i) (piSetoid.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i)) f)
but is expected to have type
  forall {ι : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] {α : ι -> Type.{u1}} [_inst_3 : forall (i : ι), Setoid.{succ u1} (α i)] (f : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u2) (succ u1)} (forall (i : ι), α i) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), α i)) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i)))) (Quotient.finChoice.{u2, u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i) (fun (i : ι) => Quotient.mk.{succ u1} (α i) (_inst_3 i) (f i))) (Quotient.mk.{max (succ u2) (succ u1)} (forall (i : ι), α i) (inferInstance.{max (succ u2) (succ u1)} (Setoid.{max (succ u2) (succ u1)} (forall (i : ι), α i)) (piSetoid.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_3 i))) f)
Case conversion may be inaccurate. Consider using '#align quotient.fin_choice_eq Quotient.finChoice_eqₓ'. -/
theorem Quotient.finChoice_eq {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _}
    [∀ i, Setoid (α i)] (f : ∀ i, α i) : (Quotient.finChoice fun i => ⟦f i⟧) = ⟦f⟧ :=
  by
  let q
  swap
  change Quotient.liftOn q _ _ = _
  have : q = ⟦fun i h => f i⟧ := by
    dsimp only [q]
    exact Quotient.inductionOn (@Finset.univ ι _).1 fun l => Quotient.finChoiceAux_eq _ _
  simp [this]
  exact Setoid.refl _
#align quotient.fin_choice_eq Quotient.finChoice_eq

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α → Prop) [DecidablePred p]

#print Fintype.chooseX /-
/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ (by simp <;> exact hp), Finset.choose_property _ _ _⟩
#align fintype.choose_x Fintype.chooseX
-/

#print Fintype.choose /-
/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α :=
  chooseX p hp
#align fintype.choose Fintype.choose
-/

#print Fintype.choose_spec /-
theorem choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
  (chooseX p hp).property
#align fintype.choose_spec Fintype.choose_spec
-/

#print Fintype.choose_subtype_eq /-
@[simp]
theorem choose_subtype_eq {α : Type _} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α]
    (x : { a : α // p a })
    (h : ∃! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by simpa [Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]
#align fintype.choose_subtype_eq Fintype.choose_subtype_eq
-/

end Choose

section BijectionInverse

open Function

variable [Fintype α] [DecidableEq β] {f : α → β}

#print Fintype.bijInv /-
/-- `bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bijInv (f_bij : Bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b)
    (by
      rcases f_bij.right b with ⟨a', fa_eq_b⟩
      rw [← fa_eq_b]
      exact ⟨a', ⟨rfl, fun a h => f_bij.left h⟩⟩)
#align fintype.bij_inv Fintype.bijInv
-/

/- warning: fintype.left_inverse_bij_inv -> Fintype.leftInverse_bijInv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β} (f_bij : Function.Bijective.{succ u1, succ u2} α β f), Function.LeftInverse.{succ u1, succ u2} α β (Fintype.bijInv.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f f_bij) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β} (f_bij : Function.Bijective.{succ u2, succ u1} α β f), Function.LeftInverse.{succ u2, succ u1} α β (Fintype.bijInv.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f f_bij) f
Case conversion may be inaccurate. Consider using '#align fintype.left_inverse_bij_inv Fintype.leftInverse_bijInvₓ'. -/
theorem leftInverse_bijInv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)
#align fintype.left_inverse_bij_inv Fintype.leftInverse_bijInv

/- warning: fintype.right_inverse_bij_inv -> Fintype.rightInverse_bijInv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β} (f_bij : Function.Bijective.{succ u1, succ u2} α β f), Function.RightInverse.{succ u1, succ u2} α β (Fintype.bijInv.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f f_bij) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β} (f_bij : Function.Bijective.{succ u2, succ u1} α β f), Function.RightInverse.{succ u2, succ u1} α β (Fintype.bijInv.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f f_bij) f
Case conversion may be inaccurate. Consider using '#align fintype.right_inverse_bij_inv Fintype.rightInverse_bijInvₓ'. -/
theorem rightInverse_bijInv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _
#align fintype.right_inverse_bij_inv Fintype.rightInverse_bijInv

/- warning: fintype.bijective_bij_inv -> Fintype.bijective_bijInv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : α -> β} (f_bij : Function.Bijective.{succ u1, succ u2} α β f), Function.Bijective.{succ u2, succ u1} β α (Fintype.bijInv.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f f_bij)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : α -> β} (f_bij : Function.Bijective.{succ u2, succ u1} α β f), Function.Bijective.{succ u1, succ u2} β α (Fintype.bijInv.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f f_bij)
Case conversion may be inaccurate. Consider using '#align fintype.bijective_bij_inv Fintype.bijective_bijInvₓ'. -/
theorem bijective_bijInv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(rightInverse_bijInv _).Injective, (leftInverse_bijInv _).Surjective⟩
#align fintype.bijective_bij_inv Fintype.bijective_bijInv

end BijectionInverse

end Fintype

section Trunc

#print truncOfMultisetExistsMem /-
/-- For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (∃ x, x ∈ s) → Trunc α :=
  Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a
#align trunc_of_multiset_exists_mem truncOfMultisetExistsMem
-/

#print truncOfNonemptyFintype /-
/-- A `nonempty` `fintype` constructively contains an element.
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val (by simp)
#align trunc_of_nonempty_fintype truncOfNonemptyFintype
-/

#print truncSigmaOfExists /-
/-- By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) :
    Trunc (Σ'a, P a) :=
  @truncOfNonemptyFintype (Σ'a, P a) (Exists.elim h fun a ha => ⟨⟨a, ha⟩⟩) _
#align trunc_sigma_of_exists truncSigmaOfExists
-/

end Trunc

namespace Multiset

variable [Fintype α] [DecidableEq α]

#print Multiset.count_univ /-
@[simp]
theorem count_univ (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.Nodup (Finset.mem_univ _)
#align multiset.count_univ Multiset.count_univ
-/

end Multiset

#print seqOfForallFinsetExistsAux /-
/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seqOfForallFinsetExistsAux {α : Type _} [DecidableEq α] (P : α → Prop)
    (r : α → α → Prop) (h : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y) : ℕ → α
  | n =>
    Classical.choose
      (h
        (Finset.image (fun i : Fin n => seqOfForallFinsetExistsAux i)
          (Finset.univ : Finset (Fin n))))decreasing_by
  exact i.2
#align seq_of_forall_finset_exists_aux seqOfForallFinsetExistsAux
-/

#print exists_seq_of_forall_finset_exists /-
/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists {α : Type _} (P : α → Prop) (r : α → α → Prop)
    (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m < n → r (f m) (f n) := by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, hy⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : ∀ s : Finset α, ∃ y, (∀ x ∈ s, P x) → P y ∧ ∀ x ∈ s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : ∀ n : ℕ, P (f n) := by
      intro n
      induction' n using Nat.strong_induction_on with n IH
      have IH' : ∀ x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf, seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine' ⟨f, A, fun m n hmn => _⟩
    nth_rw 2 [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩
#align exists_seq_of_forall_finset_exists exists_seq_of_forall_finset_exists
-/

#print exists_seq_of_forall_finset_exists' /-
/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists' {α : Type _} (P : α → Prop) (r : α → α → Prop)
    [IsSymm α r] (h : ∀ s : Finset α, (∀ x ∈ s, P x) → ∃ y, P y ∧ ∀ x ∈ s, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m ≠ n → r (f m) (f n) :=
  by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine' ⟨f, hf, fun m n hmn => _⟩
  rcases lt_trichotomy m n with (h | rfl | h)
  · exact hf' m n h
  · exact (hmn rfl).elim
  · apply symm
    exact hf' n m h
#align exists_seq_of_forall_finset_exists' exists_seq_of_forall_finset_exists'
-/

