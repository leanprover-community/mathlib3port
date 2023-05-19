/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.complete_lattice
! leanprover-community/mathlib commit 5709b0d8725255e76f47debca6400c07b5c2d8e6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Bool.Set
import Mathbin.Data.Nat.Set
import Mathbin.Data.Ulift
import Mathbin.Order.Bounds.Basic
import Mathbin.Order.Hom.Basic

/-!
# Theory of complete lattices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supr (f : ι → α)` and `infi (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class complete_lattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class complete_linear_order`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `Sup` is called `Sup`
* `Inf` is called `Inf`
* `⨆ i, s i` is called `supr`
* `⨅ i, s i` is called `infi`
* `⨆ i j, s i j` is called `supr₂`. This is a `supr` inside a `supr`.
* `⨅ i j, s i j` is called `infi₂`. This is an `infi` inside an `infi`.
* `⨆ i ∈ s, t i` is called `bsupr` for "bounded `supr`". This is the special case of `supr₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `binfi` for "bounded `infi`". This is the special case of `infi₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `supr f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infi f`, the infimum of the range of `f`.
-/


open Function OrderDual Set

variable {α β β₂ γ : Type _} {ι ι' : Sort _} {κ : ι → Sort _} {κ' : ι' → Sort _}

#print SupSet /-
/-- class for the `Sup` operator -/
class SupSet (α : Type _) where
  sSup : Set α → α
#align has_Sup SupSet
-/

#print InfSet /-
/-- class for the `Inf` operator -/
class InfSet (α : Type _) where
  sInf : Set α → α
#align has_Inf InfSet
-/

export SupSet (sSup)

export InfSet (sInf)

/-- Supremum of a set -/
add_decl_doc SupSet.sSup

/-- Infimum of a set -/
add_decl_doc InfSet.sInf

#print iSup /-
/-- Indexed supremum -/
def iSup [SupSet α] {ι} (s : ι → α) : α :=
  sSup (range s)
#align supr iSup
-/

#print iInf /-
/-- Indexed infimum -/
def iInf [InfSet α] {ι} (s : ι → α) : α :=
  sInf (range s)
#align infi iInf
-/

#print infSet_to_nonempty /-
instance (priority := 50) infSet_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨sInf ∅⟩
#align has_Inf_to_nonempty infSet_to_nonempty
-/

#print supSet_to_nonempty /-
instance (priority := 50) supSet_to_nonempty (α) [SupSet α] : Nonempty α :=
  ⟨sSup ∅⟩
#align has_Sup_to_nonempty supSet_to_nonempty
-/

-- mathport name: «expr⨆ , »
notation3"⨆ "(...)", "r:(scoped f => iSup f) => r

-- mathport name: «expr⨅ , »
notation3"⨅ "(...)", "r:(scoped f => iInf f) => r

instance (α) [InfSet α] : SupSet αᵒᵈ :=
  ⟨(sInf : Set α → α)⟩

instance (α) [SupSet α] : InfSet αᵒᵈ :=
  ⟨(sSup : Set α → α)⟩

#print CompleteSemilatticeSup /-
/-- Note that we rarely use `complete_semilattice_Sup`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type _) extends PartialOrder α, SupSet α where
  le_sup : ∀ s, ∀ a ∈ s, a ≤ Sup s
  sup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → Sup s ≤ a
#align complete_semilattice_Sup CompleteSemilatticeSup
-/

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

/- warning: le_Sup -> le_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Sup le_sSupₓ'. -/
@[ematch]
theorem le_sSup : a ∈ s → a ≤ sSup s :=
  CompleteSemilatticeSup.le_sup s a
#align le_Sup le_sSup

/- warning: Sup_le -> sSup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Sup_le sSup_leₓ'. -/
theorem sSup_le : (∀ b ∈ s, b ≤ a) → sSup s ≤ a :=
  CompleteSemilatticeSup.sup_le s a
#align Sup_le sSup_le

/- warning: is_lub_Sup -> isLUB_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] (s : Set.{u1} α), IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] (s : Set.{u1} α), IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align is_lub_Sup isLUB_sSupₓ'. -/
theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
  ⟨fun x => le_sSup, fun x => sSup_le⟩
#align is_lub_Sup isLUB_sSup

/- warning: is_lub.Sup_eq -> IsLUB.sSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_lub.Sup_eq IsLUB.sSup_eqₓ'. -/
theorem IsLUB.sSup_eq (h : IsLUB s a) : sSup s = a :=
  (isLUB_sSup s).unique h
#align is_lub.Sup_eq IsLUB.sSup_eq

/- warning: le_Sup_of_le -> le_sSup_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Sup_of_le le_sSup_of_leₓ'. -/
theorem le_sSup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_sSup hb)
#align le_Sup_of_le le_sSup_of_le

/- warning: Sup_le_Sup -> sSup_le_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_le_Sup sSup_le_sSupₓ'. -/
theorem sSup_le_sSup (h : s ⊆ t) : sSup s ≤ sSup t :=
  (isLUB_sSup s).mono (isLUB_sSup t) h
#align Sup_le_Sup sSup_le_sSup

/- warning: Sup_le_iff -> sSup_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align Sup_le_iff sSup_le_iffₓ'. -/
@[simp]
theorem sSup_le_iff : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_sSup s)
#align Sup_le_iff sSup_le_iff

/- warning: le_Sup_iff -> le_sSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align le_Sup_iff le_sSup_iffₓ'. -/
theorem le_sSup_iff : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h b hb => le_trans h (sSup_le hb), fun hb => hb _ fun x => le_sSup⟩
#align le_Sup_iff le_sSup_iff

/- warning: le_supr_iff -> le_iSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {a : α} {s : ι -> α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (s i) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteSemilatticeSup.{u2} α] {a : α} {s : ι -> α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeSup.toPartialOrder.{u2} α _inst_1))) a (iSup.{u2, u1} α (CompleteSemilatticeSup.toSupSet.{u2} α _inst_1) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeSup.toPartialOrder.{u2} α _inst_1))) (s i) b) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeSup.toPartialOrder.{u2} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align le_supr_iff le_iSup_iffₓ'. -/
theorem le_iSup_iff {s : ι → α} : a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [iSup, le_sSup_iff, upperBounds]
#align le_supr_iff le_iSup_iff

/- warning: Sup_le_Sup_of_forall_exists_le -> sSup_le_sSup_of_forall_exists_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) x y)))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) x y)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_le_Sup_of_forall_exists_le sSup_le_sSup_of_forall_exists_leₓ'. -/
theorem sSup_le_sSup_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : sSup s ≤ sSup t :=
  le_sSup_iff.2 fun b hb =>
    sSup_le fun a ha =>
      let ⟨c, hct, hac⟩ := h a ha
      hac.trans (hb hct)
#align Sup_le_Sup_of_forall_exists_le sSup_le_sSup_of_forall_exists_le

/- warning: Sup_singleton -> sSup_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align Sup_singleton sSup_singletonₓ'. -/
-- We will generalize this to conditionally complete lattices in `cSup_singleton`.
theorem sSup_singleton {a : α} : sSup {a} = a :=
  isLUB_singleton.sSup_eq
#align Sup_singleton sSup_singleton

end

#print CompleteSemilatticeInf /-
/-- Note that we rarely use `complete_semilattice_Inf`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeInf (α : Type _) extends PartialOrder α, InfSet α where
  inf_le : ∀ s, ∀ a ∈ s, Inf s ≤ a
  le_inf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ Inf s
#align complete_semilattice_Inf CompleteSemilatticeInf
-/

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

/- warning: Inf_le -> sInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Inf_le sInf_leₓ'. -/
@[ematch]
theorem sInf_le : a ∈ s → sInf s ≤ a :=
  CompleteSemilatticeInf.inf_le s a
#align Inf_le sInf_le

/- warning: le_Inf -> le_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Inf le_sInfₓ'. -/
theorem le_sInf : (∀ b ∈ s, a ≤ b) → a ≤ sInf s :=
  CompleteSemilatticeInf.le_inf s a
#align le_Inf le_sInf

/- warning: is_glb_Inf -> isGLB_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] (s : Set.{u1} α), IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] (s : Set.{u1} α), IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align is_glb_Inf isGLB_sInfₓ'. -/
theorem isGLB_sInf (s : Set α) : IsGLB s (sInf s) :=
  ⟨fun a => sInf_le, fun a => le_sInf⟩
#align is_glb_Inf isGLB_sInf

/- warning: is_glb.Inf_eq -> IsGLB.sInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_glb.Inf_eq IsGLB.sInf_eqₓ'. -/
theorem IsGLB.sInf_eq (h : IsGLB s a) : sInf s = a :=
  (isGLB_sInf s).unique h
#align is_glb.Inf_eq IsGLB.sInf_eq

/- warning: Inf_le_of_le -> sInf_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Inf_le_of_le sInf_le_of_leₓ'. -/
theorem sInf_le_of_le (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (sInf_le hb) h
#align Inf_le_of_le sInf_le_of_le

/- warning: Inf_le_Inf -> sInf_le_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Inf sInf_le_sInfₓ'. -/
theorem sInf_le_sInf (h : s ⊆ t) : sInf t ≤ sInf s :=
  (isGLB_sInf s).mono (isGLB_sInf t) h
#align Inf_le_Inf sInf_le_sInf

/- warning: le_Inf_iff -> le_sInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align le_Inf_iff le_sInf_iffₓ'. -/
@[simp]
theorem le_sInf_iff : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_sInf s)
#align le_Inf_iff le_sInf_iff

/- warning: Inf_le_iff -> sInf_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align Inf_le_iff sInf_le_iffₓ'. -/
theorem sInf_le_iff : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h b hb => le_trans (le_sInf hb) h, fun hb => hb _ fun x => sInf_le⟩
#align Inf_le_iff sInf_le_iff

/- warning: infi_le_iff -> iInf_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {a : α} {s : ι -> α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) ι s) a) (forall (b : α), (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b (s i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteSemilatticeInf.{u2} α] {a : α} {s : ι -> α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α _inst_1))) (iInf.{u2, u1} α (CompleteSemilatticeInf.toInfSet.{u2} α _inst_1) ι s) a) (forall (b : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α _inst_1))) b (s i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align infi_le_iff iInf_le_iffₓ'. -/
theorem iInf_le_iff {s : ι → α} : iInf s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [iInf, sInf_le_iff, lowerBounds]
#align infi_le_iff iInf_le_iff

/- warning: Inf_le_Inf_of_forall_exists_le -> sInf_le_sInf_of_forall_exists_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) y x)))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) y x)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Inf_of_forall_exists_le sInf_le_sInf_of_forall_exists_leₓ'. -/
theorem sInf_le_sInf_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : sInf t ≤ sInf s :=
  le_of_forall_le
    (by
      simp only [le_sInf_iff]
      introv h₀ h₁
      rcases h _ h₁ with ⟨y, hy, hy'⟩
      solve_by_elim [le_trans _ hy'] )
#align Inf_le_Inf_of_forall_exists_le sInf_le_sInf_of_forall_exists_le

/- warning: Inf_singleton -> sInf_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align Inf_singleton sInf_singletonₓ'. -/
-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem sInf_singleton {a : α} : sInf {a} = a :=
  isGLB_singleton.sInf_eq
#align Inf_singleton sInf_singleton

end

#print CompleteLattice /-
/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
@[protect_proj]
class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α,
  CompleteSemilatticeInf α, Top α, Bot α where
  le_top : ∀ x : α, x ≤ ⊤
  bot_le : ∀ x : α, ⊥ ≤ x
#align complete_lattice CompleteLattice
-/

/- warning: complete_lattice.to_bounded_order -> CompleteLattice.toBoundedOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [h : CompleteLattice.{u1} α], BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α h))))
but is expected to have type
  forall {α : Type.{u1}} [h : CompleteLattice.{u1} α], BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α h))))
Case conversion may be inaccurate. Consider using '#align complete_lattice.to_bounded_order CompleteLattice.toBoundedOrderₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) CompleteLattice.toBoundedOrder [h : CompleteLattice α] :
    BoundedOrder α :=
  { h with }
#align complete_lattice.to_bounded_order CompleteLattice.toBoundedOrder

#print completeLatticeOfInf /-
/-- Create a `complete_lattice` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup, bot, top
  ..complete_lattice_of_Inf my_T _ }
```
-/
def completeLatticeOfInf (α : Type _) [H1 : PartialOrder α] [H2 : InfSet α]
    (is_glb_Inf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α :=
  { H1, H2 with
    bot := sInf univ
    bot_le := fun x => (isGLB_sInf univ).1 trivial
    top := sInf ∅
    le_top := fun a => (isGLB_sInf ∅).2 <| by simp
    sup := fun a b => sInf { x | a ≤ x ∧ b ≤ x }
    inf := fun a b => sInf {a, b}
    le_inf := fun a b c hab hac => by
      apply (isGLB_sInf _).2
      simp [*]
    inf_le_right := fun a b => (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf_le_left := fun a b => (isGLB_sInf _).1 <| mem_insert _ _
    sup_le := fun a b c hac hbc => (isGLB_sInf _).1 <| by simp [*]
    le_sup_left := fun a b => (isGLB_sInf _).2 fun x => And.left
    le_sup_right := fun a b => (isGLB_sInf _).2 fun x => And.right
    le_inf := fun s a ha => (isGLB_sInf s).2 ha
    inf_le := fun s a ha => (isGLB_sInf s).1 ha
    sSup := fun s => sInf (upperBounds s)
    le_sup := fun s a ha => (isGLB_sInf (upperBounds s)).2 fun b hb => hb ha
    sup_le := fun s a ha => (isGLB_sInf (upperBounds s)).1 ha }
#align complete_lattice_of_Inf completeLatticeOfInf
-/

#print completeLatticeOfCompleteSemilatticeInf /-
/-- Any `complete_semilattice_Inf` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Inf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type _) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_sInf s
#align complete_lattice_of_complete_semilattice_Inf completeLatticeOfCompleteSemilatticeInf
-/

#print completeLatticeOfSup /-
/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf, bot, top
  ..complete_lattice_of_Sup my_T _ }
```
-/
def completeLatticeOfSup (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (is_lub_Sup : ∀ s : Set α, IsLUB s (sSup s)) : CompleteLattice α :=
  { H1, H2 with
    top := sSup univ
    le_top := fun x => (isLUB_sSup univ).1 trivial
    bot := sSup ∅
    bot_le := fun x => (isLUB_sSup ∅).2 <| by simp
    sup := fun a b => sSup {a, b}
    sup_le := fun a b c hac hbc => (isLUB_sSup _).2 (by simp [*])
    le_sup_left := fun a b => (isLUB_sSup _).1 <| mem_insert _ _
    le_sup_right := fun a b => (isLUB_sSup _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf := fun a b => sSup { x | x ≤ a ∧ x ≤ b }
    le_inf := fun a b c hab hac => (isLUB_sSup _).1 <| by simp [*]
    inf_le_left := fun a b => (isLUB_sSup _).2 fun x => And.left
    inf_le_right := fun a b => (isLUB_sSup _).2 fun x => And.right
    sInf := fun s => sSup (lowerBounds s)
    sup_le := fun s a ha => (isLUB_sSup s).2 ha
    le_sup := fun s a ha => (isLUB_sSup s).1 ha
    inf_le := fun s a ha => (isLUB_sSup (lowerBounds s)).2 fun b hb => hb ha
    le_inf := fun s a ha => (isLUB_sSup (lowerBounds s)).1 ha }
#align complete_lattice_of_Sup completeLatticeOfSup
-/

#print completeLatticeOfCompleteSemilatticeSup /-
/-- Any `complete_semilattice_Sup` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Sup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type _) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_sSup s
#align complete_lattice_of_complete_semilattice_Sup completeLatticeOfCompleteSemilatticeSup
-/

#print CompleteLinearOrder /-
/- ./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure -/
/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type _) extends CompleteLattice α,
  "./././Mathport/Syntax/Translate/Command.lean:422:11: unsupported: advanced extends in structure"
#align complete_linear_order CompleteLinearOrder
-/

namespace OrderDual

variable (α)

instance [CompleteLattice α] : CompleteLattice αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.hasSup α, OrderDual.hasInf α,
    OrderDual.boundedOrder α with
    le_sup := @CompleteLattice.inf_le α _
    sup_le := @CompleteLattice.le_inf α _
    inf_le := @CompleteLattice.le_sup α _
    le_inf := @CompleteLattice.sup_le α _ }

instance [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ :=
  { OrderDual.completeLattice α, OrderDual.linearOrder α with }

end OrderDual

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

#print toDual_sSup /-
@[simp]
theorem toDual_sSup (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Sup toDual_sSup
-/

#print toDual_sInf /-
@[simp]
theorem toDual_sInf (s : Set α) : toDual (sInf s) = sSup (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Inf toDual_sInf
-/

#print ofDual_sSup /-
@[simp]
theorem ofDual_sSup (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' s) :=
  rfl
#align of_dual_Sup ofDual_sSup
-/

#print ofDual_sInf /-
@[simp]
theorem ofDual_sInf (s : Set αᵒᵈ) : ofDual (sInf s) = sSup (toDual ⁻¹' s) :=
  rfl
#align of_dual_Inf ofDual_sInf
-/

/- warning: to_dual_supr -> toDual_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (iInf.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (iInf.{u2, u1} (OrderDual.{u2} α) (OrderDual.infSet.{u2} α (CompleteLattice.toSupSet.{u2} α _inst_1)) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align to_dual_supr toDual_iSupₓ'. -/
@[simp]
theorem toDual_iSup (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl
#align to_dual_supr toDual_iSup

/- warning: to_dual_infi -> toDual_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (iSup.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (iSup.{u2, u1} (OrderDual.{u2} α) (OrderDual.supSet.{u2} α (CompleteLattice.toInfSet.{u2} α _inst_1)) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u2} α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)) (OrderDual.toDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align to_dual_infi toDual_iInfₓ'. -/
@[simp]
theorem toDual_iInf (f : ι → α) : toDual (⨅ i, f i) = ⨆ i, toDual (f i) :=
  rfl
#align to_dual_infi toDual_iInf

/- warning: of_dual_supr -> ofDual_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (iSup.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) (iSup.{u2, u1} (OrderDual.{u2} α) (OrderDual.supSet.{u2} α (CompleteLattice.toInfSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (iSup.{u2, u1} (OrderDual.{u2} α) (OrderDual.supSet.{u2} α (CompleteLattice.toInfSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align of_dual_supr ofDual_iSupₓ'. -/
@[simp]
theorem ofDual_iSup (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl
#align of_dual_supr ofDual_iSup

/- warning: of_dual_infi -> ofDual_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (iInf.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) (iInf.{u2, u1} (OrderDual.{u2} α) (OrderDual.infSet.{u2} α (CompleteLattice.toSupSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (iInf.{u2, u1} (OrderDual.{u2} α) (OrderDual.infSet.{u2} α (CompleteLattice.toSupSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u2} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.ofDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align of_dual_infi ofDual_iInfₓ'. -/
@[simp]
theorem ofDual_iInf (f : ι → αᵒᵈ) : ofDual (⨅ i, f i) = ⨆ i, ofDual (f i) :=
  rfl
#align of_dual_infi ofDual_iInf

/- warning: Inf_le_Sup -> sInf_le_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Sup sInf_le_sSupₓ'. -/
theorem sInf_le_sSup (hs : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs
#align Inf_le_Sup sInf_le_sSup

/- warning: Sup_union -> sSup_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_union sSup_unionₓ'. -/
theorem sSup_union {s t : Set α} : sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq
#align Sup_union sSup_union

/- warning: Inf_union -> sInf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Inf_union sInf_unionₓ'. -/
theorem sInf_union {s t : Set α} : sInf (s ∪ t) = sInf s ⊓ sInf t :=
  ((isGLB_sInf s).union (isGLB_sInf t)).sInf_eq
#align Inf_union sInf_union

/- warning: Sup_inter_le -> sSup_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_inter_le sSup_inter_leₓ'. -/
theorem sSup_inter_le {s t : Set α} : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  sSup_le fun b hb => le_inf (le_sSup hb.1) (le_sSup hb.2)
#align Sup_inter_le sSup_inter_le

/- warning: le_Inf_inter -> le_sInf_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) t)) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) t)) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align le_Inf_inter le_sInf_interₓ'. -/
theorem le_sInf_inter {s t : Set α} : sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  @sSup_inter_le αᵒᵈ _ _ _
#align le_Inf_inter le_sInf_inter

/- warning: Sup_empty -> sSup_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_empty sSup_emptyₓ'. -/
@[simp]
theorem sSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).sSup_eq
#align Sup_empty sSup_empty

/- warning: Inf_empty -> sInf_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Inf_empty sInf_emptyₓ'. -/
@[simp]
theorem sInf_empty : sInf ∅ = (⊤ : α) :=
  (@isGLB_empty α _ _).sInf_eq
#align Inf_empty sInf_empty

/- warning: Sup_univ -> sSup_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.univ.{u1} α)) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.univ.{u1} α)) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_univ sSup_univₓ'. -/
@[simp]
theorem sSup_univ : sSup univ = (⊤ : α) :=
  (@isLUB_univ α _ _).sSup_eq
#align Sup_univ sSup_univ

/- warning: Inf_univ -> sInf_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Set.univ.{u1} α)) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.univ.{u1} α)) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Inf_univ sInf_univₓ'. -/
@[simp]
theorem sInf_univ : sInf univ = (⊥ : α) :=
  (@isGLB_univ α _ _).sInf_eq
#align Inf_univ sInf_univ

/- warning: Sup_insert -> sSup_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Sup_insert sSup_insertₓ'. -/
-- TODO(Jeremy): get this automatically
@[simp]
theorem sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_sSup s).insert a).sSup_eq
#align Sup_insert sSup_insert

/- warning: Inf_insert -> sInf_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_insert sInf_insertₓ'. -/
@[simp]
theorem sInf_insert {a : α} {s : Set α} : sInf (insert a s) = a ⊓ sInf s :=
  ((isGLB_sInf s).insert a).sInf_eq
#align Inf_insert sInf_insert

/- warning: Sup_le_Sup_of_subset_insert_bot -> sSup_le_sSup_of_subset_insert_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_le_Sup_of_subset_insert_bot sSup_le_sSup_of_subset_insert_botₓ'. -/
theorem sSup_le_sSup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sSup s ≤ sSup t :=
  le_trans (sSup_le_sSup h) (le_of_eq (trans sSup_insert bot_sup_eq))
#align Sup_le_Sup_of_subset_insert_bot sSup_le_sSup_of_subset_insert_bot

/- warning: Inf_le_Inf_of_subset_insert_top -> sInf_le_sInf_of_subset_insert_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) t) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) t) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Inf_of_subset_insert_top sInf_le_sInf_of_subset_insert_topₓ'. -/
theorem sInf_le_sInf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : sInf t ≤ sInf s :=
  le_trans (le_of_eq (trans top_inf_eq.symm sInf_insert.symm)) (sInf_le_sInf h)
#align Inf_le_Inf_of_subset_insert_top sInf_le_sInf_of_subset_insert_top

/- warning: Sup_diff_singleton_bot -> sSup_diff_singleton_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align Sup_diff_singleton_bot sSup_diff_singleton_botₓ'. -/
@[simp]
theorem sSup_diff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s :=
  (sSup_le_sSup (diff_subset _ _)).antisymm <|
    sSup_le_sSup_of_subset_insert_bot <| subset_insert_diff_singleton _ _
#align Sup_diff_singleton_bot sSup_diff_singleton_bot

/- warning: Inf_diff_singleton_top -> sInf_diff_singleton_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align Inf_diff_singleton_top sInf_diff_singleton_topₓ'. -/
@[simp]
theorem sInf_diff_singleton_top (s : Set α) : sInf (s \ {⊤}) = sInf s :=
  @sSup_diff_singleton_bot αᵒᵈ _ s
#align Inf_diff_singleton_top sInf_diff_singleton_top

/- warning: Sup_pair -> sSup_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align Sup_pair sSup_pairₓ'. -/
theorem sSup_pair {a b : α} : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).sSup_eq
#align Sup_pair sSup_pair

/- warning: Inf_pair -> sInf_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align Inf_pair sInf_pairₓ'. -/
theorem sInf_pair {a b : α} : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair α _ a b).sInf_eq
#align Inf_pair sInf_pair

/- warning: Sup_eq_bot -> sSup_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u1} α a (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Eq.{succ u1} α a (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align Sup_eq_bot sSup_eq_botₓ'. -/
@[simp]
theorem sSup_eq_bot : sSup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h a ha => bot_unique <| h ▸ le_sSup ha, fun h =>
    bot_unique <| sSup_le fun a ha => le_bot_iff.2 <| h a ha⟩
#align Sup_eq_bot sSup_eq_bot

/- warning: Inf_eq_top -> sInf_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u1} α a (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Eq.{succ u1} α a (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align Inf_eq_top sInf_eq_topₓ'. -/
@[simp]
theorem sInf_eq_top : sInf s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  @sSup_eq_bot αᵒᵈ _ _
#align Inf_eq_top sInf_eq_top

/- warning: eq_singleton_bot_of_Sup_eq_bot_of_nonempty -> eq_singleton_bot_of_sSup_eq_bot_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_sSup_eq_bot_of_nonemptyₓ'. -/
theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} :=
  by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩
#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_sSup_eq_bot_of_nonempty

/- warning: eq_singleton_top_of_Inf_eq_top_of_nonempty -> eq_singleton_top_of_sInf_eq_top_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_sInf_eq_top_of_nonemptyₓ'. -/
theorem eq_singleton_top_of_sInf_eq_top_of_nonempty : sInf s = ⊤ → s.Nonempty → s = {⊤} :=
  @eq_singleton_bot_of_sSup_eq_bot_of_nonempty αᵒᵈ _ _
#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_sInf_eq_top_of_nonempty

/- warning: Sup_eq_of_forall_le_of_forall_lt_exists_gt -> sSup_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w b) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w a)))) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w b) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w a)))) -> (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align Sup_eq_of_forall_le_of_forall_lt_exists_gt sSup_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `cSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨a, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').False
#align Sup_eq_of_forall_le_of_forall_lt_exists_gt sSup_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: Inf_eq_of_forall_ge_of_forall_gt_exists_lt -> sInf_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b w) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a w)))) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b w) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a w)))) -> (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt sInf_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem sInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  @sSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt sInf_eq_of_forall_ge_of_forall_gt_exists_lt

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

/- warning: lt_Sup_iff -> lt_sSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a)))
Case conversion may be inaccurate. Consider using '#align lt_Sup_iff lt_sSup_iffₓ'. -/
theorem lt_sSup_iff : b < sSup s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_sSup s
#align lt_Sup_iff lt_sSup_iff

/- warning: Inf_lt_iff -> sInf_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s) b) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s) b) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align Inf_lt_iff sInf_lt_iffₓ'. -/
theorem sInf_lt_iff : sInf s < b ↔ ∃ a ∈ s, a < b :=
  isGLB_lt_iff <| isGLB_sInf s
#align Inf_lt_iff sInf_lt_iff

/- warning: Sup_eq_top -> sSup_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Top.top.{u1} α (CompleteLattice.toTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a))))
Case conversion may be inaccurate. Consider using '#align Sup_eq_top sSup_eq_topₓ'. -/
theorem sSup_eq_top : sSup s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h b hb => lt_sSup_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨a, ha, h⟩ := h _ h'
        (h.trans_le <| le_sSup ha).False⟩
#align Sup_eq_top sSup_eq_top

/- warning: Inf_eq_bot -> sInf_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b))))
Case conversion may be inaccurate. Consider using '#align Inf_eq_bot sInf_eq_botₓ'. -/
theorem sInf_eq_bot : sInf s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b :=
  @sSup_eq_top αᵒᵈ _ _
#align Inf_eq_bot sInf_eq_bot

/- warning: lt_supr_iff -> lt_iSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f)) (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) a (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f)) (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align lt_supr_iff lt_iSup_iffₓ'. -/
theorem lt_iSup_iff {f : ι → α} : a < iSup f ↔ ∃ i, a < f i :=
  lt_sSup_iff.trans exists_range_iff
#align lt_supr_iff lt_iSup_iff

/- warning: infi_lt_iff -> iInf_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f) a) (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f) a) (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align infi_lt_iff iInf_lt_iffₓ'. -/
theorem iInf_lt_iff {f : ι → α} : iInf f < a ↔ ∃ i, f i < a :=
  sInf_lt_iff.trans exists_range_iff
#align infi_lt_iff iInf_lt_iff

end CompleteLinearOrder

/-
### supr & infi
-/
section SupSet

variable [SupSet α] {f g : ι → α}

/- warning: Sup_range -> sSup_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α}, Eq.{succ u1} α (SupSet.sSup.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) (iSup.{u1, u2} α _inst_1 ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u2} α] {f : ι -> α}, Eq.{succ u2} α (SupSet.sSup.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) (iSup.{u2, u1} α _inst_1 ι f)
Case conversion may be inaccurate. Consider using '#align Sup_range sSup_rangeₓ'. -/
theorem sSup_range : sSup (range f) = iSup f :=
  rfl
#align Sup_range sSup_range

#print sSup_eq_iSup' /-
theorem sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, a := by rw [iSup, Subtype.range_coe]
#align Sup_eq_supr' sSup_eq_iSup'
-/

/- warning: supr_congr -> iSup_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u1} α (f i) (g i)) -> (Eq.{succ u1} α (iSup.{u1, u2} α _inst_1 ι (fun (i : ι) => f i)) (iSup.{u1, u2} α _inst_1 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u2} α (f i) (g i)) -> (Eq.{succ u2} α (iSup.{u2, u1} α _inst_1 ι (fun (i : ι) => f i)) (iSup.{u2, u1} α _inst_1 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align supr_congr iSup_congrₓ'. -/
theorem iSup_congr (h : ∀ i, f i = g i) : (⨆ i, f i) = ⨆ i, g i :=
  congr_arg _ <| funext h
#align supr_congr iSup_congr

/- warning: function.surjective.supr_comp -> Function.Surjective.iSup_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u2, u3} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (iSup.{u1, u2} α _inst_1 ι (fun (x : ι) => g (f x))) (iSup.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u3, u2} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (iSup.{u1, u3} α _inst_1 ι (fun (x : ι) => g (f x))) (iSup.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.supr_comp Function.Surjective.iSup_compₓ'. -/
theorem Function.Surjective.iSup_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨆ x, g (f x)) = ⨆ y, g y := by simp only [iSup, hf.range_comp]
#align function.surjective.supr_comp Function.Surjective.iSup_comp

/- warning: equiv.supr_comp -> Equiv.iSup_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), Eq.{succ u1} α (iSup.{u1, u2} α _inst_1 ι (fun (x : ι) => g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x))) (iSup.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), Eq.{succ u1} α (iSup.{u1, u3} α _inst_1 ι (fun (x : ι) => g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι) => ι') _x) (Equiv.instFunLikeEquiv.{u3, u2} ι ι') e x))) (iSup.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y))
Case conversion may be inaccurate. Consider using '#align equiv.supr_comp Equiv.iSup_compₓ'. -/
theorem Equiv.iSup_comp {g : ι' → α} (e : ι ≃ ι') : (⨆ x, g (e x)) = ⨆ y, g y :=
  e.Surjective.iSup_comp _
#align equiv.supr_comp Equiv.iSup_comp

/- warning: function.surjective.supr_congr -> Function.Surjective.iSup_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u2, u3} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (iSup.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (iSup.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u3, u2} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (iSup.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (iSup.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.supr_congr Function.Surjective.iSup_congrₓ'. -/
protected theorem Function.Surjective.iSup_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y :=
  by
  convert h1.supr_comp g
  exact (funext h2).symm
#align function.surjective.supr_congr Function.Surjective.iSup_congr

/- warning: equiv.supr_congr -> Equiv.iSup_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x)) (f x)) -> (Eq.{succ u1} α (iSup.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (iSup.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι) => ι') _x) (Equiv.instFunLikeEquiv.{u3, u2} ι ι') e x)) (f x)) -> (Eq.{succ u1} α (iSup.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (iSup.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align equiv.supr_congr Equiv.iSup_congrₓ'. -/
protected theorem Equiv.iSup_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨆ x, f x) = ⨆ y, g y :=
  e.Surjective.iSup_congr _ h
#align equiv.supr_congr Equiv.iSup_congr

#print iSup_congr_Prop /-
@[congr]
theorem iSup_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂ :=
  by
  obtain rfl := propext pq
  congr with x
  apply f
#align supr_congr_Prop iSup_congr_Prop
-/

#print iSup_plift_up /-
theorem iSup_plift_up (f : PLift ι → α) : (⨆ i, f (PLift.up i)) = ⨆ i, f i :=
  PLift.up_surjective.iSup_congr _ fun _ => rfl
#align supr_plift_up iSup_plift_up
-/

/- warning: supr_plift_down -> iSup_plift_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : SupSet.{u1} α] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α _inst_1 (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => f (PLift.down.{u2} ι i))) (iSup.{u1, u2} α _inst_1 ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u2} α] (f : ι -> α), Eq.{succ u2} α (iSup.{u2, succ u1} α _inst_1 (PLift.{u1} ι) (fun (i : PLift.{u1} ι) => f (PLift.down.{u1} ι i))) (iSup.{u2, u1} α _inst_1 ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align supr_plift_down iSup_plift_downₓ'. -/
theorem iSup_plift_down (f : ι → α) : (⨆ i, f (PLift.down i)) = ⨆ i, f i :=
  PLift.down_surjective.iSup_congr _ fun _ => rfl
#align supr_plift_down iSup_plift_down

/- warning: supr_range' -> iSup_range' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] (g : β -> α) (f : ι -> β), Eq.{succ u1} α (iSup.{u1, succ u2} α _inst_1 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) (fun (b : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) => g ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, u3} β ι f)))))) b))) (iSup.{u1, u3} α _inst_1 ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] (g : β -> α) (f : ι -> β), Eq.{succ u3} α (iSup.{u3, succ u2} α _inst_1 (Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) (fun (b : Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) => g (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f)) b))) (iSup.{u3, u1} α _inst_1 ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align supr_range' iSup_range'ₓ'. -/
theorem iSup_range' (g : β → α) (f : ι → β) : (⨆ b : range f, g b) = ⨆ i, g (f i) := by
  rw [iSup, iSup, ← image_eq_range, ← range_comp]
#align supr_range' iSup_range'

#print sSup_image' /-
theorem sSup_image' {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a : s, f a := by
  rw [iSup, image_eq_range]
#align Sup_image' sSup_image'
-/

end SupSet

section InfSet

variable [InfSet α] {f g : ι → α}

/- warning: Inf_range -> sInf_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α}, Eq.{succ u1} α (InfSet.sInf.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) (iInf.{u1, u2} α _inst_1 ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u2} α] {f : ι -> α}, Eq.{succ u2} α (InfSet.sInf.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) (iInf.{u2, u1} α _inst_1 ι f)
Case conversion may be inaccurate. Consider using '#align Inf_range sInf_rangeₓ'. -/
theorem sInf_range : sInf (range f) = iInf f :=
  rfl
#align Inf_range sInf_range

#print sInf_eq_iInf' /-
theorem sInf_eq_iInf' (s : Set α) : sInf s = ⨅ a : s, a :=
  @sSup_eq_iSup' αᵒᵈ _ _
#align Inf_eq_infi' sInf_eq_iInf'
-/

/- warning: infi_congr -> iInf_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u1} α (f i) (g i)) -> (Eq.{succ u1} α (iInf.{u1, u2} α _inst_1 ι (fun (i : ι) => f i)) (iInf.{u1, u2} α _inst_1 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u2} α (f i) (g i)) -> (Eq.{succ u2} α (iInf.{u2, u1} α _inst_1 ι (fun (i : ι) => f i)) (iInf.{u2, u1} α _inst_1 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align infi_congr iInf_congrₓ'. -/
theorem iInf_congr (h : ∀ i, f i = g i) : (⨅ i, f i) = ⨅ i, g i :=
  congr_arg _ <| funext h
#align infi_congr iInf_congr

/- warning: function.surjective.infi_comp -> Function.Surjective.iInf_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u2, u3} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (iInf.{u1, u2} α _inst_1 ι (fun (x : ι) => g (f x))) (iInf.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u3, u2} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (iInf.{u1, u3} α _inst_1 ι (fun (x : ι) => g (f x))) (iInf.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.infi_comp Function.Surjective.iInf_compₓ'. -/
theorem Function.Surjective.iInf_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨅ x, g (f x)) = ⨅ y, g y :=
  @Function.Surjective.iSup_comp αᵒᵈ _ _ _ f hf g
#align function.surjective.infi_comp Function.Surjective.iInf_comp

/- warning: equiv.infi_comp -> Equiv.iInf_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), Eq.{succ u1} α (iInf.{u1, u2} α _inst_1 ι (fun (x : ι) => g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x))) (iInf.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), Eq.{succ u1} α (iInf.{u1, u3} α _inst_1 ι (fun (x : ι) => g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι) => ι') _x) (Equiv.instFunLikeEquiv.{u3, u2} ι ι') e x))) (iInf.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y))
Case conversion may be inaccurate. Consider using '#align equiv.infi_comp Equiv.iInf_compₓ'. -/
theorem Equiv.iInf_comp {g : ι' → α} (e : ι ≃ ι') : (⨅ x, g (e x)) = ⨅ y, g y :=
  @Equiv.iSup_comp αᵒᵈ _ _ _ _ e
#align equiv.infi_comp Equiv.iInf_comp

/- warning: function.surjective.infi_congr -> Function.Surjective.iInf_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u2, u3} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (iInf.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (iInf.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u3, u2} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (iInf.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (iInf.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.infi_congr Function.Surjective.iInf_congrₓ'. -/
protected theorem Function.Surjective.iInf_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
  @Function.Surjective.iSup_congr αᵒᵈ _ _ _ _ _ h h1 h2
#align function.surjective.infi_congr Function.Surjective.iInf_congr

/- warning: equiv.infi_congr -> Equiv.iInf_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x)) (f x)) -> (Eq.{succ u1} α (iInf.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (iInf.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι) => ι') _x) (Equiv.instFunLikeEquiv.{u3, u2} ι ι') e x)) (f x)) -> (Eq.{succ u1} α (iInf.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (iInf.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align equiv.infi_congr Equiv.iInf_congrₓ'. -/
protected theorem Equiv.iInf_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨅ x, f x) = ⨅ y, g y :=
  @Equiv.iSup_congr αᵒᵈ _ _ _ _ _ e h
#align equiv.infi_congr Equiv.iInf_congr

#print iInf_congr_Prop /-
@[congr]
theorem iInf_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iInf f₁ = iInf f₂ :=
  @iSup_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f
#align infi_congr_Prop iInf_congr_Prop
-/

#print iInf_plift_up /-
theorem iInf_plift_up (f : PLift ι → α) : (⨅ i, f (PLift.up i)) = ⨅ i, f i :=
  PLift.up_surjective.iInf_congr _ fun _ => rfl
#align infi_plift_up iInf_plift_up
-/

/- warning: infi_plift_down -> iInf_plift_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : InfSet.{u1} α] (f : ι -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α _inst_1 (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => f (PLift.down.{u2} ι i))) (iInf.{u1, u2} α _inst_1 ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u2} α] (f : ι -> α), Eq.{succ u2} α (iInf.{u2, succ u1} α _inst_1 (PLift.{u1} ι) (fun (i : PLift.{u1} ι) => f (PLift.down.{u1} ι i))) (iInf.{u2, u1} α _inst_1 ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align infi_plift_down iInf_plift_downₓ'. -/
theorem iInf_plift_down (f : ι → α) : (⨅ i, f (PLift.down i)) = ⨅ i, f i :=
  PLift.down_surjective.iInf_congr _ fun _ => rfl
#align infi_plift_down iInf_plift_down

/- warning: infi_range' -> iInf_range' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] (g : β -> α) (f : ι -> β), Eq.{succ u1} α (iInf.{u1, succ u2} α _inst_1 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) (fun (b : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) => g ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, u3} β ι f)))))) b))) (iInf.{u1, u3} α _inst_1 ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] (g : β -> α) (f : ι -> β), Eq.{succ u3} α (iInf.{u3, succ u2} α _inst_1 (Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) (fun (b : Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) => g (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f)) b))) (iInf.{u3, u1} α _inst_1 ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align infi_range' iInf_range'ₓ'. -/
theorem iInf_range' (g : β → α) (f : ι → β) : (⨅ b : range f, g b) = ⨅ i, g (f i) :=
  @iSup_range' αᵒᵈ _ _ _ _ _
#align infi_range' iInf_range'

#print sInf_image' /-
theorem sInf_image' {s : Set β} {f : β → α} : sInf (f '' s) = ⨅ a : s, f a :=
  @sSup_image' αᵒᵈ _ _ _ _
#align Inf_image' sInf_image'
-/

end InfSet

section

variable [CompleteLattice α] {f g s t : ι → α} {a b : α}

/- warning: le_supr -> le_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f)
Case conversion may be inaccurate. Consider using '#align le_supr le_iSupₓ'. -/
-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_iSup (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩
#align le_supr le_iSup

/- warning: infi_le -> iInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (f i)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (f i)
Case conversion may be inaccurate. Consider using '#align infi_le iInf_leₓ'. -/
theorem iInf_le (f : ι → α) (i : ι) : iInf f ≤ f i :=
  sInf_le ⟨i, rfl⟩
#align infi_le iInf_le

/- warning: le_supr' -> le_iSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f)
Case conversion may be inaccurate. Consider using '#align le_supr' le_iSup'ₓ'. -/
@[ematch]
theorem le_iSup' (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩
#align le_supr' le_iSup'

/- warning: infi_le' -> iInf_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (f i)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (f i)
Case conversion may be inaccurate. Consider using '#align infi_le' iInf_le'ₓ'. -/
@[ematch]
theorem iInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i :=
  sInf_le ⟨i, rfl⟩
#align infi_le' iInf_le'

/- warning: is_lub_supr -> isLUB_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α}, IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (j : ι) => f j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α}, IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (j : ι) => f j))
Case conversion may be inaccurate. Consider using '#align is_lub_supr isLUB_iSupₓ'. -/
/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] lemma le_supr' (f : ι → α) (i : ι) : (: f i :) ≤ (: supr f :) :=
le_Sup ⟨i, rfl⟩
-/
theorem isLUB_iSup : IsLUB (range f) (⨆ j, f j) :=
  isLUB_sSup _
#align is_lub_supr isLUB_iSup

/- warning: is_glb_infi -> isGLB_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α}, IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (j : ι) => f j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α}, IsGLB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (j : ι) => f j))
Case conversion may be inaccurate. Consider using '#align is_glb_infi isGLB_iInfₓ'. -/
theorem isGLB_iInf : IsGLB (range f) (⨅ j, f j) :=
  isGLB_sInf _
#align is_glb_infi isGLB_iInf

/- warning: is_lub.supr_eq -> IsLUB.iSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (j : ι) => f j)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) a) -> (Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (j : ι) => f j)) a)
Case conversion may be inaccurate. Consider using '#align is_lub.supr_eq IsLUB.iSup_eqₓ'. -/
theorem IsLUB.iSup_eq (h : IsLUB (range f) a) : (⨆ j, f j) = a :=
  h.sSup_eq
#align is_lub.supr_eq IsLUB.iSup_eq

/- warning: is_glb.infi_eq -> IsGLB.iInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (j : ι) => f j)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (IsGLB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) a) -> (Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (j : ι) => f j)) a)
Case conversion may be inaccurate. Consider using '#align is_glb.infi_eq IsGLB.iInf_eqₓ'. -/
theorem IsGLB.iInf_eq (h : IsGLB (range f) a) : (⨅ j, f j) = a :=
  h.sInf_eq
#align is_glb.infi_eq IsGLB.iInf_eq

/- warning: le_supr_of_le -> le_iSup_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (f i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_supr_of_le le_iSup_of_leₓ'. -/
theorem le_iSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f :=
  h.trans <| le_iSup _ i
#align le_supr_of_le le_iSup_of_le

/- warning: infi_le_of_le -> iInf_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) a)
Case conversion may be inaccurate. Consider using '#align infi_le_of_le iInf_le_of_leₓ'. -/
theorem iInf_le_of_le (i : ι) (h : f i ≤ a) : iInf f ≤ a :=
  (iInf_le _ i).trans h
#align infi_le_of_le iInf_le_of_le

/- warning: le_supr₂ -> le_iSup₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j)))
Case conversion may be inaccurate. Consider using '#align le_supr₂ le_iSup₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_iSup₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_iSup_of_le i <| le_iSup (f i) j
#align le_supr₂ le_iSup₂

/- warning: infi₂_le -> iInf₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (f i j)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (f i j)
Case conversion may be inaccurate. Consider using '#align infi₂_le iInf₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : (⨅ (i) (j), f i j) ≤ f i j :=
  iInf_le_of_le i <| iInf_le (f i) j
#align infi₂_le iInf₂_le

/- warning: le_supr₂_of_le -> le_iSup₂_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i j)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (f i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))))
Case conversion may be inaccurate. Consider using '#align le_supr₂_of_le le_iSup₂_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_iSup₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_iSup₂ i j
#align le_supr₂_of_le le_iSup₂_of_le

/- warning: infi₂_le_of_le -> iInf₂_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) a) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) a)
Case conversion may be inaccurate. Consider using '#align infi₂_le_of_le iInf₂_le_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    (⨅ (i) (j), f i j) ≤ a :=
  (iInf₂_le i j).trans h
#align infi₂_le_of_le iInf₂_le_of_le

/- warning: supr_le -> iSup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) a)
Case conversion may be inaccurate. Consider using '#align supr_le iSup_leₓ'. -/
theorem iSup_le (h : ∀ i, f i ≤ a) : iSup f ≤ a :=
  sSup_le fun b ⟨i, Eq⟩ => Eq ▸ h i
#align supr_le iSup_le

/- warning: le_infi -> le_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (f i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_infi le_iInfₓ'. -/
theorem le_iInf (h : ∀ i, a ≤ f i) : a ≤ iInf f :=
  le_sInf fun b ⟨i, Eq⟩ => Eq ▸ h i
#align le_infi le_iInf

/- warning: supr₂_le -> iSup₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) a) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) a)
Case conversion may be inaccurate. Consider using '#align supr₂_le iSup₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : (⨆ (i) (j), f i j) ≤ a :=
  iSup_le fun i => iSup_le <| h i
#align supr₂_le iSup₂_le

/- warning: le_infi₂ -> le_iInf₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i j)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (f i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))))
Case conversion may be inaccurate. Consider using '#align le_infi₂ le_iInf₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_iInf₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_iInf fun i => le_iInf <| h i
#align le_infi₂ le_iInf₂

/- warning: supr₂_le_supr -> iSup₂_le_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) (κ i) (fun (j : κ i) => f i))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align supr₂_le_supr iSup₂_le_iSupₓ'. -/
theorem iSup₂_le_iSup (κ : ι → Sort _) (f : ι → α) : (⨆ (i) (j : κ i), f i) ≤ ⨆ i, f i :=
  iSup₂_le fun i j => le_iSup f i
#align supr₂_le_supr iSup₂_le_iSup

/- warning: infi_le_infi₂ -> iInf_le_iInf₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) (κ i) (fun (j : κ i) => f i)))
Case conversion may be inaccurate. Consider using '#align infi_le_infi₂ iInf_le_iInf₂ₓ'. -/
theorem iInf_le_iInf₂ (κ : ι → Sort _) (f : ι → α) : (⨅ i, f i) ≤ ⨅ (i) (j : κ i), f i :=
  le_iInf₂ fun i j => iInf_le f i
#align infi_le_infi₂ iInf_le_iInf₂

/- warning: supr_mono -> iSup_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align supr_mono iSup_monoₓ'. -/
theorem iSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  iSup_le fun i => le_iSup_of_le i <| h i
#align supr_mono iSup_mono

/- warning: infi_mono -> iInf_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align infi_mono iInf_monoₓ'. -/
theorem iInf_mono (h : ∀ i, f i ≤ g i) : iInf f ≤ iInf g :=
  le_iInf fun i => iInf_le_of_le i <| h i
#align infi_mono iInf_mono

/- warning: supr₂_mono -> iSup₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => g i j))))
Case conversion may be inaccurate. Consider using '#align supr₂_mono iSup₂_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  iSup_mono fun i => iSup_mono <| h i
#align supr₂_mono iSup₂_mono

/- warning: infi₂_mono -> iInf₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => g i j))))
Case conversion may be inaccurate. Consider using '#align infi₂_mono iInf₂_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  iInf_mono fun i => iInf_mono <| h i
#align infi₂_mono iInf₂_mono

/- warning: supr_mono' -> iSup_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι' -> α}, (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι' -> α}, (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι' g))
Case conversion may be inaccurate. Consider using '#align supr_mono' iSup_mono'ₓ'. -/
theorem iSup_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  iSup_le fun i => Exists.elim (h i) le_iSup_of_le
#align supr_mono' iSup_mono'

/- warning: infi_mono' -> iInf_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι' -> α}, (forall (i' : ι'), Exists.{u2} ι (fun (i : ι) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι' -> α}, (forall (i' : ι'), Exists.{u3} ι (fun (i : ι) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι' g))
Case conversion may be inaccurate. Consider using '#align infi_mono' iInf_mono'ₓ'. -/
theorem iInf_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : iInf f ≤ iInf g :=
  le_iInf fun i' => Exists.elim (h i') iInf_le_of_le
#align infi_mono' iInf_mono'

/- warning: supr₂_mono' -> iSup₂_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u5}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι) (j : κ i), Exists.{u3} ι' (fun (i' : ι') => Exists.{u5} (κ' i') (fun (j' : κ' i') => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (g i' j')))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (i : ι') => iSup.{u1, u5} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ' i) (fun (j : κ' i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u5}} {κ : ι -> Sort.{u1}} {κ' : ι' -> Sort.{u4}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι) (j : κ i), Exists.{u5} ι' (fun (i' : ι') => Exists.{u4} (κ' i') (fun (j' : κ' i') => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (g i' j')))) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (iSup.{u3, u5} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (i : ι') => iSup.{u3, u4} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ' i) (fun (j : κ' i) => g i j))))
Case conversion may be inaccurate. Consider using '#align supr₂_mono' iSup₂_mono'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h
#align supr₂_mono' iSup₂_mono'

/- warning: infi₂_mono' -> iInf₂_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u5}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι') (j : κ' i), Exists.{u2} ι (fun (i' : ι) => Exists.{u4} (κ i') (fun (j' : κ i') => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i' j') (g i j)))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (i : ι') => iInf.{u1, u5} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ' i) (fun (j : κ' i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u5}} {ι' : Sort.{u2}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι') (j : κ' i), Exists.{u5} ι (fun (i' : ι) => Exists.{u4} (κ i') (fun (j' : κ i') => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i' j') (g i j)))) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iInf.{u3, u5} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u4} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (i : ι') => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ' i) (fun (j : κ' i) => g i j))))
Case conversion may be inaccurate. Consider using '#align infi₂_mono' iInf₂_mono'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  le_iInf₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    iInf₂_le_of_le i' j' h
#align infi₂_mono' iInf₂_mono'

/- warning: supr_const_mono -> iSup_const_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, (ι -> ι') -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => a)) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (j : ι') => a)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α}, (ι -> ι') -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => a)) (iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (j : ι') => a)))
Case conversion may be inaccurate. Consider using '#align supr_const_mono iSup_const_monoₓ'. -/
theorem iSup_const_mono (h : ι → ι') : (⨆ i : ι, a) ≤ ⨆ j : ι', a :=
  iSup_le <| le_iSup _ ∘ h
#align supr_const_mono iSup_const_mono

/- warning: infi_const_mono -> iInf_const_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, (ι' -> ι) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => a)) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => a)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α}, (ι' -> ι) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => a)) (iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => a)))
Case conversion may be inaccurate. Consider using '#align infi_const_mono iInf_const_monoₓ'. -/
theorem iInf_const_mono (h : ι' → ι) : (⨅ i : ι, a) ≤ ⨅ j : ι', a :=
  le_iInf <| iInf_le _ ∘ h
#align infi_const_mono iInf_const_mono

/- warning: supr_infi_le_infi_supr -> iSup_iInf_le_iInf_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> ι' -> α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => f i j))) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] (f : ι -> ι' -> α), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => f i j))) (iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i j)))
Case conversion may be inaccurate. Consider using '#align supr_infi_le_infi_supr iSup_iInf_le_iInf_iSupₓ'. -/
theorem iSup_iInf_le_iInf_iSup (f : ι → ι' → α) : (⨆ i, ⨅ j, f i j) ≤ ⨅ j, ⨆ i, f i j :=
  iSup_le fun i => iInf_mono fun j => le_iSup _ i
#align supr_infi_le_infi_supr iSup_iInf_le_iInf_iSup

/- warning: bsupr_mono -> biSup_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (q i) (fun (h : q i) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (q i) (fun (h : q i) => f i))))
Case conversion may be inaccurate. Consider using '#align bsupr_mono biSup_monoₓ'. -/
theorem biSup_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨆ (i) (h : p i), f i) ≤ ⨆ (i) (h : q i), f i :=
  iSup_mono fun i => iSup_const_mono (hpq i)
#align bsupr_mono biSup_mono

/- warning: binfi_mono -> biInf_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (q i) (fun (h : q i) => f i))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (q i) (fun (h : q i) => f i))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))))
Case conversion may be inaccurate. Consider using '#align binfi_mono biInf_monoₓ'. -/
theorem biInf_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨅ (i) (h : q i), f i) ≤ ⨅ (i) (h : p i), f i :=
  iInf_mono fun i => iInf_const_mono (hpq i)
#align binfi_mono biInf_mono

/- warning: supr_le_iff -> iSup_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) a) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) a) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) a)
Case conversion may be inaccurate. Consider using '#align supr_le_iff iSup_le_iffₓ'. -/
@[simp]
theorem iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_iSup).trans forall_range_iff
#align supr_le_iff iSup_le_iff

/- warning: le_infi_iff -> le_iInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f)) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (f i))
Case conversion may be inaccurate. Consider using '#align le_infi_iff le_iInf_iffₓ'. -/
@[simp]
theorem le_iInf_iff : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff isGLB_iInf).trans forall_range_iff
#align le_infi_iff le_iInf_iff

/- warning: supr₂_le_iff -> iSup₂_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) a)
Case conversion may be inaccurate. Consider using '#align supr₂_le_iff iSup₂_le_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem iSup₂_le_iff {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [iSup_le_iff]
#align supr₂_le_iff iSup₂_le_iff

/- warning: le_infi₂_iff -> le_iInf₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i j))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (f i j))
Case conversion may be inaccurate. Consider using '#align le_infi₂_iff le_iInf₂_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem le_iInf₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_iInf_iff]
#align le_infi₂_iff le_iInf₂_iff

/- warning: supr_lt_iff -> iSup_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) a) (Exists.{succ u1} α (fun (b : α) => And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) a) (Exists.{succ u2} α (fun (b : α) => And (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b a) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) b)))
Case conversion may be inaccurate. Consider using '#align supr_lt_iff iSup_lt_iffₓ'. -/
theorem iSup_lt_iff : iSup f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨iSup f, h, le_iSup f⟩, fun ⟨b, h, hb⟩ => (iSup_le hb).trans_lt h⟩
#align supr_lt_iff iSup_lt_iff

/- warning: lt_infi_iff -> lt_iInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f)) (Exists.{succ u1} α (fun (b : α) => And (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b) (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f)) (Exists.{succ u2} α (fun (b : α) => And (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a b) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b (f i))))
Case conversion may be inaccurate. Consider using '#align lt_infi_iff lt_iInf_iffₓ'. -/
theorem lt_iInf_iff : a < iInf f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨iInf f, h, iInf_le f⟩, fun ⟨b, h, hb⟩ => h.trans_le <| le_iInf hb⟩
#align lt_infi_iff lt_iInf_iff

/- warning: Sup_eq_supr -> sSup_eq_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (a : α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (iSup.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (a : α) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => a)))
Case conversion may be inaccurate. Consider using '#align Sup_eq_supr sSup_eq_iSupₓ'. -/
theorem sSup_eq_iSup {s : Set α} : sSup s = ⨆ a ∈ s, a :=
  le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun b => le_sSup)
#align Sup_eq_supr sSup_eq_iSup

/- warning: Inf_eq_infi -> sInf_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (a : α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (iInf.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (a : α) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => a)))
Case conversion may be inaccurate. Consider using '#align Inf_eq_infi sInf_eq_iInfₓ'. -/
theorem sInf_eq_iInf {s : Set α} : sInf s = ⨅ a ∈ s, a :=
  @sSup_eq_iSup αᵒᵈ _ _
#align Inf_eq_infi sInf_eq_iInf

/- warning: monotone.le_map_supr -> Monotone.le_map_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))) (f (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Monotone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (iSup.{u3, u1} β (CompleteLattice.toSupSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))) (f (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι s)))
Case conversion may be inaccurate. Consider using '#align monotone.le_map_supr Monotone.le_map_iSupₓ'. -/
theorem Monotone.le_map_iSup [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    (⨆ i, f (s i)) ≤ f (iSup s) :=
  iSup_le fun i => hf <| le_iSup _ _
#align monotone.le_map_supr Monotone.le_map_iSup

/- warning: antitone.le_map_infi -> Antitone.le_map_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))) (f (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Antitone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (iSup.{u3, u1} β (CompleteLattice.toSupSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))) (f (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι s)))
Case conversion may be inaccurate. Consider using '#align antitone.le_map_infi Antitone.le_map_iInfₓ'. -/
theorem Antitone.le_map_iInf [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    (⨆ i, f (s i)) ≤ f (iInf s) :=
  hf.dual_left.le_map_iSup
#align antitone.le_map_infi Antitone.le_map_iInf

/- warning: monotone.le_map_supr₂ -> Monotone.le_map_iSup₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => iSup.{u2, u4} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))) (f (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Monotone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (iSup.{u4, u2} β (CompleteLattice.toSupSet.{u4} β _inst_2) ι (fun (i : ι) => iSup.{u4, u1} β (CompleteLattice.toSupSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))) (f (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))))
Case conversion may be inaccurate. Consider using '#align monotone.le_map_supr₂ Monotone.le_map_iSup₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨆ (i) (j), s i j) :=
  iSup₂_le fun i j => hf <| le_iSup₂ _ _
#align monotone.le_map_supr₂ Monotone.le_map_iSup₂

/- warning: antitone.le_map_infi₂ -> Antitone.le_map_iInf₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => iSup.{u2, u4} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))) (f (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Antitone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (iSup.{u4, u2} β (CompleteLattice.toSupSet.{u4} β _inst_2) ι (fun (i : ι) => iSup.{u4, u1} β (CompleteLattice.toSupSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))) (f (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))))
Case conversion may be inaccurate. Consider using '#align antitone.le_map_infi₂ Antitone.le_map_iInf₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _
#align antitone.le_map_infi₂ Antitone.le_map_iInf₂

/- warning: monotone.le_map_Sup -> Monotone.le_map_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))) (f (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))) (f (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align monotone.le_map_Sup Monotone.le_map_sSupₓ'. -/
theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    (⨆ a ∈ s, f a) ≤ f (sSup s) := by rw [sSup_eq_iSup] <;> exact hf.le_map_supr₂ _
#align monotone.le_map_Sup Monotone.le_map_sSup

/- warning: antitone.le_map_Inf -> Antitone.le_map_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))) (f (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))) (f (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align antitone.le_map_Inf Antitone.le_map_sInfₓ'. -/
theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    (⨆ a ∈ s, f a) ≤ f (sInf s) :=
  hf.dual_left.le_map_sSup
#align antitone.le_map_Inf Antitone.le_map_sInf

/- warning: order_iso.map_supr -> OrderIso.map_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : ι -> α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => x i))) (iSup.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (x i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] (f : OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))) (x : ι -> α), Eq.{succ u3} β (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u3, u2, u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => x i))) (iSup.{u3, u1} β (CompleteLattice.toSupSet.{u3} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u3, u2, u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f (x i)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_supr OrderIso.map_iSupₓ'. -/
theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.Surjective.forall.2 fun x => by simp only [f.le_iff_le, iSup_le_iff]
#align order_iso.map_supr OrderIso.map_iSup

/- warning: order_iso.map_infi -> OrderIso.map_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : ι -> α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => x i))) (iInf.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (x i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] (f : OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))) (x : ι -> α), Eq.{succ u3} β (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u3, u2, u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => x i))) (iInf.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u2 u3, u2, u3} (RelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f (x i)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_infi OrderIso.map_iInfₓ'. -/
theorem OrderIso.map_iInf [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_iSup f.dual _
#align order_iso.map_infi OrderIso.map_iInf

/- warning: order_iso.map_Sup -> OrderIso.map_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f a)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_Sup OrderIso.map_sSupₓ'. -/
theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a ∈ s, f a := by simp only [sSup_eq_iSup, OrderIso.map_iSup]
#align order_iso.map_Sup OrderIso.map_sSup

/- warning: order_iso.map_Inf -> OrderIso.map_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u1 u2, u1, u2} (RelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) f a)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_Inf OrderIso.map_sInfₓ'. -/
theorem OrderIso.map_sInf [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_sSup f.dual _
#align order_iso.map_Inf OrderIso.map_sInf

/- warning: supr_comp_le -> iSup_comp_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f (g x))) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (y : ι') => f y))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => f (g x))) (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι' (fun (y : ι') => f y))
Case conversion may be inaccurate. Consider using '#align supr_comp_le iSup_comp_leₓ'. -/
theorem iSup_comp_le {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
  iSup_mono' fun x => ⟨_, le_rfl⟩
#align supr_comp_le iSup_comp_le

/- warning: le_infi_comp -> le_iInf_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (y : ι') => f y)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f (g x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι' (fun (y : ι') => f y)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => f (g x)))
Case conversion may be inaccurate. Consider using '#align le_infi_comp le_iInf_compₓ'. -/
theorem le_iInf_comp {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
  iInf_mono' fun x => ⟨_, le_rfl⟩
#align le_infi_comp le_iInf_comp

/- warning: monotone.supr_comp_eq -> Monotone.iSup_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Preorder.{u2} β] {f : β -> α}, (Monotone.{u2, u1} β α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u3} ι (fun (i : ι) => LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) x (s i))) -> (Eq.{succ u1} α (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f (s x))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (y : β) => f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Preorder.{u3} β] {f : β -> α}, (Monotone.{u3, u2} β α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u1} ι (fun (i : ι) => LE.le.{u3} β (Preorder.toLE.{u3} β _inst_2) x (s i))) -> (Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => f (s x))) (iSup.{u2, succ u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (y : β) => f y))))
Case conversion may be inaccurate. Consider using '#align monotone.supr_comp_eq Monotone.iSup_comp_eqₓ'. -/
theorem Monotone.iSup_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : (⨆ x, f (s x)) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun i hi => hf hi)
#align monotone.supr_comp_eq Monotone.iSup_comp_eq

/- warning: monotone.infi_comp_eq -> Monotone.iInf_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Preorder.{u2} β] {f : β -> α}, (Monotone.{u2, u1} β α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u3} ι (fun (i : ι) => LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (s i) x)) -> (Eq.{succ u1} α (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f (s x))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (y : β) => f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Preorder.{u3} β] {f : β -> α}, (Monotone.{u3, u2} β α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u1} ι (fun (i : ι) => LE.le.{u3} β (Preorder.toLE.{u3} β _inst_2) (s i) x)) -> (Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => f (s x))) (iInf.{u2, succ u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (y : β) => f y))))
Case conversion may be inaccurate. Consider using '#align monotone.infi_comp_eq Monotone.iInf_comp_eqₓ'. -/
theorem Monotone.iInf_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : (⨅ x, f (s x)) = ⨅ y, f y :=
  le_antisymm (iInf_mono' fun x => (hs x).imp fun i hi => hf hi) (le_iInf_comp _ _)
#align monotone.infi_comp_eq Monotone.iInf_comp_eq

/- warning: antitone.map_supr_le -> Antitone.map_iSup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι s)) (iInf.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Antitone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (f (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι s)) (iInf.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))))
Case conversion may be inaccurate. Consider using '#align antitone.map_supr_le Antitone.map_iSup_leₓ'. -/
theorem Antitone.map_iSup_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (iSup s) ≤ ⨅ i, f (s i) :=
  le_iInf fun i => hf <| le_iSup _ _
#align antitone.map_supr_le Antitone.map_iSup_le

/- warning: monotone.map_infi_le -> Monotone.map_iInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι s)) (iInf.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Monotone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (f (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι s)) (iInf.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))))
Case conversion may be inaccurate. Consider using '#align monotone.map_infi_le Monotone.map_iInf_leₓ'. -/
theorem Monotone.map_iInf_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (iInf s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_iSup_le
#align monotone.map_infi_le Monotone.map_iInf_le

/- warning: antitone.map_supr₂_le -> Antitone.map_iSup₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))) (iInf.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => iInf.{u2, u4} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Antitone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (f (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))) (iInf.{u4, u2} β (CompleteLattice.toInfSet.{u4} β _inst_2) ι (fun (i : ι) => iInf.{u4, u1} β (CompleteLattice.toInfSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))))
Case conversion may be inaccurate. Consider using '#align antitone.map_supr₂_le Antitone.map_iSup₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Antitone.map_iSup₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iInf₂ _
#align antitone.map_supr₂_le Antitone.map_iSup₂_le

/- warning: monotone.map_infi₂_le -> Monotone.map_iInf₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))) (iInf.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => iInf.{u2, u4} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Monotone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (f (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))) (iInf.{u4, u2} β (CompleteLattice.toInfSet.{u4} β _inst_2) ι (fun (i : ι) => iInf.{u4, u1} β (CompleteLattice.toInfSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))))
Case conversion may be inaccurate. Consider using '#align monotone.map_infi₂_le Monotone.map_iInf₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Monotone.map_iInf₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iSup₂ _
#align monotone.map_infi₂_le Monotone.map_iInf₂_le

/- warning: antitone.map_Sup_le -> Antitone.map_sSup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))))
Case conversion may be inaccurate. Consider using '#align antitone.map_Sup_le Antitone.map_sSup_leₓ'. -/
theorem Antitone.map_sSup_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (sSup s) ≤ ⨅ a ∈ s, f a := by
  rw [sSup_eq_iSup]
  exact hf.map_supr₂_le _
#align antitone.map_Sup_le Antitone.map_sSup_le

/- warning: monotone.map_Inf_le -> Monotone.map_sInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))))
Case conversion may be inaccurate. Consider using '#align monotone.map_Inf_le Monotone.map_sInf_leₓ'. -/
theorem Monotone.map_sInf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (sInf s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_sSup_le
#align monotone.map_Inf_le Monotone.map_sInf_le

/- warning: supr_const_le -> iSup_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => a)) a
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {a : α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align supr_const_le iSup_const_leₓ'. -/
theorem iSup_const_le : (⨆ i : ι, a) ≤ a :=
  iSup_le fun _ => le_rfl
#align supr_const_le iSup_const_le

/- warning: le_infi_const -> le_iInf_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {a : α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => a))
Case conversion may be inaccurate. Consider using '#align le_infi_const le_iInf_constₓ'. -/
theorem le_iInf_const : a ≤ ⨅ i : ι, a :=
  le_iInf fun _ => le_rfl
#align le_infi_const le_iInf_const

/- warning: supr_const -> iSup_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align supr_const iSup_constₓ'. -/
-- We generalize this to conditionally complete lattices in `csupr_const` and `cinfi_const`.
theorem iSup_const [Nonempty ι] : (⨆ b : ι, a) = a := by rw [iSup, range_const, sSup_singleton]
#align supr_const iSup_const

/- warning: infi_const -> iInf_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align infi_const iInf_constₓ'. -/
theorem iInf_const [Nonempty ι] : (⨅ b : ι, a) = a :=
  @iSup_const αᵒᵈ _ _ a _
#align infi_const iInf_const

/- warning: supr_bot -> iSup_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α], Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_bot iSup_botₓ'. -/
@[simp]
theorem iSup_bot : (⨆ i : ι, ⊥ : α) = ⊥ :=
  bot_unique iSup_const_le
#align supr_bot iSup_bot

/- warning: infi_top -> iInf_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α], Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_top iInf_topₓ'. -/
@[simp]
theorem iInf_top : (⨅ i : ι, ⊤ : α) = ⊤ :=
  top_unique le_iInf_const
#align infi_top iInf_top

/- warning: supr_eq_bot -> iSup_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α}, Iff (Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (forall (i : ι), Eq.{succ u1} α (s i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α}, Iff (Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι s) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) (forall (i : ι), Eq.{succ u2} α (s i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_eq_bot iSup_eq_botₓ'. -/
@[simp]
theorem iSup_eq_bot : iSup s = ⊥ ↔ ∀ i, s i = ⊥ :=
  sSup_eq_bot.trans forall_range_iff
#align supr_eq_bot iSup_eq_bot

/- warning: infi_eq_top -> iInf_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α}, Iff (Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall (i : ι), Eq.{succ u1} α (s i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α}, Iff (Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι s) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) (forall (i : ι), Eq.{succ u2} α (s i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_eq_top iInf_eq_topₓ'. -/
@[simp]
theorem iInf_eq_top : iInf s = ⊤ ↔ ∀ i, s i = ⊤ :=
  sInf_eq_top.trans forall_range_iff
#align infi_eq_top iInf_eq_top

/- warning: supr₂_eq_bot -> iSup₂_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u1} α (f i j) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u3} α (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (Bot.bot.{u3} α (CompleteLattice.toBot.{u3} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u3} α (f i j) (Bot.bot.{u3} α (CompleteLattice.toBot.{u3} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr₂_eq_bot iSup₂_eq_botₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem iSup₂_eq_bot {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp_rw [iSup_eq_bot]
#align supr₂_eq_bot iSup₂_eq_bot

/- warning: infi₂_eq_top -> iInf₂_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u1} α (f i j) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u3} α (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (Top.top.{u3} α (CompleteLattice.toTop.{u3} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u3} α (f i j) (Top.top.{u3} α (CompleteLattice.toTop.{u3} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi₂_eq_top iInf₂_eq_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem iInf₂_eq_top {f : ∀ i, κ i → α} : (⨅ (i) (j), f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp_rw [iInf_eq_top]
#align infi₂_eq_top iInf₂_eq_top

/- warning: supr_pos -> iSup_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align supr_pos iSup_posₓ'. -/
@[simp]
theorem iSup_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  le_antisymm (iSup_le fun h => le_rfl) (le_iSup _ _)
#align supr_pos iSup_pos

/- warning: infi_pos -> iInf_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align infi_pos iInf_posₓ'. -/
@[simp]
theorem iInf_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  le_antisymm (iInf_le _ _) (le_iInf fun h => le_rfl)
#align infi_pos iInf_pos

/- warning: supr_neg -> iSup_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => f h)) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => f h)) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_neg iSup_negₓ'. -/
@[simp]
theorem iSup_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h : p, f h) = ⊥ :=
  le_antisymm (iSup_le fun h => (hp h).elim) bot_le
#align supr_neg iSup_neg

/- warning: infi_neg -> iInf_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => f h)) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => f h)) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_neg iInf_negₓ'. -/
@[simp]
theorem iInf_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨅ h : p, f h) = ⊤ :=
  le_antisymm le_top <| le_iInf fun h => (hp h).elim
#align infi_neg iInf_neg

/- warning: supr_eq_of_forall_le_of_forall_lt_exists_gt -> iSup_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : α} {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) b) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w b) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w (f i)))) -> (Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {b : α} {f : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) b) -> (forall (w : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) w b) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) w (f i)))) -> (Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align supr_eq_of_forall_le_of_forall_lt_exists_gt iSup_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw
#align supr_eq_of_forall_le_of_forall_lt_exists_gt iSup_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: infi_eq_of_forall_ge_of_forall_gt_exists_lt -> iInf_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {b : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b (f i)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b w) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) w))) -> (Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {b : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b (f i)) -> (forall (w : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b w) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) w))) -> (Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align infi_eq_of_forall_ge_of_forall_gt_exists_lt iInf_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem iInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ i, b ≤ f i) → (∀ w, b < w → ∃ i, f i < w) → (⨅ i, f i) = b :=
  @iSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _
#align infi_eq_of_forall_ge_of_forall_gt_exists_lt iInf_eq_of_forall_ge_of_forall_gt_exists_lt

/- warning: supr_eq_dif -> iSup_eq_dif is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_eq_dif iSup_eq_difₓ'. -/
theorem iSup_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨆ h : p, a h) = if h : p then a h else ⊥ := by by_cases p <;> simp [h]
#align supr_eq_dif iSup_eq_dif

/- warning: supr_eq_if -> iSup_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_eq_if iSup_eq_ifₓ'. -/
theorem iSup_eq_if {p : Prop} [Decidable p] (a : α) : (⨆ h : p, a) = if p then a else ⊥ :=
  iSup_eq_dif fun _ => a
#align supr_eq_if iSup_eq_if

/- warning: infi_eq_dif -> iInf_eq_dif is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_eq_dif iInf_eq_difₓ'. -/
theorem iInf_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨅ h : p, a h) = if h : p then a h else ⊤ :=
  @iSup_eq_dif αᵒᵈ _ _ _ _
#align infi_eq_dif iInf_eq_dif

/- warning: infi_eq_if -> iInf_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_eq_if iInf_eq_ifₓ'. -/
theorem iInf_eq_if {p : Prop} [Decidable p] (a : α) : (⨅ h : p, a) = if p then a else ⊤ :=
  iInf_eq_dif fun _ => a
#align infi_eq_if iInf_eq_if

/- warning: supr_comm -> iSup_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> ι' -> α}, Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (j : ι') => f i j))) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (j : ι') => iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : ι -> ι' -> α}, Eq.{succ u3} α (iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (j : ι') => f i j))) (iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (j : ι') => iSup.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i j)))
Case conversion may be inaccurate. Consider using '#align supr_comm iSup_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (j i) -/
theorem iSup_comm {f : ι → ι' → α} : (⨆ (i) (j), f i j) = ⨆ (j) (i), f i j :=
  le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup _ i)
    (iSup_le fun j => iSup_mono fun i => le_iSup _ _)
#align supr_comm iSup_comm

/- warning: infi_comm -> iInf_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> ι' -> α}, Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => f i j))) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : ι -> ι' -> α}, Eq.{succ u3} α (iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => f i j))) (iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => iInf.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => f i j)))
Case conversion may be inaccurate. Consider using '#align infi_comm iInf_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (j i) -/
theorem iInf_comm {f : ι → ι' → α} : (⨅ (i) (j), f i j) = ⨅ (j) (i), f i j :=
  @iSup_comm αᵒᵈ _ _ _ _
#align infi_comm iInf_comm

/- warning: supr₂_comm -> iSup₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u2}} {ι₂ : Sort.{u3}} {κ₁ : ι₁ -> Sort.{u4}} {κ₂ : ι₂ -> Sort.{u5}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => iSup.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => iSup.{u1, u5} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => iSup.{u1, u5} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => iSup.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u5}} {ι₂ : Sort.{u4}} {κ₁ : ι₁ -> Sort.{u3}} {κ₂ : ι₂ -> Sort.{u2}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (iSup.{u1, u5} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => iSup.{u1, u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => iSup.{u1, u4} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (iSup.{u1, u4} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => iSup.{u1, u5} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => iSup.{u1, u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align supr₂_comm iSup₂_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem iSup₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]
#align supr₂_comm iSup₂_comm

/- warning: infi₂_comm -> iInf₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u2}} {ι₂ : Sort.{u3}} {κ₁ : ι₁ -> Sort.{u4}} {κ₂ : ι₂ -> Sort.{u5}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => iInf.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => iInf.{u1, u5} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => iInf.{u1, u5} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => iInf.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u5}} {ι₂ : Sort.{u4}} {κ₁ : ι₁ -> Sort.{u3}} {κ₂ : ι₂ -> Sort.{u2}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (iInf.{u1, u5} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => iInf.{u1, u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => iInf.{u1, u4} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (iInf.{u1, u4} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => iInf.{u1, u5} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => iInf.{u1, u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align infi₂_comm iInf₂_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem iInf₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨅ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨅ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iInf_comm _ (κ₁ _), @iInf_comm _ ι₁]
#align infi₂_comm iInf₂_comm

/- warning: supr_supr_eq_left -> iSup_iSup_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align supr_supr_eq_left iSup_iSup_eq_leftₓ'. -/
/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/
@[simp]
theorem iSup_iSup_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨆ x, ⨆ h : x = b, f x h) = f b rfl :=
  (@le_iSup₂ _ _ _ _ f b rfl).antisymm'
    (iSup_le fun c =>
      iSup_le <| by
        rintro rfl
        rfl)
#align supr_supr_eq_left iSup_iSup_eq_left

/- warning: infi_infi_eq_left -> iInf_iInf_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align infi_infi_eq_left iInf_iInf_eq_leftₓ'. -/
@[simp]
theorem iInf_iInf_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
  @iSup_iSup_eq_left αᵒᵈ _ _ _ _
#align infi_infi_eq_left iInf_iInf_eq_left

/- warning: supr_supr_eq_right -> iSup_iSup_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align supr_supr_eq_right iSup_iSup_eq_rightₓ'. -/
@[simp]
theorem iSup_iSup_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
  (le_iSup₂ b rfl).antisymm'
    (iSup₂_le fun c => by
      rintro rfl
      rfl)
#align supr_supr_eq_right iSup_iSup_eq_right

/- warning: infi_infi_eq_right -> iInf_iInf_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align infi_infi_eq_right iInf_iInf_eq_rightₓ'. -/
@[simp]
theorem iInf_iInf_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
  @iSup_iSup_eq_right αᵒᵈ _ _ _ _
#align infi_infi_eq_right iInf_iInf_eq_right

attribute [ematch] le_refl

/- warning: supr_subtype -> iSup_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (iSup.{u1, max 1 u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Subtype.{u2} ι p) f) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (iSup.{u1, max 1 u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Subtype.{u2} ι p) f) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align supr_subtype iSup_subtypeₓ'. -/
theorem iSup_subtype {p : ι → Prop} {f : Subtype p → α} : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => le_iSup₂ i h) (iSup₂_le fun i h => le_iSup _ _)
#align supr_subtype iSup_subtype

/- warning: infi_subtype -> iInf_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (iInf.{u1, max 1 u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Subtype.{u2} ι p) f) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (iInf.{u1, max 1 u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Subtype.{u2} ι p) f) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align infi_subtype iInf_subtypeₓ'. -/
theorem iInf_subtype : ∀ {p : ι → Prop} {f : Subtype p → α}, iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  @iSup_subtype αᵒᵈ _ _
#align infi_subtype iInf_subtype

/- warning: supr_subtype' -> iSup_subtype' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (iSup.{u1, max 1 u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Subtype.{u2} ι p) (fun (x : Subtype.{u2} ι p) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι p) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι p) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeSubtype.{u2} ι (fun (x : ι) => p x))))) x) (Subtype.property.{u2} ι p x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (iSup.{u2, max 1 u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Subtype.{u1} ι p) (fun (x : Subtype.{u1} ι p) => f (Subtype.val.{u1} ι p x) (Subtype.property.{u1} ι p x)))
Case conversion may be inaccurate. Consider using '#align supr_subtype' iSup_subtype'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
theorem iSup_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨆ (i) (h), f i h) = ⨆ x : Subtype p, f x x.property :=
  (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm
#align supr_subtype' iSup_subtype'

/- warning: infi_subtype' -> iInf_subtype' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (iInf.{u1, max 1 u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Subtype.{u2} ι p) (fun (x : Subtype.{u2} ι p) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι p) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι p) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeSubtype.{u2} ι (fun (x : ι) => p x))))) x) (Subtype.property.{u2} ι p x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (iInf.{u2, max 1 u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Subtype.{u1} ι p) (fun (x : Subtype.{u1} ι p) => f (Subtype.val.{u1} ι p x) (Subtype.property.{u1} ι p x)))
Case conversion may be inaccurate. Consider using '#align infi_subtype' iInf_subtype'ₓ'. -/
theorem iInf_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨅ (i) (h : p i), f i h) = ⨅ x : Subtype p, f x x.property :=
  (@iInf_subtype _ _ _ p fun x => f x.val x.property).symm
#align infi_subtype' iInf_subtype'

/- warning: supr_subtype'' -> iSup_subtype'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (t : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) => f t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (t : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) => f t)))
Case conversion may be inaccurate. Consider using '#align supr_subtype'' iSup_subtype''ₓ'. -/
theorem iSup_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨆ i : s, f i) = ⨆ (t : ι) (H : t ∈ s), f t :=
  iSup_subtype
#align supr_subtype'' iSup_subtype''

/- warning: infi_subtype'' -> iInf_subtype'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (t : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) => f t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i))) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (t : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) => f t)))
Case conversion may be inaccurate. Consider using '#align infi_subtype'' iInf_subtype''ₓ'. -/
theorem iInf_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
  iInf_subtype
#align infi_subtype'' iInf_subtype''

/- warning: bsupr_const -> biSup_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => a))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => a))) a)
Case conversion may be inaccurate. Consider using '#align bsupr_const biSup_constₓ'. -/
theorem biSup_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨆ i ∈ s, a) = a :=
  by
  haveI : Nonempty s := set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'', iSup_const]
#align bsupr_const biSup_const

/- warning: binfi_const -> biInf_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => a))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => a))) a)
Case conversion may be inaccurate. Consider using '#align binfi_const biInf_constₓ'. -/
theorem biInf_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨅ i ∈ s, a) = a :=
  @biSup_const αᵒᵈ _ ι _ s hs
#align binfi_const biInf_const

/- warning: supr_sup_eq -> iSup_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) (g x))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f x)) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => g x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f x) (g x))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => f x)) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => g x)))
Case conversion may be inaccurate. Consider using '#align supr_sup_eq iSup_sup_eqₓ'. -/
theorem iSup_sup_eq : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (iSup_le fun i => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun i => le_sup_left) <| iSup_mono fun i => le_sup_right)
#align supr_sup_eq iSup_sup_eq

/- warning: infi_inf_eq -> iInf_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) (g x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f x)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => g x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f x) (g x))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => f x)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => g x)))
Case conversion may be inaccurate. Consider using '#align infi_inf_eq iInf_inf_eqₓ'. -/
theorem iInf_inf_eq : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ ⨅ x, g x :=
  @iSup_sup_eq αᵒᵈ _ _ _ _
#align infi_inf_eq iInf_inf_eq

/- warning: supr_sup -> iSup_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f x)) a) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => f x)) a) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) a))
Case conversion may be inaccurate. Consider using '#align supr_sup iSup_supₓ'. -/
/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem iSup_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [iSup_sup_eq, iSup_const]
#align supr_sup iSup_sup

/- warning: infi_inf -> iInf_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f x)) a) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => f x)) a) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f x) a))
Case conversion may be inaccurate. Consider using '#align infi_inf iInf_infₓ'. -/
theorem iInf_inf [Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a := by
  rw [iInf_inf_eq, iInf_const]
#align infi_inf iInf_inf

/- warning: sup_supr -> sup_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f x))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f x)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => f x))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f x)))
Case conversion may be inaccurate. Consider using '#align sup_supr sup_iSupₓ'. -/
theorem sup_iSup [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [iSup_sup_eq, iSup_const]
#align sup_supr sup_iSup

/- warning: inf_infi -> inf_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f x))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f x)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => f x))) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (f x)))
Case conversion may be inaccurate. Consider using '#align inf_infi inf_iInfₓ'. -/
theorem inf_iInf [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ ⨅ x, f x) = ⨅ x, a ⊓ f x := by
  rw [iInf_inf_eq, iInf_const]
#align inf_infi inf_iInf

/- warning: bsupr_sup -> biSup_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) a) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i h) a))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h))) a) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i h) a))))
Case conversion may be inaccurate. Consider using '#align bsupr_sup biSup_supₓ'. -/
theorem biSup_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
      let ⟨i, hi⟩ := h
      ⟨⟨i, hi⟩⟩ <;>
    rw [iSup_subtype', iSup_subtype', iSup_sup]
#align bsupr_sup biSup_sup

/- warning: sup_bsupr -> sup_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f i h)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h)))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f i h)))))
Case conversion may be inaccurate. Consider using '#align sup_bsupr sup_biSupₓ'. -/
theorem sup_biSup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using biSup_sup h
#align sup_bsupr sup_biSup

/- warning: binfi_inf -> biInf_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) a) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i h) a))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h))) a) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f i h) a))))
Case conversion may be inaccurate. Consider using '#align binfi_inf biInf_infₓ'. -/
theorem biInf_inf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h) ⊓ a = ⨅ (i) (h : p i), f i h ⊓ a :=
  @biSup_sup αᵒᵈ ι _ p f _ h
#align binfi_inf biInf_inf

/- warning: inf_binfi -> inf_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f i h)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h)))) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (f i h)))))
Case conversion may be inaccurate. Consider using '#align inf_binfi inf_biInfₓ'. -/
theorem inf_biInf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊓ ⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a ⊓ f i h :=
  @sup_biSup αᵒᵈ ι _ p f _ h
#align inf_binfi inf_biInf

/-! ### `supr` and `infi` under `Prop` -/


/- warning: supr_false -> iSup_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) False s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) False s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_false iSup_falseₓ'. -/
@[simp]
theorem iSup_false {s : False → α} : iSup s = ⊥ :=
  le_antisymm (iSup_le fun i => False.elim i) bot_le
#align supr_false iSup_false

/- warning: infi_false -> iInf_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) False s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) False s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_false iInf_falseₓ'. -/
@[simp]
theorem iInf_false {s : False → α} : iInf s = ⊤ :=
  le_antisymm le_top (le_iInf fun i => False.elim i)
#align infi_false iInf_false

/- warning: supr_true -> iSup_true is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) True s) (s trivial)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) True s) (s trivial)
Case conversion may be inaccurate. Consider using '#align supr_true iSup_trueₓ'. -/
theorem iSup_true {s : True → α} : iSup s = s trivial :=
  iSup_pos trivial
#align supr_true iSup_true

/- warning: infi_true -> iInf_true is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) True s) (s trivial)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) True s) (s trivial)
Case conversion may be inaccurate. Consider using '#align infi_true iInf_trueₓ'. -/
theorem iInf_true {s : True → α} : iInf s = s trivial :=
  iInf_pos trivial
#align infi_true iInf_true

/- warning: supr_exists -> iSup_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align supr_exists iSup_existsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
@[simp]
theorem iSup_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => le_iSup₂ i h) (iSup₂_le fun i h => le_iSup _ _)
#align supr_exists iSup_exists

/- warning: infi_exists -> iInf_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align infi_exists iInf_existsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
@[simp]
theorem iInf_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ (i) (h), f ⟨i, h⟩ :=
  @iSup_exists αᵒᵈ _ _ _ _
#align infi_exists iInf_exists

/- warning: supr_and -> iSup_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (And p q) s) (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h₁ : p) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (And p q) s) (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h₁ : p) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
Case conversion may be inaccurate. Consider using '#align supr_and iSup_andₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (h₁ h₂) -/
theorem iSup_and {p q : Prop} {s : p ∧ q → α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => le_iSup₂ i h) (iSup₂_le fun i h => le_iSup _ _)
#align supr_and iSup_and

/- warning: infi_and -> iInf_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (And p q) s) (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h₁ : p) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (And p q) s) (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h₁ : p) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
Case conversion may be inaccurate. Consider using '#align infi_and iInf_andₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (h₁ h₂) -/
theorem iInf_and {p q : Prop} {s : p ∧ q → α} : iInf s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @iSup_and αᵒᵈ _ _ _ _
#align infi_and iInf_and

/- warning: supr_and' -> iSup_and' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h₁ : p) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) q (fun (h₂ : q) => s h₁ h₂))) (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h₁ : p) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) q (fun (h₂ : q) => s h₁ h₂))) (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
Case conversion may be inaccurate. Consider using '#align supr_and' iSup_and'ₓ'. -/
/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
theorem iSup_and' {p q : Prop} {s : p → q → α} :
    (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iSup_and
#align supr_and' iSup_and'

/- warning: infi_and' -> iInf_and' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h₁ : p) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) q (fun (h₂ : q) => s h₁ h₂))) (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h₁ : p) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) q (fun (h₂ : q) => s h₁ h₂))) (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
Case conversion may be inaccurate. Consider using '#align infi_and' iInf_and'ₓ'. -/
/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
theorem iInf_and' {p q : Prop} {s : p → q → α} :
    (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iInf_and
#align infi_and' iInf_and'

/- warning: supr_or -> iSup_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Or p q) (fun (x : Or p q) => s x)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (i : p) => s (Or.inl p q i))) (iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) q (fun (j : q) => s (Or.inr p q j))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Or p q) (fun (x : Or p q) => s x)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (i : p) => s (Or.inl p q i))) (iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) q (fun (j : q) => s (Or.inr p q j))))
Case conversion may be inaccurate. Consider using '#align supr_or iSup_orₓ'. -/
theorem iSup_or {p q : Prop} {s : p ∨ q → α} :
    (⨆ x, s x) = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (iSup_le fun i =>
      match i with
      | Or.inl i => le_sup_of_le_left <| le_iSup _ i
      | Or.inr j => le_sup_of_le_right <| le_iSup _ j)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))
#align supr_or iSup_or

/- warning: infi_or -> iInf_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Or p q) (fun (x : Or p q) => s x)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (i : p) => s (Or.inl p q i))) (iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) q (fun (j : q) => s (Or.inr p q j))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Or p q) (fun (x : Or p q) => s x)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (i : p) => s (Or.inl p q i))) (iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) q (fun (j : q) => s (Or.inr p q j))))
Case conversion may be inaccurate. Consider using '#align infi_or iInf_orₓ'. -/
theorem iInf_or {p q : Prop} {s : p ∨ q → α} :
    (⨅ x, s x) = (⨅ i, s (Or.inl i)) ⊓ ⨅ j, s (Or.inr j) :=
  @iSup_or αᵒᵈ _ _ _ _
#align infi_or iInf_or

section

variable (p : ι → Prop) [DecidablePred p]

/- warning: supr_dite -> iSup_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => dite.{succ u1} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i h))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => dite.{succ u2} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i h))))
Case conversion may be inaccurate. Consider using '#align supr_dite iSup_diteₓ'. -/
theorem iSup_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨆ i, if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i), g i h :=
  by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]
#align supr_dite iSup_dite

/- warning: infi_dite -> iInf_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => dite.{succ u1} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i h))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => dite.{succ u2} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i h))))
Case conversion may be inaccurate. Consider using '#align infi_dite iInf_diteₓ'. -/
theorem iInf_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨅ i, if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h) ⊓ ⨅ (i) (h : ¬p i), g i h :=
  iSup_dite p (show ∀ i, p i → αᵒᵈ from f) g
#align infi_dite iInf_dite

/- warning: supr_ite -> iSup_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => ite.{succ u1} α (p i) (_inst_2 i) (f i) (g i))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => ite.{succ u2} α (p i) (_inst_2 i) (f i) (g i))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i))))
Case conversion may be inaccurate. Consider using '#align supr_ite iSup_iteₓ'. -/
theorem iSup_ite (f g : ι → α) :
    (⨆ i, if p i then f i else g i) = (⨆ (i) (h : p i), f i) ⊔ ⨆ (i) (h : ¬p i), g i :=
  iSup_dite _ _ _
#align supr_ite iSup_ite

/- warning: infi_ite -> iInf_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => ite.{succ u1} α (p i) (_inst_2 i) (f i) (g i))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => ite.{succ u2} α (p i) (_inst_2 i) (f i) (g i))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i))))
Case conversion may be inaccurate. Consider using '#align infi_ite iInf_iteₓ'. -/
theorem iInf_ite (f g : ι → α) :
    (⨅ i, if p i then f i else g i) = (⨅ (i) (h : p i), f i) ⊓ ⨅ (i) (h : ¬p i), g i :=
  iInf_dite _ _ _
#align infi_ite iInf_ite

end

/- warning: supr_range -> iSup_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {g : β -> α} {f : ι -> β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) => g b))) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {g : β -> α} {f : ι -> β}, Eq.{succ u3} α (iSup.{u3, succ u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) β (fun (b : β) => iSup.{u3, 0} α (CompleteLattice.toSupSet.{u3} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) => g b))) (iSup.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align supr_range iSup_rangeₓ'. -/
theorem iSup_range {g : β → α} {f : ι → β} : (⨆ b ∈ range f, g b) = ⨆ i, g (f i) := by
  rw [← iSup_subtype'', iSup_range']
#align supr_range iSup_range

/- warning: infi_range -> iInf_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {g : β -> α} {f : ι -> β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) => g b))) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {g : β -> α} {f : ι -> β}, Eq.{succ u3} α (iInf.{u3, succ u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) β (fun (b : β) => iInf.{u3, 0} α (CompleteLattice.toInfSet.{u3} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) => g b))) (iInf.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align infi_range iInf_rangeₓ'. -/
theorem iInf_range : ∀ {g : β → α} {f : ι → β}, (⨅ b ∈ range f, g b) = ⨅ i, g (f i) :=
  @iSup_range αᵒᵈ _ _ _
#align infi_range iInf_range

/- warning: Sup_image -> sSup_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.image.{u2, u1} β α f s)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.image.{u2, u1} β α f s)) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (a : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) => f a)))
Case conversion may be inaccurate. Consider using '#align Sup_image sSup_imageₓ'. -/
theorem sSup_image {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← iSup_subtype'', sSup_image']
#align Sup_image sSup_image

/- warning: Inf_image -> sInf_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Set.image.{u2, u1} β α f s)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.image.{u2, u1} β α f s)) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (a : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) => f a)))
Case conversion may be inaccurate. Consider using '#align Inf_image sInf_imageₓ'. -/
theorem sInf_image {s : Set β} {f : β → α} : sInf (f '' s) = ⨅ a ∈ s, f a :=
  @sSup_image αᵒᵈ _ _ _ _
#align Inf_image sInf_image

/- warning: supr_emptyset -> iSup_emptyset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) => f x))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) => f x))) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_emptyset iSup_emptysetₓ'. -/
/-
### supr and infi under set constructions
-/
theorem iSup_emptyset {f : β → α} : (⨆ x ∈ (∅ : Set β), f x) = ⊥ := by simp
#align supr_emptyset iSup_emptyset

/- warning: infi_emptyset -> iInf_emptyset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) => f x))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) => f x))) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_emptyset iInf_emptysetₓ'. -/
theorem iInf_emptyset {f : β → α} : (⨅ x ∈ (∅ : Set β), f x) = ⊤ := by simp
#align infi_emptyset iInf_emptyset

/- warning: supr_univ -> iSup_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) => f x))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) => f x))) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => f x))
Case conversion may be inaccurate. Consider using '#align supr_univ iSup_univₓ'. -/
theorem iSup_univ {f : β → α} : (⨆ x ∈ (univ : Set β), f x) = ⨆ x, f x := by simp
#align supr_univ iSup_univ

/- warning: infi_univ -> iInf_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) => f x))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) => f x))) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => f x))
Case conversion may be inaccurate. Consider using '#align infi_univ iInf_univₓ'. -/
theorem iInf_univ {f : β → α} : (⨅ x ∈ (univ : Set β), f x) = ⨅ x, f x := by simp
#align infi_univ iInf_univ

/- warning: supr_union -> iSup_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) => f x))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) => f x))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align supr_union iSup_unionₓ'. -/
theorem iSup_union {f : β → α} {s t : Set β} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x :=
  by simp_rw [mem_union, iSup_or, iSup_sup_eq]
#align supr_union iSup_union

/- warning: infi_union -> iInf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) => f x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) => f x))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align infi_union iInf_unionₓ'. -/
theorem iInf_union {f : β → α} {s t : Set β} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union αᵒᵈ _ _ _ _ _
#align infi_union iInf_union

/- warning: supr_split -> iSup_split is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (p : β -> Prop), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => f i)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (p : β -> Prop), Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => f i)) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => f i))))
Case conversion may be inaccurate. Consider using '#align supr_split iSup_splitₓ'. -/
theorem iSup_split (f : β → α) (p : β → Prop) :
    (⨆ i, f i) = (⨆ (i) (h : p i), f i) ⊔ ⨆ (i) (h : ¬p i), f i := by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }
#align supr_split iSup_split

/- warning: infi_split -> iInf_split is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (p : β -> Prop), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => f i)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (p : β -> Prop), Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => f i)) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => f i))))
Case conversion may be inaccurate. Consider using '#align infi_split iInf_splitₓ'. -/
theorem iInf_split :
    ∀ (f : β → α) (p : β → Prop), (⨅ i, f i) = (⨅ (i) (h : p i), f i) ⊓ ⨅ (i) (h : ¬p i), f i :=
  @iSup_split αᵒᵈ _ _
#align infi_split iInf_split

/- warning: supr_split_single -> iSup_split_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (i₀ : β), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => f i)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i₀) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Ne.{succ u2} β i i₀) (fun (h : Ne.{succ u2} β i i₀) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (i₀ : β), Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => f i)) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f i₀) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Ne.{succ u1} β i i₀) (fun (h : Ne.{succ u1} β i i₀) => f i))))
Case conversion may be inaccurate. Consider using '#align supr_split_single iSup_split_singleₓ'. -/
theorem iSup_split_single (f : β → α) (i₀ : β) : (⨆ i, f i) = f i₀ ⊔ ⨆ (i) (h : i ≠ i₀), f i :=
  by
  convert iSup_split _ _
  simp
#align supr_split_single iSup_split_single

/- warning: infi_split_single -> iInf_split_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (i₀ : β), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => f i)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i₀) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Ne.{succ u2} β i i₀) (fun (h : Ne.{succ u2} β i i₀) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (i₀ : β), Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => f i)) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f i₀) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Ne.{succ u1} β i i₀) (fun (h : Ne.{succ u1} β i i₀) => f i))))
Case conversion may be inaccurate. Consider using '#align infi_split_single iInf_split_singleₓ'. -/
theorem iInf_split_single (f : β → α) (i₀ : β) : (⨅ i, f i) = f i₀ ⊓ ⨅ (i) (h : i ≠ i₀), f i :=
  @iSup_split_single αᵒᵈ _ _ _ _
#align infi_split_single iInf_split_single

/- warning: supr_le_supr_of_subset -> iSup_le_iSup_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align supr_le_supr_of_subset iSup_le_iSup_of_subsetₓ'. -/
theorem iSup_le_iSup_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨆ x ∈ s, f x) ≤ ⨆ x ∈ t, f x :=
  biSup_mono
#align supr_le_supr_of_subset iSup_le_iSup_of_subset

/- warning: infi_le_infi_of_subset -> iInf_le_iInf_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align infi_le_infi_of_subset iInf_le_iInf_of_subsetₓ'. -/
theorem iInf_le_iInf_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨅ x ∈ t, f x) ≤ ⨅ x ∈ s, f x :=
  biInf_mono
#align infi_le_infi_of_subset iInf_le_iInf_of_subset

/- warning: supr_insert -> iSup_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) => f x))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f b) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) => f x))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f b) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align supr_insert iSup_insertₓ'. -/
theorem iSup_insert {f : β → α} {s : Set β} {b : β} :
    (⨆ x ∈ insert b s, f x) = f b ⊔ ⨆ x ∈ s, f x :=
  Eq.trans iSup_union <| congr_arg (fun x => x ⊔ ⨆ x ∈ s, f x) iSup_iSup_eq_left
#align supr_insert iSup_insert

/- warning: infi_insert -> iInf_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) => f x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f b) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) => f x))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f b) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align infi_insert iInf_insertₓ'. -/
theorem iInf_insert {f : β → α} {s : Set β} {b : β} :
    (⨅ x ∈ insert b s, f x) = f b ⊓ ⨅ x ∈ s, f x :=
  Eq.trans iInf_union <| congr_arg (fun x => x ⊓ ⨅ x ∈ s, f x) iInf_iInf_eq_left
#align infi_insert iInf_insert

/- warning: supr_singleton -> iSup_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {b : β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) => f x))) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {b : β}, Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) => f x))) (f b)
Case conversion may be inaccurate. Consider using '#align supr_singleton iSup_singletonₓ'. -/
theorem iSup_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : Set β), f x) = f b := by simp
#align supr_singleton iSup_singleton

/- warning: infi_singleton -> iInf_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {b : β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) => f x))) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {b : β}, Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) => f x))) (f b)
Case conversion may be inaccurate. Consider using '#align infi_singleton iInf_singletonₓ'. -/
theorem iInf_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : Set β), f x) = f b := by simp
#align infi_singleton iInf_singleton

/- warning: supr_pair -> iSup_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) => f x))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f a) (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => iSup.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) => f x))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f a) (f b))
Case conversion may be inaccurate. Consider using '#align supr_pair iSup_pairₓ'. -/
theorem iSup_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : Set β), f x) = f a ⊔ f b := by
  rw [iSup_insert, iSup_singleton]
#align supr_pair iSup_pair

/- warning: infi_pair -> iInf_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) => f x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f a) (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => iInf.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) => f x))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f a) (f b))
Case conversion may be inaccurate. Consider using '#align infi_pair iInf_pairₓ'. -/
theorem iInf_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : Set β), f x) = f a ⊓ f b := by
  rw [iInf_insert, iInf_singleton]
#align infi_pair iInf_pair

/- warning: supr_image -> iSup_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (c : γ) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) => g (f b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (iSup.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (c : γ) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (b : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) => g (f b))))
Case conversion may be inaccurate. Consider using '#align supr_image iSup_imageₓ'. -/
theorem iSup_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    (⨆ c ∈ f '' t, g c) = ⨆ b ∈ t, g (f b) := by rw [← sSup_image, ← sSup_image, ← image_comp]
#align supr_image iSup_image

/- warning: infi_image -> iInf_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (c : γ) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) => g (f b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (iInf.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (c : γ) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (b : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) => g (f b))))
Case conversion may be inaccurate. Consider using '#align infi_image iInf_imageₓ'. -/
theorem iInf_image :
    ∀ {γ} {f : β → γ} {g : γ → α} {t : Set β}, (⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b) :=
  @iSup_image αᵒᵈ _ _
#align infi_image iInf_image

/- warning: supr_extend_bot -> iSup_extend_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Bot.bot.{max u2 u1} (β -> α) (Pi.hasBot.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toHasBot.{u1} α _inst_1))) j)) (iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Bot.bot.{max u1 u2} (β -> α) (Pi.instBotForAll.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toBot.{u1} α _inst_1))) j)) (iSup.{u1, u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align supr_extend_bot iSup_extend_botₓ'. -/
theorem iSup_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨆ j, extend e f ⊥ j) = ⨆ i, f i :=
  by
  rw [iSup_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true }) [he.extend_apply, extend_apply', @iSup_comm _ β ι]
#align supr_extend_bot iSup_extend_bot

/- warning: infi_extend_top -> iInf_extend_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Top.top.{max u2 u1} (β -> α) (Pi.hasTop.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toHasTop.{u1} α _inst_1))) j)) (iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Top.top.{max u1 u2} (β -> α) (Pi.instTopForAll.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toTop.{u1} α _inst_1))) j)) (iInf.{u1, u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align infi_extend_top iInf_extend_topₓ'. -/
theorem iInf_extend_top {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨅ j, extend e f ⊤ j) = iInf f :=
  @iSup_extend_bot αᵒᵈ _ _ _ _ he _
#align infi_extend_top iInf_extend_top

/-!
### `supr` and `infi` under `Type`
-/


/- warning: supr_of_empty' -> iSup_of_empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_2 : SupSet.{u1} α] [_inst_3 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, u2} α _inst_2 ι f) (SupSet.sSup.{u1} α _inst_2 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_2 : SupSet.{u2} α] [_inst_3 : IsEmpty.{u1} ι] (f : ι -> α), Eq.{succ u2} α (iSup.{u2, u1} α _inst_2 ι f) (SupSet.sSup.{u2} α _inst_2 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align supr_of_empty' iSup_of_empty'ₓ'. -/
theorem iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : iSup f = sSup (∅ : Set α) :=
  congr_arg sSup (range_eq_empty f)
#align supr_of_empty' iSup_of_empty'

/- warning: infi_of_empty' -> iInf_of_empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_2 : InfSet.{u1} α] [_inst_3 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iInf.{u1, u2} α _inst_2 ι f) (InfSet.sInf.{u1} α _inst_2 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_2 : InfSet.{u2} α] [_inst_3 : IsEmpty.{u1} ι] (f : ι -> α), Eq.{succ u2} α (iInf.{u2, u1} α _inst_2 ι f) (InfSet.sInf.{u2} α _inst_2 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align infi_of_empty' iInf_of_empty'ₓ'. -/
theorem iInf_of_empty' {α ι} [InfSet α] [IsEmpty ι] (f : ι → α) : iInf f = sInf (∅ : Set α) :=
  congr_arg sInf (range_eq_empty f)
#align infi_of_empty' iInf_of_empty'

/- warning: supr_of_empty -> iSup_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι f) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_of_empty iSup_of_emptyₓ'. -/
theorem iSup_of_empty [IsEmpty ι] (f : ι → α) : iSup f = ⊥ :=
  (iSup_of_empty' f).trans sSup_empty
#align supr_of_empty iSup_of_empty

/- warning: infi_of_empty -> iInf_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι f) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_of_empty iInf_of_emptyₓ'. -/
theorem iInf_of_empty [IsEmpty ι] (f : ι → α) : iInf f = ⊤ :=
  @iSup_of_empty αᵒᵈ _ _ _ f
#align infi_of_empty iInf_of_empty

/- warning: supr_bool_eq -> iSup_bool_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Bool (fun (b : Bool) => f b)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f Bool.true) (f Bool.false))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Bool (fun (b : Bool) => f b)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f Bool.true) (f Bool.false))
Case conversion may be inaccurate. Consider using '#align supr_bool_eq iSup_bool_eqₓ'. -/
theorem iSup_bool_eq {f : Bool → α} : (⨆ b : Bool, f b) = f true ⊔ f false := by
  rw [iSup, Bool.range_eq, sSup_pair, sup_comm]
#align supr_bool_eq iSup_bool_eq

/- warning: infi_bool_eq -> iInf_bool_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Bool (fun (b : Bool) => f b)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f Bool.true) (f Bool.false))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Bool (fun (b : Bool) => f b)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f Bool.true) (f Bool.false))
Case conversion may be inaccurate. Consider using '#align infi_bool_eq iInf_bool_eqₓ'. -/
theorem iInf_bool_eq {f : Bool → α} : (⨅ b : Bool, f b) = f true ⊓ f false :=
  @iSup_bool_eq αᵒᵈ _ _
#align infi_bool_eq iInf_bool_eq

/- warning: sup_eq_supr -> sup_eq_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) x y) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Bool (fun (b : Bool) => cond.{u1} α b x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) x y) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Bool (fun (b : Bool) => cond.{u1} α b x y))
Case conversion may be inaccurate. Consider using '#align sup_eq_supr sup_eq_iSupₓ'. -/
theorem sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [iSup_bool_eq, Bool.cond_true, Bool.cond_false]
#align sup_eq_supr sup_eq_iSup

/- warning: inf_eq_infi -> inf_eq_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) x y) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Bool (fun (b : Bool) => cond.{u1} α b x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) x y) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Bool (fun (b : Bool) => cond.{u1} α b x y))
Case conversion may be inaccurate. Consider using '#align inf_eq_infi inf_eq_iInfₓ'. -/
theorem inf_eq_iInf (x y : α) : x ⊓ y = ⨅ b : Bool, cond b x y :=
  @sup_eq_iSup αᵒᵈ _ _ _
#align inf_eq_infi inf_eq_iInf

/- warning: is_glb_binfi -> isGLB_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align is_glb_binfi isGLB_biInfₓ'. -/
theorem isGLB_biInf {s : Set β} {f : β → α} : IsGLB (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iInf_subtype'] using @isGLB_iInf α s _ (f ∘ coe)
#align is_glb_binfi isGLB_biInf

/- warning: is_lub_bsupr -> isLUB_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align is_lub_bsupr isLUB_biSupₓ'. -/
theorem isLUB_biSup {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using @isLUB_iSup α s _ (f ∘ coe)
#align is_lub_bsupr isLUB_biSup

/- warning: supr_sigma -> iSup_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (iSup.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (iSup.{u1, max (succ u2) (succ u3)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (i : β) => iSup.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
Case conversion may be inaccurate. Consider using '#align supr_sigma iSup_sigmaₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup_sigma {p : β → Type _} {f : Sigma p → α} : (⨆ x, f x) = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]
#align supr_sigma iSup_sigma

/- warning: infi_sigma -> iInf_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (iInf.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (iInf.{u1, max (succ u2) (succ u3)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (i : β) => iInf.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
Case conversion may be inaccurate. Consider using '#align infi_sigma iInf_sigmaₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf_sigma {p : β → Type _} {f : Sigma p → α} : (⨅ x, f x) = ⨅ (i) (j), f ⟨i, j⟩ :=
  @iSup_sigma αᵒᵈ _ _ _ _
#align infi_sigma iInf_sigma

/- warning: supr_prod -> iSup_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α}, Eq.{succ u1} α (iSup.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => f x)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (j : γ) => f (Prod.mk.{u2, u3} β γ i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α}, Eq.{succ u1} α (iSup.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => f x)) (iSup.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (i : β) => iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (j : γ) => f (Prod.mk.{u3, u2} β γ i j))))
Case conversion may be inaccurate. Consider using '#align supr_prod iSup_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup_prod {f : β × γ → α} : (⨆ x, f x) = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]
#align supr_prod iSup_prod

/- warning: infi_prod -> iInf_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α}, Eq.{succ u1} α (iInf.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => f x)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (j : γ) => f (Prod.mk.{u2, u3} β γ i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α}, Eq.{succ u1} α (iInf.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => f x)) (iInf.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (i : β) => iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (j : γ) => f (Prod.mk.{u3, u2} β γ i j))))
Case conversion may be inaccurate. Consider using '#align infi_prod iInf_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf_prod {f : β × γ → α} : (⨅ x, f x) = ⨅ (i) (j), f (i, j) :=
  @iSup_prod αᵒᵈ _ _ _ _
#align infi_prod iInf_prod

/- warning: bsupr_prod -> biSup_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (iSup.{u1, succ (max u2 u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) => f x))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (b : γ) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f (Prod.mk.{u2, u3} β γ a b))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (iSup.{u1, succ (max u3 u2)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) (fun (H : Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) => f x))) (iSup.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (a : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (b : γ) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f (Prod.mk.{u3, u2} β γ a b))))))
Case conversion may be inaccurate. Consider using '#align bsupr_prod biSup_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem biSup_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨆ x ∈ s ×ˢ t, f x) = ⨆ (a ∈ s) (b ∈ t), f (a, b) :=
  by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm
#align bsupr_prod biSup_prod

/- warning: binfi_prod -> biInf_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (iInf.{u1, succ (max u2 u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) => f x))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (b : γ) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f (Prod.mk.{u2, u3} β γ a b))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (iInf.{u1, succ (max u3 u2)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) (fun (H : Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) => f x))) (iInf.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (a : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (b : γ) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f (Prod.mk.{u3, u2} β γ a b))))))
Case conversion may be inaccurate. Consider using '#align binfi_prod biInf_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem biInf_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨅ x ∈ s ×ˢ t, f x) = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
  @biSup_prod αᵒᵈ _ _ _ _ _ _
#align binfi_prod biInf_prod

/- warning: supr_sum -> iSup_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u2, u3} β γ) -> α}, Eq.{succ u1} α (iSup.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Sum.{u2, u3} β γ) (fun (x : Sum.{u2, u3} β γ) => f x)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => f (Sum.inl.{u2, u3} β γ i))) (iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (j : γ) => f (Sum.inr.{u2, u3} β γ j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u3, u2} β γ) -> α}, Eq.{succ u1} α (iSup.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Sum.{u3, u2} β γ) (fun (x : Sum.{u3, u2} β γ) => f x)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (i : β) => f (Sum.inl.{u3, u2} β γ i))) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (j : γ) => f (Sum.inr.{u3, u2} β γ j))))
Case conversion may be inaccurate. Consider using '#align supr_sum iSup_sumₓ'. -/
theorem iSup_sum {f : Sum β γ → α} : (⨆ x, f x) = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]
#align supr_sum iSup_sum

/- warning: infi_sum -> iInf_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u2, u3} β γ) -> α}, Eq.{succ u1} α (iInf.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Sum.{u2, u3} β γ) (fun (x : Sum.{u2, u3} β γ) => f x)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => f (Sum.inl.{u2, u3} β γ i))) (iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (j : γ) => f (Sum.inr.{u2, u3} β γ j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u3, u2} β γ) -> α}, Eq.{succ u1} α (iInf.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Sum.{u3, u2} β γ) (fun (x : Sum.{u3, u2} β γ) => f x)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (iInf.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (i : β) => f (Sum.inl.{u3, u2} β γ i))) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (j : γ) => f (Sum.inr.{u3, u2} β γ j))))
Case conversion may be inaccurate. Consider using '#align infi_sum iInf_sumₓ'. -/
theorem iInf_sum {f : Sum β γ → α} : (⨅ x, f x) = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.inr j) :=
  @iSup_sum αᵒᵈ _ _ _ _
#align infi_sum iInf_sum

/- warning: supr_option -> iSup_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f (Option.none.{u2} β)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => f (Option.some.{u2} β b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f (Option.none.{u2} β)) (iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (b : β) => f (Option.some.{u2} β b))))
Case conversion may be inaccurate. Consider using '#align supr_option iSup_optionₓ'. -/
theorem iSup_option (f : Option β → α) : (⨆ o, f o) = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]
#align supr_option iSup_option

/- warning: infi_option -> iInf_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f (Option.none.{u2} β)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => f (Option.some.{u2} β b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f (Option.none.{u2} β)) (iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (b : β) => f (Option.some.{u2} β b))))
Case conversion may be inaccurate. Consider using '#align infi_option iInf_optionₓ'. -/
theorem iInf_option (f : Option β → α) : (⨅ o, f o) = f none ⊓ ⨅ b, f (Option.some b) :=
  @iSup_option αᵒᵈ _ _ _
#align infi_option iInf_option

/- warning: supr_option_elim -> iSup_option_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (a : α) (f : β -> α), Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => Option.elim'.{u2, u1} β α a f o)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (a : α) (f : β -> α), Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Option.{u1} β) (fun (o : Option.{u1} β) => Option.elim.{u1, succ u2} β α o a f)) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) a (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align supr_option_elim iSup_option_elimₓ'. -/
/-- A version of `supr_option` useful for rewriting right-to-left. -/
theorem iSup_option_elim (a : α) (f : β → α) : (⨆ o : Option β, o.elim a f) = a ⊔ ⨆ b, f b := by
  simp [iSup_option]
#align supr_option_elim iSup_option_elim

/- warning: infi_option_elim -> iInf_option_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (a : α) (f : β -> α), Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => Option.elim'.{u2, u1} β α a f o)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (a : α) (f : β -> α), Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Option.{u1} β) (fun (o : Option.{u1} β) => Option.elim.{u1, succ u2} β α o a f)) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) a (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align infi_option_elim iInf_option_elimₓ'. -/
/-- A version of `infi_option` useful for rewriting right-to-left. -/
theorem iInf_option_elim (a : α) (f : β → α) : (⨅ o : Option β, o.elim a f) = a ⊓ ⨅ b, f b :=
  @iSup_option_elim αᵒᵈ _ _ _ _
#align infi_option_elim iInf_option_elim

/- warning: supr_ne_bot_subtype -> iSup_ne_bot_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} α (iSup.{u1, max 1 u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) (fun (i : Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (coeSubtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))))) i))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} α (iSup.{u2, max 1 u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1)))) (fun (i : Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1)))) => f (Subtype.val.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) i))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align supr_ne_bot_subtype iSup_ne_bot_subtypeₓ'. -/
/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
theorem iSup_ne_bot_subtype (f : ι → α) : (⨆ i : { i // f i ≠ ⊥ }, f i) = ⨆ i, f i :=
  by
  by_cases htriv : ∀ i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine' (iSup_comp_le f _).antisymm (iSup_mono' fun i => _)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩
#align supr_ne_bot_subtype iSup_ne_bot_subtype

/- warning: infi_ne_top_subtype -> iInf_ne_top_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} α (iInf.{u1, max 1 u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) (fun (i : Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (coeSubtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))))) i))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} α (iInf.{u2, max 1 u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1)))) (fun (i : Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1)))) => f (Subtype.val.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) i))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align infi_ne_top_subtype iInf_ne_top_subtypeₓ'. -/
/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem iInf_ne_top_subtype (f : ι → α) : (⨅ i : { i // f i ≠ ⊤ }, f i) = ⨅ i, f i :=
  @iSup_ne_bot_subtype αᵒᵈ ι _ f
#align infi_ne_top_subtype iInf_ne_top_subtype

/- warning: Sup_image2 -> sSup_image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.image2.{u2, u3, u1} β γ α f s t)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (b : γ) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f a b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.image2.{u3, u2, u1} β γ α f s t)) (iSup.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (a : β) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => iSup.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (b : γ) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f a b)))))
Case conversion may be inaccurate. Consider using '#align Sup_image2 sSup_image2ₓ'. -/
theorem sSup_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sSup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sSup_image, biSup_prod]
#align Sup_image2 sSup_image2

/- warning: Inf_image2 -> sInf_image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Set.image2.{u2, u3, u1} β γ α f s t)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (b : γ) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f a b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.image2.{u3, u2, u1} β γ α f s t)) (iInf.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (a : β) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => iInf.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (b : γ) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f a b)))))
Case conversion may be inaccurate. Consider using '#align Inf_image2 sInf_image2ₓ'. -/
theorem sInf_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sInf (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sInf_image, biInf_prod]
#align Inf_image2 sInf_image2

/-!
### `supr` and `infi` under `ℕ`
-/


/- warning: supr_ge_eq_supr_nat_add -> iSup_ge_eq_iSup_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => u i))) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => u i))) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i n)))
Case conversion may be inaccurate. Consider using '#align supr_ge_eq_supr_nat_add iSup_ge_eq_iSup_nat_addₓ'. -/
theorem iSup_ge_eq_iSup_nat_add (u : ℕ → α) (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) :=
  by
  apply le_antisymm <;> simp only [iSup_le_iff]
  ·
    exact fun i hi =>
      le_sSup
        ⟨i - n, by
          dsimp only
          rw [Nat.sub_add_cancel hi]⟩
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩
#align supr_ge_eq_supr_nat_add iSup_ge_eq_iSup_nat_add

/- warning: infi_ge_eq_infi_nat_add -> iInf_ge_eq_iInf_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => u i))) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => u i))) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i n)))
Case conversion may be inaccurate. Consider using '#align infi_ge_eq_infi_nat_add iInf_ge_eq_iInf_nat_addₓ'. -/
theorem iInf_ge_eq_iInf_nat_add (u : ℕ → α) (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
  @iSup_ge_eq_iSup_nat_add αᵒᵈ _ _ _
#align infi_ge_eq_infi_nat_add iInf_ge_eq_iInf_nat_add

/- warning: monotone.supr_nat_add -> Monotone.iSup_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k))) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k))) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align monotone.supr_nat_add Monotone.iSup_nat_addₓ'. -/
theorem Monotone.iSup_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : (⨆ n, f (n + k)) = ⨆ n, f n :=
  le_antisymm (iSup_le fun i => le_iSup _ (i + k)) <| iSup_mono fun i => hf <| Nat.le_add_right i k
#align monotone.supr_nat_add Monotone.iSup_nat_add

/- warning: antitone.infi_nat_add -> Antitone.iInf_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Antitone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k))) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Antitone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k))) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align antitone.infi_nat_add Antitone.iInf_nat_addₓ'. -/
theorem Antitone.iInf_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : (⨅ n, f (n + k)) = ⨅ n, f n :=
  hf.dual_right.iSup_nat_add k
#align antitone.infi_nat_add Antitone.iInf_nat_add

/- warning: supr_infi_ge_nat_add -> iSup_iInf_ge_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k))))) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k))))) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f i))))
Case conversion may be inaccurate. Consider using '#align supr_infi_ge_nat_add iSup_iInf_ge_nat_addₓ'. -/
@[simp]
theorem iSup_iInf_ge_nat_add (f : ℕ → α) (k : ℕ) : (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i :=
  by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]
#align supr_infi_ge_nat_add iSup_iInf_ge_nat_add

/- warning: infi_supr_ge_nat_add -> iInf_iSup_ge_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k))))) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k))))) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f i))))
Case conversion may be inaccurate. Consider using '#align infi_supr_ge_nat_add iInf_iSup_ge_nat_addₓ'. -/
@[simp]
theorem iInf_iSup_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), (⨅ n, ⨆ i ≥ n, f (i + k)) = ⨅ n, ⨆ i ≥ n, f i :=
  @iSup_iInf_ge_nat_add αᵒᵈ _
#align infi_supr_ge_nat_add iInf_iSup_ge_nat_add

/- warning: sup_supr_nat_succ -> sup_iSup_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => u i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => u i))
Case conversion may be inaccurate. Consider using '#align sup_supr_nat_succ sup_iSup_nat_succₓ'. -/
theorem sup_iSup_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      rw [iSup_union, iSup_singleton, iSup_range]
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]
    
#align sup_supr_nat_succ sup_iSup_nat_succ

/- warning: inf_infi_nat_succ -> inf_iInf_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => u i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => u i))
Case conversion may be inaccurate. Consider using '#align inf_infi_nat_succ inf_iInf_nat_succₓ'. -/
theorem inf_iInf_nat_succ (u : ℕ → α) : (u 0 ⊓ ⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_iSup_nat_succ αᵒᵈ _ u
#align inf_infi_nat_succ inf_iInf_nat_succ

/- warning: infi_nat_gt_zero_eq -> iInf_nat_gt_zero_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => f i))) (iInf.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (H : GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => f i))) (iInf.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align infi_nat_gt_zero_eq iInf_nat_gt_zero_eqₓ'. -/
theorem iInf_nat_gt_zero_eq (f : ℕ → α) : (⨅ i > 0, f i) = ⨅ i, f (i + 1) :=
  by
  rw [← iInf_range, Nat.range_succ]
  simp only [mem_set_of]
#align infi_nat_gt_zero_eq iInf_nat_gt_zero_eq

/- warning: supr_nat_gt_zero_eq -> iSup_nat_gt_zero_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => f i))) (iSup.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (H : GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => f i))) (iSup.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align supr_nat_gt_zero_eq iSup_nat_gt_zero_eqₓ'. -/
theorem iSup_nat_gt_zero_eq (f : ℕ → α) : (⨆ i > 0, f i) = ⨆ i, f (i + 1) :=
  @iInf_nat_gt_zero_eq αᵒᵈ _ f
#align supr_nat_gt_zero_eq iSup_nat_gt_zero_eq

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

/- warning: supr_eq_top -> iSup_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] (f : ι -> α), Iff (Eq.{succ u1} α (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] (f : ι -> α), Iff (Eq.{succ u2} α (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) (forall (b : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) b (Top.top.{u2} α (CompleteLattice.toTop.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) b (f i))))
Case conversion may be inaccurate. Consider using '#align supr_eq_top iSup_eq_topₓ'. -/
theorem iSup_eq_top (f : ι → α) : iSup f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  simp only [← sSup_range, sSup_eq_top, Set.exists_range_iff]
#align supr_eq_top iSup_eq_top

/- warning: infi_eq_bot -> iInf_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] (f : ι -> α), Iff (Eq.{succ u1} α (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (GT.gt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (f i) b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] (f : ι -> α), Iff (Eq.{succ u2} α (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) (forall (b : α), (GT.gt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) b (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) (f i) b)))
Case conversion may be inaccurate. Consider using '#align infi_eq_bot iInf_eq_botₓ'. -/
theorem iInf_eq_bot (f : ι → α) : iInf f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b := by
  simp only [← sInf_range, sInf_eq_bot, Set.exists_range_iff]
#align infi_eq_bot iInf_eq_bot

end CompleteLinearOrder

/-!
### Instances
-/


#print Prop.completeLattice /-
instance Prop.completeLattice : CompleteLattice Prop :=
  { Prop.boundedOrder,
    Prop.distribLattice with
    sSup := fun s => ∃ a ∈ s, a
    le_sup := fun s a h p => ⟨a, h, p⟩
    sup_le := fun s a h ⟨b, h', p⟩ => h b h' p
    sInf := fun s => ∀ a, a ∈ s → a
    inf_le := fun s a h p => p a h
    le_inf := fun s a h p b hb => h b hb p }
#align Prop.complete_lattice Prop.completeLattice
-/

#print Prop.completeLinearOrder /-
noncomputable instance Prop.completeLinearOrder : CompleteLinearOrder Prop :=
  { Prop.completeLattice, Prop.linearOrder with }
#align Prop.complete_linear_order Prop.completeLinearOrder
-/

/- warning: Sup_Prop_eq -> sSup_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Prop}, Eq.{1} Prop (SupSet.sSup.{0} Prop (CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)) s) (Exists.{1} Prop (fun (p : Prop) => Exists.{0} (Membership.Mem.{0, 0} Prop (Set.{0} Prop) (Set.hasMem.{0} Prop) p s) (fun (H : Membership.Mem.{0, 0} Prop (Set.{0} Prop) (Set.hasMem.{0} Prop) p s) => p)))
but is expected to have type
  forall {s : Set.{0} Prop}, Eq.{1} Prop (SupSet.sSup.{0} Prop (CompleteLattice.toSupSet.{0} Prop Prop.completeLattice) s) (Exists.{1} Prop (fun (p : Prop) => And (Membership.mem.{0, 0} Prop (Set.{0} Prop) (Set.instMembershipSet.{0} Prop) p s) p))
Case conversion may be inaccurate. Consider using '#align Sup_Prop_eq sSup_Prop_eqₓ'. -/
@[simp]
theorem sSup_Prop_eq {s : Set Prop} : sSup s = ∃ p ∈ s, p :=
  rfl
#align Sup_Prop_eq sSup_Prop_eq

/- warning: Inf_Prop_eq -> sInf_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Prop}, Eq.{1} Prop (InfSet.sInf.{0} Prop (CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)) s) (forall (p : Prop), (Membership.Mem.{0, 0} Prop (Set.{0} Prop) (Set.hasMem.{0} Prop) p s) -> p)
but is expected to have type
  forall {s : Set.{0} Prop}, Eq.{1} Prop (InfSet.sInf.{0} Prop (CompleteLattice.toInfSet.{0} Prop Prop.completeLattice) s) (forall (p : Prop), (Membership.mem.{0, 0} Prop (Set.{0} Prop) (Set.instMembershipSet.{0} Prop) p s) -> p)
Case conversion may be inaccurate. Consider using '#align Inf_Prop_eq sInf_Prop_eqₓ'. -/
@[simp]
theorem sInf_Prop_eq {s : Set Prop} : sInf s = ∀ p ∈ s, p :=
  rfl
#align Inf_Prop_eq sInf_Prop_eq

/- warning: supr_Prop_eq -> iSup_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (iSup.{0, u1} Prop (CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)) ι (fun (i : ι) => p i)) (Exists.{u1} ι (fun (i : ι) => p i))
but is expected to have type
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (iSup.{0, u1} Prop (CompleteLattice.toSupSet.{0} Prop Prop.completeLattice) ι (fun (i : ι) => p i)) (Exists.{u1} ι (fun (i : ι) => p i))
Case conversion may be inaccurate. Consider using '#align supr_Prop_eq iSup_Prop_eqₓ'. -/
@[simp]
theorem iSup_Prop_eq {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
  le_antisymm (fun ⟨q, ⟨i, (Eq : p i = q)⟩, hq⟩ => ⟨i, Eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩
#align supr_Prop_eq iSup_Prop_eq

/- warning: infi_Prop_eq -> iInf_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (iInf.{0, u1} Prop (CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)) ι (fun (i : ι) => p i)) (forall (i : ι), p i)
but is expected to have type
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (iInf.{0, u1} Prop (CompleteLattice.toInfSet.{0} Prop Prop.completeLattice) ι (fun (i : ι) => p i)) (forall (i : ι), p i)
Case conversion may be inaccurate. Consider using '#align infi_Prop_eq iInf_Prop_eqₓ'. -/
@[simp]
theorem iInf_Prop_eq {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h p ⟨i, Eq⟩ => Eq ▸ h i
#align infi_Prop_eq iInf_Prop_eq

#print Pi.supSet /-
instance Pi.supSet {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Sup Pi.supSet
-/

#print Pi.infSet /-
instance Pi.infSet {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] : InfSet (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Inf Pi.infSet
-/

#print Pi.completeLattice /-
instance Pi.completeLattice {α : Type _} {β : α → Type _} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) :=
  { Pi.boundedOrder, Pi.lattice with
    sSup := sSup
    sInf := sInf
    le_sup := fun s f hf i => le_iSup (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    inf_le := fun s f hf i => iInf_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    sup_le := fun s f hf i => iSup_le fun g => hf g g.2 i
    le_inf := fun s f hf i => le_iInf fun g => hf g g.2 i }
#align pi.complete_lattice Pi.completeLattice
-/

/- warning: Sup_apply -> sSup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (i : α), SupSet.{u2} (β i)] {s : Set.{max u1 u2} (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (SupSet.sSup.{max u1 u2} (forall (a : α), β a) (Pi.supSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (iSup.{u2, succ (max u1 u2)} (β a) (_inst_1 a) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (fun (f : coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) => (fun (a : Type.{max u1 u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ (max u1 u2), max (succ u1) (succ u2)} a b] => self.0) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (HasLiftT.mk.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (CoeTCₓ.coe.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeBase.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeSubtype.{max (succ u1) (succ u2)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), β a) (Set.{max u1 u2} (forall (a : α), β a)) (Set.hasMem.{max u1 u2} (forall (a : α), β a)) x s))))) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : forall (i : α), SupSet.{u1} (β i)] {s : Set.{max u2 u1} (forall (a : α), β a)} {a : α}, Eq.{succ u1} (β a) (SupSet.sSup.{max u2 u1} (forall (a : α), β a) (Pi.supSet.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (iSup.{u1, max (succ u2) (succ u1)} (β a) (_inst_1 a) (Set.Elem.{max u2 u1} (forall (a : α), β a) s) (fun (f : Set.Elem.{max u2 u1} (forall (a : α), β a) s) => Subtype.val.{succ (max u2 u1)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.mem.{max u2 u1, max u2 u1} (forall (a : α), β a) (Set.{max u2 u1} (forall (a : α), β a)) (Set.instMembershipSet.{max u2 u1} (forall (a : α), β a)) x s) f a))
Case conversion may be inaccurate. Consider using '#align Sup_apply sSup_applyₓ'. -/
theorem sSup_apply {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sSup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl
#align Sup_apply sSup_apply

/- warning: Inf_apply -> sInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (i : α), InfSet.{u2} (β i)] {s : Set.{max u1 u2} (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (InfSet.sInf.{max u1 u2} (forall (a : α), β a) (Pi.infSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (iInf.{u2, succ (max u1 u2)} (β a) (_inst_1 a) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (fun (f : coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) => (fun (a : Type.{max u1 u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ (max u1 u2), max (succ u1) (succ u2)} a b] => self.0) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (HasLiftT.mk.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (CoeTCₓ.coe.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeBase.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeSubtype.{max (succ u1) (succ u2)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), β a) (Set.{max u1 u2} (forall (a : α), β a)) (Set.hasMem.{max u1 u2} (forall (a : α), β a)) x s))))) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : forall (i : α), InfSet.{u1} (β i)] {s : Set.{max u2 u1} (forall (a : α), β a)} {a : α}, Eq.{succ u1} (β a) (InfSet.sInf.{max u2 u1} (forall (a : α), β a) (Pi.infSet.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (iInf.{u1, max (succ u2) (succ u1)} (β a) (_inst_1 a) (Set.Elem.{max u2 u1} (forall (a : α), β a) s) (fun (f : Set.Elem.{max u2 u1} (forall (a : α), β a) s) => Subtype.val.{succ (max u2 u1)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.mem.{max u2 u1, max u2 u1} (forall (a : α), β a) (Set.{max u2 u1} (forall (a : α), β a)) (Set.instMembershipSet.{max u2 u1} (forall (a : α), β a)) x s) f a))
Case conversion may be inaccurate. Consider using '#align Inf_apply sInf_applyₓ'. -/
theorem sInf_apply {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    sInf s a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl
#align Inf_apply sInf_apply

/- warning: supr_apply -> iSup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {ι : Sort.{u3}} [_inst_1 : forall (i : α), SupSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (iSup.{max u1 u2, u3} (forall (a : α), β a) (Pi.supSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (iSup.{u2, u3} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {ι : Sort.{u1}} [_inst_1 : forall (i : α), SupSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (iSup.{max u3 u2, u1} (forall (a : α), β a) (Pi.supSet.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (iSup.{u2, u1} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
Case conversion may be inaccurate. Consider using '#align supr_apply iSup_applyₓ'. -/
@[simp]
theorem iSup_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [iSup, sSup_apply, iSup, iSup, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]
#align supr_apply iSup_apply

/- warning: infi_apply -> iInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {ι : Sort.{u3}} [_inst_1 : forall (i : α), InfSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (iInf.{max u1 u2, u3} (forall (a : α), β a) (Pi.infSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (iInf.{u2, u3} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {ι : Sort.{u1}} [_inst_1 : forall (i : α), InfSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (iInf.{max u3 u2, u1} (forall (a : α), β a) (Pi.infSet.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (iInf.{u2, u1} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
Case conversion may be inaccurate. Consider using '#align infi_apply iInf_applyₓ'. -/
@[simp]
theorem iInf_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, InfSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
  @iSup_apply α (fun i => (β i)ᵒᵈ) _ _ _ _
#align infi_apply iInf_apply

/- warning: unary_relation_Sup_iff -> unary_relation_sSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (SupSet.sSup.{u1} (α -> Prop) (Pi.supSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice))) s a) (Exists.{succ u1} (α -> Prop) (fun (r : α -> Prop) => And (Membership.Mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.hasMem.{u1} (α -> Prop)) r s) (r a)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (SupSet.sSup.{u1} (α -> Prop) (Pi.supSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toSupSet.{0} Prop Prop.completeLattice)) s a) (Exists.{succ u1} (α -> Prop) (fun (r : α -> Prop) => And (Membership.mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.instMembershipSet.{u1} (α -> Prop)) r s) (r a)))
Case conversion may be inaccurate. Consider using '#align unary_relation_Sup_iff unary_relation_sSup_iffₓ'. -/
theorem unary_relation_sSup_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    sSup s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a :=
  by
  unfold Sup
  simp [← eq_iff_iff]
#align unary_relation_Sup_iff unary_relation_sSup_iff

/- warning: unary_relation_Inf_iff -> unary_relation_sInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (InfSet.sInf.{u1} (α -> Prop) (Pi.infSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice))) s a) (forall (r : α -> Prop), (Membership.Mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.hasMem.{u1} (α -> Prop)) r s) -> (r a))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (InfSet.sInf.{u1} (α -> Prop) (Pi.infSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toInfSet.{0} Prop Prop.completeLattice)) s a) (forall (r : α -> Prop), (Membership.mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.instMembershipSet.{u1} (α -> Prop)) r s) -> (r a))
Case conversion may be inaccurate. Consider using '#align unary_relation_Inf_iff unary_relation_sInf_iffₓ'. -/
theorem unary_relation_sInf_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    sInf s a ↔ ∀ r : α → Prop, r ∈ s → r a :=
  by
  unfold Inf
  simp [← eq_iff_iff]
#align unary_relation_Inf_iff unary_relation_sInf_iff

/- warning: binary_relation_Sup_iff -> binary_relation_sSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{max u1 u2} (α -> β -> Prop)) {a : α} {b : β}, Iff (SupSet.sSup.{max u1 u2} (α -> β -> Prop) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.supSet.{u2, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)))) s a b) (Exists.{max (succ u1) (succ u2)} (α -> β -> Prop) (fun (r : α -> β -> Prop) => And (Membership.Mem.{max u1 u2, max u1 u2} (α -> β -> Prop) (Set.{max u1 u2} (α -> β -> Prop)) (Set.hasMem.{max u1 u2} (α -> β -> Prop)) r s) (r a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{max u2 u1} (α -> β -> Prop)) {a : α} {b : β}, Iff (SupSet.sSup.{max u2 u1} (α -> β -> Prop) (Pi.supSet.{u2, u1} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.supSet.{u1, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteLattice.toSupSet.{0} Prop Prop.completeLattice))) s a b) (Exists.{max (succ u2) (succ u1)} (α -> β -> Prop) (fun (r : α -> β -> Prop) => And (Membership.mem.{max u2 u1, max u2 u1} (α -> β -> Prop) (Set.{max u2 u1} (α -> β -> Prop)) (Set.instMembershipSet.{max u2 u1} (α -> β -> Prop)) r s) (r a b)))
Case conversion may be inaccurate. Consider using '#align binary_relation_Sup_iff binary_relation_sSup_iffₓ'. -/
theorem binary_relation_sSup_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sSup s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b :=
  by
  unfold Sup
  simp [← eq_iff_iff]
#align binary_relation_Sup_iff binary_relation_sSup_iff

/- warning: binary_relation_Inf_iff -> binary_relation_sInf_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{max u1 u2} (α -> β -> Prop)) {a : α} {b : β}, Iff (InfSet.sInf.{max u1 u2} (α -> β -> Prop) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.infSet.{u2, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)))) s a b) (forall (r : α -> β -> Prop), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β -> Prop) (Set.{max u1 u2} (α -> β -> Prop)) (Set.hasMem.{max u1 u2} (α -> β -> Prop)) r s) -> (r a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{max u2 u1} (α -> β -> Prop)) {a : α} {b : β}, Iff (InfSet.sInf.{max u2 u1} (α -> β -> Prop) (Pi.infSet.{u2, u1} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.infSet.{u1, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteLattice.toInfSet.{0} Prop Prop.completeLattice))) s a b) (forall (r : α -> β -> Prop), (Membership.mem.{max u2 u1, max u2 u1} (α -> β -> Prop) (Set.{max u2 u1} (α -> β -> Prop)) (Set.instMembershipSet.{max u2 u1} (α -> β -> Prop)) r s) -> (r a b))
Case conversion may be inaccurate. Consider using '#align binary_relation_Inf_iff binary_relation_sInf_iffₓ'. -/
theorem binary_relation_sInf_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sInf s a b ↔ ∀ r : α → β → Prop, r ∈ s → r a b :=
  by
  unfold Inf
  simp [← eq_iff_iff]
#align binary_relation_Inf_iff binary_relation_sInf_iff

section CompleteLattice

variable [Preorder α] [CompleteLattice β]

/- warning: monotone_Sup_of_monotone -> monotone_sSup_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{max u1 u2} (α -> β)}, (forall (f : α -> β), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f)) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (SupSet.sSup.{max u1 u2} (α -> β) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {s : Set.{max u2 u1} (α -> β)}, (forall (f : α -> β), (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) f)) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) (SupSet.sSup.{max u1 u2} (α -> β) (Pi.supSet.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toSupSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align monotone_Sup_of_monotone monotone_sSup_of_monotoneₓ'. -/
theorem monotone_sSup_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (sSup s) := fun x y h => iSup_mono fun f => m_s f f.2 h
#align monotone_Sup_of_monotone monotone_sSup_of_monotone

/- warning: monotone_Inf_of_monotone -> monotone_sInf_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{max u1 u2} (α -> β)}, (forall (f : α -> β), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f)) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (InfSet.sInf.{max u1 u2} (α -> β) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {s : Set.{max u2 u1} (α -> β)}, (forall (f : α -> β), (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) f)) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) (InfSet.sInf.{max u1 u2} (α -> β) (Pi.infSet.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toInfSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align monotone_Inf_of_monotone monotone_sInf_of_monotoneₓ'. -/
theorem monotone_sInf_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (sInf s) := fun x y h => iInf_mono fun f => m_s f f.2 h
#align monotone_Inf_of_monotone monotone_sInf_of_monotone

end CompleteLattice

namespace Prod

variable (α β)

instance [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

instance [InfSet α] [InfSet β] : InfSet (α × β) :=
  ⟨fun s => (sInf (Prod.fst '' s), sInf (Prod.snd '' s))⟩

variable {α β}

/- warning: prod.fst_Inf -> Prod.fst_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (InfSet.sInf.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) s)) (InfSet.sInf.{u1} α _inst_1 (Set.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (InfSet.sInf.{max u2 u1} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) s)) (InfSet.sInf.{u2} α _inst_1 (Set.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.fst_Inf Prod.fst_sInfₓ'. -/
theorem fst_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).fst = sInf (Prod.fst '' s) :=
  rfl
#align prod.fst_Inf Prod.fst_sInf

/- warning: prod.snd_Inf -> Prod.snd_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (InfSet.sInf.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) s)) (InfSet.sInf.{u2} β _inst_2 (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (InfSet.sInf.{max u2 u1} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) s)) (InfSet.sInf.{u1} β _inst_2 (Set.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.snd_Inf Prod.snd_sInfₓ'. -/
theorem snd_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).snd = sInf (Prod.snd '' s) :=
  rfl
#align prod.snd_Inf Prod.snd_sInf

/- warning: prod.swap_Inf -> Prod.swap_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (InfSet.sInf.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) s)) (InfSet.sInf.{max u2 u1} (Prod.{u2, u1} β α) (Prod.hasInf.{u2, u1} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β (InfSet.sInf.{max u2 u1} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) s)) (InfSet.sInf.{max u1 u2} (Prod.{u1, u2} β α) (Prod.infSet.{u1, u2} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.swap_Inf Prod.swap_sInfₓ'. -/
theorem swap_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).symm = sInf (Prod.swap '' s) :=
  ext (congr_arg sInf <| image_comp Prod.fst swap s : _)
    (congr_arg sInf <| image_comp Prod.snd swap s : _)
#align prod.swap_Inf Prod.swap_sInf

/- warning: prod.fst_Sup -> Prod.fst_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (SupSet.sSup.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) s)) (SupSet.sSup.{u1} α _inst_1 (Set.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (SupSet.sSup.{max u2 u1} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) s)) (SupSet.sSup.{u2} α _inst_1 (Set.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.fst_Sup Prod.fst_sSupₓ'. -/
theorem fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Prod.fst '' s) :=
  rfl
#align prod.fst_Sup Prod.fst_sSup

/- warning: prod.snd_Sup -> Prod.snd_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (SupSet.sSup.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) s)) (SupSet.sSup.{u2} β _inst_2 (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (SupSet.sSup.{max u2 u1} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) s)) (SupSet.sSup.{u1} β _inst_2 (Set.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.snd_Sup Prod.snd_sSupₓ'. -/
theorem snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Prod.snd '' s) :=
  rfl
#align prod.snd_Sup Prod.snd_sSup

/- warning: prod.swap_Sup -> Prod.swap_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (SupSet.sSup.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) s)) (SupSet.sSup.{max u2 u1} (Prod.{u2, u1} β α) (Prod.hasSup.{u2, u1} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β (SupSet.sSup.{max u2 u1} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) s)) (SupSet.sSup.{max u1 u2} (Prod.{u1, u2} β α) (Prod.supSet.{u1, u2} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.swap_Sup Prod.swap_sSupₓ'. -/
theorem swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).symm = sSup (Prod.swap '' s) :=
  ext (congr_arg sSup <| image_comp Prod.fst swap s : _)
    (congr_arg sSup <| image_comp Prod.snd swap s : _)
#align prod.swap_Sup Prod.swap_sSup

/- warning: prod.fst_infi -> Prod.fst_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (iInf.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι f)) (iInf.{u1, u3} α _inst_1 ι (fun (i : ι) => Prod.fst.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u3} α (Prod.fst.{u3, u2} α β (iInf.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (iInf.{u3, u1} α _inst_1 ι (fun (i : ι) => Prod.fst.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.fst_infi Prod.fst_iInfₓ'. -/
theorem fst_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).fst = ⨅ i, (f i).fst :=
  congr_arg sInf (range_comp _ _).symm
#align prod.fst_infi Prod.fst_iInf

/- warning: prod.snd_infi -> Prod.snd_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (iInf.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι f)) (iInf.{u2, u3} β _inst_2 ι (fun (i : ι) => Prod.snd.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u2} β (Prod.snd.{u3, u2} α β (iInf.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (iInf.{u2, u1} β _inst_2 ι (fun (i : ι) => Prod.snd.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.snd_infi Prod.snd_iInfₓ'. -/
theorem snd_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).snd = ⨅ i, (f i).snd :=
  congr_arg sInf (range_comp _ _).symm
#align prod.snd_infi Prod.snd_iInf

/- warning: prod.swap_infi -> Prod.swap_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (iInf.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι f)) (iInf.{max u2 u1, u3} (Prod.{u2, u1} β α) (Prod.hasInf.{u2, u1} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{max (succ u3) (succ u2)} (Prod.{u2, u3} β α) (Prod.swap.{u3, u2} α β (iInf.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (iInf.{max u3 u2, u1} (Prod.{u2, u3} β α) (Prod.infSet.{u2, u3} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.swap_infi Prod.swap_iInfₓ'. -/
theorem swap_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).symm = ⨅ i, (f i).symm := by
  simp_rw [iInf, swap_Inf, range_comp]
#align prod.swap_infi Prod.swap_iInf

/- warning: prod.infi_mk -> Prod.iInf_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (iInf.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u1, u2} α β (f i) (g i))) (Prod.mk.{u1, u2} α β (iInf.{u1, u3} α _inst_1 ι (fun (i : ι) => f i)) (iInf.{u2, u3} β _inst_2 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (iInf.{max u2 u3, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u3, u2} α β (f i) (g i))) (Prod.mk.{u3, u2} α β (iInf.{u3, u1} α _inst_1 ι (fun (i : ι) => f i)) (iInf.{u2, u1} β _inst_2 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align prod.infi_mk Prod.iInf_mkₓ'. -/
theorem iInf_mk [InfSet α] [InfSet β] (f : ι → α) (g : ι → β) :
    (⨅ i, (f i, g i)) = (⨅ i, f i, ⨅ i, g i) :=
  congr_arg₂ Prod.mk (fst_iInf _) (snd_iInf _)
#align prod.infi_mk Prod.iInf_mk

/- warning: prod.fst_supr -> Prod.fst_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (iSup.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι f)) (iSup.{u1, u3} α _inst_1 ι (fun (i : ι) => Prod.fst.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u3} α (Prod.fst.{u3, u2} α β (iSup.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (iSup.{u3, u1} α _inst_1 ι (fun (i : ι) => Prod.fst.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.fst_supr Prod.fst_iSupₓ'. -/
theorem fst_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  congr_arg sSup (range_comp _ _).symm
#align prod.fst_supr Prod.fst_iSup

/- warning: prod.snd_supr -> Prod.snd_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (iSup.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι f)) (iSup.{u2, u3} β _inst_2 ι (fun (i : ι) => Prod.snd.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u2} β (Prod.snd.{u3, u2} α β (iSup.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (iSup.{u2, u1} β _inst_2 ι (fun (i : ι) => Prod.snd.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.snd_supr Prod.snd_iSupₓ'. -/
theorem snd_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  congr_arg sSup (range_comp _ _).symm
#align prod.snd_supr Prod.snd_iSup

/- warning: prod.swap_supr -> Prod.swap_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (iSup.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι f)) (iSup.{max u2 u1, u3} (Prod.{u2, u1} β α) (Prod.hasSup.{u2, u1} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{max (succ u3) (succ u2)} (Prod.{u2, u3} β α) (Prod.swap.{u3, u2} α β (iSup.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (iSup.{max u3 u2, u1} (Prod.{u2, u3} β α) (Prod.supSet.{u2, u3} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.swap_supr Prod.swap_iSupₓ'. -/
theorem swap_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).symm = ⨆ i, (f i).symm := by
  simp_rw [iSup, swap_Sup, range_comp]
#align prod.swap_supr Prod.swap_iSup

/- warning: prod.supr_mk -> Prod.iSup_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (iSup.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u1, u2} α β (f i) (g i))) (Prod.mk.{u1, u2} α β (iSup.{u1, u3} α _inst_1 ι (fun (i : ι) => f i)) (iSup.{u2, u3} β _inst_2 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (iSup.{max u2 u3, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u3, u2} α β (f i) (g i))) (Prod.mk.{u3, u2} α β (iSup.{u3, u1} α _inst_1 ι (fun (i : ι) => f i)) (iSup.{u2, u1} β _inst_2 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align prod.supr_mk Prod.iSup_mkₓ'. -/
theorem iSup_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    (⨆ i, (f i, g i)) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)
#align prod.supr_mk Prod.iSup_mk

variable (α β)

instance [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.hasSup α β,
    Prod.hasInf α
      β with
    le_sup := fun s p hab => ⟨le_sSup <| mem_image_of_mem _ hab, le_sSup <| mem_image_of_mem _ hab⟩
    sup_le := fun s p h =>
      ⟨sSup_le <| ball_image_of_ball fun p hp => (h p hp).1,
        sSup_le <| ball_image_of_ball fun p hp => (h p hp).2⟩
    inf_le := fun s p hab => ⟨sInf_le <| mem_image_of_mem _ hab, sInf_le <| mem_image_of_mem _ hab⟩
    le_inf := fun s p h =>
      ⟨le_sInf <| ball_image_of_ball fun p hp => (h p hp).1,
        le_sInf <| ball_image_of_ball fun p hp => (h p hp).2⟩ }

end Prod

/- warning: Inf_prod -> sInf_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (InfSet.sInf.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Prod.mk.{u1, u2} α β (InfSet.sInf.{u1} α _inst_1 s) (InfSet.sInf.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β t) -> (Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (InfSet.sInf.{max u1 u2} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) (Set.prod.{u2, u1} α β s t)) (Prod.mk.{u2, u1} α β (InfSet.sInf.{u2} α _inst_1 s) (InfSet.sInf.{u1} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align Inf_prod sInf_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sInf_prod [InfSet α] [InfSet β] {s : Set α} {t : Set β} (hs : s.Nonempty)
    (ht : t.Nonempty) : sInf (s ×ˢ t) = (sInf s, sInf t) :=
  congr_arg₂ Prod.mk (congr_arg sInf <| fst_image_prod _ ht) (congr_arg sInf <| snd_image_prod hs _)
#align Inf_prod sInf_prod

/- warning: Sup_prod -> sSup_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (SupSet.sSup.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Prod.mk.{u1, u2} α β (SupSet.sSup.{u1} α _inst_1 s) (SupSet.sSup.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β t) -> (Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (SupSet.sSup.{max u1 u2} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) (Set.prod.{u2, u1} α β s t)) (Prod.mk.{u2, u1} α β (SupSet.sSup.{u2} α _inst_1 s) (SupSet.sSup.{u1} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align Sup_prod sSup_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty)
    (ht : t.Nonempty) : sSup (s ×ˢ t) = (sSup s, sSup t) :=
  congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)
#align Sup_prod sSup_prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/- warning: sup_Inf_le_infi_sup -> sup_sInf_le_iInf_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (b : α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (iInf.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (b : α) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align sup_Inf_le_infi_sup sup_sInf_le_iInf_supₓ'. -/
/-- This is a weaker version of `sup_Inf_eq` -/
theorem sup_sInf_le_iInf_sup : a ⊔ sInf s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_iInf₂ fun i h => sup_le_sup_left (sInf_le h) _
#align sup_Inf_le_infi_sup sup_sInf_le_iInf_sup

/- warning: supr_inf_le_inf_Sup -> iSup_inf_le_inf_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (b : α) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a b))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align supr_inf_le_inf_Sup iSup_inf_le_inf_sSupₓ'. -/
/-- This is a weaker version of `inf_Sup_eq` -/
theorem iSup_inf_le_inf_sSup : (⨆ b ∈ s, a ⊓ b) ≤ a ⊓ sSup s :=
  @sup_sInf_le_iInf_sup αᵒᵈ _ _ _
#align supr_inf_le_inf_Sup iSup_inf_le_inf_sSup

/- warning: Inf_sup_le_infi_sup -> sInf_sup_le_iInf_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) a) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (b : α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) a) (iInf.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (b : α) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) b a)))
Case conversion may be inaccurate. Consider using '#align Inf_sup_le_infi_sup sInf_sup_le_iInf_supₓ'. -/
/-- This is a weaker version of `Inf_sup_eq` -/
theorem sInf_sup_le_iInf_sup : sInf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_iInf₂ fun i h => sup_le_sup_right (sInf_le h) _
#align Inf_sup_le_infi_sup sInf_sup_le_iInf_sup

/- warning: supr_inf_le_Sup_inf -> iSup_inf_le_sSup_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) b a))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (b : α) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) b a))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align supr_inf_le_Sup_inf iSup_inf_le_sSup_infₓ'. -/
/-- This is a weaker version of `Sup_inf_eq` -/
theorem iSup_inf_le_sSup_inf : (⨆ b ∈ s, b ⊓ a) ≤ sSup s ⊓ a :=
  @sInf_sup_le_iInf_sup αᵒᵈ _ _ _
#align supr_inf_le_Sup_inf iSup_inf_le_sSup_inf

/- warning: le_supr_inf_supr -> le_iSup_inf_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (g : ι -> α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i) (g i))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i)) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (g : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f i) (g i))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) (iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align le_supr_inf_supr le_iSup_inf_iSupₓ'. -/
theorem le_iSup_inf_iSup (f g : ι → α) : (⨆ i, f i ⊓ g i) ≤ (⨆ i, f i) ⊓ ⨆ i, g i :=
  le_inf (iSup_mono fun i => inf_le_left) (iSup_mono fun i => inf_le_right)
#align le_supr_inf_supr le_iSup_inf_iSup

/- warning: infi_sup_infi_le -> iInf_sup_iInf_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (g : ι -> α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => g i))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i) (g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (g : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => g i))) (iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f i) (g i)))
Case conversion may be inaccurate. Consider using '#align infi_sup_infi_le iInf_sup_iInf_leₓ'. -/
theorem iInf_sup_iInf_le (f g : ι → α) : ((⨅ i, f i) ⊔ ⨅ i, g i) ≤ ⨅ i, f i ⊔ g i :=
  @le_iSup_inf_iSup αᵒᵈ ι _ f g
#align infi_sup_infi_le iInf_sup_iInf_le

/- warning: disjoint_Sup_left -> disjoint_sSup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) a) b) -> (forall {i : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) i b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) a) b) -> (forall {i : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) i b))
Case conversion may be inaccurate. Consider using '#align disjoint_Sup_left disjoint_sSup_leftₓ'. -/
theorem disjoint_sSup_left {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi : _)
#align disjoint_Sup_left disjoint_sSup_left

/- warning: disjoint_Sup_right -> disjoint_sSup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) a)) -> (forall {i : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) a)) -> (forall {i : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b i))
Case conversion may be inaccurate. Consider using '#align disjoint_Sup_right disjoint_sSup_rightₓ'. -/
theorem disjoint_sSup_right {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi : _)
#align disjoint_Sup_right disjoint_sSup_right

end CompleteLattice

/- warning: function.injective.complete_lattice -> Function.Injective.completeLattice is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_7)) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_7)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_7)) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_7)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β _inst_7))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_7))) -> (CompleteLattice.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (Lattice.toInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7)) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_7) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_7) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_7) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_7) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β _inst_7))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β _inst_7))) -> (CompleteLattice.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.complete_lattice Function.Injective.completeLatticeₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `complete_lattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeLattice [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_Sup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α :=
  {-- we cannot use bounded_order.lift here as the `has_le` instance doesn't exist yet
        hf.Lattice
      f map_sup map_inf with
    sSup := sSup
    le_sup := fun s a h => (le_iSup₂ a h).trans (map_Sup _).ge
    sup_le := fun s a h => (map_Sup _).trans_le <| iSup₂_le h
    sInf := sInf
    inf_le := fun s a h => (map_Inf _).trans_le <| iInf₂_le a h
    le_inf := fun s a h => (le_iInf₂ h).trans (map_Inf _).ge
    top := ⊤
    le_top := fun a => (@le_top β _ _ _).trans map_top.ge
    bot := ⊥
    bot_le := fun a => map_bot.le.trans bot_le }
#align function.injective.complete_lattice Function.Injective.completeLattice

