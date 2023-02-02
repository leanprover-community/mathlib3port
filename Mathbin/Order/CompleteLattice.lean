/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.complete_lattice
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
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
  supₛ : Set α → α
#align has_Sup SupSet
-/

#print InfSet /-
/-- class for the `Inf` operator -/
class InfSet (α : Type _) where
  infₛ : Set α → α
#align has_Inf InfSet
-/

export SupSet (supₛ)

export InfSet (infₛ)

/-- Supremum of a set -/
add_decl_doc SupSet.supₛ

/-- Infimum of a set -/
add_decl_doc InfSet.infₛ

#print supᵢ /-
/-- Indexed supremum -/
def supᵢ [SupSet α] {ι} (s : ι → α) : α :=
  supₛ (range s)
#align supr supᵢ
-/

#print infᵢ /-
/-- Indexed infimum -/
def infᵢ [InfSet α] {ι} (s : ι → α) : α :=
  infₛ (range s)
#align infi infᵢ
-/

#print infSet_to_nonempty /-
instance (priority := 50) infSet_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨infₛ ∅⟩
#align has_Inf_to_nonempty infSet_to_nonempty
-/

#print supSet_to_nonempty /-
instance (priority := 50) supSet_to_nonempty (α) [SupSet α] : Nonempty α :=
  ⟨supₛ ∅⟩
#align has_Sup_to_nonempty supSet_to_nonempty
-/

-- mathport name: «expr⨆ , »
notation3"⨆ "(...)", "r:(scoped f => supᵢ f) => r

-- mathport name: «expr⨅ , »
notation3"⨅ "(...)", "r:(scoped f => infᵢ f) => r

instance (α) [InfSet α] : SupSet αᵒᵈ :=
  ⟨(infₛ : Set α → α)⟩

instance (α) [SupSet α] : InfSet αᵒᵈ :=
  ⟨(supₛ : Set α → α)⟩

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

/- warning: le_Sup -> le_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Sup le_supₛₓ'. -/
@[ematch]
theorem le_supₛ : a ∈ s → a ≤ supₛ s :=
  CompleteSemilatticeSup.le_sup s a
#align le_Sup le_supₛ

/- warning: Sup_le -> supₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Sup_le supₛ_leₓ'. -/
theorem supₛ_le : (∀ b ∈ s, b ≤ a) → supₛ s ≤ a :=
  CompleteSemilatticeSup.sup_le s a
#align Sup_le supₛ_le

/- warning: is_lub_Sup -> isLUB_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] (s : Set.{u1} α), IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] (s : Set.{u1} α), IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align is_lub_Sup isLUB_supₛₓ'. -/
theorem isLUB_supₛ (s : Set α) : IsLUB s (supₛ s) :=
  ⟨fun x => le_supₛ, fun x => supₛ_le⟩
#align is_lub_Sup isLUB_supₛ

/- warning: is_lub.Sup_eq -> IsLUB.supₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_lub.Sup_eq IsLUB.supₛ_eqₓ'. -/
theorem IsLUB.supₛ_eq (h : IsLUB s a) : supₛ s = a :=
  (isLUB_supₛ s).unique h
#align is_lub.Sup_eq IsLUB.supₛ_eq

/- warning: le_Sup_of_le -> le_supₛ_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Sup_of_le le_supₛ_of_leₓ'. -/
theorem le_supₛ_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ supₛ s :=
  le_trans h (le_supₛ hb)
#align le_Sup_of_le le_supₛ_of_le

/- warning: Sup_le_Sup -> supₛ_le_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_le_Sup supₛ_le_supₛₓ'. -/
theorem supₛ_le_supₛ (h : s ⊆ t) : supₛ s ≤ supₛ t :=
  (isLUB_supₛ s).mono (isLUB_supₛ t) h
#align Sup_le_Sup supₛ_le_supₛ

/- warning: Sup_le_iff -> supₛ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align Sup_le_iff supₛ_le_iffₓ'. -/
@[simp]
theorem supₛ_le_iff : supₛ s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_supₛ s)
#align Sup_le_iff supₛ_le_iff

/- warning: le_Sup_iff -> le_supₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align le_Sup_iff le_supₛ_iffₓ'. -/
theorem le_supₛ_iff : a ≤ supₛ s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h b hb => le_trans h (supₛ_le hb), fun hb => hb _ fun x => le_supₛ⟩
#align le_Sup_iff le_supₛ_iff

/- warning: le_supr_iff -> le_supᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {a : α} {s : ι -> α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (s i) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteSemilatticeSup.{u2} α] {a : α} {s : ι -> α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeSup.toPartialOrder.{u2} α _inst_1))) a (supᵢ.{u2, u1} α (CompleteSemilatticeSup.toSupSet.{u2} α _inst_1) ι s)) (forall (b : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeSup.toPartialOrder.{u2} α _inst_1))) (s i) b) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeSup.toPartialOrder.{u2} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align le_supr_iff le_supᵢ_iffₓ'. -/
theorem le_supᵢ_iff {s : ι → α} : a ≤ supᵢ s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [supᵢ, le_supₛ_iff, upperBounds]
#align le_supr_iff le_supᵢ_iff

/- warning: Sup_le_Sup_of_forall_exists_le -> supₛ_le_supₛ_of_forall_exists_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) x y)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) x y)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeSup.toPartialOrder.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_le_Sup_of_forall_exists_le supₛ_le_supₛ_of_forall_exists_leₓ'. -/
theorem supₛ_le_supₛ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : supₛ s ≤ supₛ t :=
  le_supₛ_iff.2 fun b hb =>
    supₛ_le fun a ha =>
      let ⟨c, hct, hac⟩ := h a ha
      hac.trans (hb hct)
#align Sup_le_Sup_of_forall_exists_le supₛ_le_supₛ_of_forall_exists_le

/- warning: Sup_singleton -> supₛ_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeSup.{u1} α] {a : α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toSupSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align Sup_singleton supₛ_singletonₓ'. -/
-- We will generalize this to conditionally complete lattices in `cSup_singleton`.
theorem supₛ_singleton {a : α} : supₛ {a} = a :=
  isLUB_singleton.supₛ_eq
#align Sup_singleton supₛ_singleton

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

/- warning: Inf_le -> infₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Inf_le infₛ_leₓ'. -/
@[ematch]
theorem infₛ_le : a ∈ s → infₛ s ≤ a :=
  CompleteSemilatticeInf.inf_le s a
#align Inf_le infₛ_le

/- warning: le_Inf -> le_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align le_Inf le_infₛₓ'. -/
theorem le_infₛ : (∀ b ∈ s, a ≤ b) → a ≤ infₛ s :=
  CompleteSemilatticeInf.le_inf s a
#align le_Inf le_infₛ

/- warning: is_glb_Inf -> isGLB_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] (s : Set.{u1} α), IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] (s : Set.{u1} α), IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align is_glb_Inf isGLB_infₛₓ'. -/
theorem isGLB_infₛ (s : Set α) : IsGLB s (infₛ s) :=
  ⟨fun a => infₛ_le, fun a => le_infₛ⟩
#align is_glb_Inf isGLB_infₛ

/- warning: is_glb.Inf_eq -> IsGLB.infₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s a) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align is_glb.Inf_eq IsGLB.infₛ_eqₓ'. -/
theorem IsGLB.infₛ_eq (h : IsGLB s a) : infₛ s = a :=
  (isGLB_infₛ s).unique h
#align is_glb.Inf_eq IsGLB.infₛ_eq

/- warning: Inf_le_of_le -> infₛ_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α} {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align Inf_le_of_le infₛ_le_of_leₓ'. -/
theorem infₛ_le_of_le (hb : b ∈ s) (h : b ≤ a) : infₛ s ≤ a :=
  le_trans (infₛ_le hb) h
#align Inf_le_of_le infₛ_le_of_le

/- warning: Inf_le_Inf -> infₛ_le_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Inf infₛ_le_infₛₓ'. -/
theorem infₛ_le_infₛ (h : s ⊆ t) : infₛ t ≤ infₛ s :=
  (isGLB_infₛ s).mono (isGLB_infₛ t) h
#align Inf_le_Inf infₛ_le_infₛ

/- warning: le_Inf_iff -> le_infₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align le_Inf_iff le_infₛ_iffₓ'. -/
@[simp]
theorem le_infₛ_iff : a ≤ infₛ s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_infₛ s)
#align le_Inf_iff le_infₛ_iff

/- warning: Inf_le_iff -> infₛ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1)) s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align Inf_le_iff infₛ_le_iffₓ'. -/
theorem infₛ_le_iff : infₛ s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h b hb => le_trans (le_infₛ hb) h, fun hb => hb _ fun x => infₛ_le⟩
#align Inf_le_iff infₛ_le_iff

/- warning: infi_le_iff -> infᵢ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {a : α} {s : ι -> α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) ι s) a) (forall (b : α), (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b (s i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteSemilatticeInf.{u2} α] {a : α} {s : ι -> α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α _inst_1))) (infᵢ.{u2, u1} α (CompleteSemilatticeInf.toInfSet.{u2} α _inst_1) ι s) a) (forall (b : α), (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α _inst_1))) b (s i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align infi_le_iff infᵢ_le_iffₓ'. -/
theorem infᵢ_le_iff {s : ι → α} : infᵢ s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [infᵢ, infₛ_le_iff, lowerBounds]
#align infi_le_iff infᵢ_le_iff

/- warning: Inf_le_Inf_of_forall_exists_le -> infₛ_le_infₛ_of_forall_exists_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) y x)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) y x)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Inf_of_forall_exists_le infₛ_le_infₛ_of_forall_exists_leₓ'. -/
theorem infₛ_le_infₛ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : infₛ t ≤ infₛ s :=
  le_of_forall_le
    (by
      simp only [le_infₛ_iff]
      introv h₀ h₁
      rcases h _ h₁ with ⟨y, hy, hy'⟩
      solve_by_elim [le_trans _ hy'] )
#align Inf_le_Inf_of_forall_exists_le infₛ_le_infₛ_of_forall_exists_le

/- warning: Inf_singleton -> infₛ_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteSemilatticeInf.{u1} α] {a : α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toInfSet.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) a
Case conversion may be inaccurate. Consider using '#align Inf_singleton infₛ_singletonₓ'. -/
-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem infₛ_singleton {a : α} : infₛ {a} = a :=
  isGLB_singleton.infₛ_eq
#align Inf_singleton infₛ_singleton

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

#print CompleteLattice.toBoundedOrder /-
-- see Note [lower instance priority]
instance (priority := 100) CompleteLattice.toBoundedOrder [h : CompleteLattice α] :
    BoundedOrder α :=
  { h with }
#align complete_lattice.to_bounded_order CompleteLattice.toBoundedOrder
-/

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
    (is_glb_Inf : ∀ s : Set α, IsGLB s (infₛ s)) : CompleteLattice α :=
  { H1, H2 with
    bot := infₛ univ
    bot_le := fun x => (isGLB_infₛ univ).1 trivial
    top := infₛ ∅
    le_top := fun a => (isGLB_infₛ ∅).2 <| by simp
    sup := fun a b => infₛ { x | a ≤ x ∧ b ≤ x }
    inf := fun a b => infₛ {a, b}
    le_inf := fun a b c hab hac => by
      apply (isGLB_infₛ _).2
      simp [*]
    inf_le_right := fun a b => (isGLB_infₛ _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf_le_left := fun a b => (isGLB_infₛ _).1 <| mem_insert _ _
    sup_le := fun a b c hac hbc => (isGLB_infₛ _).1 <| by simp [*]
    le_sup_left := fun a b => (isGLB_infₛ _).2 fun x => And.left
    le_sup_right := fun a b => (isGLB_infₛ _).2 fun x => And.right
    le_inf := fun s a ha => (isGLB_infₛ s).2 ha
    inf_le := fun s a ha => (isGLB_infₛ s).1 ha
    supₛ := fun s => infₛ (upperBounds s)
    le_sup := fun s a ha => (isGLB_infₛ (upperBounds s)).2 fun b hb => hb ha
    sup_le := fun s a ha => (isGLB_infₛ (upperBounds s)).1 ha }
#align complete_lattice_of_Inf completeLatticeOfInf
-/

#print completeLatticeOfCompleteSemilatticeInf /-
/-- Any `complete_semilattice_Inf` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Inf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type _) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_infₛ s
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
    (is_lub_Sup : ∀ s : Set α, IsLUB s (supₛ s)) : CompleteLattice α :=
  { H1, H2 with
    top := supₛ univ
    le_top := fun x => (isLUB_supₛ univ).1 trivial
    bot := supₛ ∅
    bot_le := fun x => (isLUB_supₛ ∅).2 <| by simp
    sup := fun a b => supₛ {a, b}
    sup_le := fun a b c hac hbc => (isLUB_supₛ _).2 (by simp [*])
    le_sup_left := fun a b => (isLUB_supₛ _).1 <| mem_insert _ _
    le_sup_right := fun a b => (isLUB_supₛ _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf := fun a b => supₛ { x | x ≤ a ∧ x ≤ b }
    le_inf := fun a b c hab hac => (isLUB_supₛ _).1 <| by simp [*]
    inf_le_left := fun a b => (isLUB_supₛ _).2 fun x => And.left
    inf_le_right := fun a b => (isLUB_supₛ _).2 fun x => And.right
    infₛ := fun s => supₛ (lowerBounds s)
    sup_le := fun s a ha => (isLUB_supₛ s).2 ha
    le_sup := fun s a ha => (isLUB_supₛ s).1 ha
    inf_le := fun s a ha => (isLUB_supₛ (lowerBounds s)).2 fun b hb => hb ha
    le_inf := fun s a ha => (isLUB_supₛ (lowerBounds s)).1 ha }
#align complete_lattice_of_Sup completeLatticeOfSup
-/

#print completeLatticeOfCompleteSemilatticeSup /-
/-- Any `complete_semilattice_Sup` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Sup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type _) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_supₛ s
#align complete_lattice_of_complete_semilattice_Sup completeLatticeOfCompleteSemilatticeSup
-/

#print CompleteLinearOrder /-
/- ./././Mathport/Syntax/Translate/Command.lean:417:11: unsupported: advanced extends in structure -/
/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type _) extends CompleteLattice α,
  "./././Mathport/Syntax/Translate/Command.lean:417:11: unsupported: advanced extends in structure"
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

#print toDual_supₛ /-
@[simp]
theorem toDual_supₛ (s : Set α) : toDual (supₛ s) = infₛ (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Sup toDual_supₛ
-/

#print toDual_infₛ /-
@[simp]
theorem toDual_infₛ (s : Set α) : toDual (infₛ s) = supₛ (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Inf toDual_infₛ
-/

#print ofDual_supₛ /-
@[simp]
theorem ofDual_supₛ (s : Set αᵒᵈ) : ofDual (supₛ s) = infₛ (toDual ⁻¹' s) :=
  rfl
#align of_dual_Sup ofDual_supₛ
-/

#print ofDual_infₛ /-
@[simp]
theorem ofDual_infₛ (s : Set αᵒᵈ) : ofDual (infₛ s) = supₛ (toDual ⁻¹' s) :=
  rfl
#align of_dual_Inf ofDual_infₛ
-/

/- warning: to_dual_supr -> toDual_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (infᵢ.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (infᵢ.{u2, u1} (OrderDual.{u2} α) (OrderDual.infSet.{u2} α (CompleteLattice.toSupSet.{u2} α _inst_1)) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align to_dual_supr toDual_supᵢₓ'. -/
@[simp]
theorem toDual_supᵢ (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl
#align to_dual_supr toDual_supᵢ

/- warning: to_dual_infi -> toDual_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} (OrderDual.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))) (supᵢ.{u2, u1} (OrderDual.{u2} α) (OrderDual.supSet.{u2} α (CompleteLattice.toInfSet.{u2} α _inst_1)) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => OrderDual.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (OrderDual.{u2} α)) α (OrderDual.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (OrderDual.{u2} α)))) (OrderDual.toDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align to_dual_infi toDual_infᵢₓ'. -/
@[simp]
theorem toDual_infᵢ (f : ι → α) : toDual (⨅ i, f i) = ⨆ i, toDual (f i) :=
  rfl
#align to_dual_infi toDual_infᵢ

/- warning: of_dual_supr -> ofDual_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (supᵢ.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) (supᵢ.{u2, u1} (OrderDual.{u2} α) (OrderDual.supSet.{u2} α (CompleteLattice.toInfSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) (supᵢ.{u2, u1} (OrderDual.{u2} α) (OrderDual.supSet.{u2} α (CompleteLattice.toInfSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align of_dual_supr ofDual_supᵢₓ'. -/
@[simp]
theorem ofDual_supᵢ (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl
#align of_dual_supr ofDual_supᵢ

/- warning: of_dual_infi -> ofDual_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> (OrderDual.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (infᵢ.{u1, u2} (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> (OrderDual.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) (infᵢ.{u2, u1} (OrderDual.{u2} α) (OrderDual.infSet.{u2} α (CompleteLattice.toSupSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) (infᵢ.{u2, u1} (OrderDual.{u2} α) (OrderDual.infSet.{u2} α (CompleteLattice.toSupSet.{u2} α _inst_1)) ι (fun (i : ι) => f i))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) (fun (_x : OrderDual.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : OrderDual.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} α) α) (OrderDual.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (OrderDual.{u2} α) α))) (OrderDual.ofDual.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align of_dual_infi ofDual_infᵢₓ'. -/
@[simp]
theorem ofDual_infᵢ (f : ι → αᵒᵈ) : ofDual (⨅ i, f i) = ⨆ i, ofDual (f i) :=
  rfl
#align of_dual_infi ofDual_infᵢ

/- warning: Inf_le_Sup -> infₛ_le_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Sup infₛ_le_supₛₓ'. -/
theorem infₛ_le_supₛ (hs : s.Nonempty) : infₛ s ≤ supₛ s :=
  isGLB_le_isLUB (isGLB_infₛ s) (isLUB_supₛ s) hs
#align Inf_le_Sup infₛ_le_supₛ

/- warning: Sup_union -> supₛ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_union supₛ_unionₓ'. -/
theorem supₛ_union {s t : Set α} : supₛ (s ∪ t) = supₛ s ⊔ supₛ t :=
  ((isLUB_supₛ s).union (isLUB_supₛ t)).supₛ_eq
#align Sup_union supₛ_union

/- warning: Inf_union -> infₛ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Inf_union infₛ_unionₓ'. -/
theorem infₛ_union {s t : Set α} : infₛ (s ∪ t) = infₛ s ⊓ infₛ t :=
  ((isGLB_infₛ s).union (isGLB_infₛ t)).infₛ_eq
#align Inf_union infₛ_union

/- warning: Sup_inter_le -> supₛ_inter_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_inter_le supₛ_inter_leₓ'. -/
theorem supₛ_inter_le {s t : Set α} : supₛ (s ∩ t) ≤ supₛ s ⊓ supₛ t :=
  supₛ_le fun b hb => le_inf (le_supₛ hb.1) (le_supₛ hb.2)
#align Sup_inter_le supₛ_inter_le

/- warning: le_Inf_inter -> le_infₛ_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) t)) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) t)) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align le_Inf_inter le_infₛ_interₓ'. -/
theorem le_infₛ_inter {s t : Set α} : infₛ s ⊔ infₛ t ≤ infₛ (s ∩ t) :=
  @supₛ_inter_le αᵒᵈ _ _ _
#align le_Inf_inter le_infₛ_inter

/- warning: Sup_empty -> supₛ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_empty supₛ_emptyₓ'. -/
@[simp]
theorem supₛ_empty : supₛ ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).supₛ_eq
#align Sup_empty supₛ_empty

/- warning: Inf_empty -> infₛ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Inf_empty infₛ_emptyₓ'. -/
@[simp]
theorem infₛ_empty : infₛ ∅ = (⊤ : α) :=
  (@isGLB_empty α _ _).infₛ_eq
#align Inf_empty infₛ_empty

/- warning: Sup_univ -> supₛ_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.univ.{u1} α)) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.univ.{u1} α)) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_univ supₛ_univₓ'. -/
@[simp]
theorem supₛ_univ : supₛ univ = (⊤ : α) :=
  (@isLUB_univ α _ _).supₛ_eq
#align Sup_univ supₛ_univ

/- warning: Inf_univ -> infₛ_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Set.univ.{u1} α)) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.univ.{u1} α)) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Inf_univ infₛ_univₓ'. -/
@[simp]
theorem infₛ_univ : infₛ univ = (⊥ : α) :=
  (@isGLB_univ α _ _).infₛ_eq
#align Inf_univ infₛ_univ

/- warning: Sup_insert -> supₛ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Sup_insert supₛ_insertₓ'. -/
-- TODO(Jeremy): get this automatically
@[simp]
theorem supₛ_insert {a : α} {s : Set α} : supₛ (insert a s) = a ⊔ supₛ s :=
  ((isLUB_supₛ s).insert a).supₛ_eq
#align Sup_insert supₛ_insert

/- warning: Inf_insert -> infₛ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_insert infₛ_insertₓ'. -/
@[simp]
theorem infₛ_insert {a : α} {s : Set α} : infₛ (insert a s) = a ⊓ infₛ s :=
  ((isGLB_infₛ s).insert a).infₛ_eq
#align Inf_insert infₛ_insert

/- warning: Sup_le_Sup_of_subset_insert_bot -> supₛ_le_supₛ_of_subset_insert_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align Sup_le_Sup_of_subset_insert_bot supₛ_le_supₛ_of_subset_insert_botₓ'. -/
theorem supₛ_le_supₛ_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : supₛ s ≤ supₛ t :=
  le_trans (supₛ_le_supₛ h) (le_of_eq (trans supₛ_insert bot_sup_eq))
#align Sup_le_Sup_of_subset_insert_bot supₛ_le_supₛ_of_subset_insert_bot

/- warning: Inf_le_Inf_of_subset_insert_top -> infₛ_le_infₛ_of_subset_insert_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) t) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)) t)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) t) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align Inf_le_Inf_of_subset_insert_top infₛ_le_infₛ_of_subset_insert_topₓ'. -/
theorem infₛ_le_infₛ_of_subset_insert_top (h : s ⊆ insert ⊤ t) : infₛ t ≤ infₛ s :=
  le_trans (le_of_eq (trans top_inf_eq.symm infₛ_insert.symm)) (infₛ_le_infₛ h)
#align Inf_le_Inf_of_subset_insert_top infₛ_le_infₛ_of_subset_insert_top

/- warning: Sup_diff_singleton_bot -> supₛ_diff_singleton_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align Sup_diff_singleton_bot supₛ_diff_singleton_botₓ'. -/
@[simp]
theorem supₛ_diff_singleton_bot (s : Set α) : supₛ (s \ {⊥}) = supₛ s :=
  (supₛ_le_supₛ (diff_subset _ _)).antisymm <|
    supₛ_le_supₛ_of_subset_insert_bot <| subset_insert_diff_singleton _ _
#align Sup_diff_singleton_bot supₛ_diff_singleton_bot

/- warning: Inf_diff_singleton_top -> infₛ_diff_singleton_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (s : Set.{u1} α), Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align Inf_diff_singleton_top infₛ_diff_singleton_topₓ'. -/
@[simp]
theorem infₛ_diff_singleton_top (s : Set α) : infₛ (s \ {⊤}) = infₛ s :=
  @supₛ_diff_singleton_bot αᵒᵈ _ s
#align Inf_diff_singleton_top infₛ_diff_singleton_top

/- warning: Sup_pair -> supₛ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align Sup_pair supₛ_pairₓ'. -/
theorem supₛ_pair {a b : α} : supₛ {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).supₛ_eq
#align Sup_pair supₛ_pair

/- warning: Inf_pair -> infₛ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align Inf_pair infₛ_pairₓ'. -/
theorem infₛ_pair {a b : α} : infₛ {a, b} = a ⊓ b :=
  (@isGLB_pair α _ a b).infₛ_eq
#align Inf_pair infₛ_pair

/- warning: Sup_eq_bot -> supₛ_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u1} α a (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Eq.{succ u1} α a (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align Sup_eq_bot supₛ_eq_botₓ'. -/
@[simp]
theorem supₛ_eq_bot : supₛ s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h a ha => bot_unique <| h ▸ le_supₛ ha, fun h =>
    bot_unique <| supₛ_le fun a ha => le_bot_iff.2 <| h a ha⟩
#align Sup_eq_bot supₛ_eq_bot

/- warning: Inf_eq_top -> infₛ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u1} α a (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Eq.{succ u1} α a (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align Inf_eq_top infₛ_eq_topₓ'. -/
@[simp]
theorem infₛ_eq_top : infₛ s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  @supₛ_eq_bot αᵒᵈ _ _
#align Inf_eq_top infₛ_eq_top

/- warning: eq_singleton_bot_of_Sup_eq_bot_of_nonempty -> eq_singleton_bot_of_supₛ_eq_bot_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_supₛ_eq_bot_of_nonemptyₓ'. -/
theorem eq_singleton_bot_of_supₛ_eq_bot_of_nonempty {s : Set α} (h_sup : supₛ s = ⊥)
    (hne : s.Nonempty) : s = {⊥} :=
  by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [supₛ_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩
#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_supₛ_eq_bot_of_nonempty

/- warning: eq_singleton_top_of_Inf_eq_top_of_nonempty -> eq_singleton_top_of_infₛ_eq_top_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_infₛ_eq_top_of_nonemptyₓ'. -/
theorem eq_singleton_top_of_infₛ_eq_top_of_nonempty : infₛ s = ⊤ → s.Nonempty → s = {⊤} :=
  @eq_singleton_bot_of_supₛ_eq_bot_of_nonempty αᵒᵈ _ _
#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_infₛ_eq_top_of_nonempty

/- warning: Sup_eq_of_forall_le_of_forall_lt_exists_gt -> supₛ_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w b) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w a)))) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w b) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w a)))) -> (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align Sup_eq_of_forall_le_of_forall_lt_exists_gt supₛ_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `cSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supₛ_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : supₛ s = b :=
  (supₛ_le h₁).eq_of_not_lt fun h =>
    let ⟨a, ha, ha'⟩ := h₂ _ h
    ((le_supₛ ha).trans_lt ha').False
#align Sup_eq_of_forall_le_of_forall_lt_exists_gt supₛ_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: Inf_eq_of_forall_ge_of_forall_gt_exists_lt -> infₛ_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b w) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a w)))) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α} {b : α}, (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b w) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a w)))) -> (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt infₛ_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infₛ_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → infₛ s = b :=
  @supₛ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt infₛ_eq_of_forall_ge_of_forall_gt_exists_lt

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

/- warning: lt_Sup_iff -> lt_supₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a)))
Case conversion may be inaccurate. Consider using '#align lt_Sup_iff lt_supₛ_iffₓ'. -/
theorem lt_supₛ_iff : b < supₛ s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_supₛ s
#align lt_Sup_iff lt_supₛ_iff

/- warning: Inf_lt_iff -> infₛ_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s) b) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s) b) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align Inf_lt_iff infₛ_lt_iffₓ'. -/
theorem infₛ_lt_iff : infₛ s < b ↔ ∃ a ∈ s, a < b :=
  isGLB_lt_iff <| isGLB_infₛ s
#align Inf_lt_iff infₛ_lt_iff

/- warning: Sup_eq_top -> supₛ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Top.top.{u1} α (CompleteLattice.toTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b a))))
Case conversion may be inaccurate. Consider using '#align Sup_eq_top supₛ_eq_topₓ'. -/
theorem supₛ_eq_top : supₛ s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h b hb => lt_supₛ_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨a, ha, h⟩ := h _ h'
        (h.trans_le <| le_supₛ ha).False⟩
#align Sup_eq_top supₛ_eq_top

/- warning: Inf_eq_bot -> infₛ_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLinearOrder.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)) s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a b))))
Case conversion may be inaccurate. Consider using '#align Inf_eq_bot infₛ_eq_botₓ'. -/
theorem infₛ_eq_bot : infₛ s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b :=
  @supₛ_eq_top αᵒᵈ _ _
#align Inf_eq_bot infₛ_eq_bot

/- warning: lt_supr_iff -> lt_supᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f)) (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) a (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) a (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f)) (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) a (f i)))
Case conversion may be inaccurate. Consider using '#align lt_supr_iff lt_supᵢ_iffₓ'. -/
theorem lt_supᵢ_iff {f : ι → α} : a < supᵢ f ↔ ∃ i, a < f i :=
  lt_supₛ_iff.trans exists_range_iff
#align lt_supr_iff lt_supᵢ_iff

/- warning: infi_lt_iff -> infᵢ_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f) a) (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (f i) a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] {a : α} {f : ι -> α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f) a) (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) (f i) a))
Case conversion may be inaccurate. Consider using '#align infi_lt_iff infᵢ_lt_iffₓ'. -/
theorem infᵢ_lt_iff {f : ι → α} : infᵢ f < a ↔ ∃ i, f i < a :=
  infₛ_lt_iff.trans exists_range_iff
#align infi_lt_iff infᵢ_lt_iff

end CompleteLinearOrder

/-
### supr & infi
-/
section SupSet

variable [SupSet α] {f g : ι → α}

/- warning: Sup_range -> supₛ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) (supᵢ.{u1, u2} α _inst_1 ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u2} α] {f : ι -> α}, Eq.{succ u2} α (SupSet.supₛ.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) (supᵢ.{u2, u1} α _inst_1 ι f)
Case conversion may be inaccurate. Consider using '#align Sup_range supₛ_rangeₓ'. -/
theorem supₛ_range : supₛ (range f) = supᵢ f :=
  rfl
#align Sup_range supₛ_range

#print supₛ_eq_supᵢ' /-
theorem supₛ_eq_supᵢ' (s : Set α) : supₛ s = ⨆ a : s, a := by rw [supᵢ, Subtype.range_coe]
#align Sup_eq_supr' supₛ_eq_supᵢ'
-/

/- warning: supr_congr -> supᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u1} α (f i) (g i)) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α _inst_1 ι (fun (i : ι) => f i)) (supᵢ.{u1, u2} α _inst_1 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u2} α (f i) (g i)) -> (Eq.{succ u2} α (supᵢ.{u2, u1} α _inst_1 ι (fun (i : ι) => f i)) (supᵢ.{u2, u1} α _inst_1 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align supr_congr supᵢ_congrₓ'. -/
theorem supᵢ_congr (h : ∀ i, f i = g i) : (⨆ i, f i) = ⨆ i, g i :=
  congr_arg _ <| funext h
#align supr_congr supᵢ_congr

/- warning: function.surjective.supr_comp -> Function.Surjective.supᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u2, u3} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => g (f x))) (supᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u3, u2} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (supᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => g (f x))) (supᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.supr_comp Function.Surjective.supᵢ_compₓ'. -/
theorem Function.Surjective.supᵢ_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨆ x, g (f x)) = ⨆ y, g y := by simp only [supᵢ, hf.range_comp]
#align function.surjective.supr_comp Function.Surjective.supᵢ_comp

/- warning: equiv.supr_comp -> Equiv.supᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), Eq.{succ u1} α (supᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x))) (supᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), Eq.{succ u1} α (supᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι) => ι') _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (Equiv.instEquivLikeEquiv.{u3, u2} ι ι'))) e x))) (supᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y))
Case conversion may be inaccurate. Consider using '#align equiv.supr_comp Equiv.supᵢ_compₓ'. -/
theorem Equiv.supᵢ_comp {g : ι' → α} (e : ι ≃ ι') : (⨆ x, g (e x)) = ⨆ y, g y :=
  e.Surjective.supᵢ_comp _
#align equiv.supr_comp Equiv.supᵢ_comp

/- warning: function.surjective.supr_congr -> Function.Surjective.supᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u2, u3} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (supᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u3, u2} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (supᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (supᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.supr_congr Function.Surjective.supᵢ_congrₓ'. -/
protected theorem Function.Surjective.supᵢ_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y :=
  by
  convert h1.supr_comp g
  exact (funext h2).symm
#align function.surjective.supr_congr Function.Surjective.supᵢ_congr

/- warning: equiv.supr_congr -> Equiv.supᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x)) (f x)) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (supᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : SupSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι) => ι') _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (Equiv.instEquivLikeEquiv.{u3, u2} ι ι'))) e x)) (f x)) -> (Eq.{succ u1} α (supᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (supᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align equiv.supr_congr Equiv.supᵢ_congrₓ'. -/
protected theorem Equiv.supᵢ_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨆ x, f x) = ⨆ y, g y :=
  e.Surjective.supᵢ_congr _ h
#align equiv.supr_congr Equiv.supᵢ_congr

#print supᵢ_congr_Prop /-
@[congr]
theorem supᵢ_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : supᵢ f₁ = supᵢ f₂ :=
  by
  obtain rfl := propext pq
  congr with x
  apply f
#align supr_congr_Prop supᵢ_congr_Prop
-/

#print supᵢ_plift_up /-
theorem supᵢ_plift_up (f : PLift ι → α) : (⨆ i, f (PLift.up i)) = ⨆ i, f i :=
  PLift.up_surjective.supᵢ_congr _ fun _ => rfl
#align supr_plift_up supᵢ_plift_up
-/

/- warning: supr_plift_down -> supᵢ_plift_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : SupSet.{u1} α] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α _inst_1 (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => f (PLift.down.{u2} ι i))) (supᵢ.{u1, u2} α _inst_1 ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u2} α] (f : ι -> α), Eq.{succ u2} α (supᵢ.{u2, succ u1} α _inst_1 (PLift.{u1} ι) (fun (i : PLift.{u1} ι) => f (PLift.down.{u1} ι i))) (supᵢ.{u2, u1} α _inst_1 ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align supr_plift_down supᵢ_plift_downₓ'. -/
theorem supᵢ_plift_down (f : ι → α) : (⨆ i, f (PLift.down i)) = ⨆ i, f i :=
  PLift.down_surjective.supᵢ_congr _ fun _ => rfl
#align supr_plift_down supᵢ_plift_down

/- warning: supr_range' -> supᵢ_range' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] (g : β -> α) (f : ι -> β), Eq.{succ u1} α (supᵢ.{u1, succ u2} α _inst_1 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) (fun (b : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) => g ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, u3} β ι f)))))) b))) (supᵢ.{u1, u3} α _inst_1 ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] (g : β -> α) (f : ι -> β), Eq.{succ u3} α (supᵢ.{u3, succ u2} α _inst_1 (Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) (fun (b : Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) => g (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f)) b))) (supᵢ.{u3, u1} α _inst_1 ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align supr_range' supᵢ_range'ₓ'. -/
theorem supᵢ_range' (g : β → α) (f : ι → β) : (⨆ b : range f, g b) = ⨆ i, g (f i) := by
  rw [supᵢ, supᵢ, ← image_eq_range, ← range_comp]
#align supr_range' supᵢ_range'

#print supₛ_image' /-
theorem supₛ_image' {s : Set β} {f : β → α} : supₛ (f '' s) = ⨆ a : s, f a := by
  rw [supᵢ, image_eq_range]
#align Sup_image' supₛ_image'
-/

end SupSet

section InfSet

variable [InfSet α] {f g : ι → α}

/- warning: Inf_range -> infₛ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α _inst_1 (Set.range.{u1, u2} α ι f)) (infᵢ.{u1, u2} α _inst_1 ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u2} α] {f : ι -> α}, Eq.{succ u2} α (InfSet.infₛ.{u2} α _inst_1 (Set.range.{u2, u1} α ι f)) (infᵢ.{u2, u1} α _inst_1 ι f)
Case conversion may be inaccurate. Consider using '#align Inf_range infₛ_rangeₓ'. -/
theorem infₛ_range : infₛ (range f) = infᵢ f :=
  rfl
#align Inf_range infₛ_range

#print infₛ_eq_infᵢ' /-
theorem infₛ_eq_infᵢ' (s : Set α) : infₛ s = ⨅ a : s, a :=
  @supₛ_eq_supᵢ' αᵒᵈ _ _
#align Inf_eq_infi' infₛ_eq_infᵢ'
-/

/- warning: infi_congr -> infᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u1} α (f i) (g i)) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α _inst_1 ι (fun (i : ι) => f i)) (infᵢ.{u1, u2} α _inst_1 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), Eq.{succ u2} α (f i) (g i)) -> (Eq.{succ u2} α (infᵢ.{u2, u1} α _inst_1 ι (fun (i : ι) => f i)) (infᵢ.{u2, u1} α _inst_1 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align infi_congr infᵢ_congrₓ'. -/
theorem infᵢ_congr (h : ∀ i, f i = g i) : (⨅ i, f i) = ⨅ i, g i :=
  congr_arg _ <| funext h
#align infi_congr infᵢ_congr

/- warning: function.surjective.infi_comp -> Function.Surjective.infᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u2, u3} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (infᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => g (f x))) (infᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> ι'}, (Function.Surjective.{u3, u2} ι ι' f) -> (forall (g : ι' -> α), Eq.{succ u1} α (infᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => g (f x))) (infᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.infi_comp Function.Surjective.infᵢ_compₓ'. -/
theorem Function.Surjective.infᵢ_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨅ x, g (f x)) = ⨅ y, g y :=
  @Function.Surjective.supᵢ_comp αᵒᵈ _ _ _ f hf g
#align function.surjective.infi_comp Function.Surjective.infᵢ_comp

/- warning: equiv.infi_comp -> Equiv.infᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), Eq.{succ u1} α (infᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x))) (infᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), Eq.{succ u1} α (infᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι) => ι') _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (Equiv.instEquivLikeEquiv.{u3, u2} ι ι'))) e x))) (infᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y))
Case conversion may be inaccurate. Consider using '#align equiv.infi_comp Equiv.infᵢ_compₓ'. -/
theorem Equiv.infᵢ_comp {g : ι' → α} (e : ι ≃ ι') : (⨅ x, g (e x)) = ⨅ y, g y :=
  @Equiv.supᵢ_comp αᵒᵈ _ _ _ _ e
#align equiv.infi_comp Equiv.infᵢ_comp

/- warning: function.surjective.infi_congr -> Function.Surjective.infᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u2, u3} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (infᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (h : ι -> ι'), (Function.Surjective.{u3, u2} ι ι' h) -> (forall (x : ι), Eq.{succ u1} α (g (h x)) (f x)) -> (Eq.{succ u1} α (infᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (infᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align function.surjective.infi_congr Function.Surjective.infᵢ_congrₓ'. -/
protected theorem Function.Surjective.infᵢ_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
  @Function.Surjective.supᵢ_congr αᵒᵈ _ _ _ _ _ h h1 h2
#align function.surjective.infi_congr Function.Surjective.infᵢ_congr

/- warning: equiv.infi_congr -> Equiv.infᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u2, u3} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (coeFn.{max 1 (imax u2 u3) (imax u3 u2), imax u2 u3} (Equiv.{u2, u3} ι ι') (fun (_x : Equiv.{u2, u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{u2, u3} ι ι') e x)) (f x)) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α _inst_1 ι (fun (x : ι) => f x)) (infᵢ.{u1, u3} α _inst_1 ι' (fun (y : ι') => g y)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {ι' : Sort.{u2}} [_inst_1 : InfSet.{u1} α] {f : ι -> α} {g : ι' -> α} (e : Equiv.{u3, u2} ι ι'), (forall (x : ι), Eq.{succ u1} α (g (FunLike.coe.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι) => ι') _x) (EmbeddingLike.toFunLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (EquivLike.toEmbeddingLike.{max (max 1 u3) u2, u3, u2} (Equiv.{u3, u2} ι ι') ι ι' (Equiv.instEquivLikeEquiv.{u3, u2} ι ι'))) e x)) (f x)) -> (Eq.{succ u1} α (infᵢ.{u1, u3} α _inst_1 ι (fun (x : ι) => f x)) (infᵢ.{u1, u2} α _inst_1 ι' (fun (y : ι') => g y)))
Case conversion may be inaccurate. Consider using '#align equiv.infi_congr Equiv.infᵢ_congrₓ'. -/
protected theorem Equiv.infᵢ_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨅ x, f x) = ⨅ y, g y :=
  @Equiv.supᵢ_congr αᵒᵈ _ _ _ _ _ e h
#align equiv.infi_congr Equiv.infᵢ_congr

#print infᵢ_congr_Prop /-
@[congr]
theorem infᵢ_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : infᵢ f₁ = infᵢ f₂ :=
  @supᵢ_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f
#align infi_congr_Prop infᵢ_congr_Prop
-/

#print infᵢ_plift_up /-
theorem infᵢ_plift_up (f : PLift ι → α) : (⨅ i, f (PLift.up i)) = ⨅ i, f i :=
  PLift.up_surjective.infᵢ_congr _ fun _ => rfl
#align infi_plift_up infᵢ_plift_up
-/

/- warning: infi_plift_down -> infᵢ_plift_down is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : InfSet.{u1} α] (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α _inst_1 (PLift.{u2} ι) (fun (i : PLift.{u2} ι) => f (PLift.down.{u2} ι i))) (infᵢ.{u1, u2} α _inst_1 ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u2} α] (f : ι -> α), Eq.{succ u2} α (infᵢ.{u2, succ u1} α _inst_1 (PLift.{u1} ι) (fun (i : PLift.{u1} ι) => f (PLift.down.{u1} ι i))) (infᵢ.{u2, u1} α _inst_1 ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align infi_plift_down infᵢ_plift_downₓ'. -/
theorem infᵢ_plift_down (f : ι → α) : (⨅ i, f (PLift.down i)) = ⨅ i, f i :=
  PLift.down_surjective.infᵢ_congr _ fun _ => rfl
#align infi_plift_down infᵢ_plift_down

/- warning: infi_range' -> infᵢ_range' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] (g : β -> α) (f : ι -> β), Eq.{succ u1} α (infᵢ.{u1, succ u2} α _inst_1 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) (fun (b : coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) => g ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, u3} β ι f)) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, u3} β ι f)))))) b))) (infᵢ.{u1, u3} α _inst_1 ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] (g : β -> α) (f : ι -> β), Eq.{succ u3} α (infᵢ.{u3, succ u2} α _inst_1 (Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) (fun (b : Set.Elem.{u2} β (Set.range.{u2, u1} β ι f)) => g (Subtype.val.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.range.{u2, u1} β ι f)) b))) (infᵢ.{u3, u1} α _inst_1 ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align infi_range' infᵢ_range'ₓ'. -/
theorem infᵢ_range' (g : β → α) (f : ι → β) : (⨅ b : range f, g b) = ⨅ i, g (f i) :=
  @supᵢ_range' αᵒᵈ _ _ _ _ _
#align infi_range' infᵢ_range'

#print infₛ_image' /-
theorem infₛ_image' {s : Set β} {f : β → α} : infₛ (f '' s) = ⨅ a : s, f a :=
  @supₛ_image' αᵒᵈ _ _ _ _
#align Inf_image' infₛ_image'
-/

end InfSet

section

variable [CompleteLattice α] {f g s t : ι → α} {a b : α}

/- warning: le_supr -> le_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f)
Case conversion may be inaccurate. Consider using '#align le_supr le_supᵢₓ'. -/
-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_supᵢ (f : ι → α) (i : ι) : f i ≤ supᵢ f :=
  le_supₛ ⟨i, rfl⟩
#align le_supr le_supᵢ

/- warning: infi_le -> infᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (f i)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (f i)
Case conversion may be inaccurate. Consider using '#align infi_le infᵢ_leₓ'. -/
theorem infᵢ_le (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  infₛ_le ⟨i, rfl⟩
#align infi_le infᵢ_le

/- warning: le_supr' -> le_supᵢ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f)
Case conversion may be inaccurate. Consider using '#align le_supr' le_supᵢ'ₓ'. -/
@[ematch]
theorem le_supᵢ' (f : ι → α) (i : ι) : f i ≤ supᵢ f :=
  le_supₛ ⟨i, rfl⟩
#align le_supr' le_supᵢ'

/- warning: infi_le' -> infᵢ_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (f i)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (f i)
Case conversion may be inaccurate. Consider using '#align infi_le' infᵢ_le'ₓ'. -/
@[ematch]
theorem infᵢ_le' (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  infₛ_le ⟨i, rfl⟩
#align infi_le' infᵢ_le'

/- warning: is_lub_supr -> isLUB_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α}, IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (j : ι) => f j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α}, IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (j : ι) => f j))
Case conversion may be inaccurate. Consider using '#align is_lub_supr isLUB_supᵢₓ'. -/
/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] lemma le_supr' (f : ι → α) (i : ι) : (: f i :) ≤ (: supr f :) :=
le_Sup ⟨i, rfl⟩
-/
theorem isLUB_supᵢ : IsLUB (range f) (⨆ j, f j) :=
  isLUB_supₛ _
#align is_lub_supr isLUB_supᵢ

/- warning: is_glb_infi -> isGLB_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α}, IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (j : ι) => f j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α}, IsGLB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (j : ι) => f j))
Case conversion may be inaccurate. Consider using '#align is_glb_infi isGLB_infᵢₓ'. -/
theorem isGLB_infᵢ : IsGLB (range f) (⨅ j, f j) :=
  isGLB_infₛ _
#align is_glb_infi isGLB_infᵢ

/- warning: is_lub.supr_eq -> IsLUB.supᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (j : ι) => f j)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (IsLUB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) a) -> (Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (j : ι) => f j)) a)
Case conversion may be inaccurate. Consider using '#align is_lub.supr_eq IsLUB.supᵢ_eqₓ'. -/
theorem IsLUB.supᵢ_eq (h : IsLUB (range f) a) : (⨆ j, f j) = a :=
  h.supₛ_eq
#align is_lub.supr_eq IsLUB.supᵢ_eq

/- warning: is_glb.infi_eq -> IsGLB.infᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.range.{u1, u2} α ι f) a) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (j : ι) => f j)) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (IsGLB.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (Set.range.{u2, u1} α ι f) a) -> (Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (j : ι) => f j)) a)
Case conversion may be inaccurate. Consider using '#align is_glb.infi_eq IsGLB.infᵢ_eqₓ'. -/
theorem IsGLB.infᵢ_eq (h : IsGLB (range f) a) : (⨅ j, f j) = a :=
  h.infₛ_eq
#align is_glb.infi_eq IsGLB.infᵢ_eq

/- warning: le_supr_of_le -> le_supᵢ_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (f i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_supr_of_le le_supᵢ_of_leₓ'. -/
theorem le_supᵢ_of_le (i : ι) (h : a ≤ f i) : a ≤ supᵢ f :=
  h.trans <| le_supᵢ _ i
#align le_supr_of_le le_supᵢ_of_le

/- warning: infi_le_of_le -> infᵢ_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α} (i : ι), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) a)
Case conversion may be inaccurate. Consider using '#align infi_le_of_le infᵢ_le_of_leₓ'. -/
theorem infᵢ_le_of_le (i : ι) (h : f i ≤ a) : infᵢ f ≤ a :=
  (infᵢ_le _ i).trans h
#align infi_le_of_le infᵢ_le_of_le

/- warning: le_supr₂ -> le_supᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j)))
Case conversion may be inaccurate. Consider using '#align le_supr₂ le_supᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_supᵢ₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_supᵢ_of_le i <| le_supᵢ (f i) j
#align le_supr₂ le_supᵢ₂

/- warning: infi₂_le -> infᵢ₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (f i j)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (f i j)
Case conversion may be inaccurate. Consider using '#align infi₂_le infᵢ₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : (⨅ (i) (j), f i j) ≤ f i j :=
  infᵢ_le_of_le i <| infᵢ_le (f i) j
#align infi₂_le infᵢ₂_le

/- warning: le_supr₂_of_le -> le_supᵢ₂_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i j)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (f i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))))
Case conversion may be inaccurate. Consider using '#align le_supr₂_of_le le_supᵢ₂_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_supᵢ₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_supᵢ₂ i j
#align le_supr₂_of_le le_supᵢ₂_of_le

/- warning: infi₂_le_of_le -> infᵢ₂_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α} (i : ι) (j : κ i), (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) a) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) a)
Case conversion may be inaccurate. Consider using '#align infi₂_le_of_le infᵢ₂_le_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    (⨅ (i) (j), f i j) ≤ a :=
  (infᵢ₂_le i j).trans h
#align infi₂_le_of_le infᵢ₂_le_of_le

/- warning: supr_le -> supᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) a) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) a)
Case conversion may be inaccurate. Consider using '#align supr_le supᵢ_leₓ'. -/
theorem supᵢ_le (h : ∀ i, f i ≤ a) : supᵢ f ≤ a :=
  supₛ_le fun b ⟨i, Eq⟩ => Eq ▸ h i
#align supr_le supᵢ_le

/- warning: le_infi -> le_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (f i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align le_infi le_infᵢₓ'. -/
theorem le_infᵢ (h : ∀ i, a ≤ f i) : a ≤ infᵢ f :=
  le_infₛ fun b ⟨i, Eq⟩ => Eq ▸ h i
#align le_infi le_infᵢ

/- warning: supr₂_le -> supᵢ₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) a) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) a)
Case conversion may be inaccurate. Consider using '#align supr₂_le supᵢ₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : (⨆ (i) (j), f i j) ≤ a :=
  supᵢ_le fun i => supᵢ_le <| h i
#align supr₂_le supᵢ₂_le

/- warning: le_infi₂ -> le_infᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i j)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (f i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))))
Case conversion may be inaccurate. Consider using '#align le_infi₂ le_infᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_infᵢ₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_infᵢ fun i => le_infᵢ <| h i
#align le_infi₂ le_infᵢ₂

/- warning: supr₂_le_supr -> supᵢ₂_le_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) (κ i) (fun (j : κ i) => f i))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align supr₂_le_supr supᵢ₂_le_supᵢₓ'. -/
theorem supᵢ₂_le_supᵢ (κ : ι → Sort _) (f : ι → α) : (⨆ (i) (j : κ i), f i) ≤ ⨆ i, f i :=
  supᵢ₂_le fun i j => le_supᵢ f i
#align supr₂_le_supr supᵢ₂_le_supᵢ

/- warning: infi_le_infi₂ -> infᵢ_le_infᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (κ : ι -> Sort.{u3}) (f : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) (κ i) (fun (j : κ i) => f i)))
Case conversion may be inaccurate. Consider using '#align infi_le_infi₂ infᵢ_le_infᵢ₂ₓ'. -/
theorem infᵢ_le_infᵢ₂ (κ : ι → Sort _) (f : ι → α) : (⨅ i, f i) ≤ ⨅ (i) (j : κ i), f i :=
  le_infᵢ₂ fun i j => infᵢ_le f i
#align infi_le_infi₂ infᵢ_le_infᵢ₂

/- warning: supr_mono -> supᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align supr_mono supᵢ_monoₓ'. -/
theorem supᵢ_mono (h : ∀ i, f i ≤ g i) : supᵢ f ≤ supᵢ g :=
  supᵢ_le fun i => le_supᵢ_of_le i <| h i
#align supr_mono supᵢ_mono

/- warning: infi_mono -> infᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι g))
Case conversion may be inaccurate. Consider using '#align infi_mono infᵢ_monoₓ'. -/
theorem infᵢ_mono (h : ∀ i, f i ≤ g i) : infᵢ f ≤ infᵢ g :=
  le_infᵢ fun i => infᵢ_le_of_le i <| h i
#align infi_mono infᵢ_mono

/- warning: supr₂_mono -> supᵢ₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => g i j))))
Case conversion may be inaccurate. Consider using '#align supr₂_mono supᵢ₂_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supᵢ_mono fun i => supᵢ_mono <| h i
#align supr₂_mono supᵢ₂_mono

/- warning: infi₂_mono -> infᵢ₂_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i : ι), (κ i) -> α}, (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (g i j)) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => g i j))))
Case conversion may be inaccurate. Consider using '#align infi₂_mono infᵢ₂_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  infᵢ_mono fun i => infᵢ_mono <| h i
#align infi₂_mono infᵢ₂_mono

/- warning: supr_mono' -> supᵢ_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι' -> α}, (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι' -> α}, (forall (i : ι), Exists.{u3} ι' (fun (i' : ι') => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι' g))
Case conversion may be inaccurate. Consider using '#align supr_mono' supᵢ_mono'ₓ'. -/
theorem supᵢ_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : supᵢ f ≤ supᵢ g :=
  supᵢ_le fun i => Exists.elim (h i) le_supᵢ_of_le
#align supr_mono' supᵢ_mono'

/- warning: infi_mono' -> infᵢ_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι' -> α}, (forall (i' : ι'), Exists.{u2} ι (fun (i : ι) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' g))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι' -> α}, (forall (i' : ι'), Exists.{u3} ι (fun (i : ι) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) (g i'))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι' g))
Case conversion may be inaccurate. Consider using '#align infi_mono' infᵢ_mono'ₓ'. -/
theorem infᵢ_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : infᵢ f ≤ infᵢ g :=
  le_infᵢ fun i' => Exists.elim (h i') infᵢ_le_of_le
#align infi_mono' infᵢ_mono'

/- warning: supr₂_mono' -> supᵢ₂_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u5}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι) (j : κ i), Exists.{u3} ι' (fun (i' : ι') => Exists.{u5} (κ' i') (fun (j' : κ' i') => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) (g i' j')))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (i : ι') => supᵢ.{u1, u5} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ' i) (fun (j : κ' i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u5}} {κ : ι -> Sort.{u1}} {κ' : ι' -> Sort.{u4}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι) (j : κ i), Exists.{u5} ι' (fun (i' : ι') => Exists.{u4} (κ' i') (fun (j' : κ' i') => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) (g i' j')))) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (supᵢ.{u3, u5} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (i : ι') => supᵢ.{u3, u4} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ' i) (fun (j : κ' i) => g i j))))
Case conversion may be inaccurate. Consider using '#align supr₂_mono' supᵢ₂_mono'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supᵢ₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_supᵢ₂_of_le i' j' h
#align supr₂_mono' supᵢ₂_mono'

/- warning: infi₂_mono' -> infᵢ₂_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u5}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι') (j : κ' i), Exists.{u2} ι (fun (i' : ι) => Exists.{u4} (κ i') (fun (j' : κ i') => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i' j') (g i j)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (i : ι') => infᵢ.{u1, u5} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ' i) (fun (j : κ' i) => g i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u5}} {ι' : Sort.{u2}} {κ : ι -> Sort.{u4}} {κ' : ι' -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α} {g : forall (i' : ι'), (κ' i') -> α}, (forall (i : ι') (j : κ' i), Exists.{u5} ι (fun (i' : ι) => Exists.{u4} (κ i') (fun (j' : κ i') => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i' j') (g i j)))) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (infᵢ.{u3, u5} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u4} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (i : ι') => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ' i) (fun (j : κ' i) => g i j))))
Case conversion may be inaccurate. Consider using '#align infi₂_mono' infᵢ₂_mono'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  le_infᵢ₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    infᵢ₂_le_of_le i' j' h
#align infi₂_mono' infᵢ₂_mono'

/- warning: supr_const_mono -> supᵢ_const_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, (ι -> ι') -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => a)) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (j : ι') => a)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α}, (ι -> ι') -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => a)) (supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (j : ι') => a)))
Case conversion may be inaccurate. Consider using '#align supr_const_mono supᵢ_const_monoₓ'. -/
theorem supᵢ_const_mono (h : ι → ι') : (⨆ i : ι, a) ≤ ⨆ j : ι', a :=
  supᵢ_le <| le_supᵢ _ ∘ h
#align supr_const_mono supᵢ_const_mono

/- warning: infi_const_mono -> infᵢ_const_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, (ι' -> ι) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => a)) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => a)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α}, (ι' -> ι) -> (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => a)) (infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => a)))
Case conversion may be inaccurate. Consider using '#align infi_const_mono infᵢ_const_monoₓ'. -/
theorem infᵢ_const_mono (h : ι' → ι) : (⨅ i : ι, a) ≤ ⨅ j : ι', a :=
  le_infᵢ <| infᵢ_le _ ∘ h
#align infi_const_mono infᵢ_const_mono

/- warning: supr_infi_le_infi_supr -> supᵢ_infᵢ_le_infᵢ_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> ι' -> α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => f i j))) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] (f : ι -> ι' -> α), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => f i j))) (infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i j)))
Case conversion may be inaccurate. Consider using '#align supr_infi_le_infi_supr supᵢ_infᵢ_le_infᵢ_supᵢₓ'. -/
theorem supᵢ_infᵢ_le_infᵢ_supᵢ (f : ι → ι' → α) : (⨆ i, ⨅ j, f i j) ≤ ⨅ j, ⨆ i, f i j :=
  supᵢ_le fun i => infᵢ_mono fun j => le_supᵢ _ i
#align supr_infi_le_infi_supr supᵢ_infᵢ_le_infᵢ_supᵢ

/- warning: bsupr_mono -> bsupᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (q i) (fun (h : q i) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (q i) (fun (h : q i) => f i))))
Case conversion may be inaccurate. Consider using '#align bsupr_mono bsupᵢ_monoₓ'. -/
theorem bsupᵢ_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨆ (i) (h : p i), f i) ≤ ⨆ (i) (h : q i), f i :=
  supᵢ_mono fun i => supᵢ_const_mono (hpq i)
#align bsupr_mono bsupᵢ_mono

/- warning: binfi_mono -> binfᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (q i) (fun (h : q i) => f i))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {p : ι -> Prop} {q : ι -> Prop}, (forall (i : ι), (p i) -> (q i)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (q i) (fun (h : q i) => f i))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))))
Case conversion may be inaccurate. Consider using '#align binfi_mono binfᵢ_monoₓ'. -/
theorem binfᵢ_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨅ (i) (h : q i), f i) ≤ ⨅ (i) (h : p i), f i :=
  infᵢ_mono fun i => infᵢ_const_mono (hpq i)
#align binfi_mono binfᵢ_mono

/- warning: supr_le_iff -> supᵢ_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) a) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) a) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) a)
Case conversion may be inaccurate. Consider using '#align supr_le_iff supᵢ_le_iffₓ'. -/
@[simp]
theorem supᵢ_le_iff : supᵢ f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_supᵢ).trans forall_range_iff
#align supr_le_iff supᵢ_le_iff

/- warning: le_infi_iff -> le_infᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f)) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f)) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (f i))
Case conversion may be inaccurate. Consider using '#align le_infi_iff le_infᵢ_iffₓ'. -/
@[simp]
theorem le_infᵢ_iff : a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff isGLB_infᵢ).trans forall_range_iff
#align le_infi_iff le_infᵢ_iff

/- warning: supr₂_le_iff -> supᵢ₂_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i j) a)
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) (f i j) a)
Case conversion may be inaccurate. Consider using '#align supr₂_le_iff supᵢ₂_le_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem supᵢ₂_le_iff {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [supᵢ_le_iff]
#align supr₂_le_iff supᵢ₂_le_iff

/- warning: le_infi₂_iff -> le_infᵢ₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (f i j))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) a (f i j))
Case conversion may be inaccurate. Consider using '#align le_infi₂_iff le_infᵢ₂_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem le_infᵢ₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_infᵢ_iff]
#align le_infi₂_iff le_infᵢ₂_iff

/- warning: supr_lt_iff -> supᵢ_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) a) (Exists.{succ u1} α (fun (b : α) => And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι f) a) (Exists.{succ u2} α (fun (b : α) => And (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b a) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) b)))
Case conversion may be inaccurate. Consider using '#align supr_lt_iff supᵢ_lt_iffₓ'. -/
theorem supᵢ_lt_iff : supᵢ f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨supᵢ f, h, le_supᵢ f⟩, fun ⟨b, h, hb⟩ => (supᵢ_le hb).trans_lt h⟩
#align supr_lt_iff supᵢ_lt_iff

/- warning: lt_infi_iff -> lt_infᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f)) (Exists.{succ u1} α (fun (b : α) => And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b) (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {a : α}, Iff (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι f)) (Exists.{succ u2} α (fun (b : α) => And (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a b) (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b (f i))))
Case conversion may be inaccurate. Consider using '#align lt_infi_iff lt_infᵢ_iffₓ'. -/
theorem lt_infᵢ_iff : a < infᵢ f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨infᵢ f, h, infᵢ_le f⟩, fun ⟨b, h, hb⟩ => h.trans_le <| le_infᵢ hb⟩
#align lt_infi_iff lt_infᵢ_iff

/- warning: Sup_eq_supr -> supₛ_eq_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (a : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (a : α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => a)))
Case conversion may be inaccurate. Consider using '#align Sup_eq_supr supₛ_eq_supᵢₓ'. -/
theorem supₛ_eq_supᵢ {s : Set α} : supₛ s = ⨆ a ∈ s, a :=
  le_antisymm (supₛ_le le_supᵢ₂) (supᵢ₂_le fun b => le_supₛ)
#align Sup_eq_supr supₛ_eq_supᵢ

/- warning: Inf_eq_infi -> infₛ_eq_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (a : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (a : α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => a)))
Case conversion may be inaccurate. Consider using '#align Inf_eq_infi infₛ_eq_infᵢₓ'. -/
theorem infₛ_eq_infᵢ {s : Set α} : infₛ s = ⨅ a ∈ s, a :=
  @supₛ_eq_supᵢ αᵒᵈ _ _
#align Inf_eq_infi infₛ_eq_infᵢ

/- warning: monotone.le_map_supr -> Monotone.le_map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))) (f (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Monotone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (supᵢ.{u3, u1} β (CompleteLattice.toSupSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))) (f (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι s)))
Case conversion may be inaccurate. Consider using '#align monotone.le_map_supr Monotone.le_map_supᵢₓ'. -/
theorem Monotone.le_map_supᵢ [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    (⨆ i, f (s i)) ≤ f (supᵢ s) :=
  supᵢ_le fun i => hf <| le_supᵢ _ _
#align monotone.le_map_supr Monotone.le_map_supᵢ

/- warning: antitone.le_map_infi -> Antitone.le_map_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))) (f (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Antitone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (supᵢ.{u3, u1} β (CompleteLattice.toSupSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))) (f (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι s)))
Case conversion may be inaccurate. Consider using '#align antitone.le_map_infi Antitone.le_map_infᵢₓ'. -/
theorem Antitone.le_map_infᵢ [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    (⨆ i, f (s i)) ≤ f (infᵢ s) :=
  hf.dual_left.le_map_supᵢ
#align antitone.le_map_infi Antitone.le_map_infᵢ

/- warning: monotone.le_map_supr₂ -> Monotone.le_map_supᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => supᵢ.{u2, u4} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))) (f (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Monotone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (supᵢ.{u4, u2} β (CompleteLattice.toSupSet.{u4} β _inst_2) ι (fun (i : ι) => supᵢ.{u4, u1} β (CompleteLattice.toSupSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))) (f (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))))
Case conversion may be inaccurate. Consider using '#align monotone.le_map_supr₂ Monotone.le_map_supᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Monotone.le_map_supᵢ₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨆ (i) (j), s i j) :=
  supᵢ₂_le fun i j => hf <| le_supᵢ₂ _ _
#align monotone.le_map_supr₂ Monotone.le_map_supᵢ₂

/- warning: antitone.le_map_infi₂ -> Antitone.le_map_infᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => supᵢ.{u2, u4} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))) (f (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Antitone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (supᵢ.{u4, u2} β (CompleteLattice.toSupSet.{u4} β _inst_2) ι (fun (i : ι) => supᵢ.{u4, u1} β (CompleteLattice.toSupSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))) (f (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))))
Case conversion may be inaccurate. Consider using '#align antitone.le_map_infi₂ Antitone.le_map_infᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Antitone.le_map_infᵢ₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_supᵢ₂ _
#align antitone.le_map_infi₂ Antitone.le_map_infᵢ₂

/- warning: monotone.le_map_Sup -> Monotone.le_map_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))) (f (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))) (f (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align monotone.le_map_Sup Monotone.le_map_supₛₓ'. -/
theorem Monotone.le_map_supₛ [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    (⨆ a ∈ s, f a) ≤ f (supₛ s) := by rw [supₛ_eq_supᵢ] <;> exact hf.le_map_supr₂ _
#align monotone.le_map_Sup Monotone.le_map_supₛ

/- warning: antitone.le_map_Inf -> Antitone.le_map_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))) (f (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))) (f (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align antitone.le_map_Inf Antitone.le_map_infₛₓ'. -/
theorem Antitone.le_map_infₛ [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    (⨆ a ∈ s, f a) ≤ f (infₛ s) :=
  hf.dual_left.le_map_supₛ
#align antitone.le_map_Inf Antitone.le_map_infₛ

/- warning: order_iso.map_supr -> OrderIso.map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : ι -> α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => x i))) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (x i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] (f : OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))) (x : ι -> α), Eq.{succ u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => x i))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u3} α β)) (RelEmbedding.toEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => x i))) (supᵢ.{u3, u1} β (CompleteLattice.toSupSet.{u3} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u3} α β)) (RelEmbedding.toEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) (x i)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_supr OrderIso.map_supᵢₓ'. -/
theorem OrderIso.map_supᵢ [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.Surjective.forall.2 fun x => by simp only [f.le_iff_le, supᵢ_le_iff]
#align order_iso.map_supr OrderIso.map_supᵢ

/- warning: order_iso.map_infi -> OrderIso.map_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : ι -> α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => x i))) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (x i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] (f : OrderIso.{u2, u3} α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))) (x : ι -> α), Eq.{succ u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => x i))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u3} α β)) (RelEmbedding.toEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => x i))) (infᵢ.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_2) ι (fun (i : ι) => FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (Function.Embedding.{succ u2, succ u3} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u3} α β)) (RelEmbedding.toEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u2, u3} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) (x i)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_infi OrderIso.map_infᵢₓ'. -/
theorem OrderIso.map_infᵢ [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_supᵢ f.dual _
#align order_iso.map_infi OrderIso.map_infᵢ

/- warning: order_iso.map_Sup -> OrderIso.map_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) a)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_Sup OrderIso.map_supₛₓ'. -/
theorem OrderIso.map_supₛ [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (supₛ s) = ⨆ a ∈ s, f a := by simp only [supₛ_eq_supᵢ, OrderIso.map_supᵢ]
#align order_iso.map_Sup OrderIso.map_supₛ

/- warning: order_iso.map_Inf -> OrderIso.map_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))))) f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : OrderIso.{u1, u2} α β (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (s : Set.{u1} α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) f)) a)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_Inf OrderIso.map_infₛₓ'. -/
theorem OrderIso.map_infₛ [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (infₛ s) = ⨅ a ∈ s, f a :=
  OrderIso.map_supₛ f.dual _
#align order_iso.map_Inf OrderIso.map_infₛ

/- warning: supr_comp_le -> supᵢ_comp_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f (g x))) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (y : ι') => f y))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => f (g x))) (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι' (fun (y : ι') => f y))
Case conversion may be inaccurate. Consider using '#align supr_comp_le supᵢ_comp_leₓ'. -/
theorem supᵢ_comp_le {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
  supᵢ_mono' fun x => ⟨_, le_rfl⟩
#align supr_comp_le supᵢ_comp_le

/- warning: le_infi_comp -> le_infᵢ_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (y : ι') => f y)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f (g x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {ι' : Sort.{u3}} (f : ι' -> α) (g : ι -> ι'), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι' (fun (y : ι') => f y)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => f (g x)))
Case conversion may be inaccurate. Consider using '#align le_infi_comp le_infᵢ_compₓ'. -/
theorem le_infᵢ_comp {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
  infᵢ_mono' fun x => ⟨_, le_rfl⟩
#align le_infi_comp le_infᵢ_comp

/- warning: monotone.supr_comp_eq -> Monotone.supᵢ_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Preorder.{u2} β] {f : β -> α}, (Monotone.{u2, u1} β α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u3} ι (fun (i : ι) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x (s i))) -> (Eq.{succ u1} α (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f (s x))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (y : β) => f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Preorder.{u3} β] {f : β -> α}, (Monotone.{u3, u2} β α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u1} ι (fun (i : ι) => LE.le.{u3} β (Preorder.toLE.{u3} β _inst_2) x (s i))) -> (Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => f (s x))) (supᵢ.{u2, succ u3} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (y : β) => f y))))
Case conversion may be inaccurate. Consider using '#align monotone.supr_comp_eq Monotone.supᵢ_comp_eqₓ'. -/
theorem Monotone.supᵢ_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : (⨆ x, f (s x)) = ⨆ y, f y :=
  le_antisymm (supᵢ_comp_le _ _) (supᵢ_mono' fun x => (hs x).imp fun i hi => hf hi)
#align monotone.supr_comp_eq Monotone.supᵢ_comp_eq

/- warning: monotone.infi_comp_eq -> Monotone.infᵢ_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Preorder.{u2} β] {f : β -> α}, (Monotone.{u2, u1} β α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u3} ι (fun (i : ι) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) (s i) x)) -> (Eq.{succ u1} α (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f (s x))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (y : β) => f y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : Preorder.{u3} β] {f : β -> α}, (Monotone.{u3, u2} β α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) f) -> (forall {s : ι -> β}, (forall (x : β), Exists.{u1} ι (fun (i : ι) => LE.le.{u3} β (Preorder.toLE.{u3} β _inst_2) (s i) x)) -> (Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => f (s x))) (infᵢ.{u2, succ u3} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (y : β) => f y))))
Case conversion may be inaccurate. Consider using '#align monotone.infi_comp_eq Monotone.infᵢ_comp_eqₓ'. -/
theorem Monotone.infᵢ_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : (⨅ x, f (s x)) = ⨅ y, f y :=
  le_antisymm (infᵢ_mono' fun x => (hs x).imp fun i hi => hf hi) (le_infᵢ_comp _ _)
#align monotone.infi_comp_eq Monotone.infᵢ_comp_eq

/- warning: antitone.map_supr_le -> Antitone.map_supᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι s)) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Antitone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (f (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι s)) (infᵢ.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))))
Case conversion may be inaccurate. Consider using '#align antitone.map_supr_le Antitone.map_supᵢ_leₓ'. -/
theorem Antitone.map_supᵢ_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (supᵢ s) ≤ ⨅ i, f (s i) :=
  le_infᵢ fun i => hf <| le_supᵢ _ _
#align antitone.map_supr_le Antitone.map_supᵢ_le

/- warning: monotone.map_infi_le -> Monotone.map_infᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι s)) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => f (s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α} [_inst_2 : CompleteLattice.{u3} β] {f : α -> β}, (Monotone.{u2, u3} α β (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))) f) -> (LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2)))) (f (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι s)) (infᵢ.{u3, u1} β (CompleteLattice.toInfSet.{u3} β _inst_2) ι (fun (i : ι) => f (s i))))
Case conversion may be inaccurate. Consider using '#align monotone.map_infi_le Monotone.map_infᵢ_leₓ'. -/
theorem Monotone.map_infᵢ_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (infᵢ s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_supᵢ_le
#align monotone.map_infi_le Monotone.map_infᵢ_le

/- warning: antitone.map_supr₂_le -> Antitone.map_supᵢ₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => infᵢ.{u2, u4} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Antitone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (f (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))) (infᵢ.{u4, u2} β (CompleteLattice.toInfSet.{u4} β _inst_2) ι (fun (i : ι) => infᵢ.{u4, u1} β (CompleteLattice.toInfSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))))
Case conversion may be inaccurate. Consider using '#align antitone.map_supr₂_le Antitone.map_supᵢ₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Antitone.map_supᵢ₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_infᵢ₂ _
#align antitone.map_supr₂_le Antitone.map_supᵢ₂_le

/- warning: monotone.map_infi₂_le -> Monotone.map_infᵢ₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => s i j)))) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => infᵢ.{u2, u4} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (κ i) (fun (j : κ i) => f (s i j)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : CompleteLattice.{u4} β] {f : α -> β}, (Monotone.{u3, u4} α β (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2))) f) -> (forall (s : forall (i : ι), (κ i) -> α), LE.le.{u4} β (Preorder.toLE.{u4} β (PartialOrder.toPreorder.{u4} β (CompleteSemilatticeInf.toPartialOrder.{u4} β (CompleteLattice.toCompleteSemilatticeInf.{u4} β _inst_2)))) (f (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => s i j)))) (infᵢ.{u4, u2} β (CompleteLattice.toInfSet.{u4} β _inst_2) ι (fun (i : ι) => infᵢ.{u4, u1} β (CompleteLattice.toInfSet.{u4} β _inst_2) (κ i) (fun (j : κ i) => f (s i j)))))
Case conversion may be inaccurate. Consider using '#align monotone.map_infi₂_le Monotone.map_infᵢ₂_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Monotone.map_infᵢ₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_supᵢ₂ _
#align monotone.map_infi₂_le Monotone.map_infᵢ₂_le

/- warning: antitone.map_Sup_le -> Antitone.map_supₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))))
Case conversion may be inaccurate. Consider using '#align antitone.map_Sup_le Antitone.map_supₛ_leₓ'. -/
theorem Antitone.map_supₛ_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (supₛ s) ≤ ⨅ a ∈ s, f a := by
  rw [supₛ_eq_supᵢ]
  exact hf.map_supr₂_le _
#align antitone.map_Sup_le Antitone.map_supₛ_le

/- warning: monotone.map_Inf_le -> Monotone.map_infₛ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{u1} α} {f : α -> β}, (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a))))
Case conversion may be inaccurate. Consider using '#align monotone.map_Inf_le Monotone.map_infₛ_leₓ'. -/
theorem Monotone.map_infₛ_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (infₛ s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_supₛ_le
#align monotone.map_Inf_le Monotone.map_infₛ_le

/- warning: supr_const_le -> supᵢ_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => a)) a
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {a : α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align supr_const_le supᵢ_const_leₓ'. -/
theorem supᵢ_const_le : (⨆ i : ι, a) ≤ a :=
  supᵢ_le fun _ => le_rfl
#align supr_const_le supᵢ_const_le

/- warning: le_infi_const -> le_infᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => a))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {a : α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) a (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => a))
Case conversion may be inaccurate. Consider using '#align le_infi_const le_infᵢ_constₓ'. -/
theorem le_infᵢ_const : a ≤ ⨅ i : ι, a :=
  le_infᵢ fun _ => le_rfl
#align le_infi_const le_infᵢ_const

/- warning: supr_const -> supᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align supr_const supᵢ_constₓ'. -/
-- We generalize this to conditionally complete lattices in `csupr_const` and `cinfi_const`.
theorem supᵢ_const [Nonempty ι] : (⨆ b : ι, a) = a := by rw [supᵢ, range_const, supₛ_singleton]
#align supr_const supᵢ_const

/- warning: infi_const -> infᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (b : ι) => a)) a
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {a : α} [_inst_2 : Nonempty.{u2} ι], Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (b : ι) => a)) a
Case conversion may be inaccurate. Consider using '#align infi_const infᵢ_constₓ'. -/
theorem infᵢ_const [Nonempty ι] : (⨅ b : ι, a) = a :=
  @supᵢ_const αᵒᵈ _ _ a _
#align infi_const infᵢ_const

/- warning: supr_bot -> supᵢ_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α], Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_bot supᵢ_botₓ'. -/
@[simp]
theorem supᵢ_bot : (⨆ i : ι, ⊥ : α) = ⊥ :=
  bot_unique supᵢ_const_le
#align supr_bot supᵢ_bot

/- warning: infi_top -> infᵢ_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α], Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_top infᵢ_topₓ'. -/
@[simp]
theorem infᵢ_top : (⨅ i : ι, ⊤ : α) = ⊤ :=
  top_unique le_infᵢ_const
#align infi_top infᵢ_top

/- warning: supr_eq_bot -> supᵢ_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α}, Iff (Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (forall (i : ι), Eq.{succ u1} α (s i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α}, Iff (Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι s) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) (forall (i : ι), Eq.{succ u2} α (s i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_eq_bot supᵢ_eq_botₓ'. -/
@[simp]
theorem supᵢ_eq_bot : supᵢ s = ⊥ ↔ ∀ i, s i = ⊥ :=
  supₛ_eq_bot.trans forall_range_iff
#align supr_eq_bot supᵢ_eq_bot

/- warning: infi_eq_top -> infᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : ι -> α}, Iff (Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall (i : ι), Eq.{succ u1} α (s i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {s : ι -> α}, Iff (Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι s) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) (forall (i : ι), Eq.{succ u2} α (s i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_eq_top infᵢ_eq_topₓ'. -/
@[simp]
theorem infᵢ_eq_top : infᵢ s = ⊤ ↔ ∀ i, s i = ⊤ :=
  infₛ_eq_top.trans forall_range_iff
#align infi_eq_top infᵢ_eq_top

/- warning: supr₂_eq_bot -> supᵢ₂_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u1} α (f i j) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u3} α (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (Bot.bot.{u3} α (CompleteLattice.toBot.{u3} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u3} α (f i j) (Bot.bot.{u3} α (CompleteLattice.toBot.{u3} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr₂_eq_bot supᵢ₂_eq_botₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem supᵢ₂_eq_bot {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp_rw [supᵢ_eq_bot]
#align supr₂_eq_bot supᵢ₂_eq_bot

/- warning: infi₂_eq_top -> infᵢ₂_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u1} α (f i j) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : forall (i : ι), (κ i) -> α}, Iff (Eq.{succ u3} α (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) (κ i) (fun (j : κ i) => f i j))) (Top.top.{u3} α (CompleteLattice.toTop.{u3} α _inst_1))) (forall (i : ι) (j : κ i), Eq.{succ u3} α (f i j) (Top.top.{u3} α (CompleteLattice.toTop.{u3} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi₂_eq_top infᵢ₂_eq_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem infᵢ₂_eq_top {f : ∀ i, κ i → α} : (⨅ (i) (j), f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp_rw [infᵢ_eq_top]
#align infi₂_eq_top infᵢ₂_eq_top

/- warning: supr_pos -> supᵢ_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align supr_pos supᵢ_posₓ'. -/
@[simp]
theorem supᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  le_antisymm (supᵢ_le fun h => le_rfl) (le_supᵢ _ _)
#align supr_pos supᵢ_pos

/- warning: infi_pos -> infᵢ_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => f h)) (f hp)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α} (hp : p), Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => f h)) (f hp)
Case conversion may be inaccurate. Consider using '#align infi_pos infᵢ_posₓ'. -/
@[simp]
theorem infᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  le_antisymm (infᵢ_le _ _) (le_infᵢ fun h => le_rfl)
#align infi_pos infᵢ_pos

/- warning: supr_neg -> supᵢ_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => f h)) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => f h)) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_neg supᵢ_negₓ'. -/
@[simp]
theorem supᵢ_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h : p, f h) = ⊥ :=
  le_antisymm (supᵢ_le fun h => (hp h).elim) bot_le
#align supr_neg supᵢ_neg

/- warning: infi_neg -> infᵢ_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => f h)) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {f : p -> α}, (Not p) -> (Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => f h)) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_neg infᵢ_negₓ'. -/
@[simp]
theorem infᵢ_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨅ h : p, f h) = ⊤ :=
  le_antisymm le_top <| le_infᵢ fun h => (hp h).elim
#align infi_neg infᵢ_neg

/- warning: supr_eq_of_forall_le_of_forall_lt_exists_gt -> supᵢ_eq_of_forall_le_of_forall_lt_exists_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : α} {f : ι -> α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) b) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w b) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) w (f i)))) -> (Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {b : α} {f : ι -> α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) b) -> (forall (w : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) w b) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) w (f i)))) -> (Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align supr_eq_of_forall_le_of_forall_lt_exists_gt supᵢ_eq_of_forall_le_of_forall_lt_exists_gtₓ'. -/
/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supᵢ_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  supₛ_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw
#align supr_eq_of_forall_le_of_forall_lt_exists_gt supᵢ_eq_of_forall_le_of_forall_lt_exists_gt

/- warning: infi_eq_of_forall_ge_of_forall_gt_exists_lt -> infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {b : α}, (forall (i : ι), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b (f i)) -> (forall (w : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b w) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (f i) w))) -> (Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i)) b)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {b : α}, (forall (i : ι), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b (f i)) -> (forall (w : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) b w) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (f i) w))) -> (Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) b)
Case conversion may be inaccurate. Consider using '#align infi_eq_of_forall_ge_of_forall_gt_exists_lt infᵢ_eq_of_forall_ge_of_forall_gt_exists_ltₓ'. -/
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ i, b ≤ f i) → (∀ w, b < w → ∃ i, f i < w) → (⨅ i, f i) = b :=
  @supᵢ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _
#align infi_eq_of_forall_ge_of_forall_gt_exists_lt infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt

/- warning: supr_eq_dif -> supᵢ_eq_dif is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_eq_dif supᵢ_eq_difₓ'. -/
theorem supᵢ_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨆ h : p, a h) = if h : p then a h else ⊥ := by by_cases p <;> simp [h]
#align supr_eq_dif supᵢ_eq_dif

/- warning: supr_eq_if -> supᵢ_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align supr_eq_if supᵢ_eq_ifₓ'. -/
theorem supᵢ_eq_if {p : Prop} [Decidable p] (a : α) : (⨆ h : p, a) = if p then a else ⊥ :=
  supᵢ_eq_dif fun _ => a
#align supr_eq_if supᵢ_eq_if

/- warning: infi_eq_dif -> infᵢ_eq_dif is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : p -> α), Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => a h)) (dite.{succ u1} α p _inst_2 (fun (h : p) => a h) (fun (h : Not p) => Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_eq_dif infᵢ_eq_difₓ'. -/
theorem infᵢ_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨅ h : p, a h) = if h : p then a h else ⊤ :=
  @supᵢ_eq_dif αᵒᵈ _ _ _ _
#align infi_eq_dif infᵢ_eq_dif

/- warning: infi_eq_if -> infᵢ_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} [_inst_2 : Decidable p] (a : α), Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h : p) => a)) (ite.{succ u1} α p _inst_2 a (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align infi_eq_if infᵢ_eq_ifₓ'. -/
theorem infᵢ_eq_if {p : Prop} [Decidable p] (a : α) : (⨅ h : p, a) = if p then a else ⊤ :=
  infᵢ_eq_dif fun _ => a
#align infi_eq_if infᵢ_eq_if

/- warning: supr_comm -> supᵢ_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> ι' -> α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (j : ι') => f i j))) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι' (fun (j : ι') => supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : ι -> ι' -> α}, Eq.{succ u3} α (supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (j : ι') => f i j))) (supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι' (fun (j : ι') => supᵢ.{u3, u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => f i j)))
Case conversion may be inaccurate. Consider using '#align supr_comm supᵢ_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (j i) -/
theorem supᵢ_comm {f : ι → ι' → α} : (⨆ (i) (j), f i j) = ⨆ (j) (i), f i j :=
  le_antisymm (supᵢ_le fun i => supᵢ_mono fun j => le_supᵢ _ i)
    (supᵢ_le fun j => supᵢ_mono fun i => le_supᵢ _ _)
#align supr_comm supᵢ_comm

/- warning: infi_comm -> infᵢ_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {ι' : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> ι' -> α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => f i j))) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι' (fun (j : ι') => infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i j)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {f : ι -> ι' -> α}, Eq.{succ u3} α (infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => f i j))) (infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι' (fun (j : ι') => infᵢ.{u3, u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => f i j)))
Case conversion may be inaccurate. Consider using '#align infi_comm infᵢ_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (j i) -/
theorem infᵢ_comm {f : ι → ι' → α} : (⨅ (i) (j), f i j) = ⨅ (j) (i), f i j :=
  @supᵢ_comm αᵒᵈ _ _ _ _
#align infi_comm infᵢ_comm

/- warning: supr₂_comm -> supᵢ₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u2}} {ι₂ : Sort.{u3}} {κ₁ : ι₁ -> Sort.{u4}} {κ₂ : ι₂ -> Sort.{u5}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => supᵢ.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => supᵢ.{u1, u5} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => supᵢ.{u1, u5} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => supᵢ.{u1, u4} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u5}} {ι₂ : Sort.{u4}} {κ₁ : ι₁ -> Sort.{u3}} {κ₂ : ι₂ -> Sort.{u2}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (supᵢ.{u1, u5} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => supᵢ.{u1, u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => supᵢ.{u1, u4} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (supᵢ.{u1, u4} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => supᵢ.{u1, u5} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => supᵢ.{u1, u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align supr₂_comm supᵢ₂_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem supᵢ₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@supᵢ_comm _ (κ₁ _), @supᵢ_comm _ ι₁]
#align supr₂_comm supᵢ₂_comm

/- warning: infi₂_comm -> infᵢ₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u2}} {ι₂ : Sort.{u3}} {κ₁ : ι₁ -> Sort.{u4}} {κ₂ : ι₂ -> Sort.{u5}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => infᵢ.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => infᵢ.{u1, u5} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₂ (fun (i₂ : ι₂) => infᵢ.{u1, u5} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι₁ (fun (i₁ : ι₁) => infᵢ.{u1, u4} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι₁ : Sort.{u5}} {ι₂ : Sort.{u4}} {κ₁ : ι₁ -> Sort.{u3}} {κ₂ : ι₂ -> Sort.{u2}} (f : forall (i₁ : ι₁), (κ₁ i₁) -> (forall (i₂ : ι₂), (κ₂ i₂) -> α)), Eq.{succ u1} α (infᵢ.{u1, u5} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => infᵢ.{u1, u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => infᵢ.{u1, u4} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => f i₁ j₁ i₂ j₂))))) (infᵢ.{u1, u4} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₂ (fun (i₂ : ι₂) => infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₂ i₂) (fun (j₂ : κ₂ i₂) => infᵢ.{u1, u5} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι₁ (fun (i₁ : ι₁) => infᵢ.{u1, u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) (κ₁ i₁) (fun (j₁ : κ₁ i₁) => f i₁ j₁ i₂ j₂)))))
Case conversion may be inaccurate. Consider using '#align infi₂_comm infᵢ₂_commₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem infᵢ₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨅ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨅ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@infᵢ_comm _ (κ₁ _), @infᵢ_comm _ ι₁]
#align infi₂_comm infᵢ₂_comm

/- warning: supr_supr_eq_left -> supᵢ_supᵢ_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align supr_supr_eq_left supᵢ_supᵢ_eq_leftₓ'. -/
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
theorem supᵢ_supᵢ_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨆ x, ⨆ h : x = b, f x h) = f b rfl :=
  (@le_supᵢ₂ _ _ _ _ f b rfl).antisymm'
    (supᵢ_le fun c =>
      supᵢ_le <| by
        rintro rfl
        rfl)
#align supr_supr_eq_left supᵢ_supᵢ_eq_left

/- warning: infi_infi_eq_left -> infᵢ_infᵢ_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β x b) -> α}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Eq.{succ u2} β x b) (fun (h : Eq.{succ u2} β x b) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align infi_infi_eq_left infᵢ_infᵢ_eq_leftₓ'. -/
@[simp]
theorem infᵢ_infᵢ_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
  @supᵢ_supᵢ_eq_left αᵒᵈ _ _ _ _
#align infi_infi_eq_left infᵢ_infᵢ_eq_left

/- warning: supr_supr_eq_right -> supᵢ_supᵢ_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align supr_supr_eq_right supᵢ_supᵢ_eq_rightₓ'. -/
@[simp]
theorem supᵢ_supᵢ_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
  (le_supᵢ₂ b rfl).antisymm'
    (supᵢ₂_le fun c => by
      rintro rfl
      rfl)
#align supr_supr_eq_right supᵢ_supᵢ_eq_right

/- warning: infi_infi_eq_right -> infᵢ_infᵢ_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {b : β} {f : forall (x : β), (Eq.{succ u2} β b x) -> α}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Eq.{succ u2} β b x) (fun (h : Eq.{succ u2} β b x) => f x h))) (f b (rfl.{succ u2} β b))
Case conversion may be inaccurate. Consider using '#align infi_infi_eq_right infᵢ_infᵢ_eq_rightₓ'. -/
@[simp]
theorem infᵢ_infᵢ_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
  @supᵢ_supᵢ_eq_right αᵒᵈ _ _ _ _
#align infi_infi_eq_right infᵢ_infᵢ_eq_right

attribute [ematch] le_refl

/- warning: supr_subtype -> supᵢ_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (supᵢ.{u1, max 1 u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Subtype.{u2} ι p) f) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (supᵢ.{u1, max 1 u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Subtype.{u2} ι p) f) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align supr_subtype supᵢ_subtypeₓ'. -/
theorem supᵢ_subtype {p : ι → Prop} {f : Subtype p → α} : supᵢ f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => le_supᵢ₂ i h) (supᵢ₂_le fun i h => le_supᵢ _ _)
#align supr_subtype supᵢ_subtype

/- warning: infi_subtype -> infᵢ_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (infᵢ.{u1, max 1 u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Subtype.{u2} ι p) f) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Subtype.{u2} ι p) -> α}, Eq.{succ u1} α (infᵢ.{u1, max 1 u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Subtype.{u2} ι p) f) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Subtype.mk.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align infi_subtype infᵢ_subtypeₓ'. -/
theorem infᵢ_subtype : ∀ {p : ι → Prop} {f : Subtype p → α}, infᵢ f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  @supᵢ_subtype αᵒᵈ _ _
#align infi_subtype infᵢ_subtype

/- warning: supr_subtype' -> supᵢ_subtype' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (supᵢ.{u1, max 1 u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Subtype.{u2} ι p) (fun (x : Subtype.{u2} ι p) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι p) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι p) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeSubtype.{u2} ι (fun (x : ι) => p x))))) x) (Subtype.property.{u2} ι p x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (supᵢ.{u2, max 1 u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Subtype.{u1} ι p) (fun (x : Subtype.{u1} ι p) => f (Subtype.val.{u1} ι p x) (Subtype.property.{u1} ι p x)))
Case conversion may be inaccurate. Consider using '#align supr_subtype' supᵢ_subtype'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
theorem supᵢ_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨆ (i) (h), f i h) = ⨆ x : Subtype p, f x x.property :=
  (@supᵢ_subtype _ _ _ p fun x => f x.val x.property).symm
#align supr_subtype' supᵢ_subtype'

/- warning: infi_subtype' -> infᵢ_subtype' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (infᵢ.{u1, max 1 u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Subtype.{u2} ι p) (fun (x : Subtype.{u2} ι p) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι p) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι p) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι p) ι (coeSubtype.{u2} ι (fun (x : ι) => p x))))) x) (Subtype.property.{u2} ι p x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α}, Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (infᵢ.{u2, max 1 u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Subtype.{u1} ι p) (fun (x : Subtype.{u1} ι p) => f (Subtype.val.{u1} ι p x) (Subtype.property.{u1} ι p x)))
Case conversion may be inaccurate. Consider using '#align infi_subtype' infᵢ_subtype'ₓ'. -/
theorem infᵢ_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨅ (i) (h : p i), f i h) = ⨅ x : Subtype p, f x x.property :=
  (@infᵢ_subtype _ _ _ p fun x => f x.val x.property).symm
#align infi_subtype' infᵢ_subtype'

/- warning: supr_subtype'' -> supᵢ_subtype'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (t : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) => f t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (t : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) => f t)))
Case conversion may be inaccurate. Consider using '#align supr_subtype'' supᵢ_subtype''ₓ'. -/
theorem supᵢ_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨆ i : s, f i) = ⨆ (t : ι) (H : t ∈ s), f t :=
  supᵢ_subtype
#align supr_subtype'' supᵢ_subtype''

/- warning: infi_subtype'' -> infᵢ_subtype'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) => f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s))))) i))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (t : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) t s) => f t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} (s : Set.{u2} ι) (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.Elem.{u2} ι s) (fun (i : Set.Elem.{u2} ι s) => f (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x s) i))) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (t : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) t s) => f t)))
Case conversion may be inaccurate. Consider using '#align infi_subtype'' infᵢ_subtype''ₓ'. -/
theorem infᵢ_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
  infᵢ_subtype
#align infi_subtype'' infᵢ_subtype''

/- warning: bsupr_const -> bsupᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => a))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => a))) a)
Case conversion may be inaccurate. Consider using '#align bsupr_const bsupᵢ_constₓ'. -/
theorem bsupᵢ_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨆ i ∈ s, a) = a :=
  by
  haveI : Nonempty s := set.nonempty_coe_sort.mpr hs
  rw [← supᵢ_subtype'', supᵢ_const]
#align bsupr_const bsupᵢ_const

/- warning: binfi_const -> binfᵢ_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => a))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Type.{u2}} {a : α} {s : Set.{u2} ι}, (Set.Nonempty.{u2} ι s) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => a))) a)
Case conversion may be inaccurate. Consider using '#align binfi_const binfᵢ_constₓ'. -/
theorem binfᵢ_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨅ i ∈ s, a) = a :=
  @bsupᵢ_const αᵒᵈ _ ι _ s hs
#align binfi_const binfᵢ_const

/- warning: supr_sup_eq -> supᵢ_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) (g x))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f x)) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => g x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f x) (g x))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => f x)) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (x : ι) => g x)))
Case conversion may be inaccurate. Consider using '#align supr_sup_eq supᵢ_sup_eqₓ'. -/
theorem supᵢ_sup_eq : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (supᵢ_le fun i => sup_le_sup (le_supᵢ _ _) <| le_supᵢ _ _)
    (sup_le (supᵢ_mono fun i => le_sup_left) <| supᵢ_mono fun i => le_sup_right)
#align supr_sup_eq supᵢ_sup_eq

/- warning: infi_inf_eq -> infᵢ_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) (g x))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f x)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => g x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f x) (g x))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => f x)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (x : ι) => g x)))
Case conversion may be inaccurate. Consider using '#align infi_inf_eq infᵢ_inf_eqₓ'. -/
theorem infᵢ_inf_eq : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ ⨅ x, g x :=
  @supᵢ_sup_eq αᵒᵈ _ _ _ _
#align infi_inf_eq infᵢ_inf_eq

/- warning: supr_sup -> supᵢ_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f x)) a) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => f x)) a) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) a))
Case conversion may be inaccurate. Consider using '#align supr_sup supᵢ_supₓ'. -/
/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem supᵢ_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [supᵢ_sup_eq, supᵢ_const]
#align supr_sup supᵢ_sup

/- warning: infi_inf -> infᵢ_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f x)) a) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f x) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => f x)) a) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f x) a))
Case conversion may be inaccurate. Consider using '#align infi_inf infᵢ_infₓ'. -/
theorem infᵢ_inf [Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a := by
  rw [infᵢ_inf_eq, infᵢ_const]
#align infi_inf infᵢ_inf

/- warning: sup_supr -> sup_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => f x))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (x : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f x)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => f x))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (x : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f x)))
Case conversion may be inaccurate. Consider using '#align sup_supr sup_supᵢₓ'. -/
theorem sup_supᵢ [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [supᵢ_sup_eq, supᵢ_const]
#align sup_supr sup_supᵢ

/- warning: inf_infi -> inf_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => f x))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (x : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f x)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : Nonempty.{u2} ι] {f : ι -> α} {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => f x))) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (x : ι) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (f x)))
Case conversion may be inaccurate. Consider using '#align inf_infi inf_infᵢₓ'. -/
theorem inf_infᵢ [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ ⨅ x, f x) = ⨅ x, a ⊓ f x := by
  rw [infᵢ_inf_eq, infᵢ_const]
#align inf_infi inf_infᵢ

/- warning: bsupr_sup -> bsupᵢ_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) a) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i h) a))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h))) a) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i h) a))))
Case conversion may be inaccurate. Consider using '#align bsupr_sup bsupᵢ_supₓ'. -/
theorem bsupᵢ_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
      let ⟨i, hi⟩ := h
      ⟨⟨i, hi⟩⟩ <;>
    rw [supᵢ_subtype', supᵢ_subtype', supᵢ_sup]
#align bsupr_sup bsupᵢ_sup

/- warning: sup_bsupr -> sup_bsupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f i h)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h)))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f i h)))))
Case conversion may be inaccurate. Consider using '#align sup_bsupr sup_bsupᵢₓ'. -/
theorem sup_bsupᵢ {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using bsupᵢ_sup h
#align sup_bsupr sup_bsupᵢ

/- warning: binfi_inf -> binfᵢ_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) a) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i h) a))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h))) a) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f i h) a))))
Case conversion may be inaccurate. Consider using '#align binfi_inf binfᵢ_infₓ'. -/
theorem binfᵢ_inf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h) ⊓ a = ⨅ (i) (h : p i), f i h ⊓ a :=
  @bsupᵢ_sup αᵒᵈ ι _ p f _ h
#align binfi_inf binfᵢ_inf

/- warning: inf_binfi -> inf_binfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (f i h)))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α} {a : α}, (Exists.{u2} ι (fun (i : ι) => p i)) -> (Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f i h)))) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (f i h)))))
Case conversion may be inaccurate. Consider using '#align inf_binfi inf_binfᵢₓ'. -/
theorem inf_binfᵢ {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊓ ⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a ⊓ f i h :=
  @sup_bsupᵢ αᵒᵈ ι _ p f _ h
#align inf_binfi inf_binfᵢ

/-! ### `supr` and `infi` under `Prop` -/


/- warning: supr_false -> supᵢ_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) False s) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) False s) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_false supᵢ_falseₓ'. -/
@[simp]
theorem supᵢ_false {s : False → α} : supᵢ s = ⊥ :=
  le_antisymm (supᵢ_le fun i => False.elim i) bot_le
#align supr_false supᵢ_false

/- warning: infi_false -> infᵢ_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) False s) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : False -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) False s) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_false infᵢ_falseₓ'. -/
@[simp]
theorem infᵢ_false {s : False → α} : infᵢ s = ⊤ :=
  le_antisymm le_top (le_infᵢ fun i => False.elim i)
#align infi_false infᵢ_false

/- warning: supr_true -> supᵢ_true is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) True s) (s trivial)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) True s) (s trivial)
Case conversion may be inaccurate. Consider using '#align supr_true supᵢ_trueₓ'. -/
theorem supᵢ_true {s : True → α} : supᵢ s = s trivial :=
  supᵢ_pos trivial
#align supr_true supᵢ_true

/- warning: infi_true -> infᵢ_true is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) True s) (s trivial)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {s : True -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) True s) (s trivial)
Case conversion may be inaccurate. Consider using '#align infi_true infᵢ_trueₓ'. -/
theorem infᵢ_true {s : True → α} : infᵢ s = s trivial :=
  infᵢ_pos trivial
#align infi_true infᵢ_true

/- warning: supr_exists -> supᵢ_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align supr_exists supᵢ_existsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
@[simp]
theorem supᵢ_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => le_supᵢ₂ i h) (supᵢ₂_le fun i h => le_supᵢ _ _)
#align supr_exists supᵢ_exists

/- warning: infi_exists -> infᵢ_exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {f : (Exists.{u2} ι p) -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Exists.{u2} ι p) (fun (x : Exists.{u2} ι p) => f x)) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (h : p i) => f (Exists.intro.{u2} ι p i h))))
Case conversion may be inaccurate. Consider using '#align infi_exists infᵢ_existsₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
@[simp]
theorem infᵢ_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ (i) (h), f ⟨i, h⟩ :=
  @supᵢ_exists αᵒᵈ _ _ _ _
#align infi_exists infᵢ_exists

/- warning: supr_and -> supᵢ_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (And p q) s) (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h₁ : p) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (And p q) s) (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h₁ : p) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
Case conversion may be inaccurate. Consider using '#align supr_and supᵢ_andₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (h₁ h₂) -/
theorem supᵢ_and {p q : Prop} {s : p ∧ q → α} : supᵢ s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => le_supᵢ₂ i h) (supᵢ₂_le fun i h => le_supᵢ _ _)
#align supr_and supᵢ_and

/- warning: infi_and -> infᵢ_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (And p q) s) (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h₁ : p) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (And p q) -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (And p q) s) (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h₁ : p) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) q (fun (h₂ : q) => s (And.intro p q h₁ h₂))))
Case conversion may be inaccurate. Consider using '#align infi_and infᵢ_andₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (h₁ h₂) -/
theorem infᵢ_and {p q : Prop} {s : p ∧ q → α} : infᵢ s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @supᵢ_and αᵒᵈ _ _ _ _
#align infi_and infᵢ_and

/- warning: supr_and' -> supᵢ_and' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (h₁ : p) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) q (fun (h₂ : q) => s h₁ h₂))) (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (h₁ : p) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) q (fun (h₂ : q) => s h₁ h₂))) (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
Case conversion may be inaccurate. Consider using '#align supr_and' supᵢ_and'ₓ'. -/
/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
theorem supᵢ_and' {p q : Prop} {s : p → q → α} :
    (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm supᵢ_and
#align supr_and' supᵢ_and'

/- warning: infi_and' -> infᵢ_and' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (h₁ : p) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) q (fun (h₂ : q) => s h₁ h₂))) (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : p -> q -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (h₁ : p) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) q (fun (h₂ : q) => s h₁ h₂))) (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (And p q) (fun (h : And p q) => s (And.left p q h) (And.right p q h)))
Case conversion may be inaccurate. Consider using '#align infi_and' infᵢ_and'ₓ'. -/
/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
theorem infᵢ_and' {p q : Prop} {s : p → q → α} :
    (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ h : p ∧ q, s h.1 h.2 :=
  Eq.symm infᵢ_and
#align infi_and' infᵢ_and'

/- warning: supr_or -> supᵢ_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Or p q) (fun (x : Or p q) => s x)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) p (fun (i : p) => s (Or.inl p q i))) (supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) q (fun (j : q) => s (Or.inr p q j))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Or p q) (fun (x : Or p q) => s x)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) p (fun (i : p) => s (Or.inl p q i))) (supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) q (fun (j : q) => s (Or.inr p q j))))
Case conversion may be inaccurate. Consider using '#align supr_or supᵢ_orₓ'. -/
theorem supᵢ_or {p q : Prop} {s : p ∨ q → α} :
    (⨆ x, s x) = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (supᵢ_le fun i =>
      match i with
      | Or.inl i => le_sup_of_le_left <| le_supᵢ _ i
      | Or.inr j => le_sup_of_le_right <| le_supᵢ _ j)
    (sup_le (supᵢ_comp_le _ _) (supᵢ_comp_le _ _))
#align supr_or supᵢ_or

/- warning: infi_or -> infᵢ_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Or p q) (fun (x : Or p q) => s x)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) p (fun (i : p) => s (Or.inl p q i))) (infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) q (fun (j : q) => s (Or.inr p q j))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Prop} {q : Prop} {s : (Or p q) -> α}, Eq.{succ u1} α (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Or p q) (fun (x : Or p q) => s x)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) p (fun (i : p) => s (Or.inl p q i))) (infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) q (fun (j : q) => s (Or.inr p q j))))
Case conversion may be inaccurate. Consider using '#align infi_or infᵢ_orₓ'. -/
theorem infᵢ_or {p q : Prop} {s : p ∨ q → α} :
    (⨅ x, s x) = (⨅ i, s (Or.inl i)) ⊓ ⨅ j, s (Or.inr j) :=
  @supᵢ_or αᵒᵈ _ _ _ _
#align infi_or infᵢ_or

section

variable (p : ι → Prop) [DecidablePred p]

/- warning: supr_dite -> supᵢ_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => dite.{succ u1} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i h))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => dite.{succ u2} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i h))))
Case conversion may be inaccurate. Consider using '#align supr_dite supᵢ_diteₓ'. -/
theorem supᵢ_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨆ i, if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i), g i h :=
  by
  rw [← supᵢ_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]
#align supr_dite supᵢ_dite

/- warning: infi_dite -> infᵢ_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => dite.{succ u1} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i h))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i h))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : forall (i : ι), (p i) -> α) (g : forall (i : ι), (Not (p i)) -> α), Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => dite.{succ u2} α (p i) (_inst_2 i) (fun (h : p i) => f i h) (fun (h : Not (p i)) => g i h))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i h))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i h))))
Case conversion may be inaccurate. Consider using '#align infi_dite infᵢ_diteₓ'. -/
theorem infᵢ_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨅ i, if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h) ⊓ ⨅ (i) (h : ¬p i), g i h :=
  supᵢ_dite p (show ∀ i, p i → αᵒᵈ from f) g
#align infi_dite infᵢ_dite

/- warning: supr_ite -> supᵢ_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => ite.{succ u1} α (p i) (_inst_2 i) (f i) (g i))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => ite.{succ u2} α (p i) (_inst_2 i) (f i) (g i))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i))))
Case conversion may be inaccurate. Consider using '#align supr_ite supᵢ_iteₓ'. -/
theorem supᵢ_ite (f g : ι → α) :
    (⨆ i, if p i then f i else g i) = (⨆ (i) (h : p i), f i) ⊔ ⨆ (i) (h : ¬p i), g i :=
  supᵢ_dite _ _ _
#align supr_ite supᵢ_ite

/- warning: infi_ite -> infᵢ_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u2} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => ite.{succ u1} α (p i) (_inst_2 i) (f i) (g i))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => g i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (p : ι -> Prop) [_inst_2 : DecidablePred.{u1} ι p] (f : ι -> α) (g : ι -> α), Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => ite.{succ u2} α (p i) (_inst_2 i) (f i) (g i))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => g i))))
Case conversion may be inaccurate. Consider using '#align infi_ite infᵢ_iteₓ'. -/
theorem infᵢ_ite (f g : ι → α) :
    (⨅ i, if p i then f i else g i) = (⨅ (i) (h : p i), f i) ⊓ ⨅ (i) (h : ¬p i), g i :=
  infᵢ_dite _ _ _
#align infi_ite infᵢ_ite

end

/- warning: supr_range -> supᵢ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {g : β -> α} {f : ι -> β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) => g b))) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {g : β -> α} {f : ι -> β}, Eq.{succ u3} α (supᵢ.{u3, succ u2} α (CompleteLattice.toSupSet.{u3} α _inst_1) β (fun (b : β) => supᵢ.{u3, 0} α (CompleteLattice.toSupSet.{u3} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) => g b))) (supᵢ.{u3, u1} α (CompleteLattice.toSupSet.{u3} α _inst_1) ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align supr_range supᵢ_rangeₓ'. -/
theorem supᵢ_range {g : β → α} {f : ι → β} : (⨆ b ∈ range f, g b) = ⨆ i, g (f i) := by
  rw [← supᵢ_subtype'', supᵢ_range']
#align supr_range supᵢ_range

/- warning: infi_range -> infᵢ_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {g : β -> α} {f : ι -> β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, u3} β ι f)) => g b))) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => g (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] {g : β -> α} {f : ι -> β}, Eq.{succ u3} α (infᵢ.{u3, succ u2} α (CompleteLattice.toInfSet.{u3} α _inst_1) β (fun (b : β) => infᵢ.{u3, 0} α (CompleteLattice.toInfSet.{u3} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.range.{u2, u1} β ι f)) => g b))) (infᵢ.{u3, u1} α (CompleteLattice.toInfSet.{u3} α _inst_1) ι (fun (i : ι) => g (f i)))
Case conversion may be inaccurate. Consider using '#align infi_range infᵢ_rangeₓ'. -/
theorem infᵢ_range : ∀ {g : β → α} {f : ι → β}, (⨅ b ∈ range f, g b) = ⨅ i, g (f i) :=
  @supᵢ_range αᵒᵈ _ _ _
#align infi_range infᵢ_range

/- warning: Sup_image -> supₛ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.image.{u2, u1} β α f s)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (a : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.image.{u2, u1} β α f s)) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (a : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) => f a)))
Case conversion may be inaccurate. Consider using '#align Sup_image supₛ_imageₓ'. -/
theorem supₛ_image {s : Set β} {f : β → α} : supₛ (f '' s) = ⨆ a ∈ s, f a := by
  rw [← supᵢ_subtype'', supₛ_image']
#align Sup_image supₛ_image

/- warning: Inf_image -> infₛ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Set.image.{u2, u1} β α f s)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (a : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.image.{u2, u1} β α f s)) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (a : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) => f a)))
Case conversion may be inaccurate. Consider using '#align Inf_image infₛ_imageₓ'. -/
theorem infₛ_image {s : Set β} {f : β → α} : infₛ (f '' s) = ⨅ a ∈ s, f a :=
  @supₛ_image αᵒᵈ _ _ _ _
#align Inf_image infₛ_image

/- warning: supr_emptyset -> supᵢ_emptyset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) => f x))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) => f x))) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_emptyset supᵢ_emptysetₓ'. -/
/-
### supr and infi under set constructions
-/
theorem supᵢ_emptyset {f : β → α} : (⨆ x ∈ (∅ : Set β), f x) = ⊥ := by simp
#align supr_emptyset supᵢ_emptyset

/- warning: infi_emptyset -> infᵢ_emptyset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) => f x))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) => f x))) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_emptyset infᵢ_emptysetₓ'. -/
theorem infᵢ_emptyset {f : β → α} : (⨅ x ∈ (∅ : Set β), f x) = ⊤ := by simp
#align infi_emptyset infᵢ_emptyset

/- warning: supr_univ -> supᵢ_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) => f x))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) => f x))) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => f x))
Case conversion may be inaccurate. Consider using '#align supr_univ supᵢ_univₓ'. -/
theorem supᵢ_univ {f : β → α} : (⨆ x ∈ (univ : Set β), f x) = ⨆ x, f x := by simp
#align supr_univ supᵢ_univ

/- warning: infi_univ -> infᵢ_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.univ.{u2} β)) => f x))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α}, Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.univ.{u1} β)) => f x))) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => f x))
Case conversion may be inaccurate. Consider using '#align infi_univ infᵢ_univₓ'. -/
theorem infᵢ_univ {f : β → α} : (⨅ x ∈ (univ : Set β), f x) = ⨅ x, f x := by simp
#align infi_univ infᵢ_univ

/- warning: supr_union -> supᵢ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) => f x))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) => f x))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align supr_union supᵢ_unionₓ'. -/
theorem supᵢ_union {f : β → α} {s t : Set β} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x :=
  by simp_rw [mem_union, supᵢ_or, supᵢ_sup_eq]
#align supr_union supᵢ_union

/- warning: infi_union -> infᵢ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s t)) => f x))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) s t)) => f x))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align infi_union infᵢ_unionₓ'. -/
theorem infᵢ_union {f : β → α} {s t : Set β} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @supᵢ_union αᵒᵈ _ _ _ _ _
#align infi_union infᵢ_union

/- warning: supr_split -> supᵢ_split is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (p : β -> Prop), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => f i)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (p : β -> Prop), Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => f i)) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => f i))))
Case conversion may be inaccurate. Consider using '#align supr_split supᵢ_splitₓ'. -/
theorem supᵢ_split (f : β → α) (p : β → Prop) :
    (⨆ i, f i) = (⨆ (i) (h : p i), f i) ⊔ ⨆ (i) (h : ¬p i), f i := by
  simpa [Classical.em] using @supᵢ_union _ _ _ f { i | p i } { i | ¬p i }
#align supr_split supᵢ_split

/- warning: infi_split -> infᵢ_split is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (p : β -> Prop), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => f i)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (h : p i) => f i))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Not (p i)) (fun (h : Not (p i)) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (p : β -> Prop), Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => f i)) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (p i) (fun (h : p i) => f i))) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Not (p i)) (fun (h : Not (p i)) => f i))))
Case conversion may be inaccurate. Consider using '#align infi_split infᵢ_splitₓ'. -/
theorem infᵢ_split :
    ∀ (f : β → α) (p : β → Prop), (⨅ i, f i) = (⨅ (i) (h : p i), f i) ⊓ ⨅ (i) (h : ¬p i), f i :=
  @supᵢ_split αᵒᵈ _ _
#align infi_split infᵢ_split

/- warning: supr_split_single -> supᵢ_split_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (i₀ : β), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => f i)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i₀) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Ne.{succ u2} β i i₀) (fun (h : Ne.{succ u2} β i i₀) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (i₀ : β), Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => f i)) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f i₀) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (i : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Ne.{succ u1} β i i₀) (fun (h : Ne.{succ u1} β i i₀) => f i))))
Case conversion may be inaccurate. Consider using '#align supr_split_single supᵢ_split_singleₓ'. -/
theorem supᵢ_split_single (f : β → α) (i₀ : β) : (⨆ i, f i) = f i₀ ⊔ ⨆ (i) (h : i ≠ i₀), f i :=
  by
  convert supᵢ_split _ _
  simp
#align supr_split_single supᵢ_split_single

/- warning: infi_split_single -> infᵢ_split_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : β -> α) (i₀ : β), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => f i)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i₀) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Ne.{succ u2} β i i₀) (fun (h : Ne.{succ u2} β i i₀) => f i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : β -> α) (i₀ : β), Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => f i)) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f i₀) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (i : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Ne.{succ u1} β i i₀) (fun (h : Ne.{succ u1} β i i₀) => f i))))
Case conversion may be inaccurate. Consider using '#align infi_split_single infᵢ_split_singleₓ'. -/
theorem infᵢ_split_single (f : β → α) (i₀ : β) : (⨅ i, f i) = f i₀ ⊓ ⨅ (i) (h : i ≠ i₀), f i :=
  @supᵢ_split_single αᵒᵈ _ _ _ _
#align infi_split_single infᵢ_split_single

/- warning: supr_le_supr_of_subset -> supᵢ_le_supᵢ_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))))
Case conversion may be inaccurate. Consider using '#align supr_le_supr_of_subset supᵢ_le_supᵢ_of_subsetₓ'. -/
theorem supᵢ_le_supᵢ_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨆ x ∈ s, f x) ≤ ⨆ x ∈ t, f x :=
  bsupᵢ_mono
#align supr_le_supr_of_subset supᵢ_le_supᵢ_of_subset

/- warning: infi_le_infi_of_subset -> infᵢ_le_infᵢ_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) => f x))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) s t) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) => f x))) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align infi_le_infi_of_subset infᵢ_le_infᵢ_of_subsetₓ'. -/
theorem infᵢ_le_infᵢ_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨅ x ∈ t, f x) ≤ ⨅ x ∈ s, f x :=
  binfᵢ_mono
#align infi_le_infi_of_subset infᵢ_le_infᵢ_of_subset

/- warning: supr_insert -> supᵢ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) => f x))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f b) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) => f x))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f b) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align supr_insert supᵢ_insertₓ'. -/
theorem supᵢ_insert {f : β → α} {s : Set β} {b : β} :
    (⨆ x ∈ insert b s, f x) = f b ⊔ ⨆ x ∈ s, f x :=
  Eq.trans supᵢ_union <| congr_arg (fun x => x ⊔ ⨆ x ∈ s, f x) supᵢ_supᵢ_eq_left
#align supr_insert supᵢ_insert

/- warning: infi_insert -> infᵢ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b s)) => f x))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f b) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {s : Set.{u2} β} {b : β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.instInsertSet.{u2} β) b s)) => f x))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f b) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x))))
Case conversion may be inaccurate. Consider using '#align infi_insert infᵢ_insertₓ'. -/
theorem infᵢ_insert {f : β → α} {s : Set β} {b : β} :
    (⨅ x ∈ insert b s, f x) = f b ⊓ ⨅ x ∈ s, f x :=
  Eq.trans infᵢ_union <| congr_arg (fun x => x ⊓ ⨅ x ∈ s, f x) infᵢ_infᵢ_eq_left
#align infi_insert infᵢ_insert

/- warning: supr_singleton -> supᵢ_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {b : β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) => f x))) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {b : β}, Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) => f x))) (f b)
Case conversion may be inaccurate. Consider using '#align supr_singleton supᵢ_singletonₓ'. -/
theorem supᵢ_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : Set β), f x) = f b := by simp
#align supr_singleton supᵢ_singleton

/- warning: infi_singleton -> infᵢ_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {b : β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) => f x))) (f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {b : β}, Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) => f x))) (f b)
Case conversion may be inaccurate. Consider using '#align infi_singleton infᵢ_singletonₓ'. -/
theorem infᵢ_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : Set β), f x) = f b := by simp
#align infi_singleton infᵢ_singleton

/- warning: supr_pair -> supᵢ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) => f x))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f a) (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (x : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) => f x))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f a) (f b))
Case conversion may be inaccurate. Consider using '#align supr_pair supᵢ_pairₓ'. -/
theorem supᵢ_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : Set β), f x) = f a ⊔ f b := by
  rw [supᵢ_insert, supᵢ_singleton]
#align supr_pair supᵢ_pair

/- warning: infi_pair -> infᵢ_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) a (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) => f x))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f a) (f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : β -> α} {a : β} {b : β}, Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (x : β) => infᵢ.{u2, 0} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) a (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) => f x))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f a) (f b))
Case conversion may be inaccurate. Consider using '#align infi_pair infᵢ_pairₓ'. -/
theorem infᵢ_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : Set β), f x) = f a ⊓ f b := by
  rw [infᵢ_insert, infᵢ_singleton]
#align infi_pair infᵢ_pair

/- warning: supr_image -> supᵢ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (c : γ) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) => g (f b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (c : γ) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (b : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) => g (f b))))
Case conversion may be inaccurate. Consider using '#align supr_image supᵢ_imageₓ'. -/
theorem supᵢ_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    (⨆ c ∈ f '' t, g c) = ⨆ b ∈ t, g (f b) := by rw [← supₛ_image, ← supₛ_image, ← image_comp]
#align supr_image supᵢ_image

/- warning: infi_image -> infᵢ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (c : γ) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) => g (f b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {γ : Type.{u3}} {f : β -> γ} {g : γ -> α} {t : Set.{u2} β}, Eq.{succ u1} α (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (c : γ) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) (fun (H : Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) c (Set.image.{u2, u3} β γ f t)) => g c))) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (b : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b t) => g (f b))))
Case conversion may be inaccurate. Consider using '#align infi_image infᵢ_imageₓ'. -/
theorem infᵢ_image :
    ∀ {γ} {f : β → γ} {g : γ → α} {t : Set β}, (⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b) :=
  @supᵢ_image αᵒᵈ _ _
#align infi_image infᵢ_image

/- warning: supr_extend_bot -> supᵢ_extend_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Bot.bot.{max u2 u1} (β -> α) (Pi.hasBot.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toHasBot.{u1} α _inst_1))) j)) (supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Bot.bot.{max u1 u2} (β -> α) (Pi.instBotForAll.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toBot.{u1} α _inst_1))) j)) (supᵢ.{u1, u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align supr_extend_bot supᵢ_extend_botₓ'. -/
theorem supᵢ_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨆ j, extend e f ⊥ j) = ⨆ i, f i :=
  by
  rw [supᵢ_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true }) [he.extend_apply, extend_apply', @supᵢ_comm _ β ι]
#align supr_extend_bot supᵢ_extend_bot

/- warning: infi_extend_top -> infᵢ_extend_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Top.top.{max u2 u1} (β -> α) (Pi.hasTop.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toHasTop.{u1} α _inst_1))) j)) (infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] {e : ι -> β}, (Function.Injective.{u3, succ u2} ι β e) -> (forall (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (j : β) => Function.extend.{u3, succ u2, succ u1} ι β α e f (Top.top.{max u1 u2} (β -> α) (Pi.instTopForAll.{u2, u1} β (fun (ᾰ : β) => α) (fun (i : β) => CompleteLattice.toTop.{u1} α _inst_1))) j)) (infᵢ.{u1, u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι f))
Case conversion may be inaccurate. Consider using '#align infi_extend_top infᵢ_extend_topₓ'. -/
theorem infᵢ_extend_top {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨅ j, extend e f ⊤ j) = infᵢ f :=
  @supᵢ_extend_bot αᵒᵈ _ _ _ _ he _
#align infi_extend_top infᵢ_extend_top

/-!
### `supr` and `infi` under `Type`
-/


/- warning: supr_of_empty' -> supᵢ_of_empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_2 : SupSet.{u1} α] [_inst_3 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α _inst_2 ι f) (SupSet.supₛ.{u1} α _inst_2 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_2 : SupSet.{u2} α] [_inst_3 : IsEmpty.{u1} ι] (f : ι -> α), Eq.{succ u2} α (supᵢ.{u2, u1} α _inst_2 ι f) (SupSet.supₛ.{u2} α _inst_2 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align supr_of_empty' supᵢ_of_empty'ₓ'. -/
theorem supᵢ_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : supᵢ f = supₛ (∅ : Set α) :=
  congr_arg supₛ (range_eq_empty f)
#align supr_of_empty' supᵢ_of_empty'

/- warning: infi_of_empty' -> infᵢ_of_empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_2 : InfSet.{u1} α] [_inst_3 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, u2} α _inst_2 ι f) (InfSet.infₛ.{u1} α _inst_2 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_2 : InfSet.{u2} α] [_inst_3 : IsEmpty.{u1} ι] (f : ι -> α), Eq.{succ u2} α (infᵢ.{u2, u1} α _inst_2 ι f) (InfSet.infₛ.{u2} α _inst_2 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align infi_of_empty' infᵢ_of_empty'ₓ'. -/
theorem infᵢ_of_empty' {α ι} [InfSet α] [IsEmpty ι] (f : ι → α) : infᵢ f = infₛ (∅ : Set α) :=
  congr_arg infₛ (range_eq_empty f)
#align infi_of_empty' infᵢ_of_empty'

/- warning: supr_of_empty -> supᵢ_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι f) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) ι f) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align supr_of_empty supᵢ_of_emptyₓ'. -/
theorem supᵢ_of_empty [IsEmpty ι] (f : ι → α) : supᵢ f = ⊥ :=
  (supᵢ_of_empty' f).trans supₛ_empty
#align supr_of_empty supᵢ_of_empty

/- warning: infi_of_empty -> infᵢ_of_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι f) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : IsEmpty.{u2} ι] (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) ι f) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align infi_of_empty infᵢ_of_emptyₓ'. -/
theorem infᵢ_of_empty [IsEmpty ι] (f : ι → α) : infᵢ f = ⊤ :=
  @supᵢ_of_empty αᵒᵈ _ _ _ f
#align infi_of_empty infᵢ_of_empty

/- warning: supr_bool_eq -> supᵢ_bool_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Bool (fun (b : Bool) => f b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f Bool.true) (f Bool.false))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Bool (fun (b : Bool) => f b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f Bool.true) (f Bool.false))
Case conversion may be inaccurate. Consider using '#align supr_bool_eq supᵢ_bool_eqₓ'. -/
theorem supᵢ_bool_eq {f : Bool → α} : (⨆ b : Bool, f b) = f true ⊔ f false := by
  rw [supᵢ, Bool.range_eq, supₛ_pair, sup_comm]
#align supr_bool_eq supᵢ_bool_eq

/- warning: infi_bool_eq -> infᵢ_bool_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Bool (fun (b : Bool) => f b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f Bool.true) (f Bool.false))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Bool -> α}, Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Bool (fun (b : Bool) => f b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f Bool.true) (f Bool.false))
Case conversion may be inaccurate. Consider using '#align infi_bool_eq infᵢ_bool_eqₓ'. -/
theorem infᵢ_bool_eq {f : Bool → α} : (⨅ b : Bool, f b) = f true ⊓ f false :=
  @supᵢ_bool_eq αᵒᵈ _ _
#align infi_bool_eq infᵢ_bool_eq

/- warning: sup_eq_supr -> sup_eq_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) x y) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Bool (fun (b : Bool) => cond.{u1} α b x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) x y) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Bool (fun (b : Bool) => cond.{u1} α b x y))
Case conversion may be inaccurate. Consider using '#align sup_eq_supr sup_eq_supᵢₓ'. -/
theorem sup_eq_supᵢ (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [supᵢ_bool_eq, Bool.cond_true, Bool.cond_false]
#align sup_eq_supr sup_eq_supᵢ

/- warning: inf_eq_infi -> inf_eq_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) x y) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Bool (fun (b : Bool) => cond.{u1} α b x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : α) (y : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) x y) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Bool (fun (b : Bool) => cond.{u1} α b x y))
Case conversion may be inaccurate. Consider using '#align inf_eq_infi inf_eq_infᵢₓ'. -/
theorem inf_eq_infᵢ (x y : α) : x ⊓ y = ⨅ b : Bool, cond b x y :=
  @sup_eq_supᵢ αᵒᵈ _ _ _
#align inf_eq_infi inf_eq_infᵢ

/- warning: is_glb_binfi -> isGLB_binfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsGLB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (x : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align is_glb_binfi isGLB_binfᵢₓ'. -/
theorem isGLB_binfᵢ {s : Set β} {f : β → α} : IsGLB (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, infᵢ_subtype'] using @isGLB_infᵢ α s _ (f ∘ coe)
#align is_glb_binfi isGLB_binfᵢ

/- warning: is_lub_bsupr -> isLUB_bsupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) => f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {s : Set.{u2} β} {f : β -> α}, IsLUB.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (Set.image.{u2, u1} β α f s) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (x : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) => f x)))
Case conversion may be inaccurate. Consider using '#align is_lub_bsupr isLUB_bsupᵢₓ'. -/
theorem isLUB_bsupᵢ {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, supᵢ_subtype'] using @isLUB_supᵢ α s _ (f ∘ coe)
#align is_lub_bsupr isLUB_bsupᵢ

/- warning: supr_sigma -> supᵢ_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (supᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (supᵢ.{u1, max (succ u2) (succ u3)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (i : β) => supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
Case conversion may be inaccurate. Consider using '#align supr_sigma supᵢ_sigmaₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ_sigma {p : β → Type _} {f : Sigma p → α} : (⨆ x, f x) = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, Sigma.forall]
#align supr_sigma supᵢ_sigma

/- warning: infi_sigma -> infᵢ_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (infᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : β -> Type.{u3}} {f : (Sigma.{u2, u3} β p) -> α}, Eq.{succ u1} α (infᵢ.{u1, max (succ u2) (succ u3)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Sigma.{u2, u3} β p) (fun (x : Sigma.{u2, u3} β p) => f x)) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (i : β) => infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) (p i) (fun (j : p i) => f (Sigma.mk.{u2, u3} β p i j))))
Case conversion may be inaccurate. Consider using '#align infi_sigma infᵢ_sigmaₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ_sigma {p : β → Type _} {f : Sigma p → α} : (⨅ x, f x) = ⨅ (i) (j), f ⟨i, j⟩ :=
  @supᵢ_sigma αᵒᵈ _ _ _ _
#align infi_sigma infᵢ_sigma

/- warning: supr_prod -> supᵢ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α}, Eq.{succ u1} α (supᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => f x)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (j : γ) => f (Prod.mk.{u2, u3} β γ i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α}, Eq.{succ u1} α (supᵢ.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => f x)) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (i : β) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (j : γ) => f (Prod.mk.{u3, u2} β γ i j))))
Case conversion may be inaccurate. Consider using '#align supr_prod supᵢ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ_prod {f : β × γ → α} : (⨆ x, f x) = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, Prod.forall]
#align supr_prod supᵢ_prod

/- warning: infi_prod -> infᵢ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α}, Eq.{succ u1} α (infᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => f x)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (j : γ) => f (Prod.mk.{u2, u3} β γ i j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α}, Eq.{succ u1} α (infᵢ.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => f x)) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (i : β) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (j : γ) => f (Prod.mk.{u3, u2} β γ i j))))
Case conversion may be inaccurate. Consider using '#align infi_prod infᵢ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ_prod {f : β × γ → α} : (⨅ x, f x) = ⨅ (i) (j), f (i, j) :=
  @supᵢ_prod αᵒᵈ _ _ _ _
#align infi_prod infᵢ_prod

/- warning: bsupr_prod -> bsupᵢ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (supᵢ.{u1, succ (max u2 u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) => f x))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (a : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (b : γ) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f (Prod.mk.{u2, u3} β γ a b))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (supᵢ.{u1, succ (max u3 u2)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) (fun (H : Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) => f x))) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (a : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (b : γ) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f (Prod.mk.{u3, u2} β γ a b))))))
Case conversion may be inaccurate. Consider using '#align bsupr_prod bsupᵢ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem bsupᵢ_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨆ x ∈ s ×ˢ t, f x) = ⨆ (a ∈ s) (b ∈ t), f (a, b) :=
  by
  simp_rw [supᵢ_prod, mem_prod, supᵢ_and]
  exact supᵢ_congr fun _ => supᵢ_comm
#align bsupr_prod bsupᵢ_prod

/- warning: binfi_prod -> binfᵢ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u2, u3} β γ) -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (infᵢ.{u1, succ (max u2 u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Prod.{u2, u3} β γ) (fun (x : Prod.{u2, u3} β γ) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} β γ)) x (Set.prod.{u2, u3} β γ s t)) => f x))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (a : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (b : γ) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f (Prod.mk.{u2, u3} β γ a b))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Prod.{u3, u2} β γ) -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (infᵢ.{u1, succ (max u3 u2)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Prod.{u3, u2} β γ) (fun (x : Prod.{u3, u2} β γ) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) (fun (H : Membership.mem.{max u3 u2, max u2 u3} (Prod.{u3, u2} β γ) (Set.{max u2 u3} (Prod.{u3, u2} β γ)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} β γ)) x (Set.prod.{u3, u2} β γ s t)) => f x))) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (a : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (b : γ) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f (Prod.mk.{u3, u2} β γ a b))))))
Case conversion may be inaccurate. Consider using '#align binfi_prod binfᵢ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem binfᵢ_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨅ x ∈ s ×ˢ t, f x) = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
  @bsupᵢ_prod αᵒᵈ _ _ _ _ _ _
#align binfi_prod binfᵢ_prod

/- warning: supr_sum -> supᵢ_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u2, u3} β γ) -> α}, Eq.{succ u1} α (supᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Sum.{u2, u3} β γ) (fun (x : Sum.{u2, u3} β γ) => f x)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (i : β) => f (Sum.inl.{u2, u3} β γ i))) (supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (j : γ) => f (Sum.inr.{u2, u3} β γ j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u3, u2} β γ) -> α}, Eq.{succ u1} α (supᵢ.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Sum.{u3, u2} β γ) (fun (x : Sum.{u3, u2} β γ) => f x)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (i : β) => f (Sum.inl.{u3, u2} β γ i))) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (j : γ) => f (Sum.inr.{u3, u2} β γ j))))
Case conversion may be inaccurate. Consider using '#align supr_sum supᵢ_sumₓ'. -/
theorem supᵢ_sum {f : Sum β γ → α} : (⨆ x, f x) = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, supᵢ_le_iff, Sum.forall]
#align supr_sum supᵢ_sum

/- warning: infi_sum -> infᵢ_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u2, u3} β γ) -> α}, Eq.{succ u1} α (infᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Sum.{u2, u3} β γ) (fun (x : Sum.{u2, u3} β γ) => f x)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (i : β) => f (Sum.inl.{u2, u3} β γ i))) (infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (j : γ) => f (Sum.inr.{u2, u3} β γ j))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : (Sum.{u3, u2} β γ) -> α}, Eq.{succ u1} α (infᵢ.{u1, max (succ u3) (succ u2)} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Sum.{u3, u2} β γ) (fun (x : Sum.{u3, u2} β γ) => f x)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (i : β) => f (Sum.inl.{u3, u2} β γ i))) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (j : γ) => f (Sum.inr.{u3, u2} β γ j))))
Case conversion may be inaccurate. Consider using '#align infi_sum infᵢ_sumₓ'. -/
theorem infᵢ_sum {f : Sum β γ → α} : (⨅ x, f x) = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.inr j) :=
  @supᵢ_sum αᵒᵈ _ _ _ _
#align infi_sum infᵢ_sum

/- warning: supr_option -> supᵢ_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f (Option.none.{u2} β)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => f (Option.some.{u2} β b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f (Option.none.{u2} β)) (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (b : β) => f (Option.some.{u2} β b))))
Case conversion may be inaccurate. Consider using '#align supr_option supᵢ_optionₓ'. -/
theorem supᵢ_option (f : Option β → α) : (⨆ o, f o) = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, sup_le_iff, Option.forall]
#align supr_option supᵢ_option

/- warning: infi_option -> infᵢ_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f (Option.none.{u2} β)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => f (Option.some.{u2} β b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : (Option.{u2} β) -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Option.{u2} β) (fun (o : Option.{u2} β) => f o)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (f (Option.none.{u2} β)) (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (b : β) => f (Option.some.{u2} β b))))
Case conversion may be inaccurate. Consider using '#align infi_option infᵢ_optionₓ'. -/
theorem infᵢ_option (f : Option β → α) : (⨅ o, f o) = f none ⊓ ⨅ b, f (Option.some b) :=
  @supᵢ_option αᵒᵈ _ _ _
#align infi_option infᵢ_option

/- warning: supr_option_elim -> supᵢ_option_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (a : α) (f : β -> α), Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => Option.elim'.{u2, u1} β α a f o)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (a : α) (f : β -> α), Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Option.{u1} β) (fun (o : Option.{u1} β) => Option.elim.{u1, succ u2} β α o a f)) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) a (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) β (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align supr_option_elim supᵢ_option_elimₓ'. -/
/-- A version of `supr_option` useful for rewriting right-to-left. -/
theorem supᵢ_option_elim (a : α) (f : β → α) : (⨆ o : Option β, o.elim a f) = a ⊔ ⨆ b, f b := by
  simp [supᵢ_option]
#align supr_option_elim supᵢ_option_elim

/- warning: infi_option_elim -> infᵢ_option_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] (a : α) (f : β -> α), Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Option.{u2} β) (fun (o : Option.{u2} β) => Option.elim'.{u2, u1} β α a f o)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (b : β) => f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] (a : α) (f : β -> α), Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Option.{u1} β) (fun (o : Option.{u1} β) => Option.elim.{u1, succ u2} β α o a f)) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) a (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) β (fun (b : β) => f b)))
Case conversion may be inaccurate. Consider using '#align infi_option_elim infᵢ_option_elimₓ'. -/
/-- A version of `infi_option` useful for rewriting right-to-left. -/
theorem infᵢ_option_elim (a : α) (f : β → α) : (⨅ o : Option β, o.elim a f) = a ⊓ ⨅ b, f b :=
  @supᵢ_option_elim αᵒᵈ _ _ _ _
#align infi_option_elim infᵢ_option_elim

/- warning: supr_ne_bot_subtype -> supᵢ_ne_bot_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} α (supᵢ.{u1, max 1 u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) (fun (i : Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)))) ι (coeSubtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))))))) i))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} α (supᵢ.{u2, max 1 u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) (Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1)))) (fun (i : Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1)))) => f (Subtype.val.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α _inst_1))) i))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align supr_ne_bot_subtype supᵢ_ne_bot_subtypeₓ'. -/
/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
theorem supᵢ_ne_bot_subtype (f : ι → α) : (⨆ i : { i // f i ≠ ⊥ }, f i) = ⨆ i, f i :=
  by
  by_cases htriv : ∀ i, f i = ⊥
  · simp only [supᵢ_bot, (funext htriv : f = _)]
  refine' (supᵢ_comp_le f _).antisymm (supᵢ_mono' fun i => _)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩
#align supr_ne_bot_subtype supᵢ_ne_bot_subtype

/- warning: infi_ne_top_subtype -> infᵢ_ne_top_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α), Eq.{succ u1} α (infᵢ.{u1, max 1 u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) (fun (i : Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) => f ((fun (a : Sort.{max 1 u2}) (b : Sort.{u2}) [self : HasLiftT.{max 1 u2, u2} a b] => self.0) (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (HasLiftT.mk.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (CoeTCₓ.coe.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (coeBase.{max 1 u2, u2} (Subtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)))) ι (coeSubtype.{u2} ι (fun (i : ι) => Ne.{succ u1} α (f i) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))))))) i))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α), Eq.{succ u2} α (infᵢ.{u2, max 1 u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) (Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1)))) (fun (i : Subtype.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1)))) => f (Subtype.val.{u1} ι (fun (i : ι) => Ne.{succ u2} α (f i) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α _inst_1))) i))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align infi_ne_top_subtype infᵢ_ne_top_subtypeₓ'. -/
/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem infᵢ_ne_top_subtype (f : ι → α) : (⨅ i : { i // f i ≠ ⊤ }, f i) = ⨅ i, f i :=
  @supᵢ_ne_bot_subtype αᵒᵈ ι _ f
#align infi_ne_top_subtype infᵢ_ne_top_subtype

/- warning: Sup_image2 -> supₛ_image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Set.image2.{u2, u3, u1} β γ α f s t)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) β (fun (a : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) γ (fun (b : γ) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f a b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Set.image2.{u3, u2, u1} β γ α f s t)) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α _inst_1) β (fun (a : β) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α _inst_1) γ (fun (b : γ) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f a b)))))
Case conversion may be inaccurate. Consider using '#align Sup_image2 supₛ_image2ₓ'. -/
theorem supₛ_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    supₛ (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, supₛ_image, bsupᵢ_prod]
#align Sup_image2 supₛ_image2

/- warning: Inf_image2 -> infₛ_image2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u2} β} {t : Set.{u3} γ}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Set.image2.{u2, u3, u1} β γ α f s t)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) β (fun (a : β) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) γ (fun (b : γ) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) (fun (H : Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) b t) => f a b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : β -> γ -> α} {s : Set.{u3} β} {t : Set.{u2} γ}, Eq.{succ u1} α (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Set.image2.{u3, u2, u1} β γ α f s t)) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α _inst_1) β (fun (a : β) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a s) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α _inst_1) γ (fun (b : γ) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) (fun (H : Membership.mem.{u2, u2} γ (Set.{u2} γ) (Set.instMembershipSet.{u2} γ) b t) => f a b)))))
Case conversion may be inaccurate. Consider using '#align Inf_image2 infₛ_image2ₓ'. -/
theorem infₛ_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    infₛ (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, infₛ_image, binfᵢ_prod]
#align Inf_image2 infₛ_image2

/-!
### `supr` and `infi` under `ℕ`
-/


/- warning: supr_ge_eq_supr_nat_add -> supᵢ_ge_eq_supᵢ_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => u i))) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => u i))) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i n)))
Case conversion may be inaccurate. Consider using '#align supr_ge_eq_supr_nat_add supᵢ_ge_eq_supᵢ_nat_addₓ'. -/
theorem supᵢ_ge_eq_supᵢ_nat_add (u : ℕ → α) (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) :=
  by
  apply le_antisymm <;> simp only [supᵢ_le_iff]
  ·
    exact fun i hi =>
      le_supₛ
        ⟨i - n, by
          dsimp only
          rw [Nat.sub_add_cancel hi]⟩
  · exact fun i => le_supₛ ⟨i + n, supᵢ_pos (Nat.le_add_left _ _)⟩
#align supr_ge_eq_supr_nat_add supᵢ_ge_eq_supᵢ_nat_add

/- warning: infi_ge_eq_infi_nat_add -> infᵢ_ge_eq_infᵢ_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => u i))) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => u i))) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i n)))
Case conversion may be inaccurate. Consider using '#align infi_ge_eq_infi_nat_add infᵢ_ge_eq_infᵢ_nat_addₓ'. -/
theorem infᵢ_ge_eq_infᵢ_nat_add (u : ℕ → α) (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
  @supᵢ_ge_eq_supᵢ_nat_add αᵒᵈ _ _ _
#align infi_ge_eq_infi_nat_add infᵢ_ge_eq_infᵢ_nat_add

/- warning: monotone.supr_nat_add -> Monotone.supᵢ_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k))) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k))) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align monotone.supr_nat_add Monotone.supᵢ_nat_addₓ'. -/
theorem Monotone.supᵢ_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : (⨆ n, f (n + k)) = ⨆ n, f n :=
  le_antisymm (supᵢ_le fun i => le_supᵢ _ (i + k)) <| supᵢ_mono fun i => hf <| Nat.le_add_right i k
#align monotone.supr_nat_add Monotone.supᵢ_nat_add

/- warning: antitone.infi_nat_add -> Antitone.infᵢ_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Antitone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (LinearOrder.toLattice.{0} Nat Nat.linearOrder)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k))) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => f n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Nat -> α}, (Antitone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (SemilatticeInf.toPartialOrder.{0} Nat (Lattice.toSemilatticeInf.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)))) (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) f) -> (forall (k : Nat), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k))) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => f n)))
Case conversion may be inaccurate. Consider using '#align antitone.infi_nat_add Antitone.infᵢ_nat_addₓ'. -/
theorem Antitone.infᵢ_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : (⨅ n, f (n + k)) = ⨅ n, f n :=
  hf.dual_right.supᵢ_nat_add k
#align antitone.infi_nat_add Antitone.infᵢ_nat_add

/- warning: supr_infi_ge_nat_add -> supᵢ_infᵢ_ge_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k))))) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (n : Nat) => infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k))))) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (n : Nat) => infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f i))))
Case conversion may be inaccurate. Consider using '#align supr_infi_ge_nat_add supᵢ_infᵢ_ge_nat_addₓ'. -/
@[simp]
theorem supᵢ_infᵢ_ge_nat_add (f : ℕ → α) (k : ℕ) : (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i :=
  by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => binfᵢ_mono fun i => h.trans
  rw [← Monotone.supᵢ_nat_add hf k]
  · simp_rw [infᵢ_ge_eq_infᵢ_nat_add, ← Nat.add_assoc]
#align supr_infi_ge_nat_add supᵢ_infᵢ_ge_nat_add

/- warning: infi_supr_ge_nat_add -> infᵢ_supᵢ_ge_nat_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i k))))) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (n : Nat) => supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => f i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α) (k : Nat), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i k))))) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (n : Nat) => supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => f i))))
Case conversion may be inaccurate. Consider using '#align infi_supr_ge_nat_add infᵢ_supᵢ_ge_nat_addₓ'. -/
@[simp]
theorem infᵢ_supᵢ_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), (⨅ n, ⨆ i ≥ n, f (i + k)) = ⨅ n, ⨆ i ≥ n, f i :=
  @supᵢ_infᵢ_ge_nat_add αᵒᵈ _
#align infi_supr_ge_nat_add infᵢ_supᵢ_ge_nat_add

/- warning: sup_supr_nat_succ -> sup_supᵢ_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => u i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => u i))
Case conversion may be inaccurate. Consider using '#align sup_supr_nat_succ sup_supᵢ_nat_succₓ'. -/
theorem sup_supᵢ_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      rw [supᵢ_union, supᵢ_singleton, supᵢ_range]
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, supᵢ_univ]
    
#align sup_supr_nat_succ sup_supᵢ_nat_succ

/- warning: inf_infi_nat_succ -> inf_infᵢ_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => u i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => u i))
Case conversion may be inaccurate. Consider using '#align inf_infi_nat_succ inf_infᵢ_nat_succₓ'. -/
theorem inf_infᵢ_nat_succ (u : ℕ → α) : (u 0 ⊓ ⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_supᵢ_nat_succ αᵒᵈ _ u
#align inf_infi_nat_succ inf_infᵢ_nat_succ

/- warning: infi_nat_gt_zero_eq -> infᵢ_nat_gt_zero_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => f i))) (infᵢ.{u1, 1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (H : GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => f i))) (infᵢ.{u1, 1} α (CompleteLattice.toInfSet.{u1} α _inst_1) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align infi_nat_gt_zero_eq infᵢ_nat_gt_zero_eqₓ'. -/
theorem infᵢ_nat_gt_zero_eq (f : ℕ → α) : (⨅ i > 0, f i) = ⨅ i, f (i + 1) :=
  by
  rw [← infᵢ_range, Nat.range_succ]
  simp only [mem_set_of]
#align infi_nat_gt_zero_eq infᵢ_nat_gt_zero_eq

/- warning: supr_nat_gt_zero_eq -> supᵢ_nat_gt_zero_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (H : GT.gt.{0} Nat Nat.hasLt i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => f i))) (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : Nat -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (H : GT.gt.{0} Nat instLTNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => f i))) (supᵢ.{u1, 1} α (CompleteLattice.toSupSet.{u1} α _inst_1) Nat (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align supr_nat_gt_zero_eq supᵢ_nat_gt_zero_eqₓ'. -/
theorem supᵢ_nat_gt_zero_eq (f : ℕ → α) : (⨆ i > 0, f i) = ⨆ i, f (i + 1) :=
  @infᵢ_nat_gt_zero_eq αᵒᵈ _ f
#align supr_nat_gt_zero_eq supᵢ_nat_gt_zero_eq

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

/- warning: supr_eq_top -> supᵢ_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] (f : ι -> α), Iff (Eq.{succ u1} α (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] (f : ι -> α), Iff (Eq.{succ u2} α (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f) (Top.top.{u2} α (CompleteLattice.toTop.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) (forall (b : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) b (Top.top.{u2} α (CompleteLattice.toTop.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) b (f i))))
Case conversion may be inaccurate. Consider using '#align supr_eq_top supᵢ_eq_topₓ'. -/
theorem supᵢ_eq_top (f : ι → α) : supᵢ f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  simp only [← supₛ_range, supₛ_eq_top, Set.exists_range_iff]
#align supr_eq_top supᵢ_eq_top

/- warning: infi_eq_bot -> infᵢ_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLinearOrder.{u1} α] (f : ι -> α), Iff (Eq.{succ u1} α (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))) ι f) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) (forall (b : α), (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) b (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1)))) -> (Exists.{u2} ι (fun (i : ι) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (CompleteLinearOrder.toCompleteLattice.{u1} α _inst_1))))) (f i) b)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLinearOrder.{u2} α] (f : ι -> α), Iff (Eq.{succ u2} α (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)) ι f) (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) (forall (b : α), (GT.gt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) b (Bot.bot.{u2} α (CompleteLattice.toBot.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1)))) -> (Exists.{u1} ι (fun (i : ι) => LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (CompleteLinearOrder.toCompleteLattice.{u2} α _inst_1))))) (f i) b)))
Case conversion may be inaccurate. Consider using '#align infi_eq_bot infᵢ_eq_botₓ'. -/
theorem infᵢ_eq_bot (f : ι → α) : infᵢ f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b := by
  simp only [← infₛ_range, infₛ_eq_bot, Set.exists_range_iff]
#align infi_eq_bot infᵢ_eq_bot

end CompleteLinearOrder

/-!
### Instances
-/


#print Prop.completeLattice /-
instance Prop.completeLattice : CompleteLattice Prop :=
  { Prop.boundedOrder,
    Prop.distribLattice with
    supₛ := fun s => ∃ a ∈ s, a
    le_sup := fun s a h p => ⟨a, h, p⟩
    sup_le := fun s a h ⟨b, h', p⟩ => h b h' p
    infₛ := fun s => ∀ a, a ∈ s → a
    inf_le := fun s a h p => p a h
    le_inf := fun s a h p b hb => h b hb p }
#align Prop.complete_lattice Prop.completeLattice
-/

#print Prop.completeLinearOrder /-
noncomputable instance Prop.completeLinearOrder : CompleteLinearOrder Prop :=
  { Prop.completeLattice, Prop.linearOrder with }
#align Prop.complete_linear_order Prop.completeLinearOrder
-/

/- warning: Sup_Prop_eq -> supₛ_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Prop}, Eq.{1} Prop (SupSet.supₛ.{0} Prop (CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)) s) (Exists.{1} Prop (fun (p : Prop) => Exists.{0} (Membership.Mem.{0, 0} Prop (Set.{0} Prop) (Set.hasMem.{0} Prop) p s) (fun (H : Membership.Mem.{0, 0} Prop (Set.{0} Prop) (Set.hasMem.{0} Prop) p s) => p)))
but is expected to have type
  forall {s : Set.{0} Prop}, Eq.{1} Prop (SupSet.supₛ.{0} Prop (CompleteLattice.toSupSet.{0} Prop Prop.completeLattice) s) (Exists.{1} Prop (fun (p : Prop) => And (Membership.mem.{0, 0} Prop (Set.{0} Prop) (Set.instMembershipSet.{0} Prop) p s) p))
Case conversion may be inaccurate. Consider using '#align Sup_Prop_eq supₛ_Prop_eqₓ'. -/
@[simp]
theorem supₛ_Prop_eq {s : Set Prop} : supₛ s = ∃ p ∈ s, p :=
  rfl
#align Sup_Prop_eq supₛ_Prop_eq

/- warning: Inf_Prop_eq -> infₛ_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Prop}, Eq.{1} Prop (InfSet.infₛ.{0} Prop (CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)) s) (forall (p : Prop), (Membership.Mem.{0, 0} Prop (Set.{0} Prop) (Set.hasMem.{0} Prop) p s) -> p)
but is expected to have type
  forall {s : Set.{0} Prop}, Eq.{1} Prop (InfSet.infₛ.{0} Prop (CompleteLattice.toInfSet.{0} Prop Prop.completeLattice) s) (forall (p : Prop), (Membership.mem.{0, 0} Prop (Set.{0} Prop) (Set.instMembershipSet.{0} Prop) p s) -> p)
Case conversion may be inaccurate. Consider using '#align Inf_Prop_eq infₛ_Prop_eqₓ'. -/
@[simp]
theorem infₛ_Prop_eq {s : Set Prop} : infₛ s = ∀ p ∈ s, p :=
  rfl
#align Inf_Prop_eq infₛ_Prop_eq

/- warning: supr_Prop_eq -> supᵢ_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (supᵢ.{0, u1} Prop (CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)) ι (fun (i : ι) => p i)) (Exists.{u1} ι (fun (i : ι) => p i))
but is expected to have type
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (supᵢ.{0, u1} Prop (CompleteLattice.toSupSet.{0} Prop Prop.completeLattice) ι (fun (i : ι) => p i)) (Exists.{u1} ι (fun (i : ι) => p i))
Case conversion may be inaccurate. Consider using '#align supr_Prop_eq supᵢ_Prop_eqₓ'. -/
@[simp]
theorem supᵢ_Prop_eq {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
  le_antisymm (fun ⟨q, ⟨i, (Eq : p i = q)⟩, hq⟩ => ⟨i, Eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩
#align supr_Prop_eq supᵢ_Prop_eq

/- warning: infi_Prop_eq -> infᵢ_Prop_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (infᵢ.{0, u1} Prop (CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)) ι (fun (i : ι) => p i)) (forall (i : ι), p i)
but is expected to have type
  forall {ι : Sort.{u1}} {p : ι -> Prop}, Eq.{1} Prop (infᵢ.{0, u1} Prop (CompleteLattice.toInfSet.{0} Prop Prop.completeLattice) ι (fun (i : ι) => p i)) (forall (i : ι), p i)
Case conversion may be inaccurate. Consider using '#align infi_Prop_eq infᵢ_Prop_eqₓ'. -/
@[simp]
theorem infᵢ_Prop_eq {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h p ⟨i, Eq⟩ => Eq ▸ h i
#align infi_Prop_eq infᵢ_Prop_eq

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
    supₛ := supₛ
    infₛ := infₛ
    le_sup := fun s f hf i => le_supᵢ (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    inf_le := fun s f hf i => infᵢ_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    sup_le := fun s f hf i => supᵢ_le fun g => hf g g.2 i
    le_inf := fun s f hf i => le_infᵢ fun g => hf g g.2 i }
#align pi.complete_lattice Pi.completeLattice
-/

/- warning: Sup_apply -> supₛ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (i : α), SupSet.{u2} (β i)] {s : Set.{max u1 u2} (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (SupSet.supₛ.{max u1 u2} (forall (a : α), β a) (Pi.supSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (supᵢ.{u2, succ (max u1 u2)} (β a) (_inst_1 a) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (fun (f : coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) => (fun (a : Type.{max u1 u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ (max u1 u2), max (succ u1) (succ u2)} a b] => self.0) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (HasLiftT.mk.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (CoeTCₓ.coe.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeBase.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeSubtype.{max (succ u1) (succ u2)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), β a) (Set.{max u1 u2} (forall (a : α), β a)) (Set.hasMem.{max u1 u2} (forall (a : α), β a)) x s))))) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : forall (i : α), SupSet.{u1} (β i)] {s : Set.{max u2 u1} (forall (a : α), β a)} {a : α}, Eq.{succ u1} (β a) (SupSet.supₛ.{max u2 u1} (forall (a : α), β a) (Pi.supSet.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (supᵢ.{u1, max (succ u2) (succ u1)} (β a) (_inst_1 a) (Set.Elem.{max u2 u1} (forall (a : α), β a) s) (fun (f : Set.Elem.{max u2 u1} (forall (a : α), β a) s) => Subtype.val.{succ (max u2 u1)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.mem.{max u2 u1, max u2 u1} (forall (a : α), β a) (Set.{max u2 u1} (forall (a : α), β a)) (Set.instMembershipSet.{max u2 u1} (forall (a : α), β a)) x s) f a))
Case conversion may be inaccurate. Consider using '#align Sup_apply supₛ_applyₓ'. -/
theorem supₛ_apply {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (supₛ s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl
#align Sup_apply supₛ_apply

/- warning: Inf_apply -> infₛ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : forall (i : α), InfSet.{u2} (β i)] {s : Set.{max u1 u2} (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (InfSet.infₛ.{max u1 u2} (forall (a : α), β a) (Pi.infSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (infᵢ.{u2, succ (max u1 u2)} (β a) (_inst_1 a) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (fun (f : coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) => (fun (a : Type.{max u1 u2}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{succ (max u1 u2), max (succ u1) (succ u2)} a b] => self.0) (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (HasLiftT.mk.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (CoeTCₓ.coe.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeBase.{succ (max u1 u2), max (succ u1) (succ u2)} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (forall (a : α), β a)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (forall (a : α), β a)) s) (forall (a : α), β a) (coeSubtype.{max (succ u1) (succ u2)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.Mem.{max u1 u2, max u1 u2} (forall (a : α), β a) (Set.{max u1 u2} (forall (a : α), β a)) (Set.hasMem.{max u1 u2} (forall (a : α), β a)) x s))))) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : forall (i : α), InfSet.{u1} (β i)] {s : Set.{max u2 u1} (forall (a : α), β a)} {a : α}, Eq.{succ u1} (β a) (InfSet.infₛ.{max u2 u1} (forall (a : α), β a) (Pi.infSet.{u2, u1} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) s a) (infᵢ.{u1, max (succ u2) (succ u1)} (β a) (_inst_1 a) (Set.Elem.{max u2 u1} (forall (a : α), β a) s) (fun (f : Set.Elem.{max u2 u1} (forall (a : α), β a) s) => Subtype.val.{succ (max u2 u1)} (forall (a : α), β a) (fun (x : forall (a : α), β a) => Membership.mem.{max u2 u1, max u2 u1} (forall (a : α), β a) (Set.{max u2 u1} (forall (a : α), β a)) (Set.instMembershipSet.{max u2 u1} (forall (a : α), β a)) x s) f a))
Case conversion may be inaccurate. Consider using '#align Inf_apply infₛ_applyₓ'. -/
theorem infₛ_apply {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    infₛ s a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl
#align Inf_apply infₛ_apply

/- warning: supr_apply -> supᵢ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {ι : Sort.{u3}} [_inst_1 : forall (i : α), SupSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (supᵢ.{max u1 u2, u3} (forall (a : α), β a) (Pi.supSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (supᵢ.{u2, u3} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {ι : Sort.{u1}} [_inst_1 : forall (i : α), SupSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (supᵢ.{max u3 u2, u1} (forall (a : α), β a) (Pi.supSet.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (supᵢ.{u2, u1} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
Case conversion may be inaccurate. Consider using '#align supr_apply supᵢ_applyₓ'. -/
@[simp]
theorem supᵢ_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [supᵢ, supₛ_apply, supᵢ, supᵢ, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]
#align supr_apply supᵢ_apply

/- warning: infi_apply -> infᵢ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} {ι : Sort.{u3}} [_inst_1 : forall (i : α), InfSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (infᵢ.{max u1 u2, u3} (forall (a : α), β a) (Pi.infSet.{u1, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (infᵢ.{u2, u3} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
but is expected to have type
  forall {α : Type.{u3}} {β : α -> Type.{u2}} {ι : Sort.{u1}} [_inst_1 : forall (i : α), InfSet.{u2} (β i)] {f : ι -> (forall (a : α), β a)} {a : α}, Eq.{succ u2} (β a) (infᵢ.{max u3 u2, u1} (forall (a : α), β a) (Pi.infSet.{u3, u2} α (fun (a : α) => β a) (fun (i : α) => _inst_1 i)) ι (fun (i : ι) => f i) a) (infᵢ.{u2, u1} (β a) (_inst_1 a) ι (fun (i : ι) => f i a))
Case conversion may be inaccurate. Consider using '#align infi_apply infᵢ_applyₓ'. -/
@[simp]
theorem infᵢ_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, InfSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
  @supᵢ_apply α (fun i => (β i)ᵒᵈ) _ _ _ _
#align infi_apply infᵢ_apply

/- warning: unary_relation_Sup_iff -> unary_relation_supₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (SupSet.supₛ.{u1} (α -> Prop) (Pi.supSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice))) s a) (Exists.{succ u1} (α -> Prop) (fun (r : α -> Prop) => And (Membership.Mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.hasMem.{u1} (α -> Prop)) r s) (r a)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (SupSet.supₛ.{u1} (α -> Prop) (Pi.supSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toSupSet.{0} Prop Prop.completeLattice)) s a) (Exists.{succ u1} (α -> Prop) (fun (r : α -> Prop) => And (Membership.mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.instMembershipSet.{u1} (α -> Prop)) r s) (r a)))
Case conversion may be inaccurate. Consider using '#align unary_relation_Sup_iff unary_relation_supₛ_iffₓ'. -/
theorem unary_relation_supₛ_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    supₛ s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a :=
  by
  unfold Sup
  simp [← eq_iff_iff]
#align unary_relation_Sup_iff unary_relation_supₛ_iff

/- warning: unary_relation_Inf_iff -> unary_relation_infₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (InfSet.infₛ.{u1} (α -> Prop) (Pi.infSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice))) s a) (forall (r : α -> Prop), (Membership.Mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.hasMem.{u1} (α -> Prop)) r s) -> (r a))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} (α -> Prop)) {a : α}, Iff (InfSet.infₛ.{u1} (α -> Prop) (Pi.infSet.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toInfSet.{0} Prop Prop.completeLattice)) s a) (forall (r : α -> Prop), (Membership.mem.{u1, u1} (α -> Prop) (Set.{u1} (α -> Prop)) (Set.instMembershipSet.{u1} (α -> Prop)) r s) -> (r a))
Case conversion may be inaccurate. Consider using '#align unary_relation_Inf_iff unary_relation_infₛ_iffₓ'. -/
theorem unary_relation_infₛ_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    infₛ s a ↔ ∀ r : α → Prop, r ∈ s → r a :=
  by
  unfold Inf
  simp [← eq_iff_iff]
#align unary_relation_Inf_iff unary_relation_infₛ_iff

/- warning: binary_relation_Sup_iff -> binary_relation_supₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{max u1 u2} (α -> β -> Prop)) {a : α} {b : β}, Iff (SupSet.supₛ.{max u1 u2} (α -> β -> Prop) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.supSet.{u2, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteSemilatticeSup.toHasSup.{0} Prop (CompleteLattice.toCompleteSemilatticeSup.{0} Prop Prop.completeLattice)))) s a b) (Exists.{max (succ u1) (succ u2)} (α -> β -> Prop) (fun (r : α -> β -> Prop) => And (Membership.Mem.{max u1 u2, max u1 u2} (α -> β -> Prop) (Set.{max u1 u2} (α -> β -> Prop)) (Set.hasMem.{max u1 u2} (α -> β -> Prop)) r s) (r a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{max u2 u1} (α -> β -> Prop)) {a : α} {b : β}, Iff (SupSet.supₛ.{max u2 u1} (α -> β -> Prop) (Pi.supSet.{u2, u1} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.supSet.{u1, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteLattice.toSupSet.{0} Prop Prop.completeLattice))) s a b) (Exists.{max (succ u2) (succ u1)} (α -> β -> Prop) (fun (r : α -> β -> Prop) => And (Membership.mem.{max u2 u1, max u2 u1} (α -> β -> Prop) (Set.{max u2 u1} (α -> β -> Prop)) (Set.instMembershipSet.{max u2 u1} (α -> β -> Prop)) r s) (r a b)))
Case conversion may be inaccurate. Consider using '#align binary_relation_Sup_iff binary_relation_supₛ_iffₓ'. -/
theorem binary_relation_supₛ_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    supₛ s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b :=
  by
  unfold Sup
  simp [← eq_iff_iff]
#align binary_relation_Sup_iff binary_relation_supₛ_iff

/- warning: binary_relation_Inf_iff -> binary_relation_infₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{max u1 u2} (α -> β -> Prop)) {a : α} {b : β}, Iff (InfSet.infₛ.{max u1 u2} (α -> β -> Prop) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.infSet.{u2, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteSemilatticeInf.toHasInf.{0} Prop (CompleteLattice.toCompleteSemilatticeInf.{0} Prop Prop.completeLattice)))) s a b) (forall (r : α -> β -> Prop), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β -> Prop) (Set.{max u1 u2} (α -> β -> Prop)) (Set.hasMem.{max u1 u2} (α -> β -> Prop)) r s) -> (r a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{max u2 u1} (α -> β -> Prop)) {a : α} {b : β}, Iff (InfSet.infₛ.{max u2 u1} (α -> β -> Prop) (Pi.infSet.{u2, u1} α (fun (ᾰ : α) => β -> Prop) (fun (i : α) => Pi.infSet.{u1, 0} β (fun (ᾰ : β) => Prop) (fun (i : β) => CompleteLattice.toInfSet.{0} Prop Prop.completeLattice))) s a b) (forall (r : α -> β -> Prop), (Membership.mem.{max u2 u1, max u2 u1} (α -> β -> Prop) (Set.{max u2 u1} (α -> β -> Prop)) (Set.instMembershipSet.{max u2 u1} (α -> β -> Prop)) r s) -> (r a b))
Case conversion may be inaccurate. Consider using '#align binary_relation_Inf_iff binary_relation_infₛ_iffₓ'. -/
theorem binary_relation_infₛ_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    infₛ s a b ↔ ∀ r : α → β → Prop, r ∈ s → r a b :=
  by
  unfold Inf
  simp [← eq_iff_iff]
#align binary_relation_Inf_iff binary_relation_infₛ_iff

section CompleteLattice

variable [Preorder α] [CompleteLattice β]

/- warning: monotone_Sup_of_monotone -> monotone_supₛ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{max u1 u2} (α -> β)}, (forall (f : α -> β), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f)) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (SupSet.supₛ.{max u1 u2} (α -> β) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {s : Set.{max u2 u1} (α -> β)}, (forall (f : α -> β), (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) f)) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) (SupSet.supₛ.{max u1 u2} (α -> β) (Pi.supSet.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toSupSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align monotone_Sup_of_monotone monotone_supₛ_of_monotoneₓ'. -/
theorem monotone_supₛ_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (supₛ s) := fun x y h => supᵢ_mono fun f => m_s f f.2 h
#align monotone_Sup_of_monotone monotone_supₛ_of_monotone

/- warning: monotone_Inf_of_monotone -> monotone_infₛ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {s : Set.{max u1 u2} (α -> β)}, (forall (f : α -> β), (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f s) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f)) -> (Monotone.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (InfSet.infₛ.{max u1 u2} (α -> β) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {s : Set.{max u2 u1} (α -> β)}, (forall (f : α -> β), (Membership.mem.{max u2 u1, max u2 u1} (α -> β) (Set.{max u2 u1} (α -> β)) (Set.instMembershipSet.{max u2 u1} (α -> β)) f s) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) f)) -> (Monotone.{u2, u1} α β _inst_1 (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2))) (InfSet.infₛ.{max u1 u2} (α -> β) (Pi.infSet.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toInfSet.{u1} β _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align monotone_Inf_of_monotone monotone_infₛ_of_monotoneₓ'. -/
theorem monotone_infₛ_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (infₛ s) := fun x y h => infᵢ_mono fun f => m_s f f.2 h
#align monotone_Inf_of_monotone monotone_infₛ_of_monotone

end CompleteLattice

namespace Prod

variable (α β)

instance [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (supₛ (Prod.fst '' s), supₛ (Prod.snd '' s))⟩

instance [InfSet α] [InfSet β] : InfSet (α × β) :=
  ⟨fun s => (infₛ (Prod.fst '' s), infₛ (Prod.snd '' s))⟩

variable {α β}

/- warning: prod.fst_Inf -> Prod.fst_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (InfSet.infₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) s)) (InfSet.infₛ.{u1} α _inst_1 (Set.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (InfSet.infₛ.{max u2 u1} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) s)) (InfSet.infₛ.{u2} α _inst_1 (Set.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.fst_Inf Prod.fst_infₛₓ'. -/
theorem fst_infₛ [InfSet α] [InfSet β] (s : Set (α × β)) : (infₛ s).fst = infₛ (Prod.fst '' s) :=
  rfl
#align prod.fst_Inf Prod.fst_infₛ

/- warning: prod.snd_Inf -> Prod.snd_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (InfSet.infₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) s)) (InfSet.infₛ.{u2} β _inst_2 (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (InfSet.infₛ.{max u2 u1} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) s)) (InfSet.infₛ.{u1} β _inst_2 (Set.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.snd_Inf Prod.snd_infₛₓ'. -/
theorem snd_infₛ [InfSet α] [InfSet β] (s : Set (α × β)) : (infₛ s).snd = infₛ (Prod.snd '' s) :=
  rfl
#align prod.snd_Inf Prod.snd_infₛ

/- warning: prod.swap_Inf -> Prod.swap_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (InfSet.infₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) s)) (InfSet.infₛ.{max u2 u1} (Prod.{u2, u1} β α) (Prod.hasInf.{u2, u1} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β (InfSet.infₛ.{max u2 u1} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) s)) (InfSet.infₛ.{max u1 u2} (Prod.{u1, u2} β α) (Prod.infSet.{u1, u2} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.swap_Inf Prod.swap_infₛₓ'. -/
theorem swap_infₛ [InfSet α] [InfSet β] (s : Set (α × β)) : (infₛ s).symm = infₛ (Prod.swap '' s) :=
  ext (congr_arg infₛ <| image_comp Prod.fst swap s : _)
    (congr_arg infₛ <| image_comp Prod.snd swap s : _)
#align prod.swap_Inf Prod.swap_infₛ

/- warning: prod.fst_Sup -> Prod.fst_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (SupSet.supₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) s)) (SupSet.supₛ.{u1} α _inst_1 (Set.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u2} α (Prod.fst.{u2, u1} α β (SupSet.supₛ.{max u2 u1} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) s)) (SupSet.supₛ.{u2} α _inst_1 (Set.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.fst_Sup Prod.fst_supₛₓ'. -/
theorem fst_supₛ [SupSet α] [SupSet β] (s : Set (α × β)) : (supₛ s).fst = supₛ (Prod.fst '' s) :=
  rfl
#align prod.fst_Sup Prod.fst_supₛ

/- warning: prod.snd_Sup -> Prod.snd_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (SupSet.supₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) s)) (SupSet.supₛ.{u2} β _inst_2 (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{succ u1} β (Prod.snd.{u2, u1} α β (SupSet.supₛ.{max u2 u1} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) s)) (SupSet.supₛ.{u1} β _inst_2 (Set.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.snd_Sup Prod.snd_supₛₓ'. -/
theorem snd_supₛ [SupSet α] [SupSet β] (s : Set (α × β)) : (supₛ s).snd = supₛ (Prod.snd '' s) :=
  rfl
#align prod.snd_Sup Prod.snd_supₛ

/- warning: prod.swap_Sup -> Prod.swap_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (s : Set.{max u1 u2} (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (SupSet.supₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) s)) (SupSet.supₛ.{max u2 u1} (Prod.{u2, u1} β α) (Prod.hasSup.{u2, u1} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (s : Set.{max u1 u2} (Prod.{u2, u1} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β (SupSet.supₛ.{max u2 u1} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) s)) (SupSet.supₛ.{max u1 u2} (Prod.{u1, u2} β α) (Prod.supSet.{u1, u2} β α _inst_2 _inst_1) (Set.image.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align prod.swap_Sup Prod.swap_supₛₓ'. -/
theorem swap_supₛ [SupSet α] [SupSet β] (s : Set (α × β)) : (supₛ s).symm = supₛ (Prod.swap '' s) :=
  ext (congr_arg supₛ <| image_comp Prod.fst swap s : _)
    (congr_arg supₛ <| image_comp Prod.snd swap s : _)
#align prod.swap_Sup Prod.swap_supₛ

/- warning: prod.fst_infi -> Prod.fst_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (infᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι f)) (infᵢ.{u1, u3} α _inst_1 ι (fun (i : ι) => Prod.fst.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u3} α (Prod.fst.{u3, u2} α β (infᵢ.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (infᵢ.{u3, u1} α _inst_1 ι (fun (i : ι) => Prod.fst.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.fst_infi Prod.fst_infᵢₓ'. -/
theorem fst_infᵢ [InfSet α] [InfSet β] (f : ι → α × β) : (infᵢ f).fst = ⨅ i, (f i).fst :=
  congr_arg infₛ (range_comp _ _).symm
#align prod.fst_infi Prod.fst_infᵢ

/- warning: prod.snd_infi -> Prod.snd_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (infᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι f)) (infᵢ.{u2, u3} β _inst_2 ι (fun (i : ι) => Prod.snd.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u2} β (Prod.snd.{u3, u2} α β (infᵢ.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (infᵢ.{u2, u1} β _inst_2 ι (fun (i : ι) => Prod.snd.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.snd_infi Prod.snd_infᵢₓ'. -/
theorem snd_infᵢ [InfSet α] [InfSet β] (f : ι → α × β) : (infᵢ f).snd = ⨅ i, (f i).snd :=
  congr_arg infₛ (range_comp _ _).symm
#align prod.snd_infi Prod.snd_infᵢ

/- warning: prod.swap_infi -> Prod.swap_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (infᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι f)) (infᵢ.{max u2 u1, u3} (Prod.{u2, u1} β α) (Prod.hasInf.{u2, u1} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{max (succ u3) (succ u2)} (Prod.{u2, u3} β α) (Prod.swap.{u3, u2} α β (infᵢ.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (infᵢ.{max u3 u2, u1} (Prod.{u2, u3} β α) (Prod.infSet.{u2, u3} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.swap_infi Prod.swap_infᵢₓ'. -/
theorem swap_infᵢ [InfSet α] [InfSet β] (f : ι → α × β) : (infᵢ f).symm = ⨅ i, (f i).symm := by
  simp_rw [infᵢ, swap_Inf, range_comp]
#align prod.swap_infi Prod.swap_infᵢ

/- warning: prod.infi_mk -> Prod.infᵢ_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (infᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u1, u2} α β (f i) (g i))) (Prod.mk.{u1, u2} α β (infᵢ.{u1, u3} α _inst_1 ι (fun (i : ι) => f i)) (infᵢ.{u2, u3} β _inst_2 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u3} α] [_inst_2 : InfSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (infᵢ.{max u2 u3, u1} (Prod.{u3, u2} α β) (Prod.infSet.{u3, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u3, u2} α β (f i) (g i))) (Prod.mk.{u3, u2} α β (infᵢ.{u3, u1} α _inst_1 ι (fun (i : ι) => f i)) (infᵢ.{u2, u1} β _inst_2 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align prod.infi_mk Prod.infᵢ_mkₓ'. -/
theorem infᵢ_mk [InfSet α] [InfSet β] (f : ι → α) (g : ι → β) :
    (⨅ i, (f i, g i)) = (⨅ i, f i, ⨅ i, g i) :=
  congr_arg₂ Prod.mk (fst_infᵢ _) (snd_infᵢ _)
#align prod.infi_mk Prod.infᵢ_mk

/- warning: prod.fst_supr -> Prod.fst_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u1} α (Prod.fst.{u1, u2} α β (supᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι f)) (supᵢ.{u1, u3} α _inst_1 ι (fun (i : ι) => Prod.fst.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u3} α (Prod.fst.{u3, u2} α β (supᵢ.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (supᵢ.{u3, u1} α _inst_1 ι (fun (i : ι) => Prod.fst.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.fst_supr Prod.fst_supᵢₓ'. -/
theorem fst_supᵢ [SupSet α] [SupSet β] (f : ι → α × β) : (supᵢ f).fst = ⨆ i, (f i).fst :=
  congr_arg supₛ (range_comp _ _).symm
#align prod.fst_supr Prod.fst_supᵢ

/- warning: prod.snd_supr -> Prod.snd_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{succ u2} β (Prod.snd.{u1, u2} α β (supᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι f)) (supᵢ.{u2, u3} β _inst_2 ι (fun (i : ι) => Prod.snd.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{succ u2} β (Prod.snd.{u3, u2} α β (supᵢ.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (supᵢ.{u2, u1} β _inst_2 ι (fun (i : ι) => Prod.snd.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.snd_supr Prod.snd_supᵢₓ'. -/
theorem snd_supᵢ [SupSet α] [SupSet β] (f : ι → α × β) : (supᵢ f).snd = ⨆ i, (f i).snd :=
  congr_arg supₛ (range_comp _ _).symm
#align prod.snd_supr Prod.snd_supᵢ

/- warning: prod.swap_supr -> Prod.swap_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u1, u2} α β)), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β (supᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι f)) (supᵢ.{max u2 u1, u3} (Prod.{u2, u1} β α) (Prod.hasSup.{u2, u1} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u1, u2} α β (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> (Prod.{u3, u2} α β)), Eq.{max (succ u3) (succ u2)} (Prod.{u2, u3} β α) (Prod.swap.{u3, u2} α β (supᵢ.{max u3 u2, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι f)) (supᵢ.{max u3 u2, u1} (Prod.{u2, u3} β α) (Prod.supSet.{u2, u3} β α _inst_2 _inst_1) ι (fun (i : ι) => Prod.swap.{u3, u2} α β (f i)))
Case conversion may be inaccurate. Consider using '#align prod.swap_supr Prod.swap_supᵢₓ'. -/
theorem swap_supᵢ [SupSet α] [SupSet β] (f : ι → α × β) : (supᵢ f).symm = ⨆ i, (f i).symm := by
  simp_rw [supᵢ, swap_Sup, range_comp]
#align prod.swap_supr Prod.swap_supᵢ

/- warning: prod.supr_mk -> Prod.supᵢ_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (supᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u1, u2} α β (f i) (g i))) (Prod.mk.{u1, u2} α β (supᵢ.{u1, u3} α _inst_1 ι (fun (i : ι) => f i)) (supᵢ.{u2, u3} β _inst_2 ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u3} α] [_inst_2 : SupSet.{u2} β] (f : ι -> α) (g : ι -> β), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} α β) (supᵢ.{max u2 u3, u1} (Prod.{u3, u2} α β) (Prod.supSet.{u3, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => Prod.mk.{u3, u2} α β (f i) (g i))) (Prod.mk.{u3, u2} α β (supᵢ.{u3, u1} α _inst_1 ι (fun (i : ι) => f i)) (supᵢ.{u2, u1} β _inst_2 ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align prod.supr_mk Prod.supᵢ_mkₓ'. -/
theorem supᵢ_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    (⨆ i, (f i, g i)) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_supᵢ _) (snd_supᵢ _)
#align prod.supr_mk Prod.supᵢ_mk

variable (α β)

instance [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.hasSup α β,
    Prod.hasInf α
      β with
    le_sup := fun s p hab => ⟨le_supₛ <| mem_image_of_mem _ hab, le_supₛ <| mem_image_of_mem _ hab⟩
    sup_le := fun s p h =>
      ⟨supₛ_le <| ball_image_of_ball fun p hp => (h p hp).1,
        supₛ_le <| ball_image_of_ball fun p hp => (h p hp).2⟩
    inf_le := fun s p hab => ⟨infₛ_le <| mem_image_of_mem _ hab, infₛ_le <| mem_image_of_mem _ hab⟩
    le_inf := fun s p h =>
      ⟨le_infₛ <| ball_image_of_ball fun p hp => (h p hp).1,
        le_infₛ <| ball_image_of_ball fun p hp => (h p hp).2⟩ }

end Prod

/- warning: Inf_prod -> infₛ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (InfSet.infₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasInf.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Prod.mk.{u1, u2} α β (InfSet.infₛ.{u1} α _inst_1 s) (InfSet.infₛ.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β t) -> (Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (InfSet.infₛ.{max u1 u2} (Prod.{u2, u1} α β) (Prod.infSet.{u2, u1} α β _inst_1 _inst_2) (Set.prod.{u2, u1} α β s t)) (Prod.mk.{u2, u1} α β (InfSet.infₛ.{u2} α _inst_1 s) (InfSet.infₛ.{u1} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align Inf_prod infₛ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem infₛ_prod [InfSet α] [InfSet β] {s : Set α} {t : Set β} (hs : s.Nonempty)
    (ht : t.Nonempty) : infₛ (s ×ˢ t) = (infₛ s, infₛ t) :=
  congr_arg₂ Prod.mk (congr_arg infₛ <| fst_image_prod _ ht) (congr_arg infₛ <| snd_image_prod hs _)
#align Inf_prod infₛ_prod

/- warning: Sup_prod -> supₛ_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Eq.{succ (max u1 u2)} (Prod.{u1, u2} α β) (SupSet.supₛ.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasSup.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t)) (Prod.mk.{u1, u2} α β (SupSet.supₛ.{u1} α _inst_1 s) (SupSet.supₛ.{u2} β _inst_2 t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β t) -> (Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β) (SupSet.supₛ.{max u1 u2} (Prod.{u2, u1} α β) (Prod.supSet.{u2, u1} α β _inst_1 _inst_2) (Set.prod.{u2, u1} α β s t)) (Prod.mk.{u2, u1} α β (SupSet.supₛ.{u2} α _inst_1 s) (SupSet.supₛ.{u1} β _inst_2 t)))
Case conversion may be inaccurate. Consider using '#align Sup_prod supₛ_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem supₛ_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty)
    (ht : t.Nonempty) : supₛ (s ×ˢ t) = (supₛ s, supₛ t) :=
  congr_arg₂ Prod.mk (congr_arg supₛ <| fst_image_prod _ ht) (congr_arg supₛ <| snd_image_prod hs _)
#align Sup_prod supₛ_prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/- warning: sup_Inf_le_infi_sup -> sup_infₛ_le_infᵢ_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s)) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s)) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align sup_Inf_le_infi_sup sup_infₛ_le_infᵢ_supₓ'. -/
/-- This is a weaker version of `sup_Inf_eq` -/
theorem sup_infₛ_le_infᵢ_sup : a ⊔ infₛ s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_infᵢ₂ fun i h => sup_le_sup_left (infₛ_le h) _
#align sup_Inf_le_infi_sup sup_infₛ_le_infᵢ_sup

/- warning: supr_inf_le_inf_Sup -> supᵢ_inf_le_inf_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a b))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a b))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) a (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align supr_inf_le_inf_Sup supᵢ_inf_le_inf_supₛₓ'. -/
/-- This is a weaker version of `inf_Sup_eq` -/
theorem supᵢ_inf_le_inf_supₛ : (⨆ b ∈ s, a ⊓ b) ≤ a ⊓ supₛ s :=
  @sup_infₛ_le_infᵢ_sup αᵒᵈ _ _ _
#align supr_inf_le_inf_Sup supᵢ_inf_le_inf_supₛ

/- warning: Inf_sup_le_infi_sup -> infₛ_sup_le_infᵢ_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) s) a) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) s) a) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) b a)))
Case conversion may be inaccurate. Consider using '#align Inf_sup_le_infi_sup infₛ_sup_le_infᵢ_supₓ'. -/
/-- This is a weaker version of `Inf_sup_eq` -/
theorem infₛ_sup_le_infᵢ_sup : infₛ s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_infᵢ₂ fun i h => sup_le_sup_right (infₛ_le h) _
#align Inf_sup_le_infi_sup infₛ_sup_le_infᵢ_sup

/- warning: supr_inf_le_Sup_inf -> supᵢ_inf_le_supₛ_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) b a))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) s) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : α} {s : Set.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) b a))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) s) a)
Case conversion may be inaccurate. Consider using '#align supr_inf_le_Sup_inf supᵢ_inf_le_supₛ_infₓ'. -/
/-- This is a weaker version of `Sup_inf_eq` -/
theorem supᵢ_inf_le_supₛ_inf : (⨆ b ∈ s, b ⊓ a) ≤ supₛ s ⊓ a :=
  @infₛ_sup_le_infᵢ_sup αᵒᵈ _ _ _
#align supr_inf_le_Sup_inf supᵢ_inf_le_supₛ_inf

/- warning: le_supr_inf_supr -> le_supᵢ_inf_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (g : ι -> α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i) (g i))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => f i)) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) ι (fun (i : ι) => g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (g : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (f i) (g i))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) (supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α _inst_1) ι (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align le_supr_inf_supr le_supᵢ_inf_supᵢₓ'. -/
theorem le_supᵢ_inf_supᵢ (f g : ι → α) : (⨆ i, f i ⊓ g i) ≤ (⨆ i, f i) ⊓ ⨆ i, g i :=
  le_inf (supᵢ_mono fun i => inf_le_left) (supᵢ_mono fun i => inf_le_right)
#align le_supr_inf_supr le_supᵢ_inf_supᵢ

/- warning: infi_sup_infi_le -> infᵢ_sup_infᵢ_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] (f : ι -> α) (g : ι -> α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => f i)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => g i))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (f i) (g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] (f : ι -> α) (g : ι -> α), LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => f i)) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => g i))) (infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α _inst_1) ι (fun (i : ι) => HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (f i) (g i)))
Case conversion may be inaccurate. Consider using '#align infi_sup_infi_le infᵢ_sup_infᵢ_leₓ'. -/
theorem infᵢ_sup_infᵢ_le (f g : ι → α) : ((⨅ i, f i) ⊔ ⨅ i, g i) ≤ ⨅ i, f i ⊔ g i :=
  @le_supᵢ_inf_supᵢ αᵒᵈ ι _ f g
#align infi_sup_infi_le infᵢ_sup_infᵢ_le

/- warning: disjoint_Sup_left -> disjoint_supₛ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) a) b) -> (forall {i : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) i b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) a) b) -> (forall {i : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) i b))
Case conversion may be inaccurate. Consider using '#align disjoint_Sup_left disjoint_supₛ_leftₓ'. -/
theorem disjoint_supₛ_left {a : Set α} {b : α} (d : Disjoint (supₛ a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (supᵢ₂_le_iff.1 (supᵢ_inf_le_supₛ_inf.trans d.le_bot) i hi : _)
#align disjoint_Sup_left disjoint_supₛ_left

/- warning: disjoint_Sup_right -> disjoint_supₛ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) a)) -> (forall {i : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b i))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {a : Set.{u1} α} {b : α}, (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) a)) -> (forall {i : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i a) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} α _inst_1)) b i))
Case conversion may be inaccurate. Consider using '#align disjoint_Sup_right disjoint_supₛ_rightₓ'. -/
theorem disjoint_supₛ_right {a : Set α} {b : α} (d : Disjoint b (supₛ a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (supᵢ₂_le_iff.mp (supᵢ_inf_le_inf_supₛ.trans d.le_bot) i hi : _)
#align disjoint_Sup_right disjoint_supₛ_right

end CompleteLattice

/- warning: function.injective.complete_lattice -> Function.Injective.completeLattice is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_7)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_7)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_7)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_7)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β _inst_7))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_7))) -> (CompleteLattice.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_7)) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_7) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_7) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_7) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_7) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β _inst_7))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β _inst_7))) -> (CompleteLattice.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.complete_lattice Function.Injective.completeLatticeₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `complete_lattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeLattice [HasSup α] [HasInf α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_Sup : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α :=
  {-- we cannot use bounded_order.lift here as the `has_le` instance doesn't exist yet
        hf.Lattice
      f map_sup map_inf with
    supₛ := supₛ
    le_sup := fun s a h => (le_supᵢ₂ a h).trans (map_Sup _).ge
    sup_le := fun s a h => (map_Sup _).trans_le <| supᵢ₂_le h
    infₛ := infₛ
    inf_le := fun s a h => (map_Inf _).trans_le <| infᵢ₂_le a h
    le_inf := fun s a h => (le_infᵢ₂ h).trans (map_Inf _).ge
    top := ⊤
    le_top := fun a => (@le_top β _ _ _).trans map_top.ge
    bot := ⊥
    bot_le := fun a => map_bot.le.trans bot_le }
#align function.injective.complete_lattice Function.Injective.completeLattice

