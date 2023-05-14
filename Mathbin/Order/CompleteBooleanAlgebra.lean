/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies

! This file was ported from Lean 3 source module order.complete_boolean_algebra
! leanprover-community/mathlib commit 71b36b6f3bbe3b44e6538673819324d3ee9fcc96
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Directed
import Mathbin.Logic.Equiv.Set

/-!
# Frames, completely distributive lattices and Boolean algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define and provide API for frames, completely distributive lattices and completely
distributive Boolean algebras.

## Typeclasses

* `order.frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `order.coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `complete_distrib_lattice`: Completely distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `complete_boolean_algebra`: Completely distributive Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `filter` is a coframe but not a completely
distributive lattice.

## TODO

Add instances for `prod`

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/


open Function Set

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort _}

#print Order.Frame /-
/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class Order.Frame (α : Type _) extends CompleteLattice α where
  inf_sup_le_iSup_inf (a : α) (s : Set α) : a ⊓ Sup s ≤ ⨆ b ∈ s, a ⊓ b
#align order.frame Order.Frame
-/

#print Order.Coframe /-
/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class Order.Coframe (α : Type _) extends CompleteLattice α where
  iInf_sup_le_sup_inf (a : α) (s : Set α) : (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s
#align order.coframe Order.Coframe
-/

open Order

#print CompleteDistribLattice /-
/-- A completely distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type _) extends Frame α where
  iInf_sup_le_sup_inf : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s
#align complete_distrib_lattice CompleteDistribLattice
-/

#print CompleteDistribLattice.toCoframe /-
-- See note [lower instance priority]
instance (priority := 100) CompleteDistribLattice.toCoframe [CompleteDistribLattice α] :
    Coframe α :=
  { ‹CompleteDistribLattice α› with }
#align complete_distrib_lattice.to_coframe CompleteDistribLattice.toCoframe
-/

section Frame

variable [Frame α] {s t : Set α} {a b : α}

#print OrderDual.coframe /-
instance OrderDual.coframe : Coframe αᵒᵈ :=
  { OrderDual.completeLattice α with iInf_sup_le_sup_inf := Frame.inf_sup_le_iSup_inf }
#align order_dual.coframe OrderDual.coframe
-/

/- warning: inf_Sup_eq -> inf_sSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s)) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) α (fun (b : α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s)) (iSup.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align inf_Sup_eq inf_sSup_eqₓ'. -/
theorem inf_sSup_eq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  (Frame.inf_sup_le_iSup_inf _ _).antisymm iSup_inf_le_inf_sSup
#align inf_Sup_eq inf_sSup_eq

/- warning: Sup_inf_eq -> sSup_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s) b) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) α (fun (a : α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s) b) (iSup.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) α (fun (a : α) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align Sup_inf_eq sSup_inf_eqₓ'. -/
theorem sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b
#align Sup_inf_eq sSup_inf_eq

/- warning: supr_inf_eq -> iSup_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i)) a) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i) a))
Case conversion may be inaccurate. Consider using '#align supr_inf_eq iSup_inf_eqₓ'. -/
theorem iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]
#align supr_inf_eq iSup_inf_eq

/- warning: inf_supr_eq -> inf_iSup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i)))
Case conversion may be inaccurate. Consider using '#align inf_supr_eq inf_iSup_eqₓ'. -/
theorem inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a
#align inf_supr_eq inf_iSup_eq

/- warning: bsupr_inf_eq -> iSup₂_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j))) a) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i j) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i j) a)))
Case conversion may be inaccurate. Consider using '#align bsupr_inf_eq iSup₂_inf_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) : (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a :=
  by simp only [iSup_inf_eq]
#align bsupr_inf_eq iSup₂_inf_eq

/- warning: inf_bsupr_eq -> inf_iSup₂_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j)))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (f i j))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (f i j))))
Case conversion may be inaccurate. Consider using '#align inf_bsupr_eq inf_iSup₂_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j :=
  by simp only [inf_iSup_eq]
#align inf_bsupr_eq inf_iSup₂_eq

/- warning: supr_inf_supr -> iSup_inf_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι' (fun (j : ι') => g j))) (iSup.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (i : Prod.{u2, u3} ι ι') => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' i)) (g (Prod.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Frame.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u3} α (Inf.inf.{u3} α (Lattice.toInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (iSup.{u3, succ u2} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => f i)) (iSup.{u3, succ u1} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι' (fun (j : ι') => g j))) (iSup.{u3, max (succ u2) (succ u1)} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (i : Prod.{u2, u1} ι ι') => Inf.inf.{u3} α (Lattice.toInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (f (Prod.fst.{u2, u1} ι ι' i)) (g (Prod.snd.{u2, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align supr_inf_supr iSup_inf_iSupₓ'. -/
theorem iSup_inf_iSup {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp only [inf_iSup_eq, iSup_inf_eq, iSup_prod]
#align supr_inf_supr iSup_inf_iSup

/- warning: bsupr_inf_bsupr -> biSup_inf_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u3} ι'}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (iSup.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι' (fun (j : ι') => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) (fun (H : Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) => g j)))) (iSup.{u1, succ (max u2 u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (p : Prod.{u2, u3} ι ι') => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' p)) (g (Prod.snd.{u2, u3} ι ι' p)))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Frame.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u1} ι'}, Eq.{succ u3} α (Inf.inf.{u3} α (Lattice.toInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (iSup.{u3, succ u2} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => iSup.{u3, 0} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (iSup.{u3, succ u1} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι' (fun (j : ι') => iSup.{u3, 0} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) (fun (H : Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) => g j)))) (iSup.{u3, succ (max u2 u1)} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (p : Prod.{u2, u1} ι ι') => iSup.{u3, 0} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) (fun (H : Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) => Inf.inf.{u3} α (Lattice.toInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (f (Prod.fst.{u2, u1} ι ι' p)) (g (Prod.snd.{u2, u1} ι ι' p)))))
Case conversion may be inaccurate. Consider using '#align bsupr_inf_bsupr biSup_inf_biSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem biSup_inf_biSup {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 :=
  by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl
#align bsupr_inf_bsupr biSup_inf_biSup

/- warning: Sup_inf_Sup -> sSup_inf_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) t)) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) t)) (iSup.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => iSup.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
Case conversion may be inaccurate. Consider using '#align Sup_inf_Sup sSup_inf_sSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]
#align Sup_inf_Sup sSup_inf_sSup

/- warning: supr_disjoint_iff -> iSup_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i)) a) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i) a)
Case conversion may be inaccurate. Consider using '#align supr_disjoint_iff iSup_disjoint_iffₓ'. -/
theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]
#align supr_disjoint_iff iSup_disjoint_iff

/- warning: disjoint_supr_iff -> disjoint_iSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i))
Case conversion may be inaccurate. Consider using '#align disjoint_supr_iff disjoint_iSup_iffₓ'. -/
theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using iSup_disjoint_iff
#align disjoint_supr_iff disjoint_iSup_iff

/- warning: supr₂_disjoint_iff -> iSup₂_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i j) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i j) a)
Case conversion may be inaccurate. Consider using '#align supr₂_disjoint_iff iSup₂_disjoint_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by simp_rw [iSup_disjoint_iff]
#align supr₂_disjoint_iff iSup₂_disjoint_iff

/- warning: disjoint_supr₂_iff -> disjoint_iSup₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iSup.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (iSup.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (f i j))
Case conversion may be inaccurate. Consider using '#align disjoint_supr₂_iff disjoint_iSup₂_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by simp_rw [disjoint_iSup_iff]
#align disjoint_supr₂_iff disjoint_iSup₂_iff

/- warning: Sup_disjoint_iff -> sSup_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align Sup_disjoint_iff sSup_disjoint_iffₓ'. -/
theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]
#align Sup_disjoint_iff sSup_disjoint_iff

/- warning: disjoint_Sup_iff -> disjoint_sSup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (SupSet.sSup.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align disjoint_Sup_iff disjoint_sSup_iffₓ'. -/
theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using sSup_disjoint_iff
#align disjoint_Sup_iff disjoint_sSup_iff

/- warning: supr_inf_of_monotone -> iSup_inf_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2))] {f : ι -> α} {g : ι -> α}, (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) f) -> (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Frame.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1516 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1518 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1516 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1518)] {f : ι -> α} {g : ι -> α}, (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) f) -> (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i) (g i))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align supr_inf_of_monotone iSup_inf_of_monotoneₓ'. -/
theorem iSup_inf_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i :=
  by
  refine' (le_iSup_inf_iSup f g).antisymm _
  rw [iSup_inf_iSup]
  refine' iSup_mono' fun i => _
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩
#align supr_inf_of_monotone iSup_inf_of_monotone

/- warning: supr_inf_of_antitone -> iSup_inf_of_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2)))] {f : ι -> α} {g : ι -> α}, (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (iSup.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Frame.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1711 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1713 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1711 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1713))] {f : ι -> α} {g : ι -> α}, (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) f) -> (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i) (g i))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (iSup.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align supr_inf_of_antitone iSup_inf_of_antitoneₓ'. -/
theorem iSup_inf_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left
#align supr_inf_of_antitone iSup_inf_of_antitone

#print Pi.frame /-
instance Pi.frame {ι : Type _} {π : ι → Type _} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with
    inf_sup_le_iSup_inf := fun a s i => by
      simp only [CompleteLattice.sup, sSup_apply, iSup_apply, Pi.inf_apply, inf_iSup_eq, ←
        iSup_subtype''] }
#align pi.frame Pi.frame
-/

#print Frame.toDistribLattice /-
-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]
#align frame.to_distrib_lattice Frame.toDistribLattice
-/

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b : α}

#print OrderDual.frame /-
instance OrderDual.frame : Frame αᵒᵈ :=
  { OrderDual.completeLattice α with inf_sup_le_iSup_inf := Coframe.iInf_sup_le_sup_inf }
#align order_dual.frame OrderDual.frame
-/

/- warning: sup_Inf_eq -> sup_sInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) s)) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) α (fun (b : α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) s)) (iInf.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
Case conversion may be inaccurate. Consider using '#align sup_Inf_eq sup_sInf_eqₓ'. -/
theorem sup_sInf_eq : a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  @inf_sSup_eq αᵒᵈ _ _ _
#align sup_Inf_eq sup_sInf_eq

/- warning: Inf_sup_eq -> sInf_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) s) b) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) α (fun (a : α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) s) b) (iInf.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) α (fun (a : α) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
Case conversion may be inaccurate. Consider using '#align Inf_sup_eq sInf_sup_eqₓ'. -/
theorem sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b :=
  @sSup_inf_eq αᵒᵈ _ _ _
#align Inf_sup_eq sInf_sup_eq

/- warning: infi_sup_eq -> iInf_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i)) a) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) a))
Case conversion may be inaccurate. Consider using '#align infi_sup_eq iInf_sup_eqₓ'. -/
theorem iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
  @iSup_inf_eq αᵒᵈ _ _ _ _
#align infi_sup_eq iInf_sup_eq

/- warning: sup_infi_eq -> sup_iInf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (iInf.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (f i)))
Case conversion may be inaccurate. Consider using '#align sup_infi_eq sup_iInf_eqₓ'. -/
theorem sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i :=
  @inf_iSup_eq αᵒᵈ _ _ _ _
#align sup_infi_eq sup_iInf_eq

/- warning: binfi_sup_eq -> iInf₂_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Coframe.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j))) a) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i j) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Coframe.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (f i j) a)))
Case conversion may be inaccurate. Consider using '#align binfi_sup_eq iInf₂_sup_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem iInf₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @iSup₂_inf_eq αᵒᵈ _ _ _ _ _
#align binfi_sup_eq iInf₂_sup_eq

/- warning: sup_binfi_eq -> sup_iInf₂_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Coframe.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j)))) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iInf.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (f i j))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Coframe.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) a (iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (iInf.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iInf.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) a (f i j))))
Case conversion may be inaccurate. Consider using '#align sup_binfi_eq sup_iInf₂_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_iSup₂_eq αᵒᵈ _ _ _ _ _
#align sup_binfi_eq sup_iInf₂_eq

/- warning: infi_sup_infi -> iInf_sup_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι' (fun (i : ι') => g i))) (iInf.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (i : Prod.{u2, u3} ι ι') => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' i)) (g (Prod.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Coframe.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u3} α (Sup.sup.{u3} α (SemilatticeSup.toSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (iInf.{u3, succ u2} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => f i)) (iInf.{u3, succ u1} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι' (fun (i : ι') => g i))) (iInf.{u3, max (succ u2) (succ u1)} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (i : Prod.{u2, u1} ι ι') => Sup.sup.{u3} α (SemilatticeSup.toSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (f (Prod.fst.{u2, u1} ι ι' i)) (g (Prod.snd.{u2, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align infi_sup_infi iInf_sup_iInfₓ'. -/
theorem iInf_sup_iInf {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @iSup_inf_iSup αᵒᵈ _ _ _ _ _
#align infi_sup_infi iInf_sup_iInf

/- warning: binfi_sup_binfi -> biInf_sup_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u3} ι'}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (iInf.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι' (fun (j : ι') => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) (fun (H : Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) => g j)))) (iInf.{u1, succ (max u2 u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (p : Prod.{u2, u3} ι ι') => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' p)) (g (Prod.snd.{u2, u3} ι ι' p)))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Coframe.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u1} ι'}, Eq.{succ u3} α (Sup.sup.{u3} α (SemilatticeSup.toSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (iInf.{u3, succ u2} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => iInf.{u3, 0} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (iInf.{u3, succ u1} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι' (fun (j : ι') => iInf.{u3, 0} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) (fun (H : Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) => g j)))) (iInf.{u3, succ (max u2 u1)} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (p : Prod.{u2, u1} ι ι') => iInf.{u3, 0} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) (fun (H : Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) => Sup.sup.{u3} α (SemilatticeSup.toSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (f (Prod.fst.{u2, u1} ι ι' p)) (g (Prod.snd.{u2, u1} ι ι' p)))))
Case conversion may be inaccurate. Consider using '#align binfi_sup_binfi biInf_sup_biInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem biInf_sup_biInf {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @biSup_inf_biSup αᵒᵈ _ _ _ _ _ _ _
#align binfi_sup_binfi biInf_sup_biInf

/- warning: Inf_sup_Inf -> sInf_sup_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) s) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) t)) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) s) (InfSet.sInf.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) t)) (iInf.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => iInf.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
Case conversion may be inaccurate. Consider using '#align Inf_sup_Inf sInf_sup_sInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sInf_sup_sInf : sInf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @sSup_inf_sSup αᵒᵈ _ _ _
#align Inf_sup_Inf sInf_sup_sInf

/- warning: infi_sup_of_monotone -> iInf_sup_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2)))] {f : ι -> α} {g : ι -> α}, (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) f) -> (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Coframe.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2832 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2834 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2832 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2834))] {f : ι -> α} {g : ι -> α}, (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) f) -> (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (f i) (g i))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align infi_sup_of_monotone iInf_sup_of_monotoneₓ'. -/
theorem iInf_sup_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  iSup_inf_of_antitone hf.dual_right hg.dual_right
#align infi_sup_of_monotone iInf_sup_of_monotone

/- warning: infi_sup_of_antitone -> iInf_sup_of_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2))] {f : ι -> α} {g : ι -> α}, (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (iInf.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Coframe.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2954 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2956 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2954 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.2956)] {f : ι -> α} {g : ι -> α}, (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) f) -> (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (f i) (g i))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (iInf.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align infi_sup_of_antitone iInf_sup_of_antitoneₓ'. -/
theorem iInf_sup_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  iSup_inf_of_monotone hf.dual_right hg.dual_right
#align infi_sup_of_antitone iInf_sup_of_antitone

#print Pi.coframe /-
instance Pi.coframe {ι : Type _} {π : ι → Type _} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with
    sInf := sInf
    iInf_sup_le_sup_inf := fun a s i => by
      simp only [← sup_iInf_eq, sInf_apply, ← iInf_subtype'', iInf_apply, Pi.sup_apply] }
#align pi.coframe Pi.coframe
-/

#print Coframe.toDistribLattice /-
-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α :=
  { ‹Coframe α› with
    le_sup_inf := fun a b c => by
      rw [← sInf_pair, ← sInf_pair, sup_sInf_eq, ← sInf_image, image_pair] }
#align coframe.to_distrib_lattice Coframe.toDistribLattice
-/

end Coframe

section CompleteDistribLattice

variable [CompleteDistribLattice α] {a b : α} {s t : Set α}

instance : CompleteDistribLattice αᵒᵈ :=
  { OrderDual.frame, OrderDual.coframe with }

#print Pi.completeDistribLattice /-
instance Pi.completeDistribLattice {ι : Type _} {π : ι → Type _}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) :=
  { Pi.frame, Pi.coframe with }
#align pi.complete_distrib_lattice Pi.completeDistribLattice
-/

end CompleteDistribLattice

#print CompleteBooleanAlgebra /-
/-- A complete Boolean algebra is a completely distributive Boolean algebra. -/
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteDistribLattice α
#align complete_boolean_algebra CompleteBooleanAlgebra
-/

#print Pi.completeBooleanAlgebra /-
instance Pi.completeBooleanAlgebra {ι : Type _} {π : ι → Type _}
    [∀ i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (∀ i, π i) :=
  { Pi.booleanAlgebra, Pi.completeDistribLattice with }
#align pi.complete_boolean_algebra Pi.completeBooleanAlgebra
-/

#print Prop.completeBooleanAlgebra /-
instance Prop.completeBooleanAlgebra : CompleteBooleanAlgebra Prop :=
  { Prop.booleanAlgebra,
    Prop.completeLattice with
    iInf_sup_le_sup_inf := fun p s =>
      Iff.mp <| by simp only [forall_or_left, CompleteLattice.inf, iInf_Prop_eq, sup_Prop_eq]
    inf_sup_le_iSup_inf := fun p s =>
      Iff.mp <| by simp only [CompleteLattice.sup, exists_and_left, inf_Prop_eq, iSup_Prop_eq] }
#align Prop.complete_boolean_algebra Prop.completeBooleanAlgebra
-/

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

/- warning: compl_infi -> compl_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι f)) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (iInf.{u1, u2} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) ι f)) (iSup.{u1, u2} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
Case conversion may be inaccurate. Consider using '#align compl_infi compl_iInfₓ'. -/
theorem compl_iInf : iInf fᶜ = ⨆ i, f iᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <| le_iSup (compl ∘ f) i)
    (iSup_le fun i => compl_le_compl <| iInf_le _ _)
#align compl_infi compl_iInf

/- warning: compl_supr -> compl_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (iSup.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι f)) (iInf.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (iSup.{u1, u2} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) ι f)) (iInf.{u1, u2} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
Case conversion may be inaccurate. Consider using '#align compl_supr compl_iSupₓ'. -/
theorem compl_iSup : iSup fᶜ = ⨅ i, f iᶜ :=
  compl_injective (by simp [compl_iInf])
#align compl_supr compl_iSup

/- warning: compl_Inf -> compl_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (iSup.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) α (fun (i : α) => iSup.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.sInf.{u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) s)) (iSup.{u1, succ u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) α (fun (i : α) => iSup.{u1, 0} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
Case conversion may be inaccurate. Consider using '#align compl_Inf compl_sInfₓ'. -/
theorem compl_sInf : sInf sᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]
#align compl_Inf compl_sInf

/- warning: compl_Sup -> compl_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (iInf.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) α (fun (i : α) => iInf.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) s)) (iInf.{u1, succ u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) α (fun (i : α) => iInf.{u1, 0} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
Case conversion may be inaccurate. Consider using '#align compl_Sup compl_sSupₓ'. -/
theorem compl_sSup : sSup sᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]
#align compl_Sup compl_sSup

/- warning: compl_Inf' -> compl_sInf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.sInf.{u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) s)) (SupSet.sSup.{u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align compl_Inf' compl_sInf'ₓ'. -/
theorem compl_sInf' : sInf sᶜ = sSup (compl '' s) :=
  compl_sInf.trans sSup_image.symm
#align compl_Inf' compl_sInf'

/- warning: compl_Sup' -> compl_sSup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (InfSet.sInf.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.sSup.{u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) s)) (InfSet.sInf.{u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align compl_Sup' compl_sSup'ₓ'. -/
theorem compl_sSup' : sSup sᶜ = sInf (compl '' s) :=
  compl_sSup.trans sInf_image.symm
#align compl_Sup' compl_sSup'

end CompleteBooleanAlgebra

section lift

/- warning: function.injective.frame -> Function.Injective.frame is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Frame.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Frame.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Frame.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (Lattice.toInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Frame.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.frame Function.Injective.frameₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `order.frame` along an injection. -/
@[reducible]
protected def Function.Injective.frame [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Frame β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : Frame α :=
  { hf.CompleteLattice f map_sup map_inf map_Sup map_Inf map_top map_bot with
    inf_sup_le_iSup_inf := fun a s => by
      change f (a ⊓ Sup s) ≤ f _
      rw [← sSup_image, map_inf, map_Sup s, inf_iSup₂_eq]
      simp_rw [← map_inf]
      exact ((map_Sup _).trans iSup_image).ge }
#align function.injective.frame Function.Injective.frame

/- warning: function.injective.coframe -> Function.Injective.coframe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Coframe.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Coframe.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Coframe.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (Lattice.toInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Coframe.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.coframe Function.Injective.coframeₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `order.coframe` along an injection. -/
@[reducible]
protected def Function.Injective.coframe [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Coframe β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Coframe α :=
  { hf.CompleteLattice f map_sup map_inf map_Sup map_Inf map_top map_bot with
    iInf_sup_le_sup_inf := fun a s => by
      change f _ ≤ f (a ⊔ Inf s)
      rw [← sInf_image, map_sup, map_Inf s, sup_iInf₂_eq]
      simp_rw [← map_sup]
      exact ((map_Inf _).trans iInf_image).le }
#align function.injective.coframe Function.Injective.coframe

/- warning: function.injective.complete_distrib_lattice -> Function.Injective.completeDistribLattice is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteDistribLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (CompleteDistribLattice.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteDistribLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (Lattice.toInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) α (fun (a : α) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) α (fun (a : α) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (CompleteDistribLattice.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLatticeₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `complete_distrib_lattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeDistribLattice [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompleteDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_Sup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteDistribLattice α :=
  { hf.Frame f map_sup map_inf map_Sup map_Inf map_top map_bot,
    hf.Coframe f map_sup map_inf map_Sup map_Inf map_top map_bot with }
#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLattice

/- warning: function.injective.complete_boolean_algebra -> Function.Injective.completeBooleanAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : HasCompl.{u1} α] [_inst_8 : SDiff.{u1} α] [_inst_9 : CompleteBooleanAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) α (fun (a : α) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) α (fun (a : α) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_7 a)) (HasCompl.compl.{u2} β (BooleanAlgebra.toHasCompl.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_8 a b)) (SDiff.sdiff.{u2} β (BooleanAlgebra.toHasSdiff.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a) (f b))) -> (CompleteBooleanAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Sup.{u1} α] [_inst_2 : Inf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : HasCompl.{u1} α] [_inst_8 : SDiff.{u1} α] [_inst_9 : CompleteBooleanAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Sup.sup.{u1} α _inst_1 a b)) (Sup.sup.{u2} β (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (Inf.inf.{u1} α _inst_2 a b)) (Inf.inf.{u2} β (Lattice.toInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.sSup.{u1} α _inst_3 s)) (iSup.{u2, succ u1} β (CompleteBooleanAlgebra.toSupSet.{u2} β _inst_9) α (fun (a : α) => iSup.{u2, 0} β (CompleteBooleanAlgebra.toSupSet.{u2} β _inst_9) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.sInf.{u1} α _inst_4 s)) (iInf.{u2, succ u1} β (CompleteBooleanAlgebra.toInfSet.{u2} β _inst_9) α (fun (a : α) => iInf.{u2, 0} β (CompleteBooleanAlgebra.toInfSet.{u2} β _inst_9) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_7 a)) (HasCompl.compl.{u2} β (BooleanAlgebra.toHasCompl.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_8 a b)) (SDiff.sdiff.{u2} β (BooleanAlgebra.toSDiff.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a) (f b))) -> (CompleteBooleanAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `complete_boolean_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [Sup α] [Inf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f (aᶜ) = f aᶜ) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α :=
  { hf.CompleteDistribLattice f map_sup map_inf map_Sup map_Inf map_top map_bot,
    hf.BooleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff with }
#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebra

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1}) (x y : PUnit.{u + 1})

instance : CompleteBooleanAlgebra PUnit := by
  refine_struct
        { PUnit.booleanAlgebra with
          sSup := fun _ => star
          sInf := fun _ => star } <;>
      intros <;>
    first |trivial|simp only [eq_iff_true_of_subsingleton, not_true, and_false_iff]

#print PUnit.sSup_eq /-
@[simp]
theorem sSup_eq : sSup s = unit :=
  rfl
#align punit.Sup_eq PUnit.sSup_eq
-/

#print PUnit.sInf_eq /-
@[simp]
theorem sInf_eq : sInf s = unit :=
  rfl
#align punit.Inf_eq PUnit.sInf_eq
-/

end PUnit

