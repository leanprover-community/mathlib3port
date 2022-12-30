/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies

! This file was ported from Lean 3 source module order.complete_boolean_algebra
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Directed
import Mathbin.Logic.Equiv.Set

/-!
# Frames, completely distributive lattices and Boolean algebras

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
  inf_Sup_le_supr_inf (a : α) (s : Set α) : a ⊓ Sup s ≤ ⨆ b ∈ s, a ⊓ b
#align order.frame Order.Frame
-/

#print Order.Coframe /-
/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
class Order.Coframe (α : Type _) extends CompleteLattice α where
  infi_sup_le_sup_Inf (a : α) (s : Set α) : (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s
#align order.coframe Order.Coframe
-/

open Order

#print CompleteDistribLattice /-
/-- A completely distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type _) extends Frame α where
  infi_sup_le_sup_Inf : ∀ a s, (⨅ b ∈ s, a ⊔ b) ≤ a ⊔ Inf s
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
  { OrderDual.completeLattice α with infi_sup_le_sup_Inf := Frame.inf_Sup_le_supr_inf }
#align order_dual.coframe OrderDual.coframe
-/

/- warning: inf_Sup_eq -> inf_supₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s)) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s)) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align inf_Sup_eq inf_supₛ_eqₓ'. -/
theorem inf_supₛ_eq : a ⊓ supₛ s = ⨆ b ∈ s, a ⊓ b :=
  (Frame.inf_Sup_le_supr_inf _ _).antisymm supᵢ_inf_le_inf_supₛ
#align inf_Sup_eq inf_supₛ_eq

/- warning: Sup_inf_eq -> supₛ_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s) b) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) α (fun (a : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s) b) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) α (fun (a : α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align Sup_inf_eq supₛ_inf_eqₓ'. -/
theorem supₛ_inf_eq : supₛ s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_supₛ_eq α _ s b
#align Sup_inf_eq supₛ_inf_eq

/- warning: supr_inf_eq -> supᵢ_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i)) a) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i) a))
Case conversion may be inaccurate. Consider using '#align supr_inf_eq supᵢ_inf_eqₓ'. -/
theorem supᵢ_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [supᵢ, supₛ_inf_eq, supᵢ_range]
#align supr_inf_eq supᵢ_inf_eq

/- warning: inf_supr_eq -> inf_supᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i)))
Case conversion may be inaccurate. Consider using '#align inf_supr_eq inf_supᵢ_eqₓ'. -/
theorem inf_supᵢ_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using supᵢ_inf_eq f a
#align inf_supr_eq inf_supᵢ_eq

/- warning: bsupr_inf_eq -> supᵢ₂_inf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j))) a) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i j) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i j) a)))
Case conversion may be inaccurate. Consider using '#align bsupr_inf_eq supᵢ₂_inf_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_inf_eq {f : ∀ i, κ i → α} (a : α) : (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a :=
  by simp only [supᵢ_inf_eq]
#align bsupr_inf_eq supᵢ₂_inf_eq

/- warning: inf_bsupr_eq -> inf_supᵢ₂_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j)))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) a (f i j))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (f i j))))
Case conversion may be inaccurate. Consider using '#align inf_bsupr_eq inf_supᵢ₂_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem inf_supᵢ₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j :=
  by simp only [inf_supᵢ_eq]
#align inf_bsupr_eq inf_supᵢ₂_eq

/- warning: supr_inf_supr -> supᵢ_inf_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι' (fun (j : ι') => g j))) (supᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (i : Prod.{u2, u3} ι ι') => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' i)) (g (Prod.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Frame.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u3} α (HasInf.inf.{u3} α (Lattice.toHasInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (supᵢ.{u3, succ u2} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => f i)) (supᵢ.{u3, succ u1} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι' (fun (j : ι') => g j))) (supᵢ.{u3, max (succ u2) (succ u1)} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (i : Prod.{u2, u1} ι ι') => HasInf.inf.{u3} α (Lattice.toHasInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (f (Prod.fst.{u2, u1} ι ι' i)) (g (Prod.snd.{u2, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align supr_inf_supr supᵢ_inf_supᵢₓ'. -/
theorem supᵢ_inf_supᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp only [inf_supᵢ_eq, supᵢ_inf_eq, supᵢ_prod]
#align supr_inf_supr supᵢ_inf_supᵢ

/- warning: bsupr_inf_bsupr -> bsupᵢ_inf_bsupᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u3} ι'}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (supᵢ.{u1, succ u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι' (fun (j : ι') => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) (fun (H : Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) => g j)))) (supᵢ.{u1, succ (max u2 u3)} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (p : Prod.{u2, u3} ι ι') => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' p)) (g (Prod.snd.{u2, u3} ι ι' p)))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Frame.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u1} ι'}, Eq.{succ u3} α (HasInf.inf.{u3} α (Lattice.toHasInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (supᵢ.{u3, succ u2} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => supᵢ.{u3, 0} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (supᵢ.{u3, succ u1} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) ι' (fun (j : ι') => supᵢ.{u3, 0} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) (fun (H : Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) => g j)))) (supᵢ.{u3, succ (max u2 u1)} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (p : Prod.{u2, u1} ι ι') => supᵢ.{u3, 0} α (CompleteLattice.toSupSet.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) (fun (H : Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) => HasInf.inf.{u3} α (Lattice.toHasInf.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_1))) (f (Prod.fst.{u2, u1} ι ι' p)) (g (Prod.snd.{u2, u1} ι ι' p)))))
Case conversion may be inaccurate. Consider using '#align bsupr_inf_bsupr bsupᵢ_inf_bsupᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem bsupᵢ_inf_bsupᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 :=
  by
  simp only [supᵢ_subtype', supᵢ_inf_supᵢ]
  exact (Equiv.surjective _).supr_congr (Equiv.Set.prod s t).symm fun x => rfl
#align bsupr_inf_bsupr bsupᵢ_inf_bsupᵢ

/- warning: Sup_inf_Sup -> supₛ_inf_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) t)) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) t)) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
Case conversion may be inaccurate. Consider using '#align Sup_inf_Sup supₛ_inf_supₛₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem supₛ_inf_supₛ : supₛ s ⊓ supₛ t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [supₛ_eq_supᵢ, bsupᵢ_inf_bsupᵢ]
#align Sup_inf_Sup supₛ_inf_supₛ

/- warning: supr_disjoint_iff -> supᵢ_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i) a)
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i)) a) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i) a)
Case conversion may be inaccurate. Consider using '#align supr_disjoint_iff supᵢ_disjoint_iffₓ'. -/
theorem supᵢ_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, supᵢ_inf_eq, supᵢ_eq_bot]
#align supr_disjoint_iff supᵢ_disjoint_iff

/- warning: disjoint_supr_iff -> disjoint_supᵢ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : ι -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (forall (i : ι), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i))
Case conversion may be inaccurate. Consider using '#align disjoint_supr_iff disjoint_supᵢ_iffₓ'. -/
theorem disjoint_supᵢ_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [Disjoint.comm] using supᵢ_disjoint_iff
#align disjoint_supr_iff disjoint_supᵢ_iff

/- warning: supr₂_disjoint_iff -> supᵢ₂_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (f i j) a)
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (forall (i : ι) (j : κ i), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i j) a)
Case conversion may be inaccurate. Consider using '#align supr₂_disjoint_iff supᵢ₂_disjoint_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by simp_rw [supᵢ_disjoint_iff]
#align supr₂_disjoint_iff supᵢ₂_disjoint_iff

/- warning: disjoint_supr₂_iff -> disjoint_supᵢ₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Frame.{u1} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => supᵢ.{u1, u3} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (f i j))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Frame.{u2} α] {a : α} {f : forall (i : ι), (κ i) -> α}, Iff (Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (supᵢ.{u2, u3} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => supᵢ.{u2, u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (forall (i : ι) (j : κ i), Disjoint.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (BoundedOrder.toOrderBot.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) a (f i j))
Case conversion may be inaccurate. Consider using '#align disjoint_supr₂_iff disjoint_supᵢ₂_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem disjoint_supᵢ₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by simp_rw [disjoint_supᵢ_iff]
#align disjoint_supr₂_iff disjoint_supᵢ₂_iff

/- warning: Sup_disjoint_iff -> supₛ_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s) a) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s) a) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) b a))
Case conversion may be inaccurate. Consider using '#align Sup_disjoint_iff supₛ_disjoint_iffₓ'. -/
theorem supₛ_disjoint_iff {s : Set α} : Disjoint (supₛ s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, supₛ_inf_eq, supᵢ_eq_bot]
#align Sup_disjoint_iff supₛ_disjoint_iff

/- warning: disjoint_Sup_iff -> disjoint_supₛ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) s)) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a (SupSet.supₛ.{u1} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)) s)) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (Disjoint.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) (BoundedOrder.toOrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align disjoint_Sup_iff disjoint_supₛ_iffₓ'. -/
theorem disjoint_supₛ_iff {s : Set α} : Disjoint a (supₛ s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [Disjoint.comm] using supₛ_disjoint_iff
#align disjoint_Sup_iff disjoint_supₛ_iff

/- warning: supr_inf_of_monotone -> supᵢ_inf_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2))] {f : ι -> α} {g : ι -> α}, (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) f) -> (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Frame.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1669 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1671 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1669 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1671)] {f : ι -> α} {g : ι -> α}, (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) f) -> (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i) (g i))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align supr_inf_of_monotone supᵢ_inf_of_monotoneₓ'. -/
theorem supᵢ_inf_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i :=
  by
  refine' (le_supᵢ_inf_supᵢ f g).antisymm _
  rw [supᵢ_inf_supᵢ]
  refine' supᵢ_mono' fun i => _
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩
#align supr_inf_of_monotone supᵢ_inf_of_monotone

/- warning: supr_inf_of_antitone -> supᵢ_inf_of_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Frame.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2)))] {f : ι -> α} {g : ι -> α}, (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1)))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Frame.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1876 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1878 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1876 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.1878))] {f : ι -> α} {g : ι -> α}, (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) f) -> (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (f i) (g i))) (HasInf.inf.{u2} α (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1))) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α (Order.Frame.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align supr_inf_of_antitone supᵢ_inf_of_antitoneₓ'. -/
theorem supᵢ_inf_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨆ i, f i ⊓ g i) = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @supᵢ_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left
#align supr_inf_of_antitone supᵢ_inf_of_antitone

#print Pi.frame /-
instance Pi.frame {ι : Type _} {π : ι → Type _} [∀ i, Frame (π i)] : Frame (∀ i, π i) :=
  { Pi.completeLattice with
    inf_Sup_le_supr_inf := fun a s i => by
      simp only [CompleteLattice.sup, supₛ_apply, supᵢ_apply, Pi.inf_apply, inf_supᵢ_eq, ←
        supᵢ_subtype''] }
#align pi.frame Pi.frame
-/

#print Frame.toDistribLattice /-
-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← supₛ_pair, ← supₛ_pair, inf_supₛ_eq, ← supₛ_image, image_pair]
#align frame.to_distrib_lattice Frame.toDistribLattice
-/

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b : α}

#print OrderDual.frame /-
instance OrderDual.frame : Frame αᵒᵈ :=
  { OrderDual.completeLattice α with inf_Sup_le_supr_inf := Coframe.infi_sup_le_sup_Inf }
#align order_dual.frame OrderDual.frame
-/

/- warning: sup_Inf_eq -> sup_infₛ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) s)) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {a : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) s)) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
Case conversion may be inaccurate. Consider using '#align sup_Inf_eq sup_infₛ_eqₓ'. -/
theorem sup_infₛ_eq : a ⊔ infₛ s = ⨅ b ∈ s, a ⊔ b :=
  @inf_supₛ_eq αᵒᵈ _ _ _
#align sup_Inf_eq sup_infₛ_eq

/- warning: Inf_sup_eq -> infₛ_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) s) b) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) α (fun (a : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {b : α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) s) b) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) α (fun (a : α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a b)))
Case conversion may be inaccurate. Consider using '#align Inf_sup_eq infₛ_sup_eqₓ'. -/
theorem infₛ_sup_eq : infₛ s ⊔ b = ⨅ a ∈ s, a ⊔ b :=
  @supₛ_inf_eq αᵒᵈ _ _ _
#align Inf_sup_eq infₛ_sup_eq

/- warning: infi_sup_eq -> infᵢ_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) a) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (f : ι -> α) (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i)) a) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) a))
Case conversion may be inaccurate. Consider using '#align infi_sup_eq infᵢ_sup_eqₓ'. -/
theorem infᵢ_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
  @supᵢ_inf_eq αᵒᵈ _ _ _ _
#align infi_sup_eq infᵢ_sup_eq

/- warning: sup_infi_eq -> sup_infᵢ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Order.Coframe.{u1} α] (a : α) (f : ι -> α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => f i))) (infᵢ.{u1, u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (f i)))
Case conversion may be inaccurate. Consider using '#align sup_infi_eq sup_infᵢ_eqₓ'. -/
theorem sup_infᵢ_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i :=
  @inf_supᵢ_eq αᵒᵈ _ _ _ _
#align sup_infi_eq sup_infᵢ_eq

/- warning: binfi_sup_eq -> infᵢ₂_sup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Coframe.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j))) a) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i j) a)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Coframe.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j))) a) (infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (f i j) a)))
Case conversion may be inaccurate. Consider using '#align binfi_sup_eq infᵢ₂_sup_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @supᵢ₂_inf_eq αᵒᵈ _ _ _ _ _
#align binfi_sup_eq infᵢ₂_sup_eq

/- warning: sup_binfi_eq -> sup_infᵢ₂_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Order.Coframe.{u1} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => f i j)))) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => infᵢ.{u1, u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (κ i) (fun (j : κ i) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) a (f i j))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u1}} [_inst_1 : Order.Coframe.{u2} α] {f : forall (i : ι), (κ i) -> α} (a : α), Eq.{succ u2} α (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) a (infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => f i j)))) (infᵢ.{u2, u3} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => infᵢ.{u2, u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) (κ i) (fun (j : κ i) => HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) a (f i j))))
Case conversion may be inaccurate. Consider using '#align sup_binfi_eq sup_infᵢ₂_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem sup_infᵢ₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_supᵢ₂_eq αᵒᵈ _ _ _ _ _
#align sup_binfi_eq sup_infᵢ₂_eq

/- warning: infi_sup_infi -> infᵢ_sup_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι' (fun (i : ι') => g i))) (infᵢ.{u1, max (succ u2) (succ u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (i : Prod.{u2, u3} ι ι') => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' i)) (g (Prod.snd.{u2, u3} ι ι' i))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Coframe.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α}, Eq.{succ u3} α (HasSup.sup.{u3} α (SemilatticeSup.toHasSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (infᵢ.{u3, succ u2} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => f i)) (infᵢ.{u3, succ u1} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι' (fun (i : ι') => g i))) (infᵢ.{u3, max (succ u2) (succ u1)} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (i : Prod.{u2, u1} ι ι') => HasSup.sup.{u3} α (SemilatticeSup.toHasSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (f (Prod.fst.{u2, u1} ι ι' i)) (g (Prod.snd.{u2, u1} ι ι' i))))
Case conversion may be inaccurate. Consider using '#align infi_sup_infi infᵢ_sup_infᵢₓ'. -/
theorem infᵢ_sup_infᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @supᵢ_inf_supᵢ αᵒᵈ _ _ _ _ _
#align infi_sup_infi infᵢ_sup_infᵢ

/- warning: binfi_sup_binfi -> binfᵢ_sup_binfᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} {ι' : Type.{u3}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u3} ι'}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => f i))) (infᵢ.{u1, succ u3} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι' (fun (j : ι') => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) (fun (H : Membership.Mem.{u3, u3} ι' (Set.{u3} ι') (Set.hasMem.{u3} ι') j t) => g j)))) (infᵢ.{u1, succ (max u2 u3)} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Prod.{u2, u3} ι ι') (fun (p : Prod.{u2, u3} ι ι') => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) (fun (H : Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} ι ι') (Set.{max u2 u3} (Prod.{u2, u3} ι ι')) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} ι ι')) p (Set.prod.{u2, u3} ι ι' s t)) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' p)) (g (Prod.snd.{u2, u3} ι ι' p)))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : Order.Coframe.{u3} α] {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> α} {g : ι' -> α} {s : Set.{u2} ι} {t : Set.{u1} ι'}, Eq.{succ u3} α (HasSup.sup.{u3} α (SemilatticeSup.toHasSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (infᵢ.{u3, succ u2} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι (fun (i : ι) => infᵢ.{u3, 0} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i))) (infᵢ.{u3, succ u1} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) ι' (fun (j : ι') => infᵢ.{u3, 0} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) (fun (H : Membership.mem.{u1, u1} ι' (Set.{u1} ι') (Set.instMembershipSet.{u1} ι') j t) => g j)))) (infᵢ.{u3, succ (max u2 u1)} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Prod.{u2, u1} ι ι') (fun (p : Prod.{u2, u1} ι ι') => infᵢ.{u3, 0} α (CompleteLattice.toInfSet.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)) (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) (fun (H : Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} ι ι') (Set.{max u1 u2} (Prod.{u2, u1} ι ι')) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} ι ι')) p (Set.prod.{u2, u1} ι ι' s t)) => HasSup.sup.{u3} α (SemilatticeSup.toHasSup.{u3} α (Lattice.toSemilatticeSup.{u3} α (CompleteLattice.toLattice.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_1)))) (f (Prod.fst.{u2, u1} ι ι' p)) (g (Prod.snd.{u2, u1} ι ι' p)))))
Case conversion may be inaccurate. Consider using '#align binfi_sup_binfi binfᵢ_sup_binfᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem binfᵢ_sup_binfᵢ {ι ι' : Type _} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @bsupᵢ_inf_bsupᵢ αᵒᵈ _ _ _ _ _ _ _
#align binfi_sup_binfi binfᵢ_sup_binfᵢ

/- warning: Inf_sup_Inf -> infₛ_sup_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) s) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) t)) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) s) (InfSet.infₛ.{u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) t)) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) (fun (H : Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) p (Set.prod.{u1, u1} α α s t)) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))))
Case conversion may be inaccurate. Consider using '#align Inf_sup_Inf infₛ_sup_infₛₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem infₛ_sup_infₛ : infₛ s ⊔ infₛ t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @supₛ_inf_supₛ αᵒᵈ _ _ _
#align Inf_sup_Inf infₛ_sup_infₛ

/- warning: infi_sup_of_monotone -> infᵢ_sup_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (Function.swap.{succ u2, succ u2, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2)))] {f : ι -> α} {g : ι -> α}, (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) f) -> (Monotone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Coframe.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (Function.swap.{succ u1, succ u1, 1} ι ι (fun (ᾰ : ι) (ᾰ : ι) => Prop) (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3115 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3117 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3115 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3117))] {f : ι -> α} {g : ι -> α}, (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) f) -> (Monotone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (f i) (g i))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align infi_sup_of_monotone infᵢ_sup_of_monotoneₓ'. -/
theorem infᵢ_sup_of_monotone {ι : Type _} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  supᵢ_inf_of_antitone hf.dual_right hg.dual_right
#align infi_sup_of_monotone infᵢ_sup_of_monotone

/- warning: infi_sup_of_antitone -> infᵢ_sup_of_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Order.Coframe.{u1} α] {ι : Type.{u2}} [_inst_2 : Preorder.{u2} ι] [_inst_3 : IsDirected.{u2} ι (LE.le.{u2} ι (Preorder.toLE.{u2} ι _inst_2))] {f : ι -> α} {g : ι -> α}, (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) f) -> (Antitone.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) g) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (f i) (g i))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1)))) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => f i)) (infᵢ.{u1, succ u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_1))) ι (fun (i : ι) => g i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Order.Coframe.{u2} α] {ι : Type.{u1}} [_inst_2 : Preorder.{u1} ι] [_inst_3 : IsDirected.{u1} ι (fun (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3249 : ι) (x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3251 : ι) => LE.le.{u1} ι (Preorder.toLE.{u1} ι _inst_2) x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3249 x._@.Mathlib.Order.CompleteBooleanAlgebra._hyg.3251)] {f : ι -> α} {g : ι -> α}, (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) f) -> (Antitone.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) g) -> (Eq.{succ u2} α (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (f i) (g i))) (HasSup.sup.{u2} α (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)))) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => f i)) (infᵢ.{u2, succ u1} α (CompleteLattice.toInfSet.{u2} α (Order.Coframe.toCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => g i))))
Case conversion may be inaccurate. Consider using '#align infi_sup_of_antitone infᵢ_sup_of_antitoneₓ'. -/
theorem infᵢ_sup_of_antitone {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : (⨅ i, f i ⊔ g i) = (⨅ i, f i) ⊔ ⨅ i, g i :=
  supᵢ_inf_of_monotone hf.dual_right hg.dual_right
#align infi_sup_of_antitone infᵢ_sup_of_antitone

#print Pi.coframe /-
instance Pi.coframe {ι : Type _} {π : ι → Type _} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) :=
  { Pi.completeLattice with
    inf := infₛ
    infi_sup_le_sup_Inf := fun a s i => by
      simp only [← sup_infᵢ_eq, infₛ_apply, ← infᵢ_subtype'', infᵢ_apply, Pi.sup_apply] }
#align pi.coframe Pi.coframe
-/

#print Coframe.toDistribLattice /-
-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α :=
  { ‹Coframe α› with
    le_sup_inf := fun a b c => by
      rw [← infₛ_pair, ← infₛ_pair, sup_infₛ_eq, ← infₛ_image, image_pair] }
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
    infi_sup_le_sup_Inf := fun p s =>
      Iff.mp <| by simp only [forall_or_left, CompleteLattice.inf, infᵢ_Prop_eq, sup_Prop_eq]
    inf_Sup_le_supr_inf := fun p s =>
      Iff.mp <| by simp only [CompleteLattice.sup, exists_and_left, inf_Prop_eq, supᵢ_Prop_eq] }
#align Prop.complete_boolean_algebra Prop.completeBooleanAlgebra
-/

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {a b : α} {s : Set α} {f : ι → α}

/- warning: compl_infi -> compl_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι f)) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (infᵢ.{u1, u2} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) ι f)) (supᵢ.{u1, u2} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
Case conversion may be inaccurate. Consider using '#align compl_infi compl_infᵢₓ'. -/
theorem compl_infᵢ : infᵢ fᶜ = ⨆ i, f iᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_infᵢ fun i => compl_le_of_compl_le <| le_supᵢ (compl ∘ f) i)
    (supᵢ_le fun i => compl_le_compl <| infᵢ_le _ _)
#align compl_infi compl_infᵢ

/- warning: compl_supr -> compl_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (supᵢ.{u1, u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι f)) (infᵢ.{u1, u2} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {f : ι -> α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (supᵢ.{u1, u2} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) ι f)) (infᵢ.{u1, u2} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) ι (fun (i : ι) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (f i)))
Case conversion may be inaccurate. Consider using '#align compl_supr compl_supᵢₓ'. -/
theorem compl_supᵢ : supᵢ fᶜ = ⨅ i, f iᶜ :=
  compl_injective (by simp [compl_infᵢ])
#align compl_supr compl_supᵢ

/- warning: compl_Inf -> compl_infₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) α (fun (i : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.infₛ.{u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) s)) (supᵢ.{u1, succ u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) α (fun (i : α) => supᵢ.{u1, 0} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
Case conversion may be inaccurate. Consider using '#align compl_Inf compl_infₛₓ'. -/
theorem compl_infₛ : infₛ sᶜ = ⨆ i ∈ s, iᶜ := by simp only [infₛ_eq_infᵢ, compl_infᵢ]
#align compl_Inf compl_infₛ

/- warning: compl_Sup -> compl_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) α (fun (i : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) s)) (infᵢ.{u1, succ u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) α (fun (i : α) => infᵢ.{u1, 0} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) i s) => HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) i)))
Case conversion may be inaccurate. Consider using '#align compl_Sup compl_supₛₓ'. -/
theorem compl_supₛ : supₛ sᶜ = ⨅ i ∈ s, iᶜ := by simp only [supₛ_eq_supᵢ, compl_supᵢ]
#align compl_Sup compl_supₛ

/- warning: compl_Inf' -> compl_infₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (InfSet.infₛ.{u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) s)) (SupSet.supₛ.{u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align compl_Inf' compl_infₛ'ₓ'. -/
theorem compl_infₛ' : infₛ sᶜ = supₛ (compl '' s) :=
  compl_infₛ.trans supₛ_image.symm
#align compl_Inf' compl_infₛ'

/- warning: compl_Sup' -> compl_supₛ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) s)) (InfSet.infₛ.{u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1))))) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (SupSet.supₛ.{u1} α (CompleteBooleanAlgebra.toSupSet.{u1} α _inst_1) s)) (InfSet.infₛ.{u1} α (CompleteBooleanAlgebra.toInfSet.{u1} α _inst_1) (Set.image.{u1, u1} α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align compl_Sup' compl_supₛ'ₓ'. -/
theorem compl_supₛ' : supₛ sᶜ = infₛ (compl '' s) :=
  compl_supₛ.trans infₛ_image.symm
#align compl_Sup' compl_supₛ'

end CompleteBooleanAlgebra

section lift

/- warning: function.injective.frame -> Function.Injective.frame is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Frame.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Frame.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Frame.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Frame.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Frame.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.frame Function.Injective.frameₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `order.frame` along an injection. -/
@[reducible]
protected def Function.Injective.frame [HasSup α] [HasInf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Frame β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : Frame α :=
  { hf.CompleteLattice f map_sup map_inf map_Sup map_Inf map_top map_bot with
    inf_Sup_le_supr_inf := fun a s => by
      change f (a ⊓ Sup s) ≤ f _
      rw [← supₛ_image, map_inf, map_Sup s, inf_supᵢ₂_eq]
      simp_rw [← map_inf]
      exact ((map_Sup _).trans supᵢ_image).ge }
#align function.injective.frame Function.Injective.frame

/- warning: function.injective.coframe -> Function.Injective.coframe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Coframe.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Coframe.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : Order.Coframe.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β _inst_7)))) -> (Order.Coframe.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.coframe Function.Injective.coframeₓ'. -/
-- See note [reducible non-instances]
/-- Pullback an `order.coframe` along an injection. -/
@[reducible]
protected def Function.Injective.coframe [HasSup α] [HasInf α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [Coframe β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) :
    Coframe α :=
  { hf.CompleteLattice f map_sup map_inf map_Sup map_Inf map_top map_bot with
    infi_sup_le_sup_Inf := fun a s => by
      change f _ ≤ f (a ⊔ Inf s)
      rw [← infₛ_image, map_sup, map_Inf s, sup_infᵢ₂_eq]
      simp_rw [← map_sup]
      exact ((map_Inf _).trans infᵢ_image).le }
#align function.injective.coframe Function.Injective.coframe

/- warning: function.injective.complete_distrib_lattice -> Function.Injective.completeDistribLattice is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteDistribLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (CompleteDistribLattice.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : CompleteDistribLattice.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7)))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β _inst_7))))) -> (CompleteDistribLattice.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLatticeₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `complete_distrib_lattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeDistribLattice [HasSup α] [HasInf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [CompleteDistribLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_Sup : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteDistribLattice α :=
  { hf.Frame f map_sup map_inf map_Sup map_Inf map_top map_bot,
    hf.Coframe f map_sup map_inf map_Sup map_Inf map_top map_bot with }
#align function.injective.complete_distrib_lattice Function.Injective.completeDistribLattice

/- warning: function.injective.complete_boolean_algebra -> Function.Injective.completeBooleanAlgebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : HasCompl.{u1} α] [_inst_8 : SDiff.{u1} α] [_inst_9 : CompleteBooleanAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_7 a)) (HasCompl.compl.{u2} β (BooleanAlgebra.toHasCompl.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_8 a b)) (SDiff.sdiff.{u2} β (BooleanAlgebra.toHasSdiff.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a) (f b))) -> (CompleteBooleanAlgebra.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : HasSup.{u1} α] [_inst_2 : HasInf.{u1} α] [_inst_3 : SupSet.{u1} α] [_inst_4 : InfSet.{u1} α] [_inst_5 : Top.{u1} α] [_inst_6 : Bot.{u1} α] [_inst_7 : HasCompl.{u1} α] [_inst_8 : SDiff.{u1} α] [_inst_9 : CompleteBooleanAlgebra.{u2} β] (f : α -> β), (Function.Injective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasSup.sup.{u1} α _inst_1 a b)) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) (f a) (f b))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (HasInf.inf.{u1} α _inst_2 a b)) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (CompleteLattice.toLattice.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9))))) (f a) (f b))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (SupSet.supₛ.{u1} α _inst_3 s)) (supᵢ.{u2, succ u1} β (CompleteBooleanAlgebra.toSupSet.{u2} β _inst_9) α (fun (a : α) => supᵢ.{u2, 0} β (CompleteBooleanAlgebra.toSupSet.{u2} β _inst_9) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (forall (s : Set.{u1} α), Eq.{succ u2} β (f (InfSet.infₛ.{u1} α _inst_4 s)) (infᵢ.{u2, succ u1} β (CompleteBooleanAlgebra.toInfSet.{u2} β _inst_9) α (fun (a : α) => infᵢ.{u2, 0} β (CompleteBooleanAlgebra.toInfSet.{u2} β _inst_9) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) => f a)))) -> (Eq.{succ u2} β (f (Top.top.{u1} α _inst_5)) (Top.top.{u2} β (CompleteLattice.toTop.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (Eq.{succ u2} β (f (Bot.bot.{u1} α _inst_6)) (Bot.bot.{u2} β (CompleteLattice.toBot.{u2} β (Order.Coframe.toCompleteLattice.{u2} β (CompleteDistribLattice.toCoframe.{u2} β (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} β _inst_9)))))) -> (forall (a : α), Eq.{succ u2} β (f (HasCompl.compl.{u1} α _inst_7 a)) (HasCompl.compl.{u2} β (BooleanAlgebra.toHasCompl.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a))) -> (forall (a : α) (b : α), Eq.{succ u2} β (f (SDiff.sdiff.{u1} α _inst_8 a b)) (SDiff.sdiff.{u2} β (BooleanAlgebra.toSDiff.{u2} β (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} β _inst_9)) (f a) (f b))) -> (CompleteBooleanAlgebra.{u1} α)
Case conversion may be inaccurate. Consider using '#align function.injective.complete_boolean_algebra Function.Injective.completeBooleanAlgebraₓ'. -/
-- See note [reducible non-instances]
/-- Pullback a `complete_boolean_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.completeBooleanAlgebra [HasSup α] [HasInf α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Function.Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_Sup : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
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
          sup := fun _ => star
          inf := fun _ => star } <;>
      intros <;>
    first |trivial|simp only [eq_iff_true_of_subsingleton, not_true, and_false_iff]

#print PUnit.supₛ_eq /-
@[simp]
theorem supₛ_eq : supₛ s = star :=
  rfl
#align punit.Sup_eq PUnit.supₛ_eq
-/

#print PUnit.infₛ_eq /-
@[simp]
theorem infₛ_eq : infₛ s = star :=
  rfl
#align punit.Inf_eq PUnit.infₛ_eq
-/

end PUnit

