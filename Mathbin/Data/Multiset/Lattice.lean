/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.multiset.lattice
! leanprover-community/mathlib commit f2f413b9d4be3a02840d0663dace76e8fe3da053
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.FinsetOps
import Mathbin.Data.Multiset.Fold

/-!
# Lattice operations on multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Multiset

variable {α : Type _}

/-! ### sup -/


section Sup

-- can be defined with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variable [SemilatticeSup α] [OrderBot α]

#print Multiset.sup /-
/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup (s : Multiset α) : α :=
  s.fold (· ⊔ ·) ⊥
#align multiset.sup Multiset.sup
-/

/- warning: multiset.sup_coe -> Multiset.sup_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (l : List.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.foldr.{u1, u1} α α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)) l)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (l : List.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.ofList.{u1} α l)) (List.foldr.{u1, u1} α α (fun (x._@.Mathlib.Data.Multiset.Lattice._hyg.73 : α) (x._@.Mathlib.Data.Multiset.Lattice._hyg.75 : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) x._@.Mathlib.Data.Multiset.Lattice._hyg.73 x._@.Mathlib.Data.Multiset.Lattice._hyg.75) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2)) l)
Case conversion may be inaccurate. Consider using '#align multiset.sup_coe Multiset.sup_coeₓ'. -/
@[simp]
theorem sup_coe (l : List α) : sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥ :=
  rfl
#align multiset.sup_coe Multiset.sup_coe

/- warning: multiset.sup_zero -> Multiset.sup_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))], Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))], Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align multiset.sup_zero Multiset.sup_zeroₓ'. -/
@[simp]
theorem sup_zero : (0 : Multiset α).sup = ⊥ :=
  fold_zero _ _
#align multiset.sup_zero Multiset.sup_zero

/- warning: multiset.sup_cons -> Multiset.sup_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.cons.{u1} α a s)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a (Multiset.sup.{u1} α _inst_1 _inst_2 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.cons.{u1} α a s)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a (Multiset.sup.{u1} α _inst_1 _inst_2 s))
Case conversion may be inaccurate. Consider using '#align multiset.sup_cons Multiset.sup_consₓ'. -/
@[simp]
theorem sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a ⊔ s.sup :=
  fold_cons_left _ _ _ _
#align multiset.sup_cons Multiset.sup_cons

#print Multiset.sup_singleton /-
@[simp]
theorem sup_singleton {a : α} : ({a} : Multiset α).sup = a :=
  sup_bot_eq
#align multiset.sup_singleton Multiset.sup_singleton
-/

/- warning: multiset.sup_add -> Multiset.sup_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s₁ s₂)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (Multiset.sup.{u1} α _inst_1 _inst_2 s₁) (Multiset.sup.{u1} α _inst_1 _inst_2 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s₁ s₂)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (Multiset.sup.{u1} α _inst_1 _inst_2 s₁) (Multiset.sup.{u1} α _inst_1 _inst_2 s₂))
Case conversion may be inaccurate. Consider using '#align multiset.sup_add Multiset.sup_addₓ'. -/
@[simp]
theorem sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
  Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)
#align multiset.sup_add Multiset.sup_add

#print Multiset.sup_le /-
theorem sup_le {s : Multiset α} {a : α} : s.sup ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [or_imp, forall_and])
#align multiset.sup_le Multiset.sup_le
-/

#print Multiset.le_sup /-
theorem le_sup {s : Multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
  sup_le.1 le_rfl _ h
#align multiset.le_sup Multiset.le_sup
-/

#print Multiset.sup_mono /-
theorem sup_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
  sup_le.2 fun b hb => le_sup (h hb)
#align multiset.sup_mono Multiset.sup_mono
-/

variable [DecidableEq α]

#print Multiset.sup_dedup /-
@[simp]
theorem sup_dedup (s : Multiset α) : (dedup s).sup = s.sup :=
  fold_dedup_idem _ _ _
#align multiset.sup_dedup Multiset.sup_dedup
-/

/- warning: multiset.sup_ndunion -> Multiset.sup_ndunion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.ndunion.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s₁ s₂)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (Multiset.sup.{u1} α _inst_1 _inst_2 s₁) (Multiset.sup.{u1} α _inst_1 _inst_2 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.ndunion.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s₁ s₂)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (Multiset.sup.{u1} α _inst_1 _inst_2 s₁) (Multiset.sup.{u1} α _inst_1 _inst_2 s₂))
Case conversion may be inaccurate. Consider using '#align multiset.sup_ndunion Multiset.sup_ndunionₓ'. -/
@[simp]
theorem sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add] <;> simp
#align multiset.sup_ndunion Multiset.sup_ndunion

/- warning: multiset.sup_union -> Multiset.sup_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (Multiset.sup.{u1} α _inst_1 _inst_2 s₁) (Multiset.sup.{u1} α _inst_1 _inst_2 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) (Multiset.sup.{u1} α _inst_1 _inst_2 s₁) (Multiset.sup.{u1} α _inst_1 _inst_2 s₂))
Case conversion may be inaccurate. Consider using '#align multiset.sup_union Multiset.sup_unionₓ'. -/
@[simp]
theorem sup_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add] <;> simp
#align multiset.sup_union Multiset.sup_union

/- warning: multiset.sup_ndinsert -> Multiset.sup_ndinsert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.ndinsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b) a s)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) a (Multiset.sup.{u1} α _inst_1 _inst_2 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.sup.{u1} α _inst_1 _inst_2 (Multiset.ndinsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b) a s)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_1) a (Multiset.sup.{u1} α _inst_1 _inst_2 s))
Case conversion may be inaccurate. Consider using '#align multiset.sup_ndinsert Multiset.sup_ndinsertₓ'. -/
@[simp]
theorem sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a ⊔ s.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_cons] <;> simp
#align multiset.sup_ndinsert Multiset.sup_ndinsert

/- warning: multiset.nodup_sup_iff -> Multiset.nodup_sup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_4 : DecidableEq.{succ u1} α] {m : Multiset.{u1} (Multiset.{u1} α)}, Iff (Multiset.Nodup.{u1} α (Multiset.sup.{u1} (Multiset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} α) (Multiset.lattice.{u1} α (fun (a : α) (b : α) => _inst_4 a b))) (Multiset.orderBot.{u1} α) m)) (forall (a : Multiset.{u1} α), (Membership.Mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.hasMem.{u1} (Multiset.{u1} α)) a m) -> (Multiset.Nodup.{u1} α a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_4 : DecidableEq.{succ u1} α] {m : Multiset.{u1} (Multiset.{u1} α)}, Iff (Multiset.Nodup.{u1} α (Multiset.sup.{u1} (Multiset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} α) (Multiset.instLatticeMultiset.{u1} α (fun (a : α) (b : α) => _inst_4 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} α) m)) (forall (a : Multiset.{u1} α), (Membership.mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instMembershipMultiset.{u1} (Multiset.{u1} α)) a m) -> (Multiset.Nodup.{u1} α a))
Case conversion may be inaccurate. Consider using '#align multiset.nodup_sup_iff Multiset.nodup_sup_iffₓ'. -/
theorem nodup_sup_iff {α : Type _} [DecidableEq α] {m : Multiset (Multiset α)} :
    m.sup.Nodup ↔ ∀ a : Multiset α, a ∈ m → a.Nodup :=
  by
  apply m.induction_on
  · simp
  · intro a s h
    simp [h]
#align multiset.nodup_sup_iff Multiset.nodup_sup_iff

end Sup

/-! ### inf -/


section Inf

-- can be defined with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variable [SemilatticeInf α] [OrderTop α]

#print Multiset.inf /-
/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf (s : Multiset α) : α :=
  s.fold (· ⊓ ·) ⊤
#align multiset.inf Multiset.inf
-/

/- warning: multiset.inf_coe -> Multiset.inf_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (l : List.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.foldr.{u1, u1} α α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) l)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (l : List.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.ofList.{u1} α l)) (List.foldr.{u1, u1} α α (fun (x._@.Mathlib.Data.Multiset.Lattice._hyg.698 : α) (x._@.Mathlib.Data.Multiset.Lattice._hyg.700 : α) => Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) x._@.Mathlib.Data.Multiset.Lattice._hyg.698 x._@.Mathlib.Data.Multiset.Lattice._hyg.700) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2)) l)
Case conversion may be inaccurate. Consider using '#align multiset.inf_coe Multiset.inf_coeₓ'. -/
@[simp]
theorem inf_coe (l : List α) : inf (l : Multiset α) = l.foldr (· ⊓ ·) ⊤ :=
  rfl
#align multiset.inf_coe Multiset.inf_coe

/- warning: multiset.inf_zero -> Multiset.inf_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))], Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))], Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))) _inst_2))
Case conversion may be inaccurate. Consider using '#align multiset.inf_zero Multiset.inf_zeroₓ'. -/
@[simp]
theorem inf_zero : (0 : Multiset α).inf = ⊤ :=
  fold_zero _ _
#align multiset.inf_zero Multiset.inf_zero

/- warning: multiset.inf_cons -> Multiset.inf_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.cons.{u1} α a s)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a (Multiset.inf.{u1} α _inst_1 _inst_2 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.cons.{u1} α a s)) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a (Multiset.inf.{u1} α _inst_1 _inst_2 s))
Case conversion may be inaccurate. Consider using '#align multiset.inf_cons Multiset.inf_consₓ'. -/
@[simp]
theorem inf_cons (a : α) (s : Multiset α) : (a ::ₘ s).inf = a ⊓ s.inf :=
  fold_cons_left _ _ _ _
#align multiset.inf_cons Multiset.inf_cons

#print Multiset.inf_singleton /-
@[simp]
theorem inf_singleton {a : α} : ({a} : Multiset α).inf = a :=
  inf_top_eq
#align multiset.inf_singleton Multiset.inf_singleton
-/

/- warning: multiset.inf_add -> Multiset.inf_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s₁ s₂)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (Multiset.inf.{u1} α _inst_1 _inst_2 s₁) (Multiset.inf.{u1} α _inst_1 _inst_2 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s₁ s₂)) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (Multiset.inf.{u1} α _inst_1 _inst_2 s₁) (Multiset.inf.{u1} α _inst_1 _inst_2 s₂))
Case conversion may be inaccurate. Consider using '#align multiset.inf_add Multiset.inf_addₓ'. -/
@[simp]
theorem inf_add (s₁ s₂ : Multiset α) : (s₁ + s₂).inf = s₁.inf ⊓ s₂.inf :=
  Eq.trans (by simp [inf]) (fold_add _ _ _ _ _)
#align multiset.inf_add Multiset.inf_add

#print Multiset.le_inf /-
theorem le_inf {s : Multiset α} {a : α} : a ≤ s.inf ↔ ∀ b ∈ s, a ≤ b :=
  Multiset.induction_on s (by simp)
    (by simp (config := { contextual := true }) [or_imp, forall_and])
#align multiset.le_inf Multiset.le_inf
-/

#print Multiset.inf_le /-
theorem inf_le {s : Multiset α} {a : α} (h : a ∈ s) : s.inf ≤ a :=
  le_inf.1 le_rfl _ h
#align multiset.inf_le Multiset.inf_le
-/

#print Multiset.inf_mono /-
theorem inf_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.inf ≤ s₁.inf :=
  le_inf.2 fun b hb => inf_le (h hb)
#align multiset.inf_mono Multiset.inf_mono
-/

variable [DecidableEq α]

#print Multiset.inf_dedup /-
@[simp]
theorem inf_dedup (s : Multiset α) : (dedup s).inf = s.inf :=
  fold_dedup_idem _ _ _
#align multiset.inf_dedup Multiset.inf_dedup
-/

/- warning: multiset.inf_ndunion -> Multiset.inf_ndunion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.ndunion.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s₁ s₂)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (Multiset.inf.{u1} α _inst_1 _inst_2 s₁) (Multiset.inf.{u1} α _inst_1 _inst_2 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.ndunion.{u1} α (fun (a : α) (b : α) => _inst_3 a b) s₁ s₂)) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (Multiset.inf.{u1} α _inst_1 _inst_2 s₁) (Multiset.inf.{u1} α _inst_1 _inst_2 s₂))
Case conversion may be inaccurate. Consider using '#align multiset.inf_ndunion Multiset.inf_ndunionₓ'. -/
@[simp]
theorem inf_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).inf = s₁.inf ⊓ s₂.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add] <;> simp
#align multiset.inf_ndunion Multiset.inf_ndunion

/- warning: multiset.inf_union -> Multiset.inf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (Multiset.inf.{u1} α _inst_1 _inst_2 s₁) (Multiset.inf.{u1} α _inst_1 _inst_2 s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (s₁ : Multiset.{u1} α) (s₂ : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂)) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) (Multiset.inf.{u1} α _inst_1 _inst_2 s₁) (Multiset.inf.{u1} α _inst_1 _inst_2 s₂))
Case conversion may be inaccurate. Consider using '#align multiset.inf_union Multiset.inf_unionₓ'. -/
@[simp]
theorem inf_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).inf = s₁.inf ⊓ s₂.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_add] <;> simp
#align multiset.inf_union Multiset.inf_union

/- warning: multiset.inf_ndinsert -> Multiset.inf_ndinsert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.ndinsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b) a s)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) a (Multiset.inf.{u1} α _inst_1 _inst_2 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))] [_inst_3 : DecidableEq.{succ u1} α] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.inf.{u1} α _inst_1 _inst_2 (Multiset.ndinsert.{u1} α (fun (a : α) (b : α) => _inst_3 a b) a s)) (Inf.inf.{u1} α (SemilatticeInf.toInf.{u1} α _inst_1) a (Multiset.inf.{u1} α _inst_1 _inst_2 s))
Case conversion may be inaccurate. Consider using '#align multiset.inf_ndinsert Multiset.inf_ndinsertₓ'. -/
@[simp]
theorem inf_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).inf = a ⊓ s.inf := by
  rw [← inf_dedup, dedup_ext.2, inf_dedup, inf_cons] <;> simp
#align multiset.inf_ndinsert Multiset.inf_ndinsert

end Inf

end Multiset

