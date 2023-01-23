/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.lattice
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Lattice

/-!
# Lemmas relating fintypes and order/lattice structure.
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

namespace Finset

variable [Fintype α] {s : Finset α}

/- warning: finset.sup_univ_eq_supr -> Finset.sup_univ_eq_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : α -> β), Eq.{succ u2} β (Finset.sup.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2)) (BoundedOrder.toOrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_2)) (Finset.univ.{u1} α _inst_1) f) (supᵢ.{u2, succ u1} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) α f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : α -> β), Eq.{succ u2} β (Finset.sup.{u2, u1} β α (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2)) (BoundedOrder.toOrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β (Lattice.toSemilatticeSup.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_2)) (Finset.univ.{u1} α _inst_1) f) (supᵢ.{u2, succ u1} β (CompleteLattice.toSupSet.{u2} β _inst_2) α f)
Case conversion may be inaccurate. Consider using '#align finset.sup_univ_eq_supr Finset.sup_univ_eq_supᵢₓ'. -/
/-- A special case of `finset.sup_eq_supr` that omits the useless `x ∈ univ` binder. -/
theorem sup_univ_eq_supᵢ [CompleteLattice β] (f : α → β) : Finset.univ.sup f = supᵢ f :=
  (sup_eq_supᵢ _ f).trans <| congr_arg _ <| funext fun a => supᵢ_pos (mem_univ _)
#align finset.sup_univ_eq_supr Finset.sup_univ_eq_supᵢ

/- warning: finset.inf_univ_eq_infi -> Finset.inf_univ_eq_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : α -> β), Eq.{succ u2} β (Finset.inf.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2)) (BoundedOrder.toOrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_2)) (Finset.univ.{u1} α _inst_1) f) (infᵢ.{u2, succ u1} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) α f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : α -> β), Eq.{succ u2} β (Finset.inf.{u2, u1} β α (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2)) (BoundedOrder.toOrderTop.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2))))) (CompleteLattice.toBoundedOrder.{u2} β _inst_2)) (Finset.univ.{u1} α _inst_1) f) (infᵢ.{u2, succ u1} β (CompleteLattice.toInfSet.{u2} β _inst_2) α f)
Case conversion may be inaccurate. Consider using '#align finset.inf_univ_eq_infi Finset.inf_univ_eq_infᵢₓ'. -/
/-- A special case of `finset.inf_eq_infi` that omits the useless `x ∈ univ` binder. -/
theorem inf_univ_eq_infᵢ [CompleteLattice β] (f : α → β) : Finset.univ.inf f = infᵢ f :=
  sup_univ_eq_supᵢ (f : α → βᵒᵈ)
#align finset.inf_univ_eq_infi Finset.inf_univ_eq_infᵢ

/- warning: finset.fold_inf_univ -> Finset.fold_inf_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : SemilatticeInf.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2)))] (a : α), Eq.{succ u1} α (Finset.fold.{u1, u1} α α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2)) (inf_isCommutative.{u1} α _inst_2) (inf_isAssociative.{u1} α _inst_2) a (fun (x : α) => x) (Finset.univ.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2))) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : SemilatticeInf.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2)))] (a : α), Eq.{succ u1} α (Finset.fold.{u1, u1} α α (fun (x._@.Mathlib.Data.Fintype.Lattice._hyg.147 : α) (x._@.Mathlib.Data.Fintype.Lattice._hyg.149 : α) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) x._@.Mathlib.Data.Fintype.Lattice._hyg.147 x._@.Mathlib.Data.Fintype.Lattice._hyg.149) (inferInstance.{0} (IsCommutative.{u1} α (fun (x._@.Mathlib.Data.Fintype.Lattice._hyg.127 : α) (x._@.Mathlib.Data.Fintype.Lattice._hyg.129 : α) => HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_2) x._@.Mathlib.Data.Fintype.Lattice._hyg.127 x._@.Mathlib.Data.Fintype.Lattice._hyg.129)) (instIsCommutativeInfToHasInf.{u1} α _inst_2)) (instIsAssociativeInfToHasInf.{u1} α _inst_2) a (fun (x : α) => x) (Finset.univ.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_2))) _inst_3))
Case conversion may be inaccurate. Consider using '#align finset.fold_inf_univ Finset.fold_inf_univₓ'. -/
@[simp]
theorem fold_inf_univ [SemilatticeInf α] [OrderBot α] (a : α) :
    (Finset.univ.fold (· ⊓ ·) a fun x => x) = ⊥ :=
  eq_bot_iff.2 <|
    ((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ <| Finset.mem_univ _
#align finset.fold_inf_univ Finset.fold_inf_univ

/- warning: finset.fold_sup_univ -> Finset.fold_sup_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] (a : α), Eq.{succ u1} α (Finset.fold.{u1, u1} α α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2)) (sup_isCommutative.{u1} α _inst_2) (sup_isAssociative.{u1} α _inst_2) a (fun (x : α) => x) (Finset.univ.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] (a : α), Eq.{succ u1} α (Finset.fold.{u1, u1} α α (fun (x._@.Mathlib.Data.Fintype.Lattice._hyg.235 : α) (x._@.Mathlib.Data.Fintype.Lattice._hyg.237 : α) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) x._@.Mathlib.Data.Fintype.Lattice._hyg.235 x._@.Mathlib.Data.Fintype.Lattice._hyg.237) (inferInstance.{0} (IsCommutative.{u1} α (fun (x._@.Mathlib.Data.Fintype.Lattice._hyg.215 : α) (x._@.Mathlib.Data.Fintype.Lattice._hyg.217 : α) => HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) x._@.Mathlib.Data.Fintype.Lattice._hyg.215 x._@.Mathlib.Data.Fintype.Lattice._hyg.217)) (instIsCommutativeSupToHasSup.{u1} α _inst_2)) (instIsAssociativeSupToHasSup.{u1} α _inst_2) a (fun (x : α) => x) (Finset.univ.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) _inst_3))
Case conversion may be inaccurate. Consider using '#align finset.fold_sup_univ Finset.fold_sup_univₓ'. -/
@[simp]
theorem fold_sup_univ [SemilatticeSup α] [OrderTop α] (a : α) :
    (Finset.univ.fold (· ⊔ ·) a fun x => x) = ⊤ :=
  @fold_inf_univ αᵒᵈ ‹Fintype α› _ _ _
#align finset.fold_sup_univ Finset.fold_sup_univ

end Finset

open Finset Function

/- warning: finite.exists_max -> Finite.exists_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : LinearOrder.{u2} β] (f : α -> β), Exists.{succ u1} α (fun (x₀ : α) => forall (x : α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_3))))) (f x) (f x₀))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u2} α] [_inst_2 : Nonempty.{succ u2} α] [_inst_3 : LinearOrder.{u1} β] (f : α -> β), Exists.{succ u2} α (fun (x₀ : α) => forall (x : α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_3)))))) (f x) (f x₀))
Case conversion may be inaccurate. Consider using '#align finite.exists_max Finite.exists_maxₓ'. -/
theorem Finite.exists_max [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x ≤ f x₀ := by
  cases nonempty_fintype α
  simpa using exists_max_image univ f univ_nonempty
#align finite.exists_max Finite.exists_max

/- warning: finite.exists_min -> Finite.exists_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : LinearOrder.{u2} β] (f : α -> β), Exists.{succ u1} α (fun (x₀ : α) => forall (x : α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_3))))) (f x₀) (f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Finite.{succ u2} α] [_inst_2 : Nonempty.{succ u2} α] [_inst_3 : LinearOrder.{u1} β] (f : α -> β), Exists.{succ u2} α (fun (x₀ : α) => forall (x : α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_3)))))) (f x₀) (f x))
Case conversion may be inaccurate. Consider using '#align finite.exists_min Finite.exists_minₓ'. -/
theorem Finite.exists_min [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty
#align finite.exists_min Finite.exists_min

