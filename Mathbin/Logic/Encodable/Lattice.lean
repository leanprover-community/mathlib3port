/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module logic.encodable.lattice
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Encodable.Basic
import Mathbin.Logic.Pairwise

/-!
# Lattice operations on encodable types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lemmas about lattice and set operations on encodable types

## Implementation Notes

This is a separate file, to avoid unnecessary imports in basic files.

Previously some of these results were in the `measure_theory` folder.
-/


open Set

namespace Encodable

variable {α : Type _} {β : Type _} [Encodable β]

/- warning: encodable.supr_decode₂ -> Encodable.supᵢ_decode₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Encodable.{u2} β] [_inst_2 : CompleteLattice.{u1} α] (f : β -> α), Eq.{succ u1} α (supᵢ.{u1, 1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_2)) Nat (fun (i : Nat) => supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_2)) β (fun (b : β) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_2)) (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 i)) (fun (H : Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 i)) => f b)))) (supᵢ.{u1, succ u2} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_2)) β (fun (b : β) => f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Encodable.{u1} β] [_inst_2 : CompleteLattice.{u2} α] (f : β -> α), Eq.{succ u2} α (supᵢ.{u2, 1} α (CompleteLattice.toSupSet.{u2} α _inst_2) Nat (fun (i : Nat) => supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_2) β (fun (b : β) => supᵢ.{u2, 0} α (CompleteLattice.toSupSet.{u2} α _inst_2) (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 i)) (fun (H : Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 i)) => f b)))) (supᵢ.{u2, succ u1} α (CompleteLattice.toSupSet.{u2} α _inst_2) β (fun (b : β) => f b))
Case conversion may be inaccurate. Consider using '#align encodable.supr_decode₂ Encodable.supᵢ_decode₂ₓ'. -/
theorem supᵢ_decode₂ [CompleteLattice α] (f : β → α) :
    (⨆ (i : ℕ) (b ∈ decode₂ β i), f b) = ⨆ b, f b :=
  by
  rw [supᵢ_comm]
  simp [mem_decode₂]
#align encodable.supr_decode₂ Encodable.supᵢ_decode₂

/- warning: encodable.Union_decode₂ -> Encodable.unionᵢ_decode₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Encodable.{u2} β] (f : β -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, 1} α Nat (fun (i : Nat) => Set.unionᵢ.{u1, succ u2} α β (fun (b : β) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 i)) (fun (H : Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 i)) => f b)))) (Set.unionᵢ.{u1, succ u2} α β (fun (b : β) => f b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Encodable.{u1} β] (f : β -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, 1} α Nat (fun (i : Nat) => Set.unionᵢ.{u2, succ u1} α β (fun (b : β) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 i)) (fun (H : Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 i)) => f b)))) (Set.unionᵢ.{u2, succ u1} α β (fun (b : β) => f b))
Case conversion may be inaccurate. Consider using '#align encodable.Union_decode₂ Encodable.unionᵢ_decode₂ₓ'. -/
theorem unionᵢ_decode₂ (f : β → Set α) : (⋃ (i : ℕ) (b ∈ decode₂ β i), f b) = ⋃ b, f b :=
  supᵢ_decode₂ f
#align encodable.Union_decode₂ Encodable.unionᵢ_decode₂

/- warning: encodable.Union_decode₂_cases -> Encodable.unionᵢ_decode₂_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Encodable.{u2} β] {f : β -> (Set.{u1} α)} {C : (Set.{u1} α) -> Prop}, (C (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (forall (b : β), C (f b)) -> (forall {n : Nat}, C (Set.unionᵢ.{u1, succ u2} α β (fun (b : β) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 n)) (fun (H : Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 n)) => f b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Encodable.{u1} β] {f : β -> (Set.{u2} α)} {C : (Set.{u2} α) -> Prop}, (C (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) -> (forall (b : β), C (f b)) -> (forall {n : Nat}, C (Set.unionᵢ.{u2, succ u1} α β (fun (b : β) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 n)) (fun (H : Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 n)) => f b))))
Case conversion may be inaccurate. Consider using '#align encodable.Union_decode₂_cases Encodable.unionᵢ_decode₂_casesₓ'. -/
@[elab_as_elim]
theorem unionᵢ_decode₂_cases {f : β → Set α} {C : Set α → Prop} (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
    C (⋃ b ∈ decode₂ β n, f b) :=
  match decode₂ β n with
  | none => by
    simp
    apply H0
  | some b => by
    convert H1 b
    simp [ext_iff]
#align encodable.Union_decode₂_cases Encodable.unionᵢ_decode₂_cases

/- warning: encodable.Union_decode₂_disjoint_on -> Encodable.unionᵢ_decode₂_disjoint_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Encodable.{u2} β] {f : β -> (Set.{u1} α)}, (Pairwise.{u2} β (Function.onFun.{succ u2, succ u1, 1} β (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) f)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u1, 1} Nat (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))) (fun (i : Nat) => Set.unionᵢ.{u1, succ u2} α β (fun (b : β) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 i)) (fun (H : Membership.Mem.{u2, u2} β (Option.{u2} β) (Option.hasMem.{u2} β) b (Encodable.decode₂.{u2} β _inst_1 i)) => f b)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Encodable.{u1} β] {f : β -> (Set.{u2} α)}, (Pairwise.{u1} β (Function.onFun.{succ u1, succ u2, 1} β (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) f)) -> (Pairwise.{0} Nat (Function.onFun.{1, succ u2, 1} Nat (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (fun (i : Nat) => Set.unionᵢ.{u2, succ u1} α β (fun (b : β) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 i)) (fun (H : Membership.mem.{u1, u1} β (Option.{u1} β) (Option.instMembershipOption.{u1} β) b (Encodable.decode₂.{u1} β _inst_1 i)) => f b)))))
Case conversion may be inaccurate. Consider using '#align encodable.Union_decode₂_disjoint_on Encodable.unionᵢ_decode₂_disjoint_onₓ'. -/
theorem unionᵢ_decode₂_disjoint_on {f : β → Set α} (hd : Pairwise (Disjoint on f)) :
    Pairwise (Disjoint on fun i => ⋃ b ∈ decode₂ β i, f b) :=
  by
  rintro i j ij
  refine' disjoint_left.mpr fun x => _
  suffices ∀ a, encode a = i → x ∈ f a → ∀ b, encode b = j → x ∉ f b by simpa [decode₂_eq_some]
  rintro a rfl ha b rfl hb
  exact (hd (mt (congr_arg encode) ij)).le_bot ⟨ha, hb⟩
#align encodable.Union_decode₂_disjoint_on Encodable.unionᵢ_decode₂_disjoint_on

end Encodable

