/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.monotone
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.Disjoint
import Mathbin.Order.SuccPred.Basic

/-!
# Monotonicity on intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that `set.Ici` etc are monotone/antitone functions. We also prove some lemmas
about functions monotone on intervals in `succ_order`s.
-/


open Set

section Ixx

variable {α β : Type _} [Preorder α] [Preorder β] {f g : α → β} {s : Set α}

/- warning: antitone_Ici -> antitone_Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Antitone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.Ici.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Antitone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.Ici.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align antitone_Ici antitone_Iciₓ'. -/
theorem antitone_Ici : Antitone (Ici : α → Set α) := fun _ _ => Ici_subset_Ici.2
#align antitone_Ici antitone_Ici

/- warning: monotone_Iic -> monotone_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Monotone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.Iic.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Monotone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.Iic.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align monotone_Iic monotone_Iicₓ'. -/
theorem monotone_Iic : Monotone (Iic : α → Set α) := fun _ _ => Iic_subset_Iic.2
#align monotone_Iic monotone_Iic

/- warning: antitone_Ioi -> antitone_Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Antitone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.Ioi.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Antitone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.Ioi.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align antitone_Ioi antitone_Ioiₓ'. -/
theorem antitone_Ioi : Antitone (Ioi : α → Set α) := fun _ _ => Ioi_subset_Ioi
#align antitone_Ioi antitone_Ioi

/- warning: monotone_Iio -> monotone_Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Monotone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Set.Iio.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Monotone.{u1, u1} α (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.Iio.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align monotone_Iio monotone_Iioₓ'. -/
theorem monotone_Iio : Monotone (Iio : α → Set α) := fun _ _ => Iio_subset_Iio
#align monotone_Iio monotone_Iio

/- warning: monotone.Ici -> Monotone.Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ici.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ici.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.Ici Monotone.Iciₓ'. -/
protected theorem Monotone.Ici (hf : Monotone f) : Antitone fun x => Ici (f x) :=
  antitone_Ici.comp_monotone hf
#align monotone.Ici Monotone.Ici

/- warning: monotone_on.Ici -> MonotoneOn.Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ici.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ici.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Ici MonotoneOn.Iciₓ'. -/
protected theorem MonotoneOn.Ici (hf : MonotoneOn f s) : AntitoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_monotoneOn hf
#align monotone_on.Ici MonotoneOn.Ici

/- warning: antitone.Ici -> Antitone.Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ici.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ici.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.Ici Antitone.Iciₓ'. -/
protected theorem Antitone.Ici (hf : Antitone f) : Monotone fun x => Ici (f x) :=
  antitone_Ici.comp hf
#align antitone.Ici Antitone.Ici

/- warning: antitone_on.Ici -> AntitoneOn.Ici is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ici.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ici.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Ici AntitoneOn.Iciₓ'. -/
protected theorem AntitoneOn.Ici (hf : AntitoneOn f s) : MonotoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_antitoneOn hf
#align antitone_on.Ici AntitoneOn.Ici

/- warning: monotone.Iic -> Monotone.Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iic.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iic.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.Iic Monotone.Iicₓ'. -/
protected theorem Monotone.Iic (hf : Monotone f) : Monotone fun x => Iic (f x) :=
  monotone_Iic.comp hf
#align monotone.Iic Monotone.Iic

/- warning: monotone_on.Iic -> MonotoneOn.Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iic.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iic.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Iic MonotoneOn.Iicₓ'. -/
protected theorem MonotoneOn.Iic (hf : MonotoneOn f s) : MonotoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_monotoneOn hf
#align monotone_on.Iic MonotoneOn.Iic

/- warning: antitone.Iic -> Antitone.Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iic.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iic.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.Iic Antitone.Iicₓ'. -/
protected theorem Antitone.Iic (hf : Antitone f) : Antitone fun x => Iic (f x) :=
  monotone_Iic.comp_antitone hf
#align antitone.Iic Antitone.Iic

/- warning: antitone_on.Iic -> AntitoneOn.Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iic.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iic.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Iic AntitoneOn.Iicₓ'. -/
protected theorem AntitoneOn.Iic (hf : AntitoneOn f s) : AntitoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_antitoneOn hf
#align antitone_on.Iic AntitoneOn.Iic

/- warning: monotone.Ioi -> Monotone.Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioi.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioi.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.Ioi Monotone.Ioiₓ'. -/
protected theorem Monotone.Ioi (hf : Monotone f) : Antitone fun x => Ioi (f x) :=
  antitone_Ioi.comp_monotone hf
#align monotone.Ioi Monotone.Ioi

/- warning: monotone_on.Ioi -> MonotoneOn.Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioi.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioi.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Ioi MonotoneOn.Ioiₓ'. -/
protected theorem MonotoneOn.Ioi (hf : MonotoneOn f s) : AntitoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_monotoneOn hf
#align monotone_on.Ioi MonotoneOn.Ioi

/- warning: antitone.Ioi -> Antitone.Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioi.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioi.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.Ioi Antitone.Ioiₓ'. -/
protected theorem Antitone.Ioi (hf : Antitone f) : Monotone fun x => Ioi (f x) :=
  antitone_Ioi.comp hf
#align antitone.Ioi Antitone.Ioi

/- warning: antitone_on.Ioi -> AntitoneOn.Ioi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioi.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioi.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Ioi AntitoneOn.Ioiₓ'. -/
protected theorem AntitoneOn.Ioi (hf : AntitoneOn f s) : MonotoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_antitoneOn hf
#align antitone_on.Ioi AntitoneOn.Ioi

/- warning: monotone.Iio -> Monotone.Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iio.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iio.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.Iio Monotone.Iioₓ'. -/
protected theorem Monotone.Iio (hf : Monotone f) : Monotone fun x => Iio (f x) :=
  monotone_Iio.comp hf
#align monotone.Iio Monotone.Iio

/- warning: monotone_on.Iio -> MonotoneOn.Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iio.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iio.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Iio MonotoneOn.Iioₓ'. -/
protected theorem MonotoneOn.Iio (hf : MonotoneOn f s) : MonotoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_monotoneOn hf
#align monotone_on.Iio MonotoneOn.Iio

/- warning: antitone.Iio -> Antitone.Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iio.{u2} β _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iio.{u1} β _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.Iio Antitone.Iioₓ'. -/
protected theorem Antitone.Iio (hf : Antitone f) : Antitone fun x => Iio (f x) :=
  monotone_Iio.comp_antitone hf
#align antitone.Iio Antitone.Iio

/- warning: antitone_on.Iio -> AntitoneOn.Iio is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Iio.{u2} β _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Iio.{u1} β _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Iio AntitoneOn.Iioₓ'. -/
protected theorem AntitoneOn.Iio (hf : AntitoneOn f s) : AntitoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_antitoneOn hf
#align antitone_on.Iio AntitoneOn.Iio

/- warning: monotone.Icc -> Monotone.Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α β _inst_1 _inst_2 g) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Icc.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α β _inst_1 _inst_2 g) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Icc.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.Icc Monotone.Iccₓ'. -/
protected theorem Monotone.Icc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic
#align monotone.Icc Monotone.Icc

/- warning: monotone_on.Icc -> MonotoneOn.Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Icc.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Icc.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Icc MonotoneOn.Iccₓ'. -/
protected theorem MonotoneOn.Icc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic
#align monotone_on.Icc MonotoneOn.Icc

/- warning: antitone.Icc -> Antitone.Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α β _inst_1 _inst_2 g) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Icc.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α β _inst_1 _inst_2 g) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Icc.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.Icc Antitone.Iccₓ'. -/
protected theorem Antitone.Icc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic
#align antitone.Icc Antitone.Icc

/- warning: antitone_on.Icc -> AntitoneOn.Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Icc.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Icc.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Icc AntitoneOn.Iccₓ'. -/
protected theorem AntitoneOn.Icc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic
#align antitone_on.Icc AntitoneOn.Icc

/- warning: monotone.Ico -> Monotone.Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α β _inst_1 _inst_2 g) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ico.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α β _inst_1 _inst_2 g) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ico.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.Ico Monotone.Icoₓ'. -/
protected theorem Monotone.Ico (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio
#align monotone.Ico Monotone.Ico

/- warning: monotone_on.Ico -> MonotoneOn.Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ico.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ico.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Ico MonotoneOn.Icoₓ'. -/
protected theorem MonotoneOn.Ico (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio
#align monotone_on.Ico MonotoneOn.Ico

/- warning: antitone.Ico -> Antitone.Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α β _inst_1 _inst_2 g) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ico.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α β _inst_1 _inst_2 g) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ico.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.Ico Antitone.Icoₓ'. -/
protected theorem Antitone.Ico (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio
#align antitone.Ico Antitone.Ico

/- warning: antitone_on.Ico -> AntitoneOn.Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ico.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ico.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Ico AntitoneOn.Icoₓ'. -/
protected theorem AntitoneOn.Ico (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio
#align antitone_on.Ico AntitoneOn.Ico

/- warning: monotone.Ioc -> Monotone.Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α β _inst_1 _inst_2 g) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioc.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α β _inst_1 _inst_2 g) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioc.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.Ioc Monotone.Iocₓ'. -/
protected theorem Monotone.Ioc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic
#align monotone.Ioc Monotone.Ioc

/- warning: monotone_on.Ioc -> MonotoneOn.Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioc.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioc.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Ioc MonotoneOn.Iocₓ'. -/
protected theorem MonotoneOn.Ioc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic
#align monotone_on.Ioc MonotoneOn.Ioc

/- warning: antitone.Ioc -> Antitone.Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α β _inst_1 _inst_2 g) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioc.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α β _inst_1 _inst_2 g) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioc.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.Ioc Antitone.Iocₓ'. -/
protected theorem Antitone.Ioc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic
#align antitone.Ioc Antitone.Ioc

/- warning: antitone_on.Ioc -> AntitoneOn.Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioc.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioc.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Ioc AntitoneOn.Iocₓ'. -/
protected theorem AntitoneOn.Ioc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic
#align antitone_on.Ioc AntitoneOn.Ioc

/- warning: monotone.Ioo -> Monotone.Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Antitone.{u1, u2} α β _inst_1 _inst_2 g) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioo.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Antitone.{u2, u1} α β _inst_1 _inst_2 g) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioo.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.Ioo Monotone.Iooₓ'. -/
protected theorem Monotone.Ioo (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio
#align monotone.Ioo Monotone.Ioo

/- warning: monotone_on.Ioo -> MonotoneOn.Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioo.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (AntitoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioo.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.Ioo MonotoneOn.Iooₓ'. -/
protected theorem MonotoneOn.Ioo (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio
#align monotone_on.Ioo MonotoneOn.Ioo

/- warning: antitone.Ioo -> Antitone.Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β}, (Antitone.{u1, u2} α β _inst_1 _inst_2 f) -> (Monotone.{u1, u2} α β _inst_1 _inst_2 g) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioo.{u2} β _inst_2 (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β}, (Antitone.{u2, u1} α β _inst_1 _inst_2 f) -> (Monotone.{u2, u1} α β _inst_1 _inst_2 g) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioo.{u1} β _inst_2 (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.Ioo Antitone.Iooₓ'. -/
protected theorem Antitone.Ioo (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio
#align antitone.Ioo Antitone.Ioo

/- warning: antitone_on.Ioo -> AntitoneOn.Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {f : α -> β} {g : α -> β} {s : Set.{u1} α}, (AntitoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (fun (x : α) => Set.Ioo.{u2} β _inst_2 (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {f : α -> β} {g : α -> β} {s : Set.{u2} α}, (AntitoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 g s) -> (MonotoneOn.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (fun (x : α) => Set.Ioo.{u1} β _inst_2 (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.Ioo AntitoneOn.Iooₓ'. -/
protected theorem AntitoneOn.Ioo (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio
#align antitone_on.Ioo AntitoneOn.Ioo

end Ixx

section Union

variable {α β : Type _} [SemilatticeSup α] [LinearOrder β] {f g : α → β} {a b : β}

/- warning: Union_Ioo_of_mono_of_is_glb_of_is_lub -> unionᵢ_Ioo_of_mono_of_isGLB_of_isLUB is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β} {g : α -> β} {a : β} {b : β}, (Antitone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f) -> (Monotone.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) g) -> (IsGLB.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (Set.range.{u2, succ u1} β α f) a) -> (IsLUB.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (Set.range.{u2, succ u1} β α g) b) -> (Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.Ioo.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) (f x) (g x))) (Set.Ioo.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] [_inst_2 : LinearOrder.{u1} β] {f : α -> β} {g : α -> β} {a : β} {b : β}, (Antitone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) f) -> (Monotone.{u2, u1} α β (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1)) (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) g) -> (IsGLB.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (Set.range.{u1, succ u2} β α f) a) -> (IsLUB.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (Set.range.{u1, succ u2} β α g) b) -> (Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (x : α) => Set.Ioo.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) (f x) (g x))) (Set.Ioo.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_2))))) a b))
Case conversion may be inaccurate. Consider using '#align Union_Ioo_of_mono_of_is_glb_of_is_lub unionᵢ_Ioo_of_mono_of_isGLB_of_isLUBₓ'. -/
theorem unionᵢ_Ioo_of_mono_of_isGLB_of_isLUB (hf : Antitone f) (hg : Monotone g)
    (ha : IsGLB (range f) a) (hb : IsLUB (range g) b) : (⋃ x, Ioo (f x) (g x)) = Ioo a b :=
  calc
    (⋃ x, Ioo (f x) (g x)) = (⋃ x, Ioi (f x)) ∩ ⋃ x, Iio (g x) :=
      unionᵢ_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a ∩ Iio b := congr_arg₂ (· ∩ ·) ha.unionᵢ_Ioi_eq hb.unionᵢ_Iio_eq
    
#align Union_Ioo_of_mono_of_is_glb_of_is_lub unionᵢ_Ioo_of_mono_of_isGLB_of_isLUB

end Union

section SuccOrder

open Order

variable {α β : Type _} [PartialOrder α]

#print StrictMonoOn.Iic_id_le /-
theorem StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArchimedean α] [OrderBot α] {n : α} {φ : α → α}
    (hφ : StrictMonoOn φ (Set.Iic n)) : ∀ m ≤ n, m ≤ φ m :=
  by
  revert hφ
  refine'
    Succ.rec_bot (fun n => StrictMonoOn φ (Set.Iic n) → ∀ m ≤ n, m ≤ φ m)
      (fun _ _ hm => hm.trans bot_le) _ _
  rintro k ih hφ m hm
  by_cases hk : IsMax k
  · rw [succ_eq_iff_is_max.2 hk] at hm
    exact ih (hφ.mono <| Iic_subset_Iic.2 (le_succ _)) _ hm
  obtain rfl | h := le_succ_iff_eq_or_le.1 hm
  · specialize ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) k le_rfl
    refine' le_trans (succ_mono ih) (succ_le_of_lt (hφ (le_succ _) le_rfl _))
    rw [lt_succ_iff_eq_or_lt_of_not_is_max hk]
    exact Or.inl rfl
  · exact ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) _ h
#align strict_mono_on.Iic_id_le StrictMonoOn.Iic_id_le
-/

#print StrictMonoOn.Iic_le_id /-
theorem StrictMonoOn.Iic_le_id [PredOrder α] [IsPredArchimedean α] [OrderTop α] {n : α} {φ : α → α}
    (hφ : StrictMonoOn φ (Set.Ici n)) : ∀ m, n ≤ m → φ m ≤ m :=
  @StrictMonoOn.Iic_id_le αᵒᵈ _ _ _ _ _ _ fun i hi j hj hij => hφ hj hi hij
#align strict_mono_on.Iic_le_id StrictMonoOn.Iic_le_id
-/

variable [Preorder β] {ψ : α → β}

/- warning: strict_mono_on_Iic_of_lt_succ -> strictMonoOn_Iic_of_lt_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Preorder.{u2} β] {ψ : α -> β} [_inst_3 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_4 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m n) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_2) (ψ m) (ψ (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 m)))) -> (StrictMonoOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 ψ (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Preorder.{u1} β] {ψ : α -> β} [_inst_3 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] [_inst_4 : IsSuccArchimedean.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) m n) -> (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_2) (ψ m) (ψ (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 m)))) -> (StrictMonoOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 ψ (Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align strict_mono_on_Iic_of_lt_succ strictMonoOn_Iic_of_lt_succₓ'. -/
/-- A function `ψ` on a `succ_order` is strictly monotone before some `n` if for all `m` such that
`m < n`, we have `ψ m < ψ (succ m)`. -/
theorem strictMonoOn_Iic_of_lt_succ [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : ∀ m, m < n → ψ m < ψ (succ m)) : StrictMonoOn ψ (Set.Iic n) :=
  by
  intro x hx y hy hxy
  obtain ⟨i, rfl⟩ := hxy.le.exists_succ_iterate
  induction' i with k ih
  · simpa using hxy
  cases k
  · exact hψ _ (lt_of_lt_of_le hxy hy)
  rw [Set.mem_Iic] at *
  simp only [Function.iterate_succ', Function.comp_apply] at ih hxy hy⊢
  by_cases hmax : IsMax ((succ^[k]) x)
  · rw [succ_eq_iff_is_max.2 hmax] at hxy⊢
    exact ih (le_trans (le_succ _) hy) hxy
  by_cases hmax' : IsMax (succ ((succ^[k]) x))
  · rw [succ_eq_iff_is_max.2 hmax'] at hxy⊢
    exact ih (le_trans (le_succ _) hy) hxy
  refine'
    lt_trans
      (ih (le_trans (le_succ _) hy)
        (lt_of_le_of_lt (le_succ_iterate k _) (lt_succ_iff_not_is_max.2 hmax)))
      _
  rw [← Function.comp_apply succ, ← Function.iterate_succ']
  refine' hψ _ (lt_of_lt_of_le _ hy)
  rwa [Function.iterate_succ', Function.comp_apply, lt_succ_iff_not_is_max]
#align strict_mono_on_Iic_of_lt_succ strictMonoOn_Iic_of_lt_succ

/- warning: strict_anti_on_Iic_of_succ_lt -> strictAntiOn_Iic_of_succ_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Preorder.{u2} β] {ψ : α -> β} [_inst_3 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_4 : IsSuccArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m n) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_2) (ψ (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 m)) (ψ m))) -> (StrictAntiOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 ψ (Set.Iic.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Preorder.{u1} β] {ψ : α -> β} [_inst_3 : SuccOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] [_inst_4 : IsSuccArchimedean.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) m n) -> (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_2) (ψ (Order.succ.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 m)) (ψ m))) -> (StrictAntiOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 ψ (Set.Iic.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align strict_anti_on_Iic_of_succ_lt strictAntiOn_Iic_of_succ_ltₓ'. -/
theorem strictAntiOn_Iic_of_succ_lt [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : ∀ m, m < n → ψ (succ m) < ψ m) : StrictAntiOn ψ (Set.Iic n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij
#align strict_anti_on_Iic_of_succ_lt strictAntiOn_Iic_of_succ_lt

/- warning: strict_mono_on_Iic_of_pred_lt -> strictMonoOn_Iic_of_pred_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Preorder.{u2} β] {ψ : α -> β} [_inst_3 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_4 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) n m) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_2) (ψ (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 m)) (ψ m))) -> (StrictMonoOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 ψ (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Preorder.{u1} β] {ψ : α -> β} [_inst_3 : PredOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] [_inst_4 : IsPredArchimedean.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) n m) -> (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_2) (ψ (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 m)) (ψ m))) -> (StrictMonoOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 ψ (Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align strict_mono_on_Iic_of_pred_lt strictMonoOn_Iic_of_pred_ltₓ'. -/
theorem strictMonoOn_Iic_of_pred_lt [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : ∀ m, n < m → ψ (pred m) < ψ m) : StrictMonoOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij
#align strict_mono_on_Iic_of_pred_lt strictMonoOn_Iic_of_pred_lt

/- warning: strict_anti_on_Iic_of_lt_pred -> strictAntiOn_Iic_of_lt_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Preorder.{u2} β] {ψ : α -> β} [_inst_3 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_4 : IsPredArchimedean.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) n m) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_2) (ψ m) (ψ (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3 m)))) -> (StrictAntiOn.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 ψ (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Preorder.{u1} β] {ψ : α -> β} [_inst_3 : PredOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] [_inst_4 : IsPredArchimedean.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3] {n : α}, (forall (m : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)) n m) -> (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_2) (ψ m) (ψ (Order.pred.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 m)))) -> (StrictAntiOn.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) _inst_2 ψ (Set.Ici.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) n))
Case conversion may be inaccurate. Consider using '#align strict_anti_on_Iic_of_lt_pred strictAntiOn_Iic_of_lt_predₓ'. -/
theorem strictAntiOn_Iic_of_lt_pred [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : ∀ m, n < m → ψ m < ψ (pred m)) : StrictAntiOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictAntiOn_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij
#align strict_anti_on_Iic_of_lt_pred strictAntiOn_Iic_of_lt_pred

end SuccOrder

