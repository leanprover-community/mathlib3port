/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.sigma.interval
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sigma.Order
import Mathbin.Order.LocallyFinite

/-!
# Finite intervals in a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/


open Finset Function

namespace Sigma

variable {ι : Type _} {α : ι → Type _}

/-! ### Disjoint sum of orders -/


section Disjoint

variable [DecidableEq ι] [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (Σi, α i)
    where
  finsetIcc := sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ico, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ioc, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, lt_def, mem_Ioo, exists_and_left, ← exists_and_right, ← exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σi, α i)

/- warning: sigma.card_Icc -> Sigma.card_Icc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (a : Sigma.{u1, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u1, u2} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Finset.Icc.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => Finset.card.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Finset.Icc.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (a : Sigma.{u2, u1} ι (fun (i : ι) => α i)) (b : Sigma.{u2, u1} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.Icc.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => Finset.card.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Finset.Icc.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Interval._hyg.785 : ι) (x._@.Mathlib.Data.Sigma.Interval._hyg.784 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Interval._hyg.785) => α x._@.Mathlib.Data.Sigma.Interval._hyg.785) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align sigma.card_Icc Sigma.card_Iccₓ'. -/
theorem card_Icc : (Icc a b).card = if h : a.1 = b.1 then (Icc (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Icc Sigma.card_Icc

/- warning: sigma.card_Ico -> Sigma.card_Ico is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (a : Sigma.{u1, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u1, u2} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Finset.Ico.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => Finset.card.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Finset.Ico.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (a : Sigma.{u2, u1} ι (fun (i : ι) => α i)) (b : Sigma.{u2, u1} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.Ico.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => Finset.card.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Finset.Ico.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Interval._hyg.880 : ι) (x._@.Mathlib.Data.Sigma.Interval._hyg.879 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Interval._hyg.880) => α x._@.Mathlib.Data.Sigma.Interval._hyg.880) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align sigma.card_Ico Sigma.card_Icoₓ'. -/
theorem card_Ico : (Ico a b).card = if h : a.1 = b.1 then (Ico (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ico Sigma.card_Ico

/- warning: sigma.card_Ioc -> Sigma.card_Ioc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (a : Sigma.{u1, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u1, u2} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Finset.Ioc.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => Finset.card.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Finset.Ioc.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (a : Sigma.{u2, u1} ι (fun (i : ι) => α i)) (b : Sigma.{u2, u1} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.Ioc.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => Finset.card.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Finset.Ioc.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Interval._hyg.975 : ι) (x._@.Mathlib.Data.Sigma.Interval._hyg.974 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Interval._hyg.975) => α x._@.Mathlib.Data.Sigma.Interval._hyg.975) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align sigma.card_Ioc Sigma.card_Iocₓ'. -/
theorem card_Ioc : (Ioc a b).card = if h : a.1 = b.1 then (Ioc (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ioc Sigma.card_Ioc

/- warning: sigma.card_Ioo -> Sigma.card_Ioo is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (a : Sigma.{u1, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u1, u2} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Finset.Ioo.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) => Finset.card.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Finset.Ioo.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b)) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (a : Sigma.{u2, u1} ι (fun (i : ι) => α i)) (b : Sigma.{u2, u1} ι (fun (i : ι) => α i)), Eq.{1} Nat (Finset.card.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.Ioo.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) a b)) (dite.{1} Nat (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_1 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (fun (h : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) => Finset.card.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Finset.Ioo.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_2 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (_inst_3 (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b)) (Eq.rec.{succ u1, succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Sigma.Interval._hyg.1070 : ι) (x._@.Mathlib.Data.Sigma.Interval._hyg.1069 : Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Sigma.Interval._hyg.1070) => α x._@.Mathlib.Data.Sigma.Interval._hyg.1070) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b) h) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) b))) (fun (h : Not (Eq.{succ u2} ι (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) b))) => OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align sigma.card_Ioo Sigma.card_Iooₓ'. -/
theorem card_Ioo : (Ioo a b).card = if h : a.1 = b.1 then (Ioo (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ioo Sigma.card_Ioo

end

variable (i : ι) (a b : α i)

/- warning: sigma.Icc_mk_mk -> Sigma.Icc_mk_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι α)) (Finset.Icc.{max u1 u2} (Sigma.{u1, u2} ι α) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u1, u2} ι α i a) (Sigma.mk.{u1, u2} ι α i b)) (Finset.map.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι α) (Function.Embedding.sigmaMk.{u1, u2} ι α i) (Finset.Icc.{u2} (α i) (_inst_2 i) (_inst_3 i) a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sigma.{u2, u1} ι α)) (Finset.Icc.{max u2 u1} (Sigma.{u2, u1} ι α) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u2, u1} ι α i a) (Sigma.mk.{u2, u1} ι α i b)) (Finset.map.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u2, u1} ι α i) (Finset.Icc.{u1} (α i) (_inst_2 i) (_inst_3 i) a b))
Case conversion may be inaccurate. Consider using '#align sigma.Icc_mk_mk Sigma.Icc_mk_mkₓ'. -/
@[simp]
theorem Icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Icc_mk_mk Sigma.Icc_mk_mk

/- warning: sigma.Ico_mk_mk -> Sigma.Ico_mk_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι α)) (Finset.Ico.{max u1 u2} (Sigma.{u1, u2} ι α) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u1, u2} ι α i a) (Sigma.mk.{u1, u2} ι α i b)) (Finset.map.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι α) (Function.Embedding.sigmaMk.{u1, u2} ι α i) (Finset.Ico.{u2} (α i) (_inst_2 i) (_inst_3 i) a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sigma.{u2, u1} ι α)) (Finset.Ico.{max u2 u1} (Sigma.{u2, u1} ι α) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u2, u1} ι α i a) (Sigma.mk.{u2, u1} ι α i b)) (Finset.map.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u2, u1} ι α i) (Finset.Ico.{u1} (α i) (_inst_2 i) (_inst_3 i) a b))
Case conversion may be inaccurate. Consider using '#align sigma.Ico_mk_mk Sigma.Ico_mk_mkₓ'. -/
@[simp]
theorem Ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ico_mk_mk Sigma.Ico_mk_mk

/- warning: sigma.Ioc_mk_mk -> Sigma.Ioc_mk_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι α)) (Finset.Ioc.{max u1 u2} (Sigma.{u1, u2} ι α) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u1, u2} ι α i a) (Sigma.mk.{u1, u2} ι α i b)) (Finset.map.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι α) (Function.Embedding.sigmaMk.{u1, u2} ι α i) (Finset.Ioc.{u2} (α i) (_inst_2 i) (_inst_3 i) a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sigma.{u2, u1} ι α)) (Finset.Ioc.{max u2 u1} (Sigma.{u2, u1} ι α) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u2, u1} ι α i a) (Sigma.mk.{u2, u1} ι α i b)) (Finset.map.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u2, u1} ι α i) (Finset.Ioc.{u1} (α i) (_inst_2 i) (_inst_3 i) a b))
Case conversion may be inaccurate. Consider using '#align sigma.Ioc_mk_mk Sigma.Ioc_mk_mkₓ'. -/
@[simp]
theorem Ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ioc_mk_mk Sigma.Ioc_mk_mk

/- warning: sigma.Ioo_mk_mk -> Sigma.Ioo_mk_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : forall (i : ι), Preorder.{u2} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι α)) (Finset.Ioo.{max u1 u2} (Sigma.{u1, u2} ι α) (Sigma.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u1, u2} ι α i a) (Sigma.mk.{u1, u2} ι α i b)) (Finset.map.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι α) (Function.Embedding.sigmaMk.{u1, u2} ι α i) (Finset.Ioo.{u2} (α i) (_inst_2 i) (_inst_3 i) a b))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : forall (i : ι), Preorder.{u1} (α i)] [_inst_3 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (_inst_2 i)] (i : ι) (a : α i) (b : α i), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sigma.{u2, u1} ι α)) (Finset.Ioo.{max u2 u1} (Sigma.{u2, u1} ι α) (Sigma.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_2 i)) (Sigma.instLocallyFiniteOrderSigmaPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => _inst_2 i) (fun (i : ι) => _inst_3 i)) (Sigma.mk.{u2, u1} ι α i a) (Sigma.mk.{u2, u1} ι α i b)) (Finset.map.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u2, u1} ι α i) (Finset.Ioo.{u1} (α i) (_inst_2 i) (_inst_3 i) a b))
Case conversion may be inaccurate. Consider using '#align sigma.Ioo_mk_mk Sigma.Ioo_mk_mkₓ'. -/
@[simp]
theorem Ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ioo_mk_mk Sigma.Ioo_mk_mk

end Disjoint

end Sigma

