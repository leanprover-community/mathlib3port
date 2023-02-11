/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.pi.interval
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Fintype.BigOperators

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/


open Finset Fintype

open BigOperators

variable {ι : Type _} {α : ι → Type _}

namespace Pi

section LocallyFinite

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrder (α i)]
  [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_pi_finset, mem_Icc, le_def, forall_and]

variable (a b : ∀ i, α i)

/- warning: pi.Icc_eq -> Pi.Icc_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (i : ι), α i)) (Finset.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b) (Fintype.piFinset.{u1, u2} ι (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) => α i) (fun (i : ι) => Finset.Icc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (i : ι), α i)) (Finset.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b) (Fintype.piFinset.{u2, u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) => α i) (fun (i : ι) => Finset.Icc.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))
Case conversion may be inaccurate. Consider using '#align pi.Icc_eq Pi.Icc_eqₓ'. -/
theorem Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) :=
  rfl
#align pi.Icc_eq Pi.Icc_eq

/- warning: pi.card_Icc -> Pi.card_Icc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Icc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Icc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Icc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Icc.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i))))
Case conversion may be inaccurate. Consider using '#align pi.card_Icc Pi.card_Iccₓ'. -/
theorem card_Icc : (Icc a b).card = ∏ i, (Icc (a i) (b i)).card :=
  card_piFinset _
#align pi.card_Icc Pi.card_Icc

/- warning: pi.card_Ico -> Pi.card_Ico is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Ico.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Icc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Ico.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Icc.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pi.card_Ico Pi.card_Icoₓ'. -/
theorem card_Ico : (Ico a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align pi.card_Ico Pi.card_Ico

/- warning: pi.card_Ioc -> Pi.card_Ioc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Ioc.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Icc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Ioc.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Icc.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pi.card_Ioc Pi.card_Iocₓ'. -/
theorem card_Ioc : (Ioc a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align pi.card_Ioc Pi.card_Ioc

/- warning: pi.card_Ioo -> Pi.card_Ioo is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Ioo.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrder.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Icc.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrder.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i) (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Ioo.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Icc.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i) (b i)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align pi.card_Ioo Pi.card_Iooₓ'. -/
theorem card_Ioo : (Ioo a b).card = (∏ i, (Icc (a i) (b i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align pi.card_Ioo Pi.card_Ioo

end LocallyFinite

section Bounded

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrder (α i)]

section Bot

variable [∀ i, LocallyFiniteOrderBot (α i)] (b : ∀ i, α i)

instance : LocallyFiniteOrderBot (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_pi_finset, mem_Iic, le_def]

/- warning: pi.card_Iic -> Pi.card_Iic is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderBot.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Iic.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrderBot.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) b)) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Iic.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (b i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderBot.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Iic.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderBotForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) b)) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Iic.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (b i))))
Case conversion may be inaccurate. Consider using '#align pi.card_Iic Pi.card_Iicₓ'. -/
theorem card_Iic : (Iic b).card = ∏ i, (Iic (b i)).card :=
  card_piFinset _
#align pi.card_Iic Pi.card_Iic

/- warning: pi.card_Iio -> Pi.card_Iio is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderBot.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Iio.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrderBot.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Iic.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (b i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderBot.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (b : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Iio.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderBotForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Iic.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (b i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pi.card_Iio Pi.card_Iioₓ'. -/
theorem card_Iio : (Iio b).card = (∏ i, (Iic (b i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
#align pi.card_Iio Pi.card_Iio

end Bot

section Top

variable [∀ i, LocallyFiniteOrderTop (α i)] (a : ∀ i, α i)

instance : LocallyFiniteOrderTop (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_pi_finset, mem_Ici, le_def]

/- warning: pi.card_Ici -> Pi.card_Ici is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderTop.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Ici.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrderTop.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a)) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Ici.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderTop.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Ici.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderTopForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a)) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Ici.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i))))
Case conversion may be inaccurate. Consider using '#align pi.card_Ici Pi.card_Iciₓ'. -/
theorem card_Ici : (Ici a).card = ∏ i, (Ici (a i)).card :=
  card_piFinset _
#align pi.card_Ici Pi.card_Ici

/- warning: pi.card_Ioi -> Pi.card_Ioi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u2} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderTop.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))] (a : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (i : ι), α i) (Finset.Ioi.{max u1 u2} (forall (i : ι), α i) (Pi.preorder.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u2} (α i) (_inst_4 i))) (Pi.locallyFiniteOrderTop.{u1, u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => Finset.card.{u2} (α i) (Finset.Ici.{u2} (α i) (PartialOrder.toPreorder.{u2} (α i) (_inst_4 i)) (_inst_5 i) (a i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (α i)] [_inst_4 : forall (i : ι), PartialOrder.{u1} (α i)] [_inst_5 : forall (i : ι), LocallyFiniteOrderTop.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))] (a : forall (i : ι), α i), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (i : ι), α i) (Finset.Ioi.{max u2 u1} (forall (i : ι), α i) (Pi.preorder.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => PartialOrder.toPreorder.{u1} (α i) (_inst_4 i))) (Pi.instLocallyFiniteOrderTopForAllPreorderToPreorder.{u2, u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) _inst_2 (fun (i : ι) (a : α i) (b : α i) => _inst_3 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => _inst_5 i)) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => Finset.card.{u1} (α i) (Finset.Ici.{u1} (α i) (PartialOrder.toPreorder.{u1} (α i) (_inst_4 i)) (_inst_5 i) (a i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pi.card_Ioi Pi.card_Ioiₓ'. -/
theorem card_Ioi : (Ioi a).card = (∏ i, (Ici (a i)).card) - 1 := by
  rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]
#align pi.card_Ioi Pi.card_Ioi

end Top

end Bounded

end Pi

