/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.multiset.interval
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Dfinsupp.Interval
import Mathbin.Data.Dfinsupp.Multiset
import Mathbin.Data.Nat.Interval

/-!
# Finite intervals of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `dfinsupp`, rather than via filtering
`multiset.powerset`; this is because `(multiset.replicate n x).powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/


open Finset Dfinsupp Function

open BigOperators Pointwise

variable {α : Type _} {β : α → Type _}

namespace Multiset

variable [DecidableEq α] (f g : Multiset α)

instance : LocallyFiniteOrder (Multiset α) :=
  LocallyFiniteOrder.ofIcc (Multiset α)
    (fun f g =>
      (Finset.Icc f.toDfinsupp g.toDfinsupp).map Multiset.equivDfinsupp.toEquiv.symm.toEmbedding)
    fun f g x => by simp

/- warning: multiset.Icc_eq -> Multiset.Icc_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align multiset.Icc_eq Multiset.Icc_eqₓ'. -/
theorem Icc_eq :
    Finset.Icc f g =
      (Finset.Icc f.toDfinsupp g.toDfinsupp).map Multiset.equivDfinsupp.toEquiv.symm.toEmbedding :=
  rfl
#align multiset.Icc_eq Multiset.Icc_eq

/- warning: multiset.card_Icc -> Multiset.card_Icc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Icc.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Multiset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Icc.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Multiset.instLocallyFiniteOrderMultisetToPreorderInstPartialOrderMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Icc Multiset.card_Iccₓ'. -/
theorem card_Icc :
    (Finset.Icc f g).card = ∏ i in f.toFinset ∪ g.toFinset, g.count i + 1 - f.count i := by
  simp_rw [Icc_eq, Finset.card_map, Dfinsupp.card_Icc, Nat.card_Icc, Multiset.toDfinsupp_apply,
    toDfinsupp_support]
#align multiset.card_Icc Multiset.card_Icc

/- warning: multiset.card_Ico -> Multiset.card_Ico is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Ico.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Multiset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Ico.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Multiset.instLocallyFiniteOrderMultisetToPreorderInstPartialOrderMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ico Multiset.card_Icoₓ'. -/
theorem card_Ico :
    (Finset.Ico f g).card = (∏ i in f.toFinset ∪ g.toFinset, g.count i + 1 - f.count i) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ico Multiset.card_Ico

/- warning: multiset.card_Ioc -> Multiset.card_Ioc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Ioc.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Multiset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Ioc.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Multiset.instLocallyFiniteOrderMultisetToPreorderInstPartialOrderMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ioc Multiset.card_Iocₓ'. -/
theorem card_Ioc :
    (Finset.Ioc f g).card = (∏ i in f.toFinset ∪ g.toFinset, g.count i + 1 - f.count i) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ioc Multiset.card_Ioc

/- warning: multiset.card_Ioo -> Multiset.card_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Ioo.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Multiset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α) (g : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Ioo.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Multiset.instLocallyFiniteOrderMultisetToPreorderInstPartialOrderMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) g)) (fun (i : α) => HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i g) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align multiset.card_Ioo Multiset.card_Iooₓ'. -/
theorem card_Ioo :
    (Finset.Ioo f g).card = (∏ i in f.toFinset ∪ g.toFinset, g.count i + 1 - f.count i) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align multiset.card_Ioo Multiset.card_Ioo

/- warning: multiset.card_Iic -> Multiset.card_Iic is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Iic.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α)) (Multiset.orderBot.{u1} α) (Multiset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) f)) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (fun (i : α) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Multiset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Multiset.{u1} α) (Finset.Iic.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α)) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} α) (Multiset.instLocallyFiniteOrderMultisetToPreorderInstPartialOrderMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) f)) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) f) (fun (i : α) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) i f) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align multiset.card_Iic Multiset.card_Iicₓ'. -/
theorem card_Iic : (Finset.Iic f).card = ∏ i in f.toFinset, f.count i + 1 := by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, to_finset_zero, empty_union, count_zero, tsub_zero]
#align multiset.card_Iic Multiset.card_Iic

end Multiset

