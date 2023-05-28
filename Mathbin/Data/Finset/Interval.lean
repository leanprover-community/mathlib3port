/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.interval
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite

/-!
# Intervals of finsets as finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : finset α`, then `finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`finset.Icc {0, 1, 2} {0, 1, 3} = {}`.
-/


variable {α : Type _}

namespace Finset

variable [DecidableEq α] (s t : Finset α)

instance : LocallyFiniteOrder (Finset α)
    where
  finsetIcc s t := t.powerset.filterₓ ((· ⊆ ·) s)
  finsetIco s t := t.ssubsets.filterₓ ((· ⊆ ·) s)
  finsetIoc s t := t.powerset.filterₓ ((· ⊂ ·) s)
  finsetIoo s t := t.ssubsets.filterₓ ((· ⊂ ·) s)
  finset_mem_Icc s t u := by rw [mem_filter, mem_powerset]; exact and_comm' _ _
  finset_mem_Ico s t u := by rw [mem_filter, mem_ssubsets]; exact and_comm' _ _
  finset_mem_Ioc s t u := by rw [mem_filter, mem_powerset]; exact and_comm' _ _
  finset_mem_Ioo s t u := by rw [mem_filter, mem_ssubsets]; exact and_comm' _ _

/- warning: finset.Icc_eq_filter_powerset -> Finset.Icc_eq_filter_powerset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Icc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s) (fun (a : Finset.{u1} α) => Finset.decidableDforallFinset.{u1} α s (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 a)) (Finset.powerset.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Icc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) ((fun (x._@.Mathlib.Data.Finset.Interval._hyg.383 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Interval._hyg.385 : Finset.{u1} α) => HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) x._@.Mathlib.Data.Finset.Interval._hyg.383 x._@.Mathlib.Data.Finset.Interval._hyg.385) s) (fun (a : Finset.{u1} α) => Finset.decidableSubsetFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) (Finset.powerset.{u1} α t))
Case conversion may be inaccurate. Consider using '#align finset.Icc_eq_filter_powerset Finset.Icc_eq_filter_powersetₓ'. -/
theorem Icc_eq_filter_powerset : Icc s t = t.powerset.filterₓ ((· ⊆ ·) s) :=
  rfl
#align finset.Icc_eq_filter_powerset Finset.Icc_eq_filter_powerset

/- warning: finset.Ico_eq_filter_ssubsets -> Finset.Ico_eq_filter_ssubsets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ico.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s) (fun (a : Finset.{u1} α) => Finset.decidableDforallFinset.{u1} α s (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 a)) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ico.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) ((fun (x._@.Mathlib.Data.Finset.Interval._hyg.420 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Interval._hyg.422 : Finset.{u1} α) => HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) x._@.Mathlib.Data.Finset.Interval._hyg.420 x._@.Mathlib.Data.Finset.Interval._hyg.422) s) (fun (a : Finset.{u1} α) => Finset.decidableSubsetFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
Case conversion may be inaccurate. Consider using '#align finset.Ico_eq_filter_ssubsets Finset.Ico_eq_filter_ssubsetsₓ'. -/
theorem Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filterₓ ((· ⊆ ·) s) :=
  rfl
#align finset.Ico_eq_filter_ssubsets Finset.Ico_eq_filter_ssubsets

/- warning: finset.Ioc_eq_filter_powerset -> Finset.Ioc_eq_filter_powerset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ioc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s) (fun (a : Finset.{u1} α) => And.decidable (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s a) (Not (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) a s)) (Finset.decidableDforallFinset.{u1} α s (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 a)) (Not.decidable (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) a s) (Finset.decidableDforallFinset.{u1} α a (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 s)))) (Finset.powerset.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ioc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) ((fun (x._@.Mathlib.Data.Finset.Interval._hyg.457 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Interval._hyg.459 : Finset.{u1} α) => HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) x._@.Mathlib.Data.Finset.Interval._hyg.457 x._@.Mathlib.Data.Finset.Interval._hyg.459) s) (fun (a : Finset.{u1} α) => Finset.decidableSSubsetFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) (Finset.powerset.{u1} α t))
Case conversion may be inaccurate. Consider using '#align finset.Ioc_eq_filter_powerset Finset.Ioc_eq_filter_powersetₓ'. -/
theorem Ioc_eq_filter_powerset : Ioc s t = t.powerset.filterₓ ((· ⊂ ·) s) :=
  rfl
#align finset.Ioc_eq_filter_powerset Finset.Ioc_eq_filter_powerset

/- warning: finset.Ioo_eq_filter_ssubsets -> Finset.Ioo_eq_filter_ssubsets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ioo.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s) (fun (a : Finset.{u1} α) => And.decidable (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s a) (Not (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) a s)) (Finset.decidableDforallFinset.{u1} α s (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 a)) (Not.decidable (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) a s) (Finset.decidableDforallFinset.{u1} α a (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 s)))) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ioo.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.filter.{u1} (Finset.{u1} α) ((fun (x._@.Mathlib.Data.Finset.Interval._hyg.494 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Interval._hyg.496 : Finset.{u1} α) => HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) x._@.Mathlib.Data.Finset.Interval._hyg.494 x._@.Mathlib.Data.Finset.Interval._hyg.496) s) (fun (a : Finset.{u1} α) => Finset.decidableSSubsetFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
Case conversion may be inaccurate. Consider using '#align finset.Ioo_eq_filter_ssubsets Finset.Ioo_eq_filter_ssubsetsₓ'. -/
theorem Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filterₓ ((· ⊂ ·) s) :=
  rfl
#align finset.Ioo_eq_filter_ssubsets Finset.Ioo_eq_filter_ssubsets

/- warning: finset.Iic_eq_powerset -> Finset.Iic_eq_powerset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Iic.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.orderBot.{u1} α) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s) (Finset.powerset.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Iic.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s) (Finset.powerset.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.Iic_eq_powerset Finset.Iic_eq_powersetₓ'. -/
theorem Iic_eq_powerset : Iic s = s.powerset :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iic_eq_powerset Finset.Iic_eq_powerset

/- warning: finset.Iio_eq_ssubsets -> Finset.Iio_eq_ssubsets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Iio.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.orderBot.{u1} α) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Iio.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
Case conversion may be inaccurate. Consider using '#align finset.Iio_eq_ssubsets Finset.Iio_eq_ssubsetsₓ'. -/
theorem Iio_eq_ssubsets : Iio s = s.ssubsets :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iio_eq_ssubsets Finset.Iio_eq_ssubsets

variable {s t}

/- warning: finset.Icc_eq_image_powerset -> Finset.Icc_eq_image_powerset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Icc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.image.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s) (Finset.powerset.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Icc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.image.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) ((fun (x._@.Mathlib.Data.Finset.Interval._hyg.602 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Interval._hyg.604 : Finset.{u1} α) => Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x._@.Mathlib.Data.Finset.Interval._hyg.602 x._@.Mathlib.Data.Finset.Interval._hyg.604) s) (Finset.powerset.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s))))
Case conversion may be inaccurate. Consider using '#align finset.Icc_eq_image_powerset Finset.Icc_eq_image_powersetₓ'. -/
theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image ((· ∪ ·) s) :=
  by
  ext u
  simp_rw [mem_Icc, mem_image, exists_prop, mem_powerset]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, union_subset h <| hv.trans <| sdiff_subset _ _⟩
#align finset.Icc_eq_image_powerset Finset.Icc_eq_image_powerset

/- warning: finset.Ico_eq_image_ssubsets -> Finset.Ico_eq_image_ssubsets is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ico.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.image.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.Ico.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Finset.image.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) ((fun (x._@.Mathlib.Data.Finset.Interval._hyg.698 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Interval._hyg.700 : Finset.{u1} α) => Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x._@.Mathlib.Data.Finset.Interval._hyg.698 x._@.Mathlib.Data.Finset.Interval._hyg.700) s) (Finset.ssubsets.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s))))
Case conversion may be inaccurate. Consider using '#align finset.Ico_eq_image_ssubsets Finset.Ico_eq_image_ssubsetsₓ'. -/
theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image ((· ∪ ·) s) :=
  by
  ext u
  simp_rw [mem_Ico, mem_image, exists_prop, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩
#align finset.Ico_eq_image_ssubsets Finset.Ico_eq_image_ssubsets

/- warning: finset.card_Icc_finset -> Finset.card_Icc_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Icc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.card.{u1} α t) (Finset.card.{u1} α s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Icc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.card.{u1} α t) (Finset.card.{u1} α s))))
Case conversion may be inaccurate. Consider using '#align finset.card_Icc_finset Finset.card_Icc_finsetₓ'. -/
/-- Cardinality of a non-empty `Icc` of finsets. -/
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) :=
  by
  rw [← card_sdiff h, ← card_powerset, Icc_eq_image_powerset h, Finset.card_image_iff]
  rintro u hu v hv (huv : s ⊔ u = s ⊔ v)
  rw [mem_coe, mem_powerset] at hu hv
  rw [← (disjoint_sdiff.mono_right hu : Disjoint s u).sup_sdiff_cancel_left, ←
    (disjoint_sdiff.mono_right hv : Disjoint s v).sup_sdiff_cancel_left, huv]
#align finset.card_Icc_finset Finset.card_Icc_finset

/- warning: finset.card_Ico_finset -> Finset.card_Ico_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Ico.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.card.{u1} α t) (Finset.card.{u1} α s))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Ico.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.card.{u1} α t) (Finset.card.{u1} α s))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align finset.card_Ico_finset Finset.card_Ico_finsetₓ'. -/
/-- Cardinality of an `Ico` of finsets. -/
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc_finset h]
#align finset.card_Ico_finset Finset.card_Ico_finset

/- warning: finset.card_Ioc_finset -> Finset.card_Ioc_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Ioc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.card.{u1} α t) (Finset.card.{u1} α s))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Ioc.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.card.{u1} α t) (Finset.card.{u1} α s))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align finset.card_Ioc_finset Finset.card_Ioc_finsetₓ'. -/
/-- Cardinality of an `Ioc` of finsets. -/
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc_finset h]
#align finset.card_Ioc_finset Finset.card_Ioc_finset

/- warning: finset.card_Ioo_finset -> Finset.card_Ioo_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Ioo.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.card.{u1} α t) (Finset.card.{u1} α s))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Ioo.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.card.{u1} α t) (Finset.card.{u1} α s))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align finset.card_Ioo_finset Finset.card_Ioo_finsetₓ'. -/
/-- Cardinality of an `Ioo` of finsets. -/
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc_finset h]
#align finset.card_Ioo_finset Finset.card_Ioo_finset

/- warning: finset.card_Iic_finset -> Finset.card_Iic_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Iic.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.orderBot.{u1} α) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Finset.card.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Iic.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Finset.card.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.card_Iic_finset Finset.card_Iic_finsetₓ'. -/
/-- Cardinality of an `Iic` of finsets. -/
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]
#align finset.card_Iic_finset Finset.card_Iic_finset

/- warning: finset.card_Iio_finset -> Finset.card_Iio_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Iio.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.orderBot.{u1} α) (Finset.locallyFiniteOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Finset.card.{u1} α s)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α}, Eq.{1} Nat (Finset.card.{u1} (Finset.{u1} α) (Finset.Iio.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.instLocallyFiniteOrderFinsetToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) s)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Finset.card.{u1} α s)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finset.card_Iio_finset Finset.card_Iio_finsetₓ'. -/
/-- Cardinality of an `Iio` of finsets. -/
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets, ssubsets, card_erase_of_mem (mem_powerset_self _), card_powerset]
#align finset.card_Iio_finset Finset.card_Iio_finset

end Finset

