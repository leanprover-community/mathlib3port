/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finsupp.interval
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Finsupp
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Finsupp.Order

/-!
# Finite intervals of finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `finsupp.range_singleton`: Postcomposition with `has_singleton.singleton` on `finset` as a
  `finsupp`.
* `finsupp.range_Icc`: Postcomposition with `finset.Icc` as a `finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/


noncomputable section

open Finset Finsupp Function

open BigOperators Classical Pointwise

variable {ι α : Type _}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}

#print Finsupp.rangeSingleton /-
/-- Pointwise `finset.singleton` bundled as a `finsupp`. -/
@[simps]
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α
    where
  toFun i := {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not, not_mem_support_iff, not_ne_iff]
    exact singleton_injective.eq_iff.symm
#align finsupp.range_singleton Finsupp.rangeSingleton
-/

#print Finsupp.mem_rangeSingleton_apply_iff /-
theorem mem_rangeSingleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton
#align finsupp.mem_range_singleton_apply_iff Finsupp.mem_rangeSingleton_apply_iff
-/

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] {f g : ι →₀ α} {i : ι} {a : α}

#print Finsupp.rangeIcc /-
/-- Pointwise `finset.Icc` bundled as a `finsupp`. -/
@[simps toFun]
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α
    where
  toFun i := Icc (f i) (g i)
  support :=
    haveI := Classical.decEq ι
    f.support ∪ g.support
  mem_support_toFun i :=
    by
    rw [mem_union, ← not_iff_not, not_or, not_mem_support_iff, not_mem_support_iff, not_ne_iff]
    exact Icc_eq_singleton_iff.symm
#align finsupp.range_Icc Finsupp.rangeIcc
-/

/- warning: finsupp.range_Icc_support -> Finsupp.rangeIcc_support is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Zero.{u2} α] [_inst_2 : PartialOrder.{u2} α] [_inst_3 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_2)] [_inst_4 : DecidableEq.{succ u1} ι] (f : Finsupp.{u1, u2} ι α _inst_1) (g : Finsupp.{u1, u2} ι α _inst_1), Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_1) (Finsupp.rangeIcc.{u1, u2} ι α _inst_1 _inst_2 _inst_3 f g)) (Union.union.{u1} (Finset.{u1} ι) (Finset.hasUnion.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b)) (Finsupp.support.{u1, u2} ι α _inst_1 f) (Finsupp.support.{u1, u2} ι α _inst_1 g))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)] (_inst_4 : Finsupp.{u2, u1} ι α _inst_1) (f : Finsupp.{u2, u1} ι α _inst_1), Eq.{succ u2} (Finset.{u2} ι) (Finsupp.support.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_1) (Finsupp.rangeIcc.{u2, u1} ι α _inst_1 _inst_2 _inst_3 _inst_4 f)) (Union.union.{u2} (Finset.{u2} ι) (Finset.instUnionFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b))) (Finsupp.support.{u2, u1} ι α _inst_1 _inst_4) (Finsupp.support.{u2, u1} ι α _inst_1 f))
Case conversion may be inaccurate. Consider using '#align finsupp.range_Icc_support Finsupp.rangeIcc_supportₓ'. -/
@[simp]
theorem rangeIcc_support [DecidableEq ι] (f g : ι →₀ α) :
    (rangeIcc f g).support = f.support ∪ g.support := by convert rfl
#align finsupp.range_Icc_support Finsupp.rangeIcc_support

#print Finsupp.mem_rangeIcc_apply_iff /-
theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i :=
  mem_Icc
#align finsupp.mem_range_Icc_apply_iff Finsupp.mem_rangeIcc_apply_iff
-/

end RangeIcc

section PartialOrder

variable [PartialOrder α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

instance : LocallyFiniteOrder (ι →₀ α) := by
  haveI := Classical.decEq ι <;> haveI := Classical.decEq α <;>
    exact
      LocallyFiniteOrder.ofIcc (ι →₀ α) (fun f g => (f.support ∪ g.support).Finsupp <| f.rangeIcc g)
        fun f g x =>
        by
        refine'
          (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| range_Icc_support _ _).trans
            _
        simp_rw [mem_range_Icc_apply_iff]
        exact forall_and

/- warning: finsupp.Icc_eq -> Finsupp.icc_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Zero.{u2} α] [_inst_3 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] (f : Finsupp.{u1, u2} ι α _inst_2) (g : Finsupp.{u1, u2} ι α _inst_2) [_inst_4 : DecidableEq.{succ u1} ι], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2)) (Finset.Icc.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finsupp.preorder.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α _inst_1)) (Finsupp.locallyFiniteOrder.{u1, u2} ι α _inst_1 _inst_2 _inst_3) f g) (Finset.finsupp.{u1, u2} ι α _inst_2 (Union.union.{u1} (Finset.{u1} ι) (Finset.hasUnion.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b)) (Finsupp.support.{u1, u2} ι α _inst_2 f) (Finsupp.support.{u1, u2} ι α _inst_2 g)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_2)) (fun (_x : Finsupp.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_2)) => ι -> (Finset.{u2} α)) (Finsupp.hasCoeToFun.{u1, u2} ι (Finset.{u2} α) (Finset.zero.{u2} α _inst_2)) (Finsupp.rangeIcc.{u1, u2} ι α _inst_2 _inst_1 _inst_3 f g)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (f : Finsupp.{u2, u1} ι α _inst_2) (g : Finsupp.{u2, u1} ι α _inst_2), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2)) (Finset.Icc.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finsupp.preorder.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_1)) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α _inst_1 _inst_2 _inst_3) f g) (Finset.finsupp.{u2, u1} ι α _inst_2 (Union.union.{u2} (Finset.{u2} ι) (Finset.instUnionFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b))) (Finsupp.support.{u2, u1} ι α _inst_2 f) (Finsupp.support.{u2, u1} ι α _inst_2 g)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_2)) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => Finset.{u1} α) a) (Finsupp.funLike.{u2, u1} ι (Finset.{u1} α) (Finset.zero.{u1} α _inst_2)) (Finsupp.rangeIcc.{u2, u1} ι α _inst_2 _inst_1 _inst_3 f g)))
Case conversion may be inaccurate. Consider using '#align finsupp.Icc_eq Finsupp.icc_eqₓ'. -/
theorem icc_eq [DecidableEq ι] : Icc f g = (f.support ∪ g.support).Finsupp (f.rangeIcc g) := by
  convert rfl
#align finsupp.Icc_eq Finsupp.icc_eq

/- warning: finsupp.card_Icc -> Finsupp.card_Icc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Zero.{u2} α] [_inst_3 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] (f : Finsupp.{u1, u2} ι α _inst_2) (g : Finsupp.{u1, u2} ι α _inst_2) [_inst_4 : DecidableEq.{succ u1} ι], Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finset.Icc.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finsupp.preorder.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α _inst_1)) (Finsupp.locallyFiniteOrder.{u1, u2} ι α _inst_1 _inst_2 _inst_3) f g)) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Union.union.{u1} (Finset.{u1} ι) (Finset.hasUnion.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b)) (Finsupp.support.{u1, u2} ι α _inst_2 f) (Finsupp.support.{u1, u2} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u2} α (Finset.Icc.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) f i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) g i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (f : Finsupp.{u2, u1} ι α _inst_2) (g : Finsupp.{u2, u1} ι α _inst_2), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finset.Icc.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finsupp.preorder.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_1)) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α _inst_1 _inst_2 _inst_3) f g)) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Union.union.{u2} (Finset.{u2} ι) (Finset.instUnionFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b))) (Finsupp.support.{u2, u1} ι α _inst_2 f) (Finsupp.support.{u2, u1} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (Finset.Icc.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1) _inst_3 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) f i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) g i))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_Icc Finsupp.card_Iccₓ'. -/
theorem card_Icc [DecidableEq ι] :
    (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card := by
  simp_rw [Icc_eq, card_finsupp, range_Icc_to_fun]
#align finsupp.card_Icc Finsupp.card_Icc

/- warning: finsupp.card_Ico -> Finsupp.card_Ico is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Zero.{u2} α] [_inst_3 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] (f : Finsupp.{u1, u2} ι α _inst_2) (g : Finsupp.{u1, u2} ι α _inst_2) [_inst_4 : DecidableEq.{succ u1} ι], Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finset.Ico.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finsupp.preorder.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α _inst_1)) (Finsupp.locallyFiniteOrder.{u1, u2} ι α _inst_1 _inst_2 _inst_3) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Union.union.{u1} (Finset.{u1} ι) (Finset.hasUnion.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b)) (Finsupp.support.{u1, u2} ι α _inst_2 f) (Finsupp.support.{u1, u2} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u2} α (Finset.Icc.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) f i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) g i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (f : Finsupp.{u2, u1} ι α _inst_2) (g : Finsupp.{u2, u1} ι α _inst_2), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finset.Ico.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finsupp.preorder.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_1)) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α _inst_1 _inst_2 _inst_3) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Union.union.{u2} (Finset.{u2} ι) (Finset.instUnionFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b))) (Finsupp.support.{u2, u1} ι α _inst_2 f) (Finsupp.support.{u2, u1} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (Finset.Icc.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1) _inst_3 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) f i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) g i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finsupp.card_Ico Finsupp.card_Icoₓ'. -/
theorem card_Ico [DecidableEq ι] :
    (Ico f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align finsupp.card_Ico Finsupp.card_Ico

/- warning: finsupp.card_Ioc -> Finsupp.card_Ioc is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Zero.{u2} α] [_inst_3 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] (f : Finsupp.{u1, u2} ι α _inst_2) (g : Finsupp.{u1, u2} ι α _inst_2) [_inst_4 : DecidableEq.{succ u1} ι], Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finset.Ioc.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finsupp.preorder.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α _inst_1)) (Finsupp.locallyFiniteOrder.{u1, u2} ι α _inst_1 _inst_2 _inst_3) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Union.union.{u1} (Finset.{u1} ι) (Finset.hasUnion.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b)) (Finsupp.support.{u1, u2} ι α _inst_2 f) (Finsupp.support.{u1, u2} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u2} α (Finset.Icc.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) f i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) g i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (f : Finsupp.{u2, u1} ι α _inst_2) (g : Finsupp.{u2, u1} ι α _inst_2), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finset.Ioc.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finsupp.preorder.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_1)) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α _inst_1 _inst_2 _inst_3) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Union.union.{u2} (Finset.{u2} ι) (Finset.instUnionFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b))) (Finsupp.support.{u2, u1} ι α _inst_2 f) (Finsupp.support.{u2, u1} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (Finset.Icc.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1) _inst_3 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) f i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) g i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finsupp.card_Ioc Finsupp.card_Iocₓ'. -/
theorem card_Ioc [DecidableEq ι] :
    (Ioc f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align finsupp.card_Ioc Finsupp.card_Ioc

/- warning: finsupp.card_Ioo -> Finsupp.card_Ioo is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : Zero.{u2} α] [_inst_3 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1)] (f : Finsupp.{u1, u2} ι α _inst_2) (g : Finsupp.{u1, u2} ι α _inst_2) [_inst_4 : DecidableEq.{succ u1} ι], Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finset.Ioo.{max u1 u2} (Finsupp.{u1, u2} ι α _inst_2) (Finsupp.preorder.{u1, u2} ι α _inst_2 (PartialOrder.toPreorder.{u2} α _inst_1)) (Finsupp.locallyFiniteOrder.{u1, u2} ι α _inst_1 _inst_2 _inst_3) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Union.union.{u1} (Finset.{u1} ι) (Finset.hasUnion.{u1} ι (fun (a : ι) (b : ι) => _inst_4 a b)) (Finsupp.support.{u1, u2} ι α _inst_2 f) (Finsupp.support.{u1, u2} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u2} α (Finset.Icc.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1) _inst_3 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) f i) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α _inst_2) (fun (_x : Finsupp.{u1, u2} ι α _inst_2) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α _inst_2) g i)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : Zero.{u1} α] [_inst_3 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] (f : Finsupp.{u2, u1} ι α _inst_2) (g : Finsupp.{u2, u1} ι α _inst_2), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finset.Ioo.{max u2 u1} (Finsupp.{u2, u1} ι α _inst_2) (Finsupp.preorder.{u2, u1} ι α _inst_2 (PartialOrder.toPreorder.{u1} α _inst_1)) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α _inst_1 _inst_2 _inst_3) f g)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Union.union.{u2} (Finset.{u2} ι) (Finset.instUnionFinset.{u2} ι (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u2} ι a b))) (Finsupp.support.{u2, u1} ι α _inst_2 f) (Finsupp.support.{u2, u1} ι α _inst_2 g)) (fun (i : ι) => Finset.card.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (Finset.Icc.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1) _inst_3 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) f i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α _inst_2) ι (fun (a : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) a) (Finsupp.funLike.{u2, u1} ι α _inst_2) g i)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align finsupp.card_Ioo Finsupp.card_Iooₓ'. -/
theorem card_Ioo [DecidableEq ι] :
    (Ioo f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align finsupp.card_Ioo Finsupp.card_Ioo

end PartialOrder

section CanonicallyOrdered

variable [CanonicallyOrderedAddMonoid α] [LocallyFiniteOrder α]

variable (f : ι →₀ α)

/- warning: finsupp.card_Iic -> Finsupp.card_Iic is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] (f : Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))), Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (Finset.Iic.{max u1 u2} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (Finsupp.preorder.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{max u1 u2} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (Finsupp.preorder.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (Finsupp.orderBot.{u1, u2} ι α _inst_1) (Finsupp.locallyFiniteOrder.{u1, u2} ι α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2)) f)) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finsupp.support.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) f) (fun (i : ι) => Finset.card.{u2} α (Finset.Iic.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))) (CanonicallyOrderedAddMonoid.toOrderBot.{u2} α _inst_1) _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (fun (_x : Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) f i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))] (f : Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) (Finset.Iic.{max u2 u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) (Finsupp.preorder.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{max u2 u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) (Finsupp.preorder.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (Finsupp.orderBot.{u2, u1} ι α _inst_1) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)) (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2)) f)) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finsupp.support.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) f) (fun (i : ι) => Finset.card.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (Finset.Iic.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (OrderedAddCommMonoid.toPartialOrder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (OrderedAddCommMonoid.toPartialOrder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1))) (CanonicallyOrderedAddMonoid.toOrderBot.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) f i))))
Case conversion may be inaccurate. Consider using '#align finsupp.card_Iic Finsupp.card_Iicₓ'. -/
theorem card_Iic : (Iic f).card = ∏ i in f.support, (Iic (f i)).card := by
  classical simp_rw [Iic_eq_Icc, card_Icc, Finsupp.bot_eq_zero, support_zero, empty_union,
      zero_apply, bot_eq_zero]
#align finsupp.card_Iic Finsupp.card_Iic

/- warning: finsupp.card_Iio -> Finsupp.card_Iio is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} α] [_inst_2 : LocallyFiniteOrder.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))] (f : Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))), Eq.{1} Nat (Finset.card.{max u1 u2} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (Finset.Iio.{max u1 u2} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (Finsupp.preorder.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{max u1 u2} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (Finsupp.preorder.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))) (Finsupp.orderBot.{u1, u2} ι α _inst_1) (Finsupp.locallyFiniteOrder.{u1, u2} ι α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)) (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) _inst_2)) f)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Finset.prod.{0, u1} Nat ι Nat.commMonoid (Finsupp.support.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))))) f) (fun (i : ι) => Finset.card.{u2} α (Finset.Iic.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommMonoid.toPartialOrder.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1))) (CanonicallyOrderedAddMonoid.toOrderBot.{u2} α _inst_1) _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) (fun (_x : Finsupp.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) => ι -> α) (Finsupp.hasCoeToFun.{u1, u2} ι α (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (AddCommMonoid.toAddMonoid.{u2} α (OrderedAddCommMonoid.toAddCommMonoid.{u2} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} α _inst_1)))))) f i)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} α] [_inst_2 : LocallyFiniteOrder.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))] (f : Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))), Eq.{1} Nat (Finset.card.{max u2 u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) (Finset.Iio.{max u2 u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) (Finsupp.preorder.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{max u2 u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) (Finsupp.preorder.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) (Finsupp.orderBot.{u2, u1} ι α _inst_1) (Finsupp.instLocallyFiniteOrderFinsuppPreorderToPreorder.{u2, u1} ι α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)) (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) _inst_2)) f)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Finset.prod.{0, u2} Nat ι Nat.commMonoid (Finsupp.support.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1)))) f) (fun (i : ι) => Finset.card.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (Finset.Iic.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (OrderedAddCommMonoid.toPartialOrder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (OrderedAddCommMonoid.toPartialOrder.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1))) (CanonicallyOrderedAddMonoid.toOrderBot.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) i) _inst_1) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : ι) => α) _x) (Finsupp.funLike.{u2, u1} ι α (AddMonoid.toZero.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_1))))) f i)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finsupp.card_Iio Finsupp.card_Iioₓ'. -/
theorem card_Iio : (Iio f).card = (∏ i in f.support, (Iic (f i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
#align finsupp.card_Iio Finsupp.card_Iio

end CanonicallyOrdered

end Finsupp

