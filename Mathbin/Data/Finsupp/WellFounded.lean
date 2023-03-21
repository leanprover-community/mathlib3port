/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

! This file was ported from Lean 3 source module data.finsupp.well_founded
! leanprover-community/mathlib commit 290a7ba01fbcab1b64757bdaa270d28f4dcede35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Dfinsupp.WellFounded
import Mathbin.Data.Finsupp.Lex

/-!
# Well-foundedness of the lexicographic and product orders on `finsupp`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`finsupp.lex.well_founded` and the two variants that follow it essentially say that if
`(>)` is a well order on `α`, `(<)` is well-founded on `N`, and `0` is a bottom element in `N`,
then the lexicographic `(<)` is well-founded on `α →₀ N`.

`finsupp.lex.well_founded_lt_of_finite` says that if `α` is finite and equipped with a linear
order and `(<)` is well-founded on `N`, then the lexicographic `(<)` is well-founded on `α →₀ N`.

`finsupp.well_founded_lt` and `well_founded_lt_of_finite` state the same results for the product
order `(<)`, but without the ordering conditions on `α`.

All results are transferred from `dfinsupp` via `finsupp.to_dfinsupp`.
-/


variable {α N : Type _}

namespace Finsupp

variable [hz : Zero N] {r : α → α → Prop} {s : N → N → Prop} (hbot : ∀ ⦃n⦄, ¬s n 0)
  (hs : WellFounded s)

include hbot hs

/- warning: finsupp.lex.acc -> Finsupp.Lex.acc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [hz : Zero.{u2} N] {r : α -> α -> Prop} {s : N -> N -> Prop}, (forall {{n : N}}, Not (s n (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N hz))))) -> (WellFounded.{succ u2} N s) -> (forall (x : Finsupp.{u1, u2} α N hz), (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α N hz x)) -> (Acc.{succ u1} α (Inf.inf.{u1} (α -> α -> Prop) (Pi.hasInf.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasInf.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => SemilatticeInf.toHasInf.{0} Prop (Lattice.toSemilatticeInf.{0} Prop (ConditionallyCompleteLattice.toLattice.{0} Prop (CompleteLattice.toConditionallyCompleteLattice.{0} Prop Prop.completeLattice)))))) (HasCompl.compl.{u1} (α -> α -> Prop) (Pi.hasCompl.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasCompl.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.hasCompl))) r) (Ne.{succ u1} α)) a)) -> (Acc.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N hz) (Finsupp.Lex.{u1, u2} α N hz r s) x))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [hz : Zero.{u1} N] {r : α -> α -> Prop} {s : N -> N -> Prop}, (forall {{n : N}}, Not (s n (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N hz)))) -> (WellFounded.{succ u1} N s) -> (forall (x : Finsupp.{u2, u1} α N hz), (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α N hz x)) -> (Acc.{succ u2} α (Inf.inf.{u2} (α -> α -> Prop) (Pi.instInfForAll.{u2, u2} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instInfForAll.{u2, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Lattice.toInf.{0} Prop (ConditionallyCompleteLattice.toLattice.{0} Prop (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Prop (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} Prop (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} Prop Prop.completeLinearOrder))))))) (HasCompl.compl.{u2} (α -> α -> Prop) (Pi.hasCompl.{u2, u2} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasCompl.{u2, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.hasCompl))) r) (fun (x._@.Mathlib.Data.Finsupp.WellFounded._hyg.102 : α) (x._@.Mathlib.Data.Finsupp.WellFounded._hyg.104 : α) => Ne.{succ u2} α x._@.Mathlib.Data.Finsupp.WellFounded._hyg.102 x._@.Mathlib.Data.Finsupp.WellFounded._hyg.104)) a)) -> (Acc.{max (succ u1) (succ u2)} (Finsupp.{u2, u1} α N hz) (Finsupp.Lex.{u2, u1} α N hz r s) x))
Case conversion may be inaccurate. Consider using '#align finsupp.lex.acc Finsupp.Lex.accₓ'. -/
/-- Transferred from `dfinsupp.lex.acc`. See the top of that file for an explanation for the
  appearance of the relation `rᶜ ⊓ (≠)`. -/
theorem Lex.acc (x : α →₀ N) (h : ∀ a ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) a) :
    Acc (Finsupp.Lex r s) x := by
  rw [lex_eq_inv_image_dfinsupp_lex]
  classical
    refine' InvImage.accessible to_dfinsupp (Dfinsupp.Lex.acc (fun a => hbot) (fun a => hs) _ _)
    simpa only [toDfinsupp_support] using h
#align finsupp.lex.acc Finsupp.Lex.acc

/- warning: finsupp.lex.well_founded -> Finsupp.Lex.wellFounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [hz : Zero.{u2} N] {r : α -> α -> Prop} {s : N -> N -> Prop}, (forall {{n : N}}, Not (s n (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N hz))))) -> (WellFounded.{succ u2} N s) -> (WellFounded.{succ u1} α (Inf.inf.{u1} (α -> α -> Prop) (Pi.hasInf.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasInf.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => SemilatticeInf.toHasInf.{0} Prop (Lattice.toSemilatticeInf.{0} Prop (ConditionallyCompleteLattice.toLattice.{0} Prop (CompleteLattice.toConditionallyCompleteLattice.{0} Prop Prop.completeLattice)))))) (HasCompl.compl.{u1} (α -> α -> Prop) (Pi.hasCompl.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasCompl.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.hasCompl))) r) (Ne.{succ u1} α))) -> (WellFounded.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N hz) (Finsupp.Lex.{u1, u2} α N hz r s))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [hz : Zero.{u1} N] {r : α -> α -> Prop} {s : N -> N -> Prop}, (forall {{n : N}}, Not (s n (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N hz)))) -> (WellFounded.{succ u1} N s) -> (WellFounded.{succ u2} α (Inf.inf.{u2} (α -> α -> Prop) (Pi.instInfForAll.{u2, u2} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instInfForAll.{u2, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Lattice.toInf.{0} Prop (ConditionallyCompleteLattice.toLattice.{0} Prop (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} Prop (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} Prop (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} Prop Prop.completeLinearOrder))))))) (HasCompl.compl.{u2} (α -> α -> Prop) (Pi.hasCompl.{u2, u2} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasCompl.{u2, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.hasCompl))) r) (fun (x._@.Mathlib.Data.Finsupp.WellFounded._hyg.228 : α) (x._@.Mathlib.Data.Finsupp.WellFounded._hyg.230 : α) => Ne.{succ u2} α x._@.Mathlib.Data.Finsupp.WellFounded._hyg.228 x._@.Mathlib.Data.Finsupp.WellFounded._hyg.230))) -> (WellFounded.{max (succ u1) (succ u2)} (Finsupp.{u2, u1} α N hz) (Finsupp.Lex.{u2, u1} α N hz r s))
Case conversion may be inaccurate. Consider using '#align finsupp.lex.well_founded Finsupp.Lex.wellFoundedₓ'. -/
theorem Lex.wellFounded (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (Finsupp.Lex r s) :=
  ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩
#align finsupp.lex.well_founded Finsupp.Lex.wellFounded

/- warning: finsupp.lex.well_founded' -> Finsupp.Lex.wellFounded' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [hz : Zero.{u2} N] {r : α -> α -> Prop} {s : N -> N -> Prop}, (forall {{n : N}}, Not (s n (OfNat.ofNat.{u2} N 0 (OfNat.mk.{u2} N 0 (Zero.zero.{u2} N hz))))) -> (WellFounded.{succ u2} N s) -> (forall [_inst_1 : IsTrichotomous.{u1} α r], (WellFounded.{succ u1} α (Function.swap.{succ u1, succ u1, 1} α α (fun (ᾰ : α) (ᾰ : α) => Prop) r)) -> (WellFounded.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N hz) (Finsupp.Lex.{u1, u2} α N hz r s)))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [hz : Zero.{u1} N] {r : α -> α -> Prop} {s : N -> N -> Prop}, (forall {{n : N}}, Not (s n (OfNat.ofNat.{u1} N 0 (Zero.toOfNat0.{u1} N hz)))) -> (WellFounded.{succ u1} N s) -> (forall [_inst_1 : IsTrichotomous.{u2} α r], (WellFounded.{succ u2} α (Function.swap.{succ u2, succ u2, 1} α α (fun (ᾰ : α) (ᾰ : α) => Prop) r)) -> (WellFounded.{max (succ u1) (succ u2)} (Finsupp.{u2, u1} α N hz) (Finsupp.Lex.{u2, u1} α N hz r s)))
Case conversion may be inaccurate. Consider using '#align finsupp.lex.well_founded' Finsupp.Lex.wellFounded'ₓ'. -/
theorem Lex.wellFounded' [IsTrichotomous α r] (hr : WellFounded r.symm) :
    WellFounded (Finsupp.Lex r s) :=
  (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (Dfinsupp.Lex.wellFounded' (fun a => hbot) (fun a => hs) hr)
#align finsupp.lex.well_founded' Finsupp.Lex.wellFounded'

omit hbot hs

/- warning: finsupp.lex.well_founded_lt -> Finsupp.Lex.wellFoundedLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LT.{u1} α] [_inst_2 : IsTrichotomous.{u1} α (LT.lt.{u1} α _inst_1)] [hα : WellFoundedGT.{u1} α _inst_1] [_inst_3 : CanonicallyOrderedAddMonoid.{u2} N] [hN : WellFoundedLT.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3))))], WellFoundedLT.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3))))))) (Finsupp.Lex.hasLt.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3))))) _inst_1 (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3)))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LT.{u1} α] [_inst_2 : IsTrichotomous.{u1} α (fun (x._@.Mathlib.Data.Finsupp.WellFounded._hyg.381 : α) (x._@.Mathlib.Data.Finsupp.WellFounded._hyg.383 : α) => LT.lt.{u1} α _inst_1 x._@.Mathlib.Data.Finsupp.WellFounded._hyg.381 x._@.Mathlib.Data.Finsupp.WellFounded._hyg.383)] [hα : WellFoundedGT.{u1} α _inst_1] [_inst_3 : CanonicallyOrderedAddMonoid.{u2} N] [hN : WellFoundedLT.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3))))], WellFoundedLT.{max u2 u1} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3)))))) (Finsupp.instLTLexFinsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3)))) _inst_1 (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_3)))))
Case conversion may be inaccurate. Consider using '#align finsupp.lex.well_founded_lt Finsupp.Lex.wellFoundedLTₓ'. -/
instance Lex.wellFoundedLT [LT α] [IsTrichotomous α (· < ·)] [hα : WellFoundedGT α]
    [CanonicallyOrderedAddMonoid N] [hN : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  ⟨Lex.wellFounded' (fun n => (zero_le n).not_lt) hN.wf hα.wf⟩
#align finsupp.lex.well_founded_lt Finsupp.Lex.wellFoundedLT

variable (r)

/- warning: finsupp.lex.well_founded_of_finite -> Finsupp.Lex.wellFounded_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} (r : α -> α -> Prop) {s : N -> N -> Prop} [_inst_1 : IsStrictTotalOrder.{u1} α r] [_inst_2 : Finite.{succ u1} α] [_inst_3 : Zero.{u2} N], (WellFounded.{succ u2} N s) -> (WellFounded.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_3) (Finsupp.Lex.{u1, u2} α N _inst_3 r s))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} (r : α -> α -> Prop) {s : N -> N -> Prop} [_inst_1 : IsStrictTotalOrder.{u2} α r] [_inst_2 : Finite.{succ u2} α] [_inst_3 : Zero.{u1} N], (WellFounded.{succ u1} N s) -> (WellFounded.{max (succ u1) (succ u2)} (Finsupp.{u2, u1} α N _inst_3) (Finsupp.Lex.{u2, u1} α N _inst_3 r s))
Case conversion may be inaccurate. Consider using '#align finsupp.lex.well_founded_of_finite Finsupp.Lex.wellFounded_of_finiteₓ'. -/
theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α] [Zero N]
    (hs : WellFounded s) : WellFounded (Finsupp.Lex r s) :=
  InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun a => hs)
#align finsupp.lex.well_founded_of_finite Finsupp.Lex.wellFounded_of_finite

/- warning: finsupp.lex.well_founded_lt_of_finite -> Finsupp.Lex.wellFoundedLT_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Finite.{succ u1} α] [_inst_3 : Zero.{u2} N] [_inst_4 : LT.{u2} N] [hwf : WellFoundedLT.{u2} N _inst_4], WellFoundedLT.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_3)) (Finsupp.Lex.hasLt.{u1, u2} α N _inst_3 (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_4)
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : Finite.{succ u2} α] [_inst_3 : Zero.{u1} N] [_inst_4 : LT.{u1} N] [hwf : WellFoundedLT.{u1} N _inst_4], WellFoundedLT.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_3)) (Finsupp.instLTLexFinsupp.{u2, u1} α N _inst_3 (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_1)))))) _inst_4)
Case conversion may be inaccurate. Consider using '#align finsupp.lex.well_founded_lt_of_finite Finsupp.Lex.wellFoundedLT_of_finiteₓ'. -/
theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [Zero N] [LT N]
    [hwf : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩
#align finsupp.lex.well_founded_lt_of_finite Finsupp.Lex.wellFoundedLT_of_finite

#print Finsupp.wellFoundedLT /-
protected theorem wellFoundedLT [Zero N] [Preorder N] [WellFoundedLT N] (hbot : ∀ n : N, ¬n < 0) :
    WellFoundedLT (α →₀ N) :=
  ⟨InvImage.wf toDfinsupp (Dfinsupp.wellFoundedLT fun i a => hbot a).wf⟩
#align finsupp.well_founded_lt Finsupp.wellFoundedLT
-/

/- warning: finsupp.well_founded_lt' -> Finsupp.well_founded_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} N] [_inst_2 : WellFoundedLT.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1))))], WellFoundedLT.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1)))))) (Preorder.toLT.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1)))))) (Finsupp.preorder.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1))))) (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : CanonicallyOrderedAddMonoid.{u2} N] [_inst_2 : WellFoundedLT.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1))))], WellFoundedLT.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1))))) (Preorder.toLT.{max u1 u2} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1))))) (Finsupp.preorder.{u1, u2} α N (AddMonoid.toZero.{u2} N (AddCommMonoid.toAddMonoid.{u2} N (OrderedAddCommMonoid.toAddCommMonoid.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1)))) (PartialOrder.toPreorder.{u2} N (OrderedAddCommMonoid.toPartialOrder.{u2} N (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u2} N _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finsupp.well_founded_lt' Finsupp.well_founded_lt'ₓ'. -/
instance well_founded_lt' [CanonicallyOrderedAddMonoid N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  Finsupp.wellFoundedLT fun a => (zero_le a).not_lt
#align finsupp.well_founded_lt' Finsupp.well_founded_lt'

#print Finsupp.wellFoundedLT_of_finite /-
instance wellFoundedLT_of_finite [Finite α] [Zero N] [Preorder N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩
#align finsupp.well_founded_lt_of_finite Finsupp.wellFoundedLT_of_finite
-/

end Finsupp

