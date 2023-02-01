/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou

! This file was ported from Lean 3 source module algebra.indicator_function
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Support

/-!
# Indicator function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

- `indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `mul_indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `λx, 1`.

The indicator function is implemented non-computably, to avoid having to pass around `decidable`
arguments. This is in contrast with the design of `pi.single` or `set.piecewise`.

## Tags
indicator, characteristic
-/


open BigOperators

open Function

variable {α β ι M N : Type _}

namespace Set

section One

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

#print Set.indicator /-
/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
noncomputable def indicator {M} [Zero M] (s : Set α) (f : α → M) : α → M
  | x =>
    haveI := Classical.decPred (· ∈ s)
    if x ∈ s then f x else 0
#align set.indicator Set.indicator
-/

#print Set.mulIndicator /-
/-- `mul_indicator s f a` is `f a` if `a ∈ s`, `1` otherwise.  -/
@[to_additive]
noncomputable def mulIndicator (s : Set α) (f : α → M) : α → M
  | x =>
    haveI := Classical.decPred (· ∈ s)
    if x ∈ s then f x else 1
#align set.mul_indicator Set.mulIndicator
#align set.indicator Set.indicator
-/

/- warning: set.piecewise_eq_mul_indicator -> Set.piecewise_eq_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} [_inst_3 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)], Eq.{max (succ u1) (succ u2)} (α -> M) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => M) s f (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (i : α) => M) (fun (i : α) => _inst_1))))) (fun (j : α) => _inst_3 j)) (Set.mulIndicator.{u1, u2} α M _inst_1 s f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} [_inst_3 : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)], Eq.{max (succ u2) (succ u1)} (α -> M) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => M) s f (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (i : α) => M) (fun (i : α) => _inst_1)))) (fun (j : α) => _inst_3 j)) (Set.mulIndicator.{u2, u1} α M _inst_1 s f)
Case conversion may be inaccurate. Consider using '#align set.piecewise_eq_mul_indicator Set.piecewise_eq_mulIndicatorₓ'. -/
@[simp, to_additive]
theorem piecewise_eq_mulIndicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun x => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl
#align set.piecewise_eq_mul_indicator Set.piecewise_eq_mulIndicator
#align set.piecewise_eq_indicator Set.piecewise_eq_indicator

/- warning: set.mul_indicator_apply -> Set.mulIndicator_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (s : Set.{u1} α) (f : α -> M) (a : α) [_inst_3 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)], Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (ite.{succ u2} M (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) _inst_3 (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (s : Set.{u2} α) (f : α -> M) (a : α) [_inst_3 : Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)], Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (ite.{succ u1} M (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) _inst_3 (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_apply Set.mulIndicator_applyₓ'. -/
@[to_additive]
theorem mulIndicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    mulIndicator s f a = if a ∈ s then f a else 1 := by convert rfl
#align set.mul_indicator_apply Set.mulIndicator_apply
#align set.indicator_apply Set.indicator_apply

/- warning: set.mul_indicator_of_mem -> Set.mulIndicator_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (f : α -> M), Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {a : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (forall (f : α -> M), Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (f a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_of_mem Set.mulIndicator_of_memₓ'. -/
@[simp, to_additive]
theorem mulIndicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a :=
  letI := Classical.dec (a ∈ s)
  if_pos h
#align set.mul_indicator_of_mem Set.mulIndicator_of_mem
#align set.indicator_of_mem Set.indicator_of_mem

/- warning: set.mul_indicator_of_not_mem -> Set.mulIndicator_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (forall (f : α -> M), Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {a : α}, (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (forall (f : α -> M), Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_of_not_mem Set.mulIndicator_of_not_memₓ'. -/
@[simp, to_additive]
theorem mulIndicator_of_not_mem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 :=
  letI := Classical.dec (a ∈ s)
  if_neg h
#align set.mul_indicator_of_not_mem Set.mulIndicator_of_not_mem
#align set.indicator_of_not_mem Set.indicator_of_not_mem

/- warning: set.mul_indicator_eq_one_or_self -> Set.mulIndicator_eq_one_or_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (s : Set.{u1} α) (f : α -> M) (a : α), Or (Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) (Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (s : Set.{u2} α) (f : α -> M) (a : α), Or (Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))) (Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (f a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_eq_one_or_self Set.mulIndicator_eq_one_or_selfₓ'. -/
@[to_additive]
theorem mulIndicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a :=
  by
  by_cases h : a ∈ s
  · exact Or.inr (mul_indicator_of_mem h f)
  · exact Or.inl (mul_indicator_of_not_mem h f)
#align set.mul_indicator_eq_one_or_self Set.mulIndicator_eq_one_or_self
#align set.indicator_eq_zero_or_self Set.indicator_eq_zero_or_self

#print Set.mulIndicator_apply_eq_self /-
@[simp, to_additive]
theorem mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_left_iff.trans (by rw [@eq_comm _ (f a)])
#align set.mul_indicator_apply_eq_self Set.mulIndicator_apply_eq_self
#align set.indicator_apply_eq_self Set.indicator_apply_eq_self
-/

/- warning: set.mul_indicator_eq_self -> Set.mulIndicator_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M}, Iff (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) f) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 f) s)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M}, Iff (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) f) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 f) s)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_eq_self Set.mulIndicator_eq_selfₓ'. -/
@[simp, to_additive]
theorem mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f ⊆ s := by
  simp only [funext_iff, subset_def, mem_mul_support, mul_indicator_apply_eq_self, not_imp_comm]
#align set.mul_indicator_eq_self Set.mulIndicator_eq_self
#align set.indicator_eq_self Set.indicator_eq_self

/- warning: set.mul_indicator_eq_self_of_superset -> Set.mulIndicator_eq_self_of_superset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> M}, (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) f) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 t f) f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> M}, (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) f) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 t f) f)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_eq_self_of_superset Set.mulIndicator_eq_self_of_supersetₓ'. -/
@[to_additive]
theorem mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) :
    t.mulIndicator f = f := by
  rw [mul_indicator_eq_self] at h1⊢
  exact subset.trans h1 h2
#align set.mul_indicator_eq_self_of_superset Set.mulIndicator_eq_self_of_superset
#align set.indicator_eq_self_of_superset Set.indicator_eq_self_of_superset

#print Set.mulIndicator_apply_eq_one /-
@[simp, to_additive]
theorem mulIndicator_apply_eq_one : mulIndicator s f a = 1 ↔ a ∈ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_right_iff
#align set.mul_indicator_apply_eq_one Set.mulIndicator_apply_eq_one
#align set.indicator_apply_eq_zero Set.indicator_apply_eq_zero
-/

/- warning: set.mul_indicator_eq_one -> Set.mulIndicator_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M}, Iff (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) (fun (x : α) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.mulSupport.{u1, u2} α M _inst_1 f) s)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M}, Iff (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) (fun (x : α) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))) (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Function.mulSupport.{u2, u1} α M _inst_1 f) s)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_eq_one Set.mulIndicator_eq_oneₓ'. -/
@[simp, to_additive]
theorem mulIndicator_eq_one : (mulIndicator s f = fun x => 1) ↔ Disjoint (mulSupport f) s := by
  simp only [funext_iff, mul_indicator_apply_eq_one, Set.disjoint_left, mem_mul_support,
    not_imp_not]
#align set.mul_indicator_eq_one Set.mulIndicator_eq_one
#align set.indicator_eq_zero Set.indicator_eq_zero

/- warning: set.mul_indicator_eq_one' -> Set.mulIndicator_eq_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M}, Iff (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.mulSupport.{u1, u2} α M _inst_1 f) s)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M}, Iff (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.159 : α) => M) (fun (i : α) => _inst_1))))) (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Function.mulSupport.{u2, u1} α M _inst_1 f) s)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_eq_one' Set.mulIndicator_eq_one'ₓ'. -/
@[simp, to_additive]
theorem mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s :=
  mulIndicator_eq_one
#align set.mul_indicator_eq_one' Set.mulIndicator_eq_one'
#align set.indicator_eq_zero' Set.indicator_eq_zero'

/- warning: set.mul_indicator_apply_ne_one -> Set.mulIndicator_apply_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {a : α}, Iff (Ne.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M _inst_1 f)))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {a : α}, Iff (Ne.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_1))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Function.mulSupport.{u1, u2} α M _inst_1 f)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_apply_ne_one Set.mulIndicator_apply_ne_oneₓ'. -/
@[to_additive]
theorem mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ mulSupport f := by
  simp only [Ne.def, mul_indicator_apply_eq_one, not_imp, mem_inter_iff, mem_mul_support]
#align set.mul_indicator_apply_ne_one Set.mulIndicator_apply_ne_one
#align set.indicator_apply_ne_zero Set.indicator_apply_ne_zero

/- warning: set.mul_support_mul_indicator -> Set.mulSupport_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M}, Eq.{succ u1} (Set.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (Set.mulIndicator.{u1, u2} α M _inst_1 s f)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M _inst_1 f))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M}, Eq.{succ u2} (Set.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 (Set.mulIndicator.{u2, u1} α M _inst_1 s f)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M _inst_1 f))
Case conversion may be inaccurate. Consider using '#align set.mul_support_mul_indicator Set.mulSupport_mulIndicatorₓ'. -/
@[simp, to_additive]
theorem mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s ∩ Function.mulSupport f :=
  ext fun x => by simp [Function.mem_mulSupport, mul_indicator_apply_eq_one]
#align set.mul_support_mul_indicator Set.mulSupport_mulIndicator
#align set.support_indicator Set.support_indicator

#print Set.mem_of_mulIndicator_ne_one /-
/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[to_additive
      "If an additive indicator function is not equal to `0` at a point, then that point is\nin the set."]
theorem mem_of_mulIndicator_ne_one (h : mulIndicator s f a ≠ 1) : a ∈ s :=
  not_imp_comm.1 (fun hn => mulIndicator_of_not_mem hn f) h
#align set.mem_of_mul_indicator_ne_one Set.mem_of_mulIndicator_ne_one
#align set.mem_of_indicator_ne_zero Set.mem_of_indicator_ne_zero
-/

/- warning: set.eq_on_mul_indicator -> Set.eqOn_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M}, Set.EqOn.{u1, u2} α M (Set.mulIndicator.{u1, u2} α M _inst_1 s f) f s
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M}, Set.EqOn.{u2, u1} α M (Set.mulIndicator.{u2, u1} α M _inst_1 s f) f s
Case conversion may be inaccurate. Consider using '#align set.eq_on_mul_indicator Set.eqOn_mulIndicatorₓ'. -/
@[to_additive]
theorem eqOn_mulIndicator : EqOn (mulIndicator s f) f s := fun x hx => mulIndicator_of_mem hx f
#align set.eq_on_mul_indicator Set.eqOn_mulIndicator
#align set.eq_on_indicator Set.eqOn_indicator

/- warning: set.mul_support_mul_indicator_subset -> Set.mulSupport_mulIndicator_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Function.mulSupport.{u1, u2} α M _inst_1 (Set.mulIndicator.{u1, u2} α M _inst_1 s f)) s
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Function.mulSupport.{u2, u1} α M _inst_1 (Set.mulIndicator.{u2, u1} α M _inst_1 s f)) s
Case conversion may be inaccurate. Consider using '#align set.mul_support_mul_indicator_subset Set.mulSupport_mulIndicator_subsetₓ'. -/
@[to_additive]
theorem mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) ⊆ s := fun x hx =>
  hx.imp_symm fun h => mulIndicator_of_not_mem h f
#align set.mul_support_mul_indicator_subset Set.mulSupport_mulIndicator_subset
#align set.support_indicator_subset Set.support_indicator_subset

/- warning: set.mul_indicator_mul_support -> Set.mulIndicator_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {f : α -> M}, Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 (Function.mulSupport.{u1, u2} α M _inst_1 f) f) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {f : α -> M}, Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 (Function.mulSupport.{u2, u1} α M _inst_1 f) f) f
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul_support Set.mulIndicator_mulSupportₓ'. -/
@[simp, to_additive]
theorem mulIndicator_mulSupport : mulIndicator (mulSupport f) f = f :=
  mulIndicator_eq_self.2 Subset.rfl
#align set.mul_indicator_mul_support Set.mulIndicator_mulSupport
#align set.indicator_support Set.indicator_support

#print Set.mulIndicator_range_comp /-
@[simp, to_additive]
theorem mulIndicator_range_comp {ι : Sort _} (f : ι → α) (g : α → M) :
    mulIndicator (range f) g ∘ f = g ∘ f :=
  letI := Classical.decPred (· ∈ range f)
  piecewise_range_comp _ _ _
#align set.mul_indicator_range_comp Set.mulIndicator_range_comp
#align set.indicator_range_comp Set.indicator_range_comp
-/

/- warning: set.mul_indicator_congr -> Set.mulIndicator_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {g : α -> M}, (Set.EqOn.{u1, u2} α M f g s) -> (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) (Set.mulIndicator.{u1, u2} α M _inst_1 s g))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} {g : α -> M}, (Set.EqOn.{u2, u1} α M f g s) -> (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) (Set.mulIndicator.{u2, u1} α M _inst_1 s g))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_congr Set.mulIndicator_congrₓ'. -/
@[to_additive]
theorem mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    simp only [mul_indicator]
    split_ifs
    · exact h h_1
    rfl
#align set.mul_indicator_congr Set.mulIndicator_congr
#align set.indicator_congr Set.indicator_congr

/- warning: set.mul_indicator_univ -> Set.mulIndicator_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (f : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 (Set.univ.{u1} α) f) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 (Set.univ.{u2} α) f) f
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_univ Set.mulIndicator_univₓ'. -/
@[simp, to_additive]
theorem mulIndicator_univ (f : α → M) : mulIndicator (univ : Set α) f = f :=
  mulIndicator_eq_self.2 <| subset_univ _
#align set.mul_indicator_univ Set.mulIndicator_univ
#align set.indicator_univ Set.indicator_univ

/- warning: set.mul_indicator_empty -> Set.mulIndicator_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (f : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) f) (fun (a : α) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)) f) (fun (a : α) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_empty Set.mulIndicator_emptyₓ'. -/
@[simp, to_additive]
theorem mulIndicator_empty (f : α → M) : mulIndicator (∅ : Set α) f = fun a => 1 :=
  mulIndicator_eq_one.2 <| disjoint_empty _
#align set.mul_indicator_empty Set.mulIndicator_empty
#align set.indicator_empty Set.indicator_empty

/- warning: set.mul_indicator_empty' -> Set.mulIndicator_empty' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (f : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) f) (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)) f) (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.159 : α) => M) (fun (i : α) => _inst_1))))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_empty' Set.mulIndicator_empty'ₓ'. -/
@[to_additive]
theorem mulIndicator_empty' (f : α → M) : mulIndicator (∅ : Set α) f = 1 :=
  mulIndicator_empty f
#align set.mul_indicator_empty' Set.mulIndicator_empty'
#align set.indicator_empty' Set.indicator_empty'

variable (M)

/- warning: set.mul_indicator_one -> Set.mulIndicator_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (M : Type.{u2}) [_inst_1 : One.{u2} M] (s : Set.{u1} α), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s (fun (x : α) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) (fun (x : α) => OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} (M : Type.{u1}) [_inst_1 : One.{u1} M] (s : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s (fun (x : α) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))) (fun (x : α) => OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_one Set.mulIndicator_oneₓ'. -/
@[simp, to_additive]
theorem mulIndicator_one (s : Set α) : (mulIndicator s fun x => (1 : M)) = fun x => (1 : M) :=
  mulIndicator_eq_one.2 <| by simp only [mul_support_one, empty_disjoint]
#align set.mul_indicator_one Set.mulIndicator_one
#align set.indicator_zero Set.indicator_zero

/- warning: set.mul_indicator_one' -> Set.mulIndicator_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (M : Type.{u2}) [_inst_1 : One.{u2} M] {s : Set.{u1} α}, Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))) (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} (M : Type.{u1}) [_inst_1 : One.{u1} M] {s : Set.{u2} α}, Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.1615 : α) => M) (fun (i : α) => _inst_1))))) (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.159 : α) => M) (fun (i : α) => _inst_1))))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_one' Set.mulIndicator_one'ₓ'. -/
@[simp, to_additive]
theorem mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 :=
  mulIndicator_one M s
#align set.mul_indicator_one' Set.mulIndicator_one'
#align set.indicator_zero' Set.indicator_zero'

variable {M}

/- warning: set.mul_indicator_mul_indicator -> Set.mulIndicator_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (s : Set.{u1} α) (t : Set.{u1} α) (f : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 s (Set.mulIndicator.{u1, u2} α M _inst_1 t f)) (Set.mulIndicator.{u1, u2} α M _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (s : Set.{u2} α) (t : Set.{u2} α) (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 s (Set.mulIndicator.{u2, u1} α M _inst_1 t f)) (Set.mulIndicator.{u2, u1} α M _inst_1 (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t) f)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul_indicator Set.mulIndicator_mulIndicatorₓ'. -/
@[to_additive]
theorem mulIndicator_mulIndicator (s t : Set α) (f : α → M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s ∩ t) f :=
  funext fun x => by
    simp only [mul_indicator]
    split_ifs
    repeat' simp_all (config := { contextual := true })
#align set.mul_indicator_mul_indicator Set.mulIndicator_mulIndicator
#align set.indicator_indicator Set.indicator_indicator

/- warning: set.mul_indicator_inter_mul_support -> Set.mulIndicator_inter_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (s : Set.{u1} α) (f : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.mulSupport.{u1, u2} α M _inst_1 f)) f) (Set.mulIndicator.{u1, u2} α M _inst_1 s f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (s : Set.{u2} α) (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M _inst_1 (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Function.mulSupport.{u2, u1} α M _inst_1 f)) f) (Set.mulIndicator.{u2, u1} α M _inst_1 s f)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_inter_mul_support Set.mulIndicator_inter_mulSupportₓ'. -/
@[simp, to_additive]
theorem mulIndicator_inter_mulSupport (s : Set α) (f : α → M) :
    mulIndicator (s ∩ mulSupport f) f = mulIndicator s f := by
  rw [← mul_indicator_mul_indicator, mul_indicator_mul_support]
#align set.mul_indicator_inter_mul_support Set.mulIndicator_inter_mulSupport
#align set.indicator_inter_support Set.indicator_inter_support

/- warning: set.comp_mul_indicator -> Set.comp_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] (h : M -> β) (f : α -> M) {s : Set.{u1} α} {x : α} [_inst_3 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)], Eq.{succ u2} β (h (Set.mulIndicator.{u1, u3} α M _inst_1 s f x)) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s (Function.comp.{succ u1, succ u3, succ u2} α M β h f) (Function.const.{succ u2, succ u1} β α (h (OfNat.ofNat.{u3} M 1 (OfNat.mk.{u3} M 1 (One.one.{u3} M _inst_1))))) (fun (j : α) => _inst_3 j) x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (h : M -> β) (f : α -> M) {s : Set.{u3} α} {x : α} [_inst_3 : DecidablePred.{succ u3} α (fun (_x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) _x s)], Eq.{succ u2} β (h (Set.mulIndicator.{u3, u1} α M _inst_1 s f x)) (Set.piecewise.{u3, succ u2} α (fun (ᾰ : α) => β) s (Function.comp.{succ u3, succ u1, succ u2} α M β h f) (Function.const.{succ u2, succ u3} β α (h (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))) (fun (j : α) => _inst_3 j) x)
Case conversion may be inaccurate. Consider using '#align set.comp_mul_indicator Set.comp_mulIndicatorₓ'. -/
@[to_additive]
theorem comp_mulIndicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  letI := Classical.decPred (· ∈ s) <;> convert s.apply_piecewise f (const α 1) fun _ => h
#align set.comp_mul_indicator Set.comp_mulIndicator
#align set.comp_indicator Set.comp_indicator

/- warning: set.mul_indicator_comp_right -> Set.mulIndicator_comp_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] {s : Set.{u1} α} (f : β -> α) {g : α -> M} {x : β}, Eq.{succ u3} M (Set.mulIndicator.{u2, u3} β M _inst_1 (Set.preimage.{u2, u1} β α f s) (Function.comp.{succ u2, succ u1, succ u3} β α M g f) x) (Set.mulIndicator.{u1, u3} α M _inst_1 s g (f x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u3} α} (f : β -> α) {g : α -> M} {x : β}, Eq.{succ u2} M (Set.mulIndicator.{u1, u2} β M _inst_1 (Set.preimage.{u1, u3} β α f s) (Function.comp.{succ u1, succ u3, succ u2} β α M g f) x) (Set.mulIndicator.{u3, u2} α M _inst_1 s g (f x))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_comp_right Set.mulIndicator_comp_rightₓ'. -/
@[to_additive]
theorem mulIndicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) :=
  by
  simp only [mul_indicator]
  split_ifs <;> rfl
#align set.mul_indicator_comp_right Set.mulIndicator_comp_right
#align set.indicator_comp_right Set.indicator_comp_right

/- warning: set.mul_indicator_image -> Set.mulIndicator_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : One.{u3} M] {s : Set.{u1} α} {f : β -> M} {g : α -> β}, (Function.Injective.{succ u1, succ u2} α β g) -> (forall {x : α}, Eq.{succ u3} M (Set.mulIndicator.{u2, u3} β M _inst_1 (Set.image.{u1, u2} α β g s) f (g x)) (Set.mulIndicator.{u1, u3} α M _inst_1 s (Function.comp.{succ u1, succ u2, succ u3} α β M f g) x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u3} α} {f : β -> M} {g : α -> β}, (Function.Injective.{succ u3, succ u2} α β g) -> (forall {x : α}, Eq.{succ u1} M (Set.mulIndicator.{u2, u1} β M _inst_1 (Set.image.{u3, u2} α β g s) f (g x)) (Set.mulIndicator.{u3, u1} α M _inst_1 s (Function.comp.{succ u3, succ u2, succ u1} α β M f g) x))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_image Set.mulIndicator_imageₓ'. -/
@[to_additive]
theorem mulIndicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  rw [← mul_indicator_comp_right, preimage_image_eq _ hg]
#align set.mul_indicator_image Set.mulIndicator_image
#align set.indicator_image Set.indicator_image

#print Set.mulIndicator_comp_of_one /-
@[to_additive]
theorem mulIndicator_comp_of_one {g : M → N} (hg : g 1 = 1) :
    mulIndicator s (g ∘ f) = g ∘ mulIndicator s f :=
  by
  funext
  simp only [mul_indicator]
  split_ifs <;> simp [*]
#align set.mul_indicator_comp_of_one Set.mulIndicator_comp_of_one
#align set.indicator_comp_of_zero Set.indicator_comp_of_zero
-/

#print Set.comp_mulIndicator_const /-
@[to_additive]
theorem comp_mulIndicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun x => c) x)) = s.mulIndicator fun x => f c :=
  (mulIndicator_comp_of_one hf).symm
#align set.comp_mul_indicator_const Set.comp_mulIndicator_const
#align set.comp_indicator_const Set.comp_indicator_const
-/

/- warning: set.mul_indicator_preimage -> Set.mulIndicator_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (s : Set.{u1} α) (f : α -> M) (B : Set.{u2} M), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α M (Set.mulIndicator.{u1, u2} α M _inst_1 s f) B) (Set.ite.{u1} α s (Set.preimage.{u1, u2} α M f B) (Set.preimage.{u1, u2} α M (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1))))) B))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (s : Set.{u2} α) (f : α -> M) (B : Set.{u1} M), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α M (Set.mulIndicator.{u2, u1} α M _inst_1 s f) B) (Set.ite.{u2} α s (Set.preimage.{u2, u1} α M f B) (Set.preimage.{u2, u1} α M (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Data.Set.Image._hyg.23 : α) => M) (fun (i : α) => _inst_1)))) B))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_preimage Set.mulIndicator_preimageₓ'. -/
@[to_additive]
theorem mulIndicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  letI := Classical.decPred (· ∈ s)
  piecewise_preimage s f 1 B
#align set.mul_indicator_preimage Set.mulIndicator_preimage
#align set.indicator_preimage Set.indicator_preimage

#print Set.mulIndicator_one_preimage /-
@[to_additive]
theorem mulIndicator_one_preimage (s : Set M) :
    t.mulIndicator 1 ⁻¹' s ∈ ({Set.univ, ∅} : Set (Set α)) := by
  classical
    rw [mul_indicator_one', preimage_one]
    split_ifs <;> simp
#align set.mul_indicator_one_preimage Set.mulIndicator_one_preimage
#align set.indicator_zero_preimage Set.indicator_zero_preimage
-/

/- warning: set.mul_indicator_const_preimage_eq_union -> Set.mulIndicator_const_preimage_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (U : Set.{u1} α) (s : Set.{u2} M) (a : M) [_inst_3 : Decidable (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) a s)] [_inst_4 : Decidable (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) s)], Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α M (Set.mulIndicator.{u1, u2} α M _inst_1 U (fun (x : α) => a)) s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (ite.{succ u1} (Set.{u1} α) (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) a s) _inst_3 U (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (ite.{succ u1} (Set.{u1} α) (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) s) _inst_4 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) U) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (U : Set.{u2} α) (s : Set.{u1} M) (a : M) [_inst_3 : Decidable (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s)] [_inst_4 : Decidable (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) s)], Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α M (Set.mulIndicator.{u2, u1} α M _inst_1 U (fun (x : α) => a)) s) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (ite.{succ u2} (Set.{u2} α) (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s) _inst_3 U (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (ite.{succ u2} (Set.{u2} α) (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) s) _inst_4 (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) U) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_const_preimage_eq_union Set.mulIndicator_const_preimage_eq_unionₓ'. -/
@[to_additive]
theorem mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Decidable (a ∈ s)]
    [Decidable ((1 : M) ∈ s)] :
    (U.mulIndicator fun x => a) ⁻¹' s = (if a ∈ s then U else ∅) ∪ if (1 : M) ∈ s then Uᶜ else ∅ :=
  by
  rw [mul_indicator_preimage, preimage_one, preimage_const]
  split_ifs <;> simp [← compl_eq_univ_diff]
#align set.mul_indicator_const_preimage_eq_union Set.mulIndicator_const_preimage_eq_union
#align set.indicator_const_preimage_eq_union Set.indicator_const_preimage_eq_union

/- warning: set.mul_indicator_const_preimage -> Set.mulIndicator_const_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (U : Set.{u1} α) (s : Set.{u2} M) (a : M), Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Set.preimage.{u1, u2} α M (Set.mulIndicator.{u1, u2} α M _inst_1 U (fun (x : α) => a)) s) (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) (Set.univ.{u1} α) (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) U (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) U) (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (U : Set.{u2} α) (s : Set.{u1} M) (a : M), Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) (Set.preimage.{u2, u1} α M (Set.mulIndicator.{u2, u1} α M _inst_1 U (fun (x : α) => a)) s) (Insert.insert.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instInsertSet.{u2} (Set.{u2} α)) (Set.univ.{u2} α) (Insert.insert.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instInsertSet.{u2} (Set.{u2} α)) U (Insert.insert.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instInsertSet.{u2} (Set.{u2} α)) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) U) (Singleton.singleton.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instSingletonSet.{u2} (Set.{u2} α)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))))))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_const_preimage Set.mulIndicator_const_preimageₓ'. -/
@[to_additive]
theorem mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun x => a) ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  classical
    rw [mul_indicator_const_preimage_eq_union]
    split_ifs <;> simp
#align set.mul_indicator_const_preimage Set.mulIndicator_const_preimage
#align set.indicator_const_preimage Set.indicator_const_preimage

/- warning: set.indicator_one_preimage -> Set.indicator_one_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_3 : Zero.{u2} M] (U : Set.{u1} α) (s : Set.{u2} M), Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Set.preimage.{u1, u2} α M (Set.indicator.{u1, u2} α M _inst_3 U (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)))))) s) (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) (Set.univ.{u1} α) (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) U (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasInsert.{u1} (Set.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) U) (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] [_inst_3 : Zero.{u2} M] (U : Set.{u1} α) (s : Set.{u2} M), Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Set.preimage.{u1, u2} α M (Set.indicator.{u1, u2} α M _inst_3 U (OfNat.ofNat.{max u1 u2} (α -> M) 1 (One.toOfNat1.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => _inst_1))))) s) (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) (Set.univ.{u1} α) (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) U (Insert.insert.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instInsertSet.{u1} (Set.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) U) (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))))))
Case conversion may be inaccurate. Consider using '#align set.indicator_one_preimage Set.indicator_one_preimageₓ'. -/
theorem indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) :=
  indicator_const_preimage _ _ 1
#align set.indicator_one_preimage Set.indicator_one_preimage

/- warning: set.mul_indicator_preimage_of_not_mem -> Set.mulIndicator_preimage_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] (s : Set.{u1} α) (f : α -> M) {t : Set.{u2} M}, (Not (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) t)) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α M (Set.mulIndicator.{u1, u2} α M _inst_1 s f) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α M f t) s))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] (s : Set.{u2} α) (f : α -> M) {t : Set.{u1} M}, (Not (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) t)) -> (Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α M (Set.mulIndicator.{u2, u1} α M _inst_1 s f) t) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Set.preimage.{u2, u1} α M f t) s))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_preimage_of_not_mem Set.mulIndicator_preimage_of_not_memₓ'. -/
@[to_additive]
theorem mulIndicator_preimage_of_not_mem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  simp [mul_indicator_preimage, Pi.one_def, Set.preimage_const_of_not_mem ht]
#align set.mul_indicator_preimage_of_not_mem Set.mulIndicator_preimage_of_not_mem
#align set.indicator_preimage_of_not_mem Set.indicator_preimage_of_not_mem

/- warning: set.mem_range_mul_indicator -> Set.mem_range_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {r : M} {s : Set.{u1} α} {f : α -> M}, Iff (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) r (Set.range.{u2, succ u1} M α (Set.mulIndicator.{u1, u2} α M _inst_1 s f))) (Or (And (Eq.{succ u2} M r (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1)))) (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))) (Membership.Mem.{u2, u2} M (Set.{u2} M) (Set.hasMem.{u2} M) r (Set.image.{u1, u2} α M f s)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {r : M} {s : Set.{u2} α} {f : α -> M}, Iff (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) r (Set.range.{u1, succ u2} M α (Set.mulIndicator.{u2, u1} α M _inst_1 s f))) (Or (And (Eq.{succ u1} M r (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1))) (Ne.{succ u2} (Set.{u2} α) s (Set.univ.{u2} α))) (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) r (Set.image.{u2, u1} α M f s)))
Case conversion may be inaccurate. Consider using '#align set.mem_range_mul_indicator Set.mem_range_mulIndicatorₓ'. -/
@[to_additive]
theorem mem_range_mulIndicator {r : M} {s : Set α} {f : α → M} :
    r ∈ range (mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
  simp [mul_indicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm', or_comm',
    @eq_comm _ r 1]
#align set.mem_range_mul_indicator Set.mem_range_mulIndicator
#align set.mem_range_indicator Set.mem_range_indicator

#print Set.mulIndicator_rel_mulIndicator /-
@[to_additive]
theorem mulIndicator_rel_mulIndicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) :=
  by
  simp only [mul_indicator]
  split_ifs with has has
  exacts[ha has, h1]
#align set.mul_indicator_rel_mul_indicator Set.mulIndicator_rel_mulIndicator
#align set.indicator_rel_indicator Set.indicator_rel_indicator
-/

end One

section Monoid

variable [MulOneClass M] {s t : Set α} {f g : α → M} {a : α}

/- warning: set.mul_indicator_union_mul_inter_apply -> Set.mulIndicator_union_mul_inter_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (f : α -> M) (s : Set.{u1} α) (t : Set.{u1} α) (a : α), Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) f a)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) t f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (f : α -> M) (s : Set.{u2} α) (t : Set.{u2} α) (a : α), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t) f a)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) t f a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_union_mul_inter_apply Set.mulIndicator_union_mul_inter_applyₓ'. -/
@[to_additive]
theorem mulIndicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a = mulIndicator s f a * mulIndicator t f a :=
  by by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp [*]
#align set.mul_indicator_union_mul_inter_apply Set.mulIndicator_union_mul_inter_apply
#align set.indicator_union_add_inter_apply Set.indicator_union_add_inter_apply

/- warning: set.mul_indicator_union_mul_inter -> Set.mulIndicator_union_mul_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (f : α -> M) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ (max u1 u2)} (α -> M) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) f) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) f)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) t f))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (f : α -> M) (s : Set.{u2} α) (t : Set.{u2} α), Eq.{max (succ u2) (succ u1)} (α -> M) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) f) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t) f)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) t f))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_union_mul_inter Set.mulIndicator_union_mul_interₓ'. -/
@[to_additive]
theorem mulIndicator_union_mul_inter (f : α → M) (s t : Set α) :
    mulIndicator (s ∪ t) f * mulIndicator (s ∩ t) f = mulIndicator s f * mulIndicator t f :=
  funext <| mulIndicator_union_mul_inter_apply f s t
#align set.mul_indicator_union_mul_inter Set.mulIndicator_union_mul_inter
#align set.indicator_union_add_inter Set.indicator_union_add_inter

/- warning: set.mul_indicator_union_of_not_mem_inter -> Set.mulIndicator_union_of_not_mem_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))) -> (forall (f : α -> M), Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) f a) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) t f a)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α} {a : α}, (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t))) -> (forall (f : α -> M), Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) f a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) t f a)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_union_of_not_mem_inter Set.mulIndicator_union_of_not_mem_interₓ'. -/
@[to_additive]
theorem mulIndicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → M) :
    mulIndicator (s ∪ t) f a = mulIndicator s f a * mulIndicator t f a := by
  rw [← mul_indicator_union_mul_inter_apply f s t, mul_indicator_of_not_mem h, mul_one]
#align set.mul_indicator_union_of_not_mem_inter Set.mulIndicator_union_of_not_mem_inter
#align set.indicator_union_of_not_mem_inter Set.indicator_union_of_not_mem_inter

/- warning: set.mul_indicator_union_of_disjoint -> Set.mulIndicator_union_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (forall (f : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) f) (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) t f a)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α}, (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s t) -> (forall (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) f) (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) t f a)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_union_of_disjoint Set.mulIndicator_union_of_disjointₓ'. -/
@[to_additive]
theorem mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
    mulIndicator (s ∪ t) f = fun a => mulIndicator s f a * mulIndicator t f a :=
  funext fun a => mulIndicator_union_of_not_mem_inter (fun ha => h.le_bot ha) _
#align set.mul_indicator_union_of_disjoint Set.mulIndicator_union_of_disjoint
#align set.indicator_union_of_disjoint Set.indicator_union_of_disjoint

/- warning: set.mul_indicator_mul -> Set.mulIndicator_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (s : Set.{u1} α) (f : α -> M) (g : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (f a) (g a))) (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u2} α) (f : α -> M) (g : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (f a) (g a))) (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s g a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul Set.mulIndicator_mulₓ'. -/
@[to_additive]
theorem mulIndicator_mul (s : Set α) (f g : α → M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a :=
  by
  funext
  simp only [mul_indicator]
  split_ifs
  · rfl
  rw [mul_one]
#align set.mul_indicator_mul Set.mulIndicator_mul
#align set.indicator_add Set.indicator_add

/- warning: set.mul_indicator_mul' -> Set.mulIndicator_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (s : Set.{u1} α) (f : α -> M) (g : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) f g)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s g))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u2} α) (f : α -> M) (g : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) f g)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s g))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul' Set.mulIndicator_mul'ₓ'. -/
@[to_additive]
theorem mulIndicator_mul' (s : Set α) (f g : α → M) :
    mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g :=
  mulIndicator_mul s f g
#align set.mul_indicator_mul' Set.mulIndicator_mul'
#align set.indicator_add' Set.indicator_add'

/- warning: set.mul_indicator_compl_mul_self_apply -> Set.mulIndicator_compl_mul_self_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (s : Set.{u1} α) (f : α -> M) (a : α), Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f a)) (f a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u2} α) (f : α -> M) (a : α), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f a)) (f a)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_compl_mul_self_apply Set.mulIndicator_compl_mul_self_applyₓ'. -/
@[simp, to_additive]
theorem mulIndicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator (sᶜ) f a * mulIndicator s f a = f a :=
  by_cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]
#align set.mul_indicator_compl_mul_self_apply Set.mulIndicator_compl_mul_self_apply
#align set.indicator_compl_add_self_apply Set.indicator_compl_add_self_apply

/- warning: set.mul_indicator_compl_mul_self -> Set.mulIndicator_compl_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (s : Set.{u1} α) (f : α -> M), Eq.{succ (max u1 u2)} (α -> M) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u2} α) (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f)) f
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_compl_mul_self Set.mulIndicator_compl_mul_selfₓ'. -/
@[simp, to_additive]
theorem mulIndicator_compl_mul_self (s : Set α) (f : α → M) :
    mulIndicator (sᶜ) f * mulIndicator s f = f :=
  funext <| mulIndicator_compl_mul_self_apply s f
#align set.mul_indicator_compl_mul_self Set.mulIndicator_compl_mul_self
#align set.indicator_compl_add_self Set.indicator_compl_add_self

/- warning: set.mul_indicator_self_mul_compl_apply -> Set.mulIndicator_self_mul_compl_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (s : Set.{u1} α) (f : α -> M) (a : α), Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M _inst_1)) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f a) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f a)) (f a)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u2} α) (f : α -> M) (a : α), Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f a) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f a)) (f a)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_self_mul_compl_apply Set.mulIndicator_self_mul_compl_applyₓ'. -/
@[simp, to_additive]
theorem mulIndicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a * mulIndicator (sᶜ) f a = f a :=
  by_cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]
#align set.mul_indicator_self_mul_compl_apply Set.mulIndicator_self_mul_compl_apply
#align set.indicator_self_add_compl_apply Set.indicator_self_add_compl_apply

/- warning: set.mul_indicator_self_mul_compl -> Set.mulIndicator_self_mul_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] (s : Set.{u1} α) (f : α -> M), Eq.{succ (max u1 u2)} (α -> M) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u2} α) (f : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f)) f
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_self_mul_compl Set.mulIndicator_self_mul_complₓ'. -/
@[simp, to_additive]
theorem mulIndicator_self_mul_compl (s : Set α) (f : α → M) :
    mulIndicator s f * mulIndicator (sᶜ) f = f :=
  funext <| mulIndicator_self_mul_compl_apply s f
#align set.mul_indicator_self_mul_compl Set.mulIndicator_self_mul_compl
#align set.indicator_self_add_compl Set.indicator_self_add_compl

/- warning: set.mul_indicator_mul_eq_left -> Set.mulIndicator_mul_eq_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] {f : α -> M} {g : α -> M}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) f) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) g)) -> (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) f) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) f g)) f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {f : α -> M} {g : α -> M}, (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Function.mulSupport.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) f) (Function.mulSupport.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) g)) -> (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Function.mulSupport.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) f) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) f g)) f)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul_eq_left Set.mulIndicator_mul_eq_leftₓ'. -/
@[to_additive]
theorem mulIndicator_mul_eq_left {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport f).mulIndicator (f * g) = f :=
  by
  refine' (mul_indicator_congr fun x hx => _).trans mul_indicator_mul_support
  have : g x = 1 := nmem_mul_support.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply, this, mul_one]
#align set.mul_indicator_mul_eq_left Set.mulIndicator_mul_eq_left
#align set.indicator_add_eq_left Set.indicator_add_eq_left

/- warning: set.mul_indicator_mul_eq_right -> Set.mulIndicator_mul_eq_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] {f : α -> M} {g : α -> M}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) f) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) g)) -> (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (Function.mulSupport.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) g) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) f g)) g)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {f : α -> M} {g : α -> M}, (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Function.mulSupport.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) f) (Function.mulSupport.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) g)) -> (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (Function.mulSupport.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) g) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) f g)) g)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul_eq_right Set.mulIndicator_mul_eq_rightₓ'. -/
@[to_additive]
theorem mulIndicator_mul_eq_right {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport g).mulIndicator (f * g) = g :=
  by
  refine' (mul_indicator_congr fun x hx => _).trans mul_indicator_mul_support
  have : f x = 1 := nmem_mul_support.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply, this, one_mul]
#align set.mul_indicator_mul_eq_right Set.mulIndicator_mul_eq_right
#align set.indicator_add_eq_right Set.indicator_add_eq_right

/- warning: set.mul_indicator_mul_compl_eq_piecewise -> Set.mulIndicator_mul_compl_eq_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulOneClass.{u2} M] {s : Set.{u1} α} [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)] (f : α -> M) (g : α -> M), Eq.{succ (max u1 u2)} (α -> M) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s f) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) g)) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => M) s f g (fun (j : α) => _inst_2 j))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u2} α} [_inst_2 : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)] (f : α -> M) (g : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M _inst_1))) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) s f) (Set.mulIndicator.{u2, u1} α M (MulOneClass.toOne.{u1} M _inst_1) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) g)) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => M) s f g (fun (j : α) => _inst_2 j))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_mul_compl_eq_piecewise Set.mulIndicator_mul_compl_eq_piecewiseₓ'. -/
@[to_additive]
theorem mulIndicator_mul_compl_eq_piecewise [DecidablePred (· ∈ s)] (f g : α → M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g :=
  by
  ext x
  by_cases h : x ∈ s
  ·
    rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_not_mem (Set.not_mem_compl_iff.2 h), mul_one]
  ·
    rw [piecewise_eq_of_not_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_not_mem h,
      Set.mulIndicator_of_mem (Set.mem_compl h), one_mul]
#align set.mul_indicator_mul_compl_eq_piecewise Set.mulIndicator_mul_compl_eq_piecewise
#align set.indicator_add_compl_eq_piecewise Set.indicator_add_compl_eq_piecewise

#print Set.mulIndicatorHom /-
/-- `set.mul_indicator` as a `monoid_hom`. -/
@[to_additive "`set.indicator` as an `add_monoid_hom`."]
noncomputable def mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α → M) →* α → M
    where
  toFun := mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s
#align set.mul_indicator_hom Set.mulIndicatorHom
#align set.indicator_hom Set.indicatorHom
-/

end Monoid

section DistribMulAction

variable {A : Type _} [AddMonoid A] [Monoid M] [DistribMulAction M A]

/- warning: set.indicator_smul_apply -> Set.indicator_smul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddMonoid.{u3} A] [_inst_2 : Monoid.{u2} M] [_inst_3 : DistribMulAction.{u2, u3} M A _inst_2 _inst_1] (s : Set.{u1} α) (r : α -> M) (f : α -> A) (x : α), Eq.{succ u3} A (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s (fun (x : α) => SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) (r x) (f x)) x) (SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) (r x) (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s f x))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Monoid.{u1} M] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_2 _inst_1] (s : Set.{u3} α) (r : α -> M) (f : α -> A) (x : α), Eq.{succ u2} A (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s (fun (x : α) => HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) (r x) (f x)) x) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) (r x) (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s f x))
Case conversion may be inaccurate. Consider using '#align set.indicator_smul_apply Set.indicator_smul_applyₓ'. -/
theorem indicator_smul_apply (s : Set α) (r : α → M) (f : α → A) (x : α) :
    indicator s (fun x => r x • f x) x = r x • indicator s f x :=
  by
  dsimp only [indicator]
  split_ifs
  exacts[rfl, (smul_zero (r x)).symm]
#align set.indicator_smul_apply Set.indicator_smul_apply

/- warning: set.indicator_smul -> Set.indicator_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddMonoid.{u3} A] [_inst_2 : Monoid.{u2} M] [_inst_3 : DistribMulAction.{u2, u3} M A _inst_2 _inst_1] (s : Set.{u1} α) (r : α -> M) (f : α -> A), Eq.{max (succ u1) (succ u3)} (α -> A) (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s (fun (x : α) => SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) (r x) (f x))) (fun (x : α) => SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) (r x) (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s f x))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Monoid.{u1} M] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_2 _inst_1] (s : Set.{u3} α) (r : α -> M) (f : α -> A), Eq.{max (succ u3) (succ u2)} (α -> A) (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s (fun (x : α) => HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) (r x) (f x))) (fun (x : α) => HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) (r x) (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s f x))
Case conversion may be inaccurate. Consider using '#align set.indicator_smul Set.indicator_smulₓ'. -/
theorem indicator_smul (s : Set α) (r : α → M) (f : α → A) :
    (indicator s fun x : α => r x • f x) = fun x : α => r x • indicator s f x :=
  funext <| indicator_smul_apply s r f
#align set.indicator_smul Set.indicator_smul

/- warning: set.indicator_const_smul_apply -> Set.indicator_const_smul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddMonoid.{u3} A] [_inst_2 : Monoid.{u2} M] [_inst_3 : DistribMulAction.{u2, u3} M A _inst_2 _inst_1] (s : Set.{u1} α) (r : M) (f : α -> A) (x : α), Eq.{succ u3} A (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s (fun (x : α) => SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) r (f x)) x) (SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) r (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s f x))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Monoid.{u1} M] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_2 _inst_1] (s : Set.{u3} α) (r : M) (f : α -> A) (x : α), Eq.{succ u2} A (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s (fun (x : α) => HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) r (f x)) x) (HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) r (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s f x))
Case conversion may be inaccurate. Consider using '#align set.indicator_const_smul_apply Set.indicator_const_smul_applyₓ'. -/
theorem indicator_const_smul_apply (s : Set α) (r : M) (f : α → A) (x : α) :
    indicator s (fun x => r • f x) x = r • indicator s f x :=
  indicator_smul_apply s (fun x => r) f x
#align set.indicator_const_smul_apply Set.indicator_const_smul_apply

/- warning: set.indicator_const_smul -> Set.indicator_const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {A : Type.{u3}} [_inst_1 : AddMonoid.{u3} A] [_inst_2 : Monoid.{u2} M] [_inst_3 : DistribMulAction.{u2, u3} M A _inst_2 _inst_1] (s : Set.{u1} α) (r : M) (f : α -> A), Eq.{max (succ u1) (succ u3)} (α -> A) (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s (fun (x : α) => SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) r (f x))) (fun (x : α) => SMul.smul.{u2, u3} M A (SMulZeroClass.toHasSmul.{u2, u3} M A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) (DistribSMul.toSmulZeroClass.{u2, u3} M A (AddMonoid.toAddZeroClass.{u3} A _inst_1) (DistribMulAction.toDistribSMul.{u2, u3} M A _inst_2 _inst_1 _inst_3))) r (Set.indicator.{u1, u3} α A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A _inst_1)) s f x))
but is expected to have type
  forall {α : Type.{u3}} {M : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Monoid.{u1} M] [_inst_3 : DistribMulAction.{u1, u2} M A _inst_2 _inst_1] (s : Set.{u3} α) (r : M) (f : α -> A), Eq.{max (succ u3) (succ u2)} (α -> A) (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s (fun (x : α) => HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) r (f x))) (fun (x : α) => HSMul.hSMul.{u1, u2, u2} M A A (instHSMul.{u1, u2} M A (SMulZeroClass.toSMul.{u1, u2} M A (AddMonoid.toZero.{u2} A _inst_1) (DistribSMul.toSMulZeroClass.{u1, u2} M A (AddMonoid.toAddZeroClass.{u2} A _inst_1) (DistribMulAction.toDistribSMul.{u1, u2} M A _inst_2 _inst_1 _inst_3)))) r (Set.indicator.{u3, u2} α A (AddMonoid.toZero.{u2} A _inst_1) s f x))
Case conversion may be inaccurate. Consider using '#align set.indicator_const_smul Set.indicator_const_smulₓ'. -/
theorem indicator_const_smul (s : Set α) (r : M) (f : α → A) :
    (indicator s fun x : α => r • f x) = fun x : α => r • indicator s f x :=
  funext <| indicator_const_smul_apply s r f
#align set.indicator_const_smul Set.indicator_const_smul

end DistribMulAction

section Group

variable {G : Type _} [Group G] {s t : Set α} {f g : α → G} {a : α}

/- warning: set.mul_indicator_inv' -> Set.mulIndicator_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] (s : Set.{u1} α) (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) f)) (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s f))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] (s : Set.{u2} α) (f : α -> G), Eq.{max (succ u2) (succ u1)} (α -> G) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s (Inv.inv.{max u2 u1} (α -> G) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) f)) (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s f))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_inv' Set.mulIndicator_inv'ₓ'. -/
@[to_additive]
theorem mulIndicator_inv' (s : Set α) (f : α → G) : mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹ :=
  (mulIndicatorHom G s).map_inv f
#align set.mul_indicator_inv' Set.mulIndicator_inv'
#align set.indicator_neg' Set.indicator_neg'

/- warning: set.mul_indicator_inv -> Set.mulIndicator_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] (s : Set.{u1} α) (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s (fun (a : α) => Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (f a))) (fun (a : α) => Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s f a))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] (s : Set.{u2} α) (f : α -> G), Eq.{max (succ u2) (succ u1)} (α -> G) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s (fun (a : α) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (f a))) (fun (a : α) => Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s f a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_inv Set.mulIndicator_invₓ'. -/
@[to_additive]
theorem mulIndicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ :=
  mulIndicator_inv' s f
#align set.mul_indicator_inv Set.mulIndicator_inv
#align set.indicator_neg Set.indicator_neg

/- warning: set.mul_indicator_div -> Set.mulIndicator_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] (s : Set.{u1} α) (f : α -> G) (g : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s (fun (a : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (f a) (g a))) (fun (a : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s f a) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s g a))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] (s : Set.{u2} α) (f : α -> G) (g : α -> G), Eq.{max (succ u2) (succ u1)} (α -> G) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s (fun (a : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (f a) (g a))) (fun (a : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s f a) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s g a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_div Set.mulIndicator_divₓ'. -/
@[to_additive]
theorem mulIndicator_div (s : Set α) (f g : α → G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a :=
  (mulIndicatorHom G s).map_div f g
#align set.mul_indicator_div Set.mulIndicator_div
#align set.indicator_sub Set.indicator_sub

/- warning: set.mul_indicator_div' -> Set.mulIndicator_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] (s : Set.{u1} α) (f : α -> G) (g : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHDiv.{max u1 u2} (α -> G) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) f g)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHDiv.{max u1 u2} (α -> G) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s f) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s g))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] (s : Set.{u2} α) (f : α -> G) (g : α -> G), Eq.{max (succ u2) (succ u1)} (α -> G) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHDiv.{max u2 u1} (α -> G) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) f g)) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHDiv.{max u2 u1} (α -> G) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s f) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s g))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_div' Set.mulIndicator_div'ₓ'. -/
@[to_additive]
theorem mulIndicator_div' (s : Set α) (f g : α → G) :
    mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g :=
  mulIndicator_div s f g
#align set.mul_indicator_div' Set.mulIndicator_div'
#align set.indicator_sub' Set.indicator_sub'

/- warning: set.mul_indicator_compl -> Set.mulIndicator_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] (s : Set.{u1} α) (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHMul.{max u1 u2} (α -> G) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))) f (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s f)))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] (s : Set.{u2} α) (f : α -> G), Eq.{max (succ u2) (succ u1)} (α -> G) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHMul.{max u2 u1} (α -> G) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) f (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s f)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_compl Set.mulIndicator_complₓ'. -/
@[to_additive indicator_compl']
theorem mulIndicator_compl (s : Set α) (f : α → G) :
    mulIndicator (sᶜ) f = f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| s.mulIndicator_compl_mul_self f
#align set.mul_indicator_compl Set.mulIndicator_compl
#align set.indicator_compl' Set.indicator_compl'

/- warning: set.indicator_compl -> Set.indicator_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : AddGroup.{u2} G] (s : Set.{u1} α) (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.indicator.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHSub.{max u1 u2} (α -> G) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => SubNegMonoid.toHasSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) f (Set.indicator.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) s f))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : AddGroup.{u2} G] (s : Set.{u1} α) (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.indicator.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_2)))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) f) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHSub.{max u1 u2} (α -> G) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) f (Set.indicator.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_2)))) s f))
Case conversion may be inaccurate. Consider using '#align set.indicator_compl Set.indicator_complₓ'. -/
theorem indicator_compl {G} [AddGroup G] (s : Set α) (f : α → G) :
    indicator (sᶜ) f = f - indicator s f := by rw [sub_eq_add_neg, indicator_compl']
#align set.indicator_compl Set.indicator_compl

/- warning: set.mul_indicator_diff -> Set.mulIndicator_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (forall (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s) f) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHMul.{max u1 u2} (α -> G) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) t f) (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Set.mulIndicator.{u1, u2} α G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) s f))))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (forall (f : α -> G), Eq.{max (succ u2) (succ u1)} (α -> G) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) t s) f) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHMul.{max u2 u1} (α -> G) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) t f) (Inv.inv.{max u1 u2} (α -> G) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))) (Set.mulIndicator.{u2, u1} α G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) s f))))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_diff Set.mulIndicator_diffₓ'. -/
@[to_additive indicator_diff']
theorem mulIndicator_diff (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <|
    by
    rw [Pi.mul_def, ← mul_indicator_union_of_disjoint, diff_union_self,
      union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left
#align set.mul_indicator_diff Set.mulIndicator_diff
#align set.indicator_diff' Set.indicator_diff'

/- warning: set.indicator_diff -> Set.indicator_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : AddGroup.{u2} G] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (forall (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.indicator.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s) f) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHSub.{max u1 u2} (α -> G) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => SubNegMonoid.toHasSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) (Set.indicator.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) t f) (Set.indicator.{u1, u2} α G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) s f)))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : AddGroup.{u2} G] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (forall (f : α -> G), Eq.{max (succ u1) (succ u2)} (α -> G) (Set.indicator.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_2)))) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s) f) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> G) (α -> G) (α -> G) (instHSub.{max u1 u2} (α -> G) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_2)))) (Set.indicator.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_2)))) t f) (Set.indicator.{u1, u2} α G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_2)))) s f)))
Case conversion may be inaccurate. Consider using '#align set.indicator_diff Set.indicator_diffₓ'. -/
theorem indicator_diff {G : Type _} [AddGroup G] {s t : Set α} (h : s ⊆ t) (f : α → G) :
    indicator (t \ s) f = indicator t f - indicator s f := by rw [indicator_diff' h, sub_eq_add_neg]
#align set.indicator_diff Set.indicator_diff

end Group

section CommMonoid

variable [CommMonoid M]

/- warning: set.prod_mul_indicator_subset_of_eq_one -> Set.prod_mulIndicator_subset_of_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : One.{u3} N] (f : α -> N) (g : α -> N -> M) {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (forall (a : α), Eq.{succ u2} M (g a (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N _inst_2)))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => g i (f i))) (Finset.prod.{u2, u1} M α _inst_1 t (fun (i : α) => g i (Set.mulIndicator.{u1, u3} α N _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) f i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : One.{u3} N] (f : α -> N) (g : α -> N -> M) {s : Finset.{u2} α} {t : Finset.{u2} α}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s t) -> (forall (a : α), Eq.{succ u1} M (g a (OfNat.ofNat.{u3} N 1 (One.toOfNat1.{u3} N _inst_2))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) -> (Eq.{succ u1} M (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => g i (f i))) (Finset.prod.{u1, u2} M α _inst_1 t (fun (i : α) => g i (Set.mulIndicator.{u2, u3} α N _inst_2 (Finset.toSet.{u2} α s) f i))))
Case conversion may be inaccurate. Consider using '#align set.prod_mul_indicator_subset_of_eq_one Set.prod_mulIndicator_subset_of_eq_oneₓ'. -/
/-- Consider a product of `g i (f i)` over a `finset`.  Suppose `g` is a
function such as `pow`, which maps a second argument of `1` to
`1`. Then if `f` is replaced by the corresponding multiplicative indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
@[to_additive]
theorem prod_mulIndicator_subset_of_eq_one [One N] (f : α → N) (g : α → N → M) {s t : Finset α}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    (∏ i in s, g i (f i)) = ∏ i in t, g i (mulIndicator (↑s) f i) :=
  by
  rw [← Finset.prod_subset h _]
  · apply Finset.prod_congr rfl
    intro i hi
    congr
    symm
    exact mul_indicator_of_mem hi _
  · refine' fun i hi hn => _
    convert hg i
    exact mul_indicator_of_not_mem hn _
#align set.prod_mul_indicator_subset_of_eq_one Set.prod_mulIndicator_subset_of_eq_one
#align set.sum_indicator_subset_of_eq_zero Set.sum_indicator_subset_of_eq_zero

/-- Consider a sum of `g i (f i)` over a `finset`. Suppose `g` is a
function such as multiplication, which maps a second argument of 0 to
0.  (A typical use case would be a weighted sum of `f i * h i` or `f i
• h i`, where `f` gives the weights that are multiplied by some other
function `h`.)  Then if `f` is replaced by the corresponding indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
add_decl_doc Set.sum_indicator_subset_of_eq_zero

/- warning: set.prod_mul_indicator_subset -> Set.prod_mulIndicator_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => f i)) (Finset.prod.{u2, u1} M α _inst_1 t (fun (i : α) => Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) {s : Finset.{u2} α} {t : Finset.{u2} α}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s t) -> (Eq.{succ u1} M (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => f i)) (Finset.prod.{u1, u2} M α _inst_1 t (fun (i : α) => Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Finset.toSet.{u2} α s) f i)))
Case conversion may be inaccurate. Consider using '#align set.prod_mul_indicator_subset Set.prod_mulIndicator_subsetₓ'. -/
/-- Taking the product of an indicator function over a possibly larger `finset` is the same as
taking the original function over the original `finset`. -/
@[to_additive
      "Summing an indicator function over a possibly larger `finset` is the same as summing\nthe original function over the original `finset`."]
theorem prod_mulIndicator_subset (f : α → M) {s t : Finset α} (h : s ⊆ t) :
    (∏ i in s, f i) = ∏ i in t, mulIndicator (↑s) f i :=
  prod_mulIndicator_subset_of_eq_one _ (fun a b => b) h fun _ => rfl
#align set.prod_mul_indicator_subset Set.prod_mulIndicator_subset
#align set.sum_indicator_subset Set.sum_indicator_subset

/- warning: finset.prod_mul_indicator_eq_prod_filter -> Finset.prod_mulIndicator_eq_prod_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (s : Finset.{u2} ι) (f : ι -> α -> M) (t : ι -> (Set.{u1} α)) (g : ι -> α) [_inst_2 : DecidablePred.{succ u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (g i) (t i))], Eq.{succ u3} M (Finset.prod.{u3, u2} M ι _inst_1 s (fun (i : ι) => Set.mulIndicator.{u1, u3} α M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) (t i) (f i) (g i))) (Finset.prod.{u3, u2} M ι _inst_1 (Finset.filter.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (g i) (t i)) (fun (a : ι) => _inst_2 a) s) (fun (i : ι) => f i (g i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (s : Finset.{u3} ι) (f : ι -> α -> M) (t : ι -> (Set.{u2} α)) (g : ι -> α) [_inst_2 : DecidablePred.{succ u3} ι (fun (i : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (g i) (t i))], Eq.{succ u1} M (Finset.prod.{u1, u3} M ι _inst_1 s (fun (i : ι) => Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (t i) (f i) (g i))) (Finset.prod.{u1, u3} M ι _inst_1 (Finset.filter.{u3} ι (fun (i : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (g i) (t i)) (fun (a : ι) => _inst_2 a) s) (fun (i : ι) => f i (g i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_mul_indicator_eq_prod_filter Finset.prod_mulIndicator_eq_prod_filterₓ'. -/
@[to_additive]
theorem Finset.prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι → α → M) (t : ι → Set α)
    (g : ι → α) [DecidablePred fun i => g i ∈ t i] :
    (∏ i in s, mulIndicator (t i) (f i) (g i)) = ∏ i in s.filterₓ fun i => g i ∈ t i, f i (g i) :=
  by
  refine' (Finset.prod_filter_mul_prod_filter_not s (fun i => g i ∈ t i) _).symm.trans _
  refine' Eq.trans _ (mul_one _)
  exact
    congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun x hx => mul_indicator_of_mem (Finset.mem_filter.1 hx).2 _)
      (Finset.prod_eq_one fun x hx => mul_indicator_of_not_mem (Finset.mem_filter.1 hx).2 _)
#align finset.prod_mul_indicator_eq_prod_filter Finset.prod_mulIndicator_eq_prod_filter
#align finset.sum_indicator_eq_sum_filter Finset.sum_indicator_eq_sum_filter

/- warning: set.mul_indicator_finset_prod -> Set.mulIndicator_finset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommMonoid.{u3} M] (I : Finset.{u2} ι) (s : Set.{u1} α) (f : ι -> α -> M), Eq.{max (succ u1) (succ u3)} (α -> M) (Set.mulIndicator.{u1, u3} α M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) s (Finset.prod.{max u1 u3, u2} (α -> M) ι (Pi.commMonoid.{u1, u3} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) I (fun (i : ι) => f i))) (Finset.prod.{max u1 u3, u2} (α -> M) ι (Pi.commMonoid.{u1, u3} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) I (fun (i : ι) => Set.mulIndicator.{u1, u3} α M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_1))) s (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u3}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (I : Finset.{u3} ι) (s : Set.{u2} α) (f : ι -> α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) s (Finset.prod.{max u2 u1, u3} (α -> M) ι (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) I (fun (i : ι) => f i))) (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) I (fun (i : ι) => Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) s (f i)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_finset_prod Set.mulIndicator_finset_prodₓ'. -/
@[to_additive]
theorem mulIndicator_finset_prod (I : Finset ι) (s : Set α) (f : ι → α → M) :
    mulIndicator s (∏ i in I, f i) = ∏ i in I, mulIndicator s (f i) :=
  (mulIndicatorHom M s).map_prod _ _
#align set.mul_indicator_finset_prod Set.mulIndicator_finset_prod
#align set.indicator_finset_sum Set.indicator_finset_sum

/- warning: set.mul_indicator_finset_bUnion -> Set.mulIndicator_finset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {ι : Type.{u3}} (I : Finset.{u3} ι) (s : ι -> (Set.{u1} α)) {f : α -> M}, (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i I) -> (forall (j : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) j I) -> (Ne.{succ u3} ι i j) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (s i) (s j)))) -> (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (Set.unionᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i I) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i I) => s i))) f) (fun (a : α) => Finset.prod.{u2, u3} M ι _inst_1 I (fun (i : ι) => Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (s i) f a)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {ι : Type.{u3}} (I : Finset.{u3} ι) (s : ι -> (Set.{u2} α)) {f : α -> M}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i I) -> (forall (j : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) j I) -> (Ne.{succ u3} ι i j) -> (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (s i) (s j)))) -> (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Set.unionᵢ.{u2, succ u3} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i I) (fun (H : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i I) => s i))) f) (fun (a : α) => Finset.prod.{u1, u3} M ι _inst_1 I (fun (i : ι) => Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (s i) f a)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_finset_bUnion Set.mulIndicator_finset_bunionᵢₓ'. -/
@[to_additive]
theorem mulIndicator_finset_bunionᵢ {ι} (I : Finset ι) (s : ι → Set α) {f : α → M} :
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (s i) (s j)) →
      mulIndicator (⋃ i ∈ I, s i) f = fun a => ∏ i in I, mulIndicator (s i) f a :=
  by
  classical
    refine' Finset.induction_on I _ _
    · intro h
      funext
      simp
    intro a I haI ih hI
    funext
    rw [Finset.prod_insert haI, Finset.set_bunionᵢ_insert, mul_indicator_union_of_not_mem_inter,
      ih _]
    · intro i hi j hj hij
      exact hI i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    simp only [not_exists, exists_prop, mem_Union, mem_inter_iff, not_and]
    intro hx a' ha'
    refine'
      disjoint_left.1 (hI a (Finset.mem_insert_self _ _) a' (Finset.mem_insert_of_mem ha') _) hx
    exact (ne_of_mem_of_not_mem ha' haI).symm
#align set.mul_indicator_finset_bUnion Set.mulIndicator_finset_bunionᵢ
#align set.indicator_finset_bUnion Set.indicator_finset_bunionᵢ

/- warning: set.mul_indicator_finset_bUnion_apply -> Set.mulIndicator_finset_bunionᵢ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] {ι : Type.{u3}} (I : Finset.{u3} ι) (s : ι -> (Set.{u1} α)) {f : α -> M}, (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i I) -> (forall (j : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) j I) -> (Ne.{succ u3} ι i j) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (s i) (s j)))) -> (forall (x : α), Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (Set.unionᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i I) (fun (H : Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i I) => s i))) f x) (Finset.prod.{u2, u3} M ι _inst_1 I (fun (i : ι) => Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (s i) f x)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {ι : Type.{u3}} (I : Finset.{u3} ι) (s : ι -> (Set.{u2} α)) {f : α -> M}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i I) -> (forall (j : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) j I) -> (Ne.{succ u3} ι i j) -> (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (s i) (s j)))) -> (forall (x : α), Eq.{succ u1} M (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Set.unionᵢ.{u2, succ u3} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i I) (fun (H : Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i I) => s i))) f x) (Finset.prod.{u1, u3} M ι _inst_1 I (fun (i : ι) => Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (s i) f x)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_finset_bUnion_apply Set.mulIndicator_finset_bunionᵢ_applyₓ'. -/
@[to_additive]
theorem mulIndicator_finset_bunionᵢ_apply {ι} (I : Finset ι) (s : ι → Set α) {f : α → M}
    (h : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (s i) (s j)) (x : α) :
    mulIndicator (⋃ i ∈ I, s i) f x = ∏ i in I, mulIndicator (s i) f x := by
  rw [Set.mulIndicator_finset_bunionᵢ I s h]
#align set.mul_indicator_finset_bUnion_apply Set.mulIndicator_finset_bunionᵢ_apply
#align set.indicator_finset_bUnion_apply Set.indicator_finset_bunionᵢ_apply

end CommMonoid

section MulZeroClass

variable [MulZeroClass M] {s t : Set α} {f g : α → M} {a : α}

/- warning: set.indicator_mul -> Set.indicator_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulZeroClass.{u2} M] (s : Set.{u1} α) (f : α -> M) (g : α -> M), Eq.{max (succ u1) (succ u2)} (α -> M) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (f a) (g a))) (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s f a) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M] (s : Set.{u2} α) (f : α -> M) (g : α -> M), Eq.{max (succ u2) (succ u1)} (α -> M) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (f a) (g a))) (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s f a) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s g a))
Case conversion may be inaccurate. Consider using '#align set.indicator_mul Set.indicator_mulₓ'. -/
theorem indicator_mul (s : Set α) (f g : α → M) :
    (indicator s fun a => f a * g a) = fun a => indicator s f a * indicator s g a :=
  by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]
#align set.indicator_mul Set.indicator_mul

/- warning: set.indicator_mul_left -> Set.indicator_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulZeroClass.{u2} M] {a : α} (s : Set.{u1} α) (f : α -> M) (g : α -> M), Eq.{succ u2} M (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (f a) (g a)) a) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s f a) (g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M] {a : α} (s : Set.{u2} α) (f : α -> M) (g : α -> M), Eq.{succ u1} M (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (f a) (g a)) a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s f a) (g a))
Case conversion may be inaccurate. Consider using '#align set.indicator_mul_left Set.indicator_mul_leftₓ'. -/
theorem indicator_mul_left (s : Set α) (f g : α → M) :
    indicator s (fun a => f a * g a) a = indicator s f a * g a :=
  by
  simp only [indicator]
  split_ifs
  · rfl
  rw [zero_mul]
#align set.indicator_mul_left Set.indicator_mul_left

/- warning: set.indicator_mul_right -> Set.indicator_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulZeroClass.{u2} M] {a : α} (s : Set.{u1} α) (f : α -> M) (g : α -> M), Eq.{succ u2} M (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (f a) (g a)) a) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (f a) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) s g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M] {a : α} (s : Set.{u2} α) (f : α -> M) (g : α -> M), Eq.{succ u1} M (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (f a) (g a)) a) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (f a) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) s g a))
Case conversion may be inaccurate. Consider using '#align set.indicator_mul_right Set.indicator_mul_rightₓ'. -/
theorem indicator_mul_right (s : Set α) (f g : α → M) :
    indicator s (fun a => f a * g a) a = f a * indicator s g a :=
  by
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]
#align set.indicator_mul_right Set.indicator_mul_right

/- warning: set.inter_indicator_mul -> Set.inter_indicator_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulZeroClass.{u2} M] {t1 : Set.{u1} α} {t2 : Set.{u1} α} (f : α -> M) (g : α -> M) (x : α), Eq.{succ u2} M (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t1 t2) (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (f x) (g x)) x) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulZeroClass.toHasMul.{u2} M _inst_1)) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) t1 f x) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M _inst_1) t2 g x))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M] {t1 : Set.{u2} α} {t2 : Set.{u2} α} (f : α -> M) (g : α -> M) (x : α), Eq.{succ u1} M (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) t1 t2) (fun (x : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (f x) (g x)) x) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M _inst_1)) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) t1 f x) (Set.indicator.{u2, u1} α M (MulZeroClass.toZero.{u1} M _inst_1) t2 g x))
Case conversion may be inaccurate. Consider using '#align set.inter_indicator_mul Set.inter_indicator_mulₓ'. -/
theorem inter_indicator_mul {t1 t2 : Set α} (f g : α → M) (x : α) :
    (t1 ∩ t2).indicator (fun x => f x * g x) x = t1.indicator f x * t2.indicator g x :=
  by
  rw [← Set.indicator_indicator]
  simp [indicator]
#align set.inter_indicator_mul Set.inter_indicator_mul

end MulZeroClass

section MulZeroOneClass

variable [MulZeroOneClass M]

/- warning: set.inter_indicator_one -> Set.inter_indicator_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : MulZeroOneClass.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{max (succ u1) (succ u2)} (α -> M) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHMul.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulZeroClass.toHasMul.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)))) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) s (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))))) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) t (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{max (succ u2) (succ u1)} (α -> M) (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t) (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.7307 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1)))) (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) s (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))) (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) t (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align set.inter_indicator_one Set.inter_indicator_oneₓ'. -/
theorem inter_indicator_one {s t : Set α} :
    (s ∩ t).indicator (1 : _ → M) = s.indicator 1 * t.indicator 1 :=
  funext fun _ => by simpa only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]
#align set.inter_indicator_one Set.inter_indicator_one

/- warning: set.indicator_prod_one -> Set.indicator_prod_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : MulZeroOneClass.{u3} M] {s : Set.{u1} α} {t : Set.{u2} β} {x : α} {y : β}, Eq.{succ u3} M (Set.indicator.{max u1 u2, u3} (Prod.{u1, u2} α β) M (MulZeroClass.toHasZero.{u3} M (MulZeroOneClass.toMulZeroClass.{u3} M _inst_1)) (Set.prod.{u1, u2} α β s t) (OfNat.ofNat.{max (max u1 u2) u3} ((Prod.{u1, u2} α β) -> M) 1 (OfNat.mk.{max (max u1 u2) u3} ((Prod.{u1, u2} α β) -> M) 1 (One.one.{max (max u1 u2) u3} ((Prod.{u1, u2} α β) -> M) (Pi.instOne.{max u1 u2, u3} (Prod.{u1, u2} α β) (fun (ᾰ : Prod.{u1, u2} α β) => M) (fun (i : Prod.{u1, u2} α β) => MulOneClass.toHasOne.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)))))) (Prod.mk.{u1, u2} α β x y)) (HMul.hMul.{u3, u3, u3} M M M (instHMul.{u3} M (MulZeroClass.toHasMul.{u3} M (MulZeroOneClass.toMulZeroClass.{u3} M _inst_1))) (Set.indicator.{u1, u3} α M (MulZeroClass.toHasZero.{u3} M (MulZeroOneClass.toMulZeroClass.{u3} M _inst_1)) s (OfNat.ofNat.{max u1 u3} (α -> M) 1 (OfNat.mk.{max u1 u3} (α -> M) 1 (One.one.{max u1 u3} (α -> M) (Pi.instOne.{u1, u3} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)))))) x) (Set.indicator.{u2, u3} β M (MulZeroClass.toHasZero.{u3} M (MulZeroOneClass.toMulZeroClass.{u3} M _inst_1)) t (OfNat.ofNat.{max u2 u3} (β -> M) 1 (OfNat.mk.{max u2 u3} (β -> M) 1 (One.one.{max u2 u3} (β -> M) (Pi.instOne.{u2, u3} β (fun (ᾰ : β) => M) (fun (i : β) => MulOneClass.toHasOne.{u3} M (MulZeroOneClass.toMulOneClass.{u3} M _inst_1)))))) y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M] {s : Set.{u3} α} {t : Set.{u2} β} {x : α} {y : β}, Eq.{succ u1} M (Set.indicator.{max u3 u2, u1} (Prod.{u3, u2} α β) M (MulZeroOneClass.toZero.{u1} M _inst_1) (Set.prod.{u3, u2} α β s t) (OfNat.ofNat.{max (max u3 u2) u1} ((Prod.{u3, u2} α β) -> M) 1 (One.toOfNat1.{max (max u3 u2) u1} ((Prod.{u3, u2} α β) -> M) (Pi.instOne.{max u3 u2, u1} (Prod.{u3, u2} α β) (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.7366 : Prod.{u3, u2} α β) => M) (fun (i : Prod.{u3, u2} α β) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))) (Prod.mk.{u3, u2} α β x y)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M _inst_1))) (Set.indicator.{u3, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) s (OfNat.ofNat.{max u3 u1} (α -> M) 1 (One.toOfNat1.{max u3 u1} (α -> M) (Pi.instOne.{u3, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))) x) (Set.indicator.{u2, u1} β M (MulZeroOneClass.toZero.{u1} M _inst_1) t (OfNat.ofNat.{max u2 u1} (β -> M) 1 (One.toOfNat1.{max u2 u1} (β -> M) (Pi.instOne.{u2, u1} β (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : β) => M) (fun (i : β) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))) y))
Case conversion may be inaccurate. Consider using '#align set.indicator_prod_one Set.indicator_prod_oneₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem indicator_prod_one {s : Set α} {t : Set β} {x : α} {y : β} :
    (s ×ˢ t).indicator (1 : _ → M) (x, y) = s.indicator 1 x * t.indicator 1 y := by
  classical simp [indicator_apply, ← ite_and]
#align set.indicator_prod_one Set.indicator_prod_one

variable (M) [Nontrivial M]

/- warning: set.indicator_eq_zero_iff_not_mem -> Set.indicator_eq_zero_iff_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (M : Type.{u2}) [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : Nontrivial.{u2} M] {U : Set.{u1} α} {x : α}, Iff (Eq.{succ u2} M (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) U (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)))))) x) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)))))) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U))
but is expected to have type
  forall {α : Type.{u2}} (M : Type.{u1}) [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : Nontrivial.{u1} M] {U : Set.{u2} α} {x : α}, Iff (Eq.{succ u1} M (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) U (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))) x) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (MulZeroOneClass.toZero.{u1} M _inst_1)))) (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x U))
Case conversion may be inaccurate. Consider using '#align set.indicator_eq_zero_iff_not_mem Set.indicator_eq_zero_iff_not_memₓ'. -/
theorem indicator_eq_zero_iff_not_mem {U : Set α} {x : α} : indicator U 1 x = (0 : M) ↔ x ∉ U := by
  classical simp [indicator_apply, imp_false]
#align set.indicator_eq_zero_iff_not_mem Set.indicator_eq_zero_iff_not_mem

/- warning: set.indicator_eq_one_iff_mem -> Set.indicator_eq_one_iff_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (M : Type.{u2}) [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : Nontrivial.{u2} M] {U : Set.{u1} α} {x : α}, Iff (Eq.{succ u2} M (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) U (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)))))) x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)))))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U)
but is expected to have type
  forall {α : Type.{u2}} (M : Type.{u1}) [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : Nontrivial.{u1} M] {U : Set.{u2} α} {x : α}, Iff (Eq.{succ u1} M (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) U (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))) x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x U)
Case conversion may be inaccurate. Consider using '#align set.indicator_eq_one_iff_mem Set.indicator_eq_one_iff_memₓ'. -/
theorem indicator_eq_one_iff_mem {U : Set α} {x : α} : indicator U 1 x = (1 : M) ↔ x ∈ U := by
  classical simp [indicator_apply, imp_false]
#align set.indicator_eq_one_iff_mem Set.indicator_eq_one_iff_mem

/- warning: set.indicator_one_inj -> Set.indicator_one_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (M : Type.{u2}) [_inst_1 : MulZeroOneClass.{u2} M] [_inst_2 : Nontrivial.{u2} M] {U : Set.{u1} α} {V : Set.{u1} α}, (Eq.{max (succ u1) (succ u2)} (α -> M) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) U (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1))))))) (Set.indicator.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M _inst_1)) V (OfNat.ofNat.{max u1 u2} (α -> M) 1 (OfNat.mk.{max u1 u2} (α -> M) 1 (One.one.{max u1 u2} (α -> M) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (MulZeroOneClass.toMulOneClass.{u2} M _inst_1)))))))) -> (Eq.{succ u1} (Set.{u1} α) U V)
but is expected to have type
  forall {α : Type.{u2}} (M : Type.{u1}) [_inst_1 : MulZeroOneClass.{u1} M] [_inst_2 : Nontrivial.{u1} M] {U : Set.{u2} α} {V : Set.{u2} α}, (Eq.{max (succ u2) (succ u1)} (α -> M) (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) U (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.7683 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1)))))) (Set.indicator.{u2, u1} α M (MulZeroOneClass.toZero.{u1} M _inst_1) V (OfNat.ofNat.{max u2 u1} (α -> M) 1 (One.toOfNat1.{max u2 u1} (α -> M) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : α) => M) (fun (i : α) => MulOneClass.toOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M _inst_1))))))) -> (Eq.{succ u2} (Set.{u2} α) U V)
Case conversion may be inaccurate. Consider using '#align set.indicator_one_inj Set.indicator_one_injₓ'. -/
theorem indicator_one_inj {U V : Set α} (h : indicator U (1 : α → M) = indicator V 1) : U = V :=
  by
  ext
  simp_rw [← indicator_eq_one_iff_mem M, h]
#align set.indicator_one_inj Set.indicator_one_inj

end MulZeroOneClass

section Order

variable [One M] {s t : Set α} {f g : α → M} {a : α} {y : M}

section

variable [LE M]

/- warning: set.mul_indicator_apply_le' -> Set.mulIndicator_apply_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {a : α} {y : M} [_inst_2 : LE.{u2} M], ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M _inst_2 (f a) y)) -> ((Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (LE.le.{u2} M _inst_2 (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) y)) -> (LE.le.{u2} M _inst_2 (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) y)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} {a : α} {y : M} [_inst_2 : LE.{u1} M], ((Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M _inst_2 (f a) y)) -> ((Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (LE.le.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) y)) -> (LE.le.{u1} M _inst_2 (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) y)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_apply_le' Set.mulIndicator_apply_le'ₓ'. -/
@[to_additive]
theorem mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha
#align set.mul_indicator_apply_le' Set.mulIndicator_apply_le'
#align set.indicator_apply_le' Set.indicator_apply_le'

/- warning: set.mul_indicator_le' -> Set.mulIndicator_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {g : α -> M} [_inst_2 : LE.{u2} M], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M _inst_2 (f a) (g a))) -> (forall (a : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (LE.le.{u2} M _inst_2 (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (g a))) -> (LE.le.{max u1 u2} (α -> M) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) g)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} {g : α -> M} [_inst_2 : LE.{u1} M], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M _inst_2 (f a) (g a))) -> (forall (a : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (LE.le.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (g a))) -> (LE.le.{max u2 u1} (α -> M) (Pi.hasLe.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) g)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_le' Set.mulIndicator_le'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a «expr ∉ » s) -/
@[to_additive]
theorem mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ (a) (_ : a ∉ s), 1 ≤ g a) :
    mulIndicator s f ≤ g := fun a => mulIndicator_apply_le' (hfg _) (hg _)
#align set.mul_indicator_le' Set.mulIndicator_le'
#align set.indicator_le' Set.indicator_le'

/- warning: set.le_mul_indicator_apply -> Set.le_mulIndicator_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {g : α -> M} {a : α} [_inst_2 : LE.{u2} M] {y : M}, ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M _inst_2 y (g a))) -> ((Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (LE.le.{u2} M _inst_2 y (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))) -> (LE.le.{u2} M _inst_2 y (Set.mulIndicator.{u1, u2} α M _inst_1 s g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {g : α -> M} {a : α} [_inst_2 : LE.{u1} M] {y : M}, ((Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M _inst_2 y (g a))) -> ((Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (LE.le.{u1} M _inst_2 y (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))) -> (LE.le.{u1} M _inst_2 y (Set.mulIndicator.{u2, u1} α M _inst_1 s g a))
Case conversion may be inaccurate. Consider using '#align set.le_mul_indicator_apply Set.le_mulIndicator_applyₓ'. -/
@[to_additive]
theorem le_mulIndicator_apply {y} (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a :=
  @mulIndicator_apply_le' α Mᵒᵈ ‹_› _ _ _ _ _ hfg hf
#align set.le_mul_indicator_apply Set.le_mulIndicator_apply
#align set.le_indicator_apply Set.le_indicator_apply

/- warning: set.le_mul_indicator -> Set.le_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {g : α -> M} [_inst_2 : LE.{u2} M], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M _inst_2 (f a) (g a))) -> (forall (a : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (LE.le.{u2} M _inst_2 (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))) -> (LE.le.{max u1 u2} (α -> M) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) f (Set.mulIndicator.{u1, u2} α M _inst_1 s g))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} {g : α -> M} [_inst_2 : LE.{u1} M], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M _inst_2 (f a) (g a))) -> (forall (a : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (LE.le.{u1} M _inst_2 (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))) -> (LE.le.{max u2 u1} (α -> M) (Pi.hasLe.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) f (Set.mulIndicator.{u2, u1} α M _inst_1 s g))
Case conversion may be inaccurate. Consider using '#align set.le_mul_indicator Set.le_mulIndicatorₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a «expr ∉ » s) -/
@[to_additive]
theorem le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ (a) (_ : a ∉ s), f a ≤ 1) :
    f ≤ mulIndicator s g := fun a => le_mulIndicator_apply (hfg _) (hf _)
#align set.le_mul_indicator Set.le_mulIndicator
#align set.le_indicator Set.le_indicator

end

variable [Preorder M]

/- warning: set.one_le_mul_indicator_apply -> Set.one_le_mulIndicator_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {a : α} [_inst_2 : Preorder.{u2} M], ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (f a))) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M _inst_1 s f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} {a : α} [_inst_2 : Preorder.{u1} M], ((Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (f a))) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M _inst_1 s f a))
Case conversion may be inaccurate. Consider using '#align set.one_le_mul_indicator_apply Set.one_le_mulIndicator_applyₓ'. -/
@[to_additive indicator_apply_nonneg]
theorem one_le_mulIndicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mulIndicator_apply h fun _ => le_rfl
#align set.one_le_mul_indicator_apply Set.one_le_mulIndicator_apply
#align set.indicator_apply_nonneg Set.indicator_apply_nonneg

/- warning: set.one_le_mul_indicator -> Set.one_le_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} [_inst_2 : Preorder.{u2} M], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (f a))) -> (forall (a : α), LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (Set.mulIndicator.{u1, u2} α M _inst_1 s f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} [_inst_2 : Preorder.{u1} M], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (f a))) -> (forall (a : α), LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (Set.mulIndicator.{u2, u1} α M _inst_1 s f a))
Case conversion may be inaccurate. Consider using '#align set.one_le_mul_indicator Set.one_le_mulIndicatorₓ'. -/
@[to_additive indicator_nonneg]
theorem one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  one_le_mulIndicator_apply (h a)
#align set.one_le_mul_indicator Set.one_le_mulIndicator
#align set.indicator_nonneg Set.indicator_nonneg

/- warning: set.mul_indicator_apply_le_one -> Set.mulIndicator_apply_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} {a : α} [_inst_2 : Preorder.{u2} M], ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} {a : α} [_inst_2 : Preorder.{u1} M], ((Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_apply_le_one Set.mulIndicator_apply_le_oneₓ'. -/
@[to_additive]
theorem mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le' h fun _ => le_rfl
#align set.mul_indicator_apply_le_one Set.mulIndicator_apply_le_one
#align set.indicator_apply_nonpos Set.indicator_apply_nonpos

/- warning: set.mul_indicator_le_one -> Set.mulIndicator_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} [_inst_2 : Preorder.{u2} M], (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))) -> (forall (a : α), LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} [_inst_2 : Preorder.{u1} M], (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))) -> (forall (a : α), LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_le_one Set.mulIndicator_le_oneₓ'. -/
@[to_additive]
theorem mulIndicator_le_one (h : ∀ a ∈ s, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  mulIndicator_apply_le_one (h a)
#align set.mul_indicator_le_one Set.mulIndicator_le_one
#align set.indicator_nonpos Set.indicator_nonpos

#print Set.mulIndicator_le_mulIndicator /-
@[to_additive]
theorem mulIndicator_le_mulIndicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun _ => h
#align set.mul_indicator_le_mul_indicator Set.mulIndicator_le_mulIndicator
#align set.indicator_le_indicator Set.indicator_le_indicator
-/

attribute [mono] mul_indicator_le_mul_indicator indicator_le_indicator

/- warning: set.mul_indicator_le_mul_indicator_of_subset -> Set.mulIndicator_le_mulIndicator_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> M} [_inst_2 : Preorder.{u2} M], (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (forall (a : α), LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (f a)) -> (forall (a : α), LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (Set.mulIndicator.{u1, u2} α M _inst_1 s f a) (Set.mulIndicator.{u1, u2} α M _inst_1 t f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> M} [_inst_2 : Preorder.{u1} M], (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (forall (a : α), LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (f a)) -> (forall (a : α), LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (Set.mulIndicator.{u2, u1} α M _inst_1 s f a) (Set.mulIndicator.{u2, u1} α M _inst_1 t f a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_le_mul_indicator_of_subset Set.mulIndicator_le_mulIndicator_of_subsetₓ'. -/
@[to_additive]
theorem mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : ∀ a, 1 ≤ f a) (a : α) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha => le_mulIndicator_apply (fun _ => le_rfl) fun hat => (hat <| h ha).elim) fun ha =>
    one_le_mulIndicator_apply fun _ => hf _
#align set.mul_indicator_le_mul_indicator_of_subset Set.mulIndicator_le_mulIndicator_of_subset
#align set.indicator_le_indicator_of_subset Set.indicator_le_indicator_of_subset

/- warning: set.mul_indicator_le_self' -> Set.mulIndicator_le_self' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : One.{u2} M] {s : Set.{u1} α} {f : α -> M} [_inst_2 : Preorder.{u2} M], (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M _inst_2) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M _inst_1))) (f x))) -> (LE.le.{max u1 u2} (α -> M) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Preorder.toLE.{u2} M _inst_2)) (Set.mulIndicator.{u1, u2} α M _inst_1 s f) f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : One.{u1} M] {s : Set.{u2} α} {f : α -> M} [_inst_2 : Preorder.{u1} M], (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_1)) (f x))) -> (LE.le.{max u2 u1} (α -> M) (Pi.hasLe.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => Preorder.toLE.{u1} M _inst_2)) (Set.mulIndicator.{u2, u1} α M _inst_1 s f) f)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_le_self' Set.mulIndicator_le_self'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » s) -/
@[to_additive]
theorem mulIndicator_le_self' (hf : ∀ (x) (_ : x ∉ s), 1 ≤ f x) : mulIndicator s f ≤ f :=
  mulIndicator_le' (fun _ _ => le_rfl) hf
#align set.mul_indicator_le_self' Set.mulIndicator_le_self'
#align set.indicator_le_self' Set.indicator_le_self'

/- warning: set.mul_indicator_Union_apply -> Set.mulIndicator_unionᵢ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {M : Type.{u3}} [_inst_3 : CompleteLattice.{u3} M] [_inst_4 : One.{u3} M], (Eq.{succ u3} M (Bot.bot.{u3} M (CompleteLattice.toHasBot.{u3} M _inst_3)) (OfNat.ofNat.{u3} M 1 (OfNat.mk.{u3} M 1 (One.one.{u3} M _inst_4)))) -> (forall (s : ι -> (Set.{u1} α)) (f : α -> M) (x : α), Eq.{succ u3} M (Set.mulIndicator.{u1, u3} α M _inst_4 (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) f x) (supᵢ.{u3, u2} M (ConditionallyCompleteLattice.toHasSup.{u3} M (CompleteLattice.toConditionallyCompleteLattice.{u3} M _inst_3)) ι (fun (i : ι) => Set.mulIndicator.{u1, u3} α M _inst_4 (s i) f x)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Sort.{u3}} {M : Type.{u2}} [_inst_3 : CompleteLattice.{u2} M] [_inst_4 : One.{u2} M], (Eq.{succ u2} M (Bot.bot.{u2} M (CompleteLattice.toBot.{u2} M _inst_3)) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M _inst_4))) -> (forall (s : ι -> (Set.{u1} α)) (f : α -> M) (x : α), Eq.{succ u2} M (Set.mulIndicator.{u1, u2} α M _inst_4 (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) f x) (supᵢ.{u2, u3} M (ConditionallyCompleteLattice.toSupSet.{u2} M (CompleteLattice.toConditionallyCompleteLattice.{u2} M _inst_3)) ι (fun (i : ι) => Set.mulIndicator.{u1, u2} α M _inst_4 (s i) f x)))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_Union_apply Set.mulIndicator_unionᵢ_applyₓ'. -/
@[to_additive]
theorem mulIndicator_unionᵢ_apply {ι M} [CompleteLattice M] [One M] (h1 : (⊥ : M) = 1)
    (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x :=
  by
  by_cases hx : x ∈ ⋃ i, s i
  · rw [mul_indicator_of_mem hx]
    rw [mem_Union] at hx
    refine' le_antisymm _ (supᵢ_le fun i => mul_indicator_le_self' (fun x hx => h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_supᵢ_of_le i (ge_of_eq <| mul_indicator_of_mem hi _)
  · rw [mul_indicator_of_not_mem hx]
    simp only [mem_Union, not_exists] at hx
    simp [hx, ← h1]
#align set.mul_indicator_Union_apply Set.mulIndicator_unionᵢ_apply
#align set.indicator_Union_apply Set.indicator_unionᵢ_apply

end Order

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid M]

/- warning: set.mul_indicator_le_self -> Set.mulIndicator_le_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] (s : Set.{u1} α) (f : α -> M), LE.le.{max u1 u2} (α -> M) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))) s f) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] (s : Set.{u2} α) (f : α -> M), LE.le.{max u2 u1} (α -> M) (Pi.hasLe.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) s f) f
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_le_self Set.mulIndicator_le_selfₓ'. -/
@[to_additive]
theorem mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  mulIndicator_le_self' fun _ _ => one_le _
#align set.mul_indicator_le_self Set.mulIndicator_le_self
#align set.indicator_le_self Set.indicator_le_self

/- warning: set.mul_indicator_apply_le -> Set.mulIndicator_apply_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] {a : α} {s : Set.{u1} α} {f : α -> M} {g : α -> M}, ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)))) (f a) (g a))) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))) s f a) (g a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] {a : α} {s : Set.{u2} α} {f : α -> M} {g : α -> M}, ((Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) (f a) (g a))) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) s f a) (g a))
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_apply_le Set.mulIndicator_apply_leₓ'. -/
@[to_additive]
theorem mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a :=
  mulIndicator_apply_le' hfg fun _ => one_le _
#align set.mul_indicator_apply_le Set.mulIndicator_apply_le
#align set.indicator_apply_le Set.indicator_apply_le

/- warning: set.mul_indicator_le -> Set.mulIndicator_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] {s : Set.{u1} α} {f : α -> M} {g : α -> M}, (forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)))) (f a) (g a))) -> (LE.le.{max u1 u2} (α -> M) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))) (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))) s f) g)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] {s : Set.{u2} α} {f : α -> M} {g : α -> M}, (forall (a : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) (f a) (g a))) -> (LE.le.{max u2 u1} (α -> M) (Pi.hasLe.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (Set.mulIndicator.{u2, u1} α M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) s f) g)
Case conversion may be inaccurate. Consider using '#align set.mul_indicator_le Set.mulIndicator_leₓ'. -/
@[to_additive]
theorem mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g :=
  mulIndicator_le' hfg fun _ _ => one_le _
#align set.mul_indicator_le Set.mulIndicator_le
#align set.indicator_le Set.indicator_le

end CanonicallyOrderedMonoid

#print Set.indicator_le_indicator_nonneg /-
theorem indicator_le_indicator_nonneg {β} [LinearOrder β] [Zero β] (s : Set α) (f : α → β) :
    s.indicator f ≤ { x | 0 ≤ f x }.indicator f :=
  by
  intro x
  classical
    simp_rw [indicator_apply]
    split_ifs
    · exact le_rfl
    · exact (not_le.mp h_1).le
    · exact h_1
    · exact le_rfl
#align set.indicator_le_indicator_nonneg Set.indicator_le_indicator_nonneg
-/

#print Set.indicator_nonpos_le_indicator /-
theorem indicator_nonpos_le_indicator {β} [LinearOrder β] [Zero β] (s : Set α) (f : α → β) :
    { x | f x ≤ 0 }.indicator f ≤ s.indicator f :=
  @indicator_le_indicator_nonneg α βᵒᵈ _ _ s f
#align set.indicator_nonpos_le_indicator Set.indicator_nonpos_le_indicator
-/

end Set

/- warning: monoid_hom.map_mul_indicator -> MonoidHom.map_mulIndicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] (f : MonoidHom.{u2, u3} M N _inst_1 _inst_2) (s : Set.{u1} α) (g : α -> M) (x : α), Eq.{succ u3} N (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u2, u3} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N _inst_1 _inst_2) f (Set.mulIndicator.{u1, u2} α M (MulOneClass.toHasOne.{u2} M _inst_1) s g x)) (Set.mulIndicator.{u1, u3} α N (MulOneClass.toHasOne.{u3} N _inst_2) s (Function.comp.{succ u1, succ u2, succ u3} α M N (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} M N _inst_1 _inst_2) (fun (_x : MonoidHom.{u2, u3} M N _inst_1 _inst_2) => M -> N) (MonoidHom.hasCoeToFun.{u2, u3} M N _inst_1 _inst_2) f) g) x)
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u3, u2} M N _inst_1 _inst_2) (s : Set.{u1} α) (g : α -> M) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (Set.mulIndicator.{u1, u3} α M (MulOneClass.toOne.{u3} M _inst_1) s g x)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f (Set.mulIndicator.{u1, u3} α M (MulOneClass.toOne.{u3} M _inst_1) s g x)) (Set.mulIndicator.{u1, u2} α N (MulOneClass.toOne.{u2} N _inst_2) s (Function.comp.{succ u1, succ u3, succ u2} α M N (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) (MonoidHomClass.toMulHomClass.{max u3 u2, u3, u2} (MonoidHom.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MonoidHom.monoidHomClass.{u3, u2} M N _inst_1 _inst_2))) f) g) x)
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_mul_indicator MonoidHom.map_mulIndicatorₓ'. -/
@[to_additive]
theorem MonoidHom.map_mulIndicator {M N : Type _} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (s : Set α) (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x :=
  congr_fun (Set.mulIndicator_comp_of_one f.map_one).symm x
#align monoid_hom.map_mul_indicator MonoidHom.map_mulIndicator
#align add_monoid_hom.map_indicator AddMonoidHom.map_indicator

