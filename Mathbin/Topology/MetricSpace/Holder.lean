/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.holder
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Lipschitz
import Mathbin.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Hölder continuous functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define Hölder continuity on a set and on the whole space. We also prove some basic
properties of Hölder continuous functions.

## Main definitions

* `holder_on_with`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and
  exponent `r : ℝ≥0` on a set `s`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y ∈ s`;
* `holder_with`: `f : X → Y` is said to be *Hölder continuous* with constant `C : ℝ≥0` and exponent
  `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`.

## Implementation notes

We use the type `ℝ≥0` (a.k.a. `nnreal`) for `C` because this type has coercion both to `ℝ` and
`ℝ≥0∞`, so it can be easily used both in inequalities about `dist` and `edist`. We also use `ℝ≥0`
for `r` to ensure that `d ^ r` is monotone in `d`. It might be a good idea to use
`ℝ>0` for `r` but we don't have this type in `mathlib` (yet).

## Tags

Hölder continuity, Lipschitz continuity

 -/


variable {X Y Z : Type _}

open Filter Set

open NNReal ENNReal Topology

section Emetric

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

#print HolderWith /-
/-- A function `f : X → Y` between two `pseudo_emetric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0`, if `edist (f x) (f y) ≤ C * edist x y ^ r` for all `x y : X`. -/
def HolderWith (C r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x y, edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ)
#align holder_with HolderWith
-/

#print HolderOnWith /-
/-- A function `f : X → Y` between two `pseudo_emeteric_space`s is Hölder continuous with constant
`C : ℝ≥0` and exponent `r : ℝ≥0` on a set `s : set X`, if `edist (f x) (f y) ≤ C * edist x y ^ r`
for all `x y ∈ s`. -/
def HolderOnWith (C r : ℝ≥0) (f : X → Y) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ)
#align holder_on_with HolderOnWith
-/

/- warning: holder_on_with_empty -> holderOnWith_empty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] (C : NNReal) (r : NNReal) (f : X -> Y), HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f (EmptyCollection.emptyCollection.{u1} (Set.{u1} X) (Set.hasEmptyc.{u1} X))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] (C : NNReal) (r : NNReal) (f : X -> Y), HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f (EmptyCollection.emptyCollection.{u2} (Set.{u2} X) (Set.instEmptyCollectionSet.{u2} X))
Case conversion may be inaccurate. Consider using '#align holder_on_with_empty holderOnWith_emptyₓ'. -/
@[simp]
theorem holderOnWith_empty (C r : ℝ≥0) (f : X → Y) : HolderOnWith C r f ∅ := fun x hx => hx.elim
#align holder_on_with_empty holderOnWith_empty

/- warning: holder_on_with_singleton -> holderOnWith_singleton is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] (C : NNReal) (r : NNReal) (f : X -> Y) (x : X), HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.hasSingleton.{u1} X) x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] (C : NNReal) (r : NNReal) (f : X -> Y) (x : X), HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f (Singleton.singleton.{u2, u2} X (Set.{u2} X) (Set.instSingletonSet.{u2} X) x)
Case conversion may be inaccurate. Consider using '#align holder_on_with_singleton holderOnWith_singletonₓ'. -/
@[simp]
theorem holderOnWith_singleton (C r : ℝ≥0) (f : X → Y) (x : X) : HolderOnWith C r f {x} :=
  by
  rintro a (rfl : a = x) b (rfl : b = a)
  rw [edist_self]
  exact zero_le _
#align holder_on_with_singleton holderOnWith_singleton

/- warning: set.subsingleton.holder_on_with -> Set.Subsingleton.holderOnWith is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {s : Set.{u1} X}, (Set.Subsingleton.{u1} X s) -> (forall (C : NNReal) (r : NNReal) (f : X -> Y), HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {s : Set.{u2} X}, (Set.Subsingleton.{u2} X s) -> (forall (C : NNReal) (r : NNReal) (f : X -> Y), HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s)
Case conversion may be inaccurate. Consider using '#align set.subsingleton.holder_on_with Set.Subsingleton.holderOnWithₓ'. -/
theorem Set.Subsingleton.holderOnWith {s : Set X} (hs : s.Subsingleton) (C r : ℝ≥0) (f : X → Y) :
    HolderOnWith C r f s :=
  hs.inductionOn (holderOnWith_empty C r f) (holderOnWith_singleton C r f)
#align set.subsingleton.holder_on_with Set.Subsingleton.holderOnWith

/- warning: holder_on_with_univ -> holderOnWith_univ is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, Iff (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f (Set.univ.{u1} X)) (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, Iff (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f (Set.univ.{u2} X)) (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f)
Case conversion may be inaccurate. Consider using '#align holder_on_with_univ holderOnWith_univₓ'. -/
theorem holderOnWith_univ {C r : ℝ≥0} {f : X → Y} : HolderOnWith C r f univ ↔ HolderWith C r f := by
  simp only [HolderOnWith, HolderWith, mem_univ, true_imp_iff]
#align holder_on_with_univ holderOnWith_univ

/- warning: holder_on_with_one -> holderOnWith_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {f : X -> Y} {s : Set.{u1} X}, Iff (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) f s) (LipschitzOnWith.{u1, u2} X Y _inst_1 _inst_2 C f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {f : X -> Y} {s : Set.{u2} X}, Iff (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) f s) (LipschitzOnWith.{u2, u1} X Y _inst_1 _inst_2 C f s)
Case conversion may be inaccurate. Consider using '#align holder_on_with_one holderOnWith_oneₓ'. -/
@[simp]
theorem holderOnWith_one {C : ℝ≥0} {f : X → Y} {s : Set X} :
    HolderOnWith C 1 f s ↔ LipschitzOnWith C f s := by
  simp only [HolderOnWith, LipschitzOnWith, NNReal.coe_one, ENNReal.rpow_one]
#align holder_on_with_one holderOnWith_one

/- warning: lipschitz_on_with.holder_on_with -> LipschitzOnWith.holderOnWith is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {f : X -> Y} {s : Set.{u1} X}, (LipschitzOnWith.{u1, u2} X Y _inst_1 _inst_2 C f s) -> (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {f : X -> Y} {s : Set.{u2} X}, (LipschitzOnWith.{u2, u1} X Y _inst_1 _inst_2 C f s) -> (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) f s)
Case conversion may be inaccurate. Consider using '#align lipschitz_on_with.holder_on_with LipschitzOnWith.holderOnWithₓ'. -/
alias holderOnWith_one ↔ _ LipschitzOnWith.holderOnWith
#align lipschitz_on_with.holder_on_with LipschitzOnWith.holderOnWith

/- warning: holder_with_one -> holderWith_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {f : X -> Y}, Iff (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) f) (LipschitzWith.{u1, u2} X Y _inst_1 _inst_2 C f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {f : X -> Y}, Iff (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) f) (LipschitzWith.{u2, u1} X Y _inst_1 _inst_2 C f)
Case conversion may be inaccurate. Consider using '#align holder_with_one holderWith_oneₓ'. -/
@[simp]
theorem holderWith_one {C : ℝ≥0} {f : X → Y} : HolderWith C 1 f ↔ LipschitzWith C f :=
  holderOnWith_univ.symm.trans <| holderOnWith_one.trans lipschitz_on_univ
#align holder_with_one holderWith_one

/- warning: lipschitz_with.holder_with -> LipschitzWith.holderWith is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {f : X -> Y}, (LipschitzWith.{u1, u2} X Y _inst_1 _inst_2 C f) -> (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {f : X -> Y}, (LipschitzWith.{u2, u1} X Y _inst_1 _inst_2 C f) -> (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) f)
Case conversion may be inaccurate. Consider using '#align lipschitz_with.holder_with LipschitzWith.holderWithₓ'. -/
alias holderWith_one ↔ _ LipschitzWith.holderWith
#align lipschitz_with.holder_with LipschitzWith.holderWith

#print holderWith_id /-
theorem holderWith_id : HolderWith 1 1 (id : X → X) :=
  LipschitzWith.id.HolderWith
#align holder_with_id holderWith_id
-/

/- warning: holder_with.holder_on_with -> HolderWith.holderOnWith is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f) -> (forall (s : Set.{u1} X), HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f) -> (forall (s : Set.{u2} X), HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s)
Case conversion may be inaccurate. Consider using '#align holder_with.holder_on_with HolderWith.holderOnWithₓ'. -/
protected theorem HolderWith.holderOnWith {C r : ℝ≥0} {f : X → Y} (h : HolderWith C r f)
    (s : Set X) : HolderOnWith C r f s := fun x _ y _ => h x y
#align holder_with.holder_on_with HolderWith.holderOnWith

namespace HolderOnWith

variable {C r : ℝ≥0} {f : X → Y} {s t : Set X}

/- warning: holder_on_with.edist_le -> HolderOnWith.edist_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (forall {x : X} {y : X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} Y (PseudoEMetricSpace.toHasEdist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (EDist.edist.{u1} X (PseudoEMetricSpace.toHasEdist.{u1} X _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (forall {x : X} {y : X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} Y (PseudoEMetricSpace.toEDist.{u1} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (EDist.edist.{u2} X (PseudoEMetricSpace.toEDist.{u2} X _inst_1) x y) (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.edist_le HolderOnWith.edist_leₓ'. -/
theorem edist_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ) :=
  h x hx y hy
#align holder_on_with.edist_le HolderOnWith.edist_le

/- warning: holder_on_with.edist_le_of_le -> HolderOnWith.edist_le_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (forall {x : X} {y : X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x s) -> (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) y s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} X (PseudoEMetricSpace.toHasEdist.{u1} X _inst_1) x y) d) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} Y (PseudoEMetricSpace.toHasEdist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (forall {x : X} {y : X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x s) -> (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) y s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} X (PseudoEMetricSpace.toEDist.{u2} X _inst_1) x y) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} Y (PseudoEMetricSpace.toEDist.{u1} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) d (NNReal.toReal r))))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.edist_le_of_le HolderOnWith.edist_le_of_leₓ'. -/
theorem edist_le_of_le (h : HolderOnWith C r f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) {d : ℝ≥0∞}
    (hd : edist x y ≤ d) : edist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  (h.edist_le hx hy).trans (mul_le_mul_left' (ENNReal.rpow_le_rpow hd r.coe_nonneg) _)
#align holder_on_with.edist_le_of_le HolderOnWith.edist_le_of_le

/- warning: holder_on_with.comp -> HolderOnWith.comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align holder_on_with.comp HolderOnWith.compₓ'. -/
theorem comp {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : ℝ≥0}
    {f : X → Y} (hf : HolderOnWith Cf rf f s) (hst : MapsTo f s t) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
  by
  intro x hx y hy
  rw [ENNReal.coe_mul, mul_comm rg, NNReal.coe_mul, ENNReal.rpow_mul, mul_assoc, ←
    ENNReal.coe_rpow_of_nonneg _ rg.coe_nonneg, ← ENNReal.mul_rpow_of_nonneg _ _ rg.coe_nonneg]
  exact hg.edist_le_of_le (hst hx) (hst hy) (hf.edist_le hx hy)
#align holder_on_with.comp HolderOnWith.comp

/- warning: holder_on_with.comp_holder_with -> HolderOnWith.comp_holderWith is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] [_inst_3 : PseudoEMetricSpace.{u3} Z] {Cg : NNReal} {rg : NNReal} {g : Y -> Z} {t : Set.{u2} Y}, (HolderOnWith.{u2, u3} Y Z _inst_2 _inst_3 Cg rg g t) -> (forall {Cf : NNReal} {rf : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 Cf rf f) -> (forall (x : X), Membership.Mem.{u2, u2} Y (Set.{u2} Y) (Set.hasMem.{u2} Y) (f x) t) -> (HolderWith.{u1, u3} X Z _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) Cg (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) Cf ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) rg))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) rg rf) (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f)))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u3} Y] [_inst_3 : PseudoEMetricSpace.{u2} Z] {Cg : NNReal} {rg : NNReal} {g : Y -> Z} {t : Set.{u3} Y}, (HolderOnWith.{u3, u2} Y Z _inst_2 _inst_3 Cg rg g t) -> (forall {Cf : NNReal} {rf : NNReal} {f : X -> Y}, (HolderWith.{u1, u3} X Y _inst_1 _inst_2 Cf rf f) -> (forall (x : X), Membership.mem.{u3, u3} Y (Set.{u3} Y) (Set.instMembershipSet.{u3} Y) (f x) t) -> (HolderWith.{u1, u2} X Z _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) Cg (NNReal.rpow Cf (NNReal.toReal rg))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) rg rf) (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f)))
Case conversion may be inaccurate. Consider using '#align holder_on_with.comp_holder_with HolderOnWith.comp_holderWithₓ'. -/
theorem comp_holderWith {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t)
    {Cf rf : ℝ≥0} {f : X → Y} (hf : HolderWith Cf rf f) (ht : ∀ x, f x ∈ t) :
    HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  holderOnWith_univ.mp <| hg.comp (hf.HolderOnWith univ) fun x _ => ht x
#align holder_on_with.comp_holder_with HolderOnWith.comp_holderWith

/- warning: holder_on_with.uniform_continuous_on -> HolderOnWith.uniformContinuousOn is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r) -> (UniformContinuousOn.{u1, u2} X Y (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} Y _inst_2) f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r) -> (UniformContinuousOn.{u2, u1} X Y (PseudoEMetricSpace.toUniformSpace.{u2} X _inst_1) (PseudoEMetricSpace.toUniformSpace.{u1} Y _inst_2) f s)
Case conversion may be inaccurate. Consider using '#align holder_on_with.uniform_continuous_on HolderOnWith.uniformContinuousOnₓ'. -/
/-- A Hölder continuous function is uniformly continuous -/
protected theorem uniformContinuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) :
    UniformContinuousOn f s :=
  by
  refine' EMetric.uniformContinuousOn_iff.2 fun ε εpos => _
  have : tendsto (fun d : ℝ≥0∞ => (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top h0
  rcases ennreal.nhds_zero_basis.mem_iff.1 (this (gt_mem_nhds εpos)) with ⟨δ, δ0, H⟩
  exact ⟨δ, δ0, fun x hx y hy h => (hf.edist_le hx hy).trans_lt (H h)⟩
#align holder_on_with.uniform_continuous_on HolderOnWith.uniformContinuousOn

/- warning: holder_on_with.continuous_on -> HolderOnWith.continuousOn is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r) -> (ContinuousOn.{u1, u2} X Y (UniformSpace.toTopologicalSpace.{u1} X (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1)) (UniformSpace.toTopologicalSpace.{u2} Y (PseudoEMetricSpace.toUniformSpace.{u2} Y _inst_2)) f s)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r) -> (ContinuousOn.{u2, u1} X Y (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X _inst_1)) (UniformSpace.toTopologicalSpace.{u1} Y (PseudoEMetricSpace.toUniformSpace.{u1} Y _inst_2)) f s)
Case conversion may be inaccurate. Consider using '#align holder_on_with.continuous_on HolderOnWith.continuousOnₓ'. -/
protected theorem continuousOn (hf : HolderOnWith C r f s) (h0 : 0 < r) : ContinuousOn f s :=
  (hf.UniformContinuousOn h0).ContinuousOn
#align holder_on_with.continuous_on HolderOnWith.continuousOn

/- warning: holder_on_with.mono -> HolderOnWith.mono is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X} {t : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) t s) -> (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f t)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X} {t : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) t s) -> (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f t)
Case conversion may be inaccurate. Consider using '#align holder_on_with.mono HolderOnWith.monoₓ'. -/
protected theorem mono (hf : HolderOnWith C r f s) (ht : t ⊆ s) : HolderOnWith C r f t :=
  fun x hx y hy => hf.edist_le (ht hx) (ht hy)
#align holder_on_with.mono HolderOnWith.mono

/- warning: holder_on_with.ediam_image_le_of_le -> HolderOnWith.ediam_image_le_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} X _inst_1 s) d) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u2} X _inst_1 s) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) d (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.ediam_image_le_of_le HolderOnWith.ediam_image_le_of_leₓ'. -/
theorem ediam_image_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞} (hd : EMetric.diam s ≤ d) :
    EMetric.diam (f '' s) ≤ C * d ^ (r : ℝ) :=
  EMetric.diam_image_le_iff.2 fun x hx y hy =>
    hf.edist_le_of_le hx hy <| (EMetric.edist_le_diam_of_mem hx hy).trans hd
#align holder_on_with.ediam_image_le_of_le HolderOnWith.ediam_image_le_of_le

/- warning: holder_on_with.ediam_image_le -> HolderOnWith.ediam_image_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (EMetric.diam.{u1} X _inst_1 s) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (EMetric.diam.{u2} X _inst_1 s) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.ediam_image_le HolderOnWith.ediam_image_leₓ'. -/
theorem ediam_image_le (hf : HolderOnWith C r f s) :
    EMetric.diam (f '' s) ≤ C * EMetric.diam s ^ (r : ℝ) :=
  hf.ediam_image_le_of_le le_rfl
#align holder_on_with.ediam_image_le HolderOnWith.ediam_image_le

/- warning: holder_on_with.ediam_image_le_of_subset -> HolderOnWith.ediam_image_le_of_subset is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X} {t : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) t s) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f t)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (EMetric.diam.{u1} X _inst_1 t) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X} {t : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) t s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f t)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (EMetric.diam.{u2} X _inst_1 t) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.ediam_image_le_of_subset HolderOnWith.ediam_image_le_of_subsetₓ'. -/
theorem ediam_image_le_of_subset (hf : HolderOnWith C r f s) (ht : t ⊆ s) :
    EMetric.diam (f '' t) ≤ C * EMetric.diam t ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le
#align holder_on_with.ediam_image_le_of_subset HolderOnWith.ediam_image_le_of_subset

/- warning: holder_on_with.ediam_image_le_of_subset_of_le -> HolderOnWith.ediam_image_le_of_subset_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X} {t : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (HasSubset.Subset.{u1} (Set.{u1} X) (Set.hasSubset.{u1} X) t s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} X _inst_1 t) d) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f t)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X} {t : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) t s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u2} X _inst_1 t) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f t)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) d (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.ediam_image_le_of_subset_of_le HolderOnWith.ediam_image_le_of_subset_of_leₓ'. -/
theorem ediam_image_le_of_subset_of_le (hf : HolderOnWith C r f s) (ht : t ⊆ s) {d : ℝ≥0∞}
    (hd : EMetric.diam t ≤ d) : EMetric.diam (f '' t) ≤ C * d ^ (r : ℝ) :=
  (hf.mono ht).ediam_image_le_of_le hd
#align holder_on_with.ediam_image_le_of_subset_of_le HolderOnWith.ediam_image_le_of_subset_of_le

/- warning: holder_on_with.ediam_image_inter_le_of_le -> HolderOnWith.ediam_image_inter_le_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X} {t : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} X _inst_1 t) d) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f (Inter.inter.{u1} (Set.{u1} X) (Set.hasInter.{u1} X) t s))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X} {t : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (forall {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u2} X _inst_1 t) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f (Inter.inter.{u2} (Set.{u2} X) (Set.instInterSet.{u2} X) t s))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) d (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.ediam_image_inter_le_of_le HolderOnWith.ediam_image_inter_le_of_leₓ'. -/
theorem ediam_image_inter_le_of_le (hf : HolderOnWith C r f s) {d : ℝ≥0∞}
    (hd : EMetric.diam t ≤ d) : EMetric.diam (f '' (t ∩ s)) ≤ C * d ^ (r : ℝ) :=
  hf.ediam_image_le_of_subset_of_le (inter_subset_right _ _) <|
    (EMetric.diam_mono <| inter_subset_left _ _).trans hd
#align holder_on_with.ediam_image_inter_le_of_le HolderOnWith.ediam_image_inter_le_of_le

/- warning: holder_on_with.ediam_image_inter_le -> HolderOnWith.ediam_image_inter_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 C r f s) -> (forall (t : Set.{u1} X), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f (Inter.inter.{u1} (Set.{u1} X) (Set.hasInter.{u1} X) t s))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (EMetric.diam.{u1} X _inst_1 t) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y} {s : Set.{u2} X}, (HolderOnWith.{u2, u1} X Y _inst_1 _inst_2 C r f s) -> (forall (t : Set.{u2} X), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f (Inter.inter.{u2} (Set.{u2} X) (Set.instInterSet.{u2} X) t s))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (EMetric.diam.{u2} X _inst_1 t) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_on_with.ediam_image_inter_le HolderOnWith.ediam_image_inter_leₓ'. -/
theorem ediam_image_inter_le (hf : HolderOnWith C r f s) (t : Set X) :
    EMetric.diam (f '' (t ∩ s)) ≤ C * EMetric.diam t ^ (r : ℝ) :=
  hf.ediam_image_inter_le_of_le le_rfl
#align holder_on_with.ediam_image_inter_le HolderOnWith.ediam_image_inter_le

end HolderOnWith

namespace HolderWith

variable {C r : ℝ≥0} {f : X → Y}

/- warning: holder_with.edist_le -> HolderWith.edist_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f) -> (forall (x : X) (y : X), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} Y (PseudoEMetricSpace.toHasEdist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (EDist.edist.{u1} X (PseudoEMetricSpace.toHasEdist.{u1} X _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f) -> (forall (x : X) (y : X), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} Y (PseudoEMetricSpace.toEDist.{u1} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (EDist.edist.{u2} X (PseudoEMetricSpace.toEDist.{u2} X _inst_1) x y) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_with.edist_le HolderWith.edist_leₓ'. -/
theorem edist_le (h : HolderWith C r f) (x y : X) : edist (f x) (f y) ≤ C * edist x y ^ (r : ℝ) :=
  h x y
#align holder_with.edist_le HolderWith.edist_le

/- warning: holder_with.edist_le_of_le -> HolderWith.edist_le_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f) -> (forall {x : X} {y : X} {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} X (PseudoEMetricSpace.toHasEdist.{u1} X _inst_1) x y) d) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} Y (PseudoEMetricSpace.toHasEdist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f) -> (forall {x : X} {y : X} {d : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} X (PseudoEMetricSpace.toEDist.{u2} X _inst_1) x y) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} Y (PseudoEMetricSpace.toEDist.{u1} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) d (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_with.edist_le_of_le HolderWith.edist_le_of_leₓ'. -/
theorem edist_le_of_le (h : HolderWith C r f) {x y : X} {d : ℝ≥0∞} (hd : edist x y ≤ d) :
    edist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  (h.HolderOnWith univ).edist_le_of_le trivial trivial hd
#align holder_with.edist_le_of_le HolderWith.edist_le_of_le

/- warning: holder_with.comp -> HolderWith.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] [_inst_3 : PseudoEMetricSpace.{u3} Z] {Cg : NNReal} {rg : NNReal} {g : Y -> Z}, (HolderWith.{u2, u3} Y Z _inst_2 _inst_3 Cg rg g) -> (forall {Cf : NNReal} {rf : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 Cf rf f) -> (HolderWith.{u1, u3} X Z _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) Cg (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) Cf ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) rg))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) rg rf) (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f)))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u3} Y] [_inst_3 : PseudoEMetricSpace.{u2} Z] {Cg : NNReal} {rg : NNReal} {g : Y -> Z}, (HolderWith.{u3, u2} Y Z _inst_2 _inst_3 Cg rg g) -> (forall {Cf : NNReal} {rf : NNReal} {f : X -> Y}, (HolderWith.{u1, u3} X Y _inst_1 _inst_2 Cf rf f) -> (HolderWith.{u1, u2} X Z _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) Cg (NNReal.rpow Cf (NNReal.toReal rg))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) rg rf) (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f)))
Case conversion may be inaccurate. Consider using '#align holder_with.comp HolderWith.compₓ'. -/
theorem comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0} {f : X → Y}
    (hf : HolderWith Cf rf f) : HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  (hg.HolderOnWith univ).comp_holderWith hf fun _ => trivial
#align holder_with.comp HolderWith.comp

/- warning: holder_with.comp_holder_on_with -> HolderWith.comp_holderOnWith is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] [_inst_3 : PseudoEMetricSpace.{u3} Z] {Cg : NNReal} {rg : NNReal} {g : Y -> Z}, (HolderWith.{u2, u3} Y Z _inst_2 _inst_3 Cg rg g) -> (forall {Cf : NNReal} {rf : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u2} X Y _inst_1 _inst_2 Cf rf f s) -> (HolderOnWith.{u1, u3} X Z _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) Cg (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) Cf ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) rg))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) rg rf) (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f) s))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u3} Y] [_inst_3 : PseudoEMetricSpace.{u2} Z] {Cg : NNReal} {rg : NNReal} {g : Y -> Z}, (HolderWith.{u3, u2} Y Z _inst_2 _inst_3 Cg rg g) -> (forall {Cf : NNReal} {rf : NNReal} {f : X -> Y} {s : Set.{u1} X}, (HolderOnWith.{u1, u3} X Y _inst_1 _inst_2 Cf rf f s) -> (HolderOnWith.{u1, u2} X Z _inst_1 _inst_3 (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) Cg (NNReal.rpow Cf (NNReal.toReal rg))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) rg rf) (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f) s))
Case conversion may be inaccurate. Consider using '#align holder_with.comp_holder_on_with HolderWith.comp_holderOnWithₓ'. -/
theorem comp_holderOnWith {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0}
    {f : X → Y} {s : Set X} (hf : HolderOnWith Cf rf f s) :
    HolderOnWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) s :=
  (hg.HolderOnWith univ).comp hf fun _ _ => trivial
#align holder_with.comp_holder_on_with HolderWith.comp_holderOnWith

/- warning: holder_with.uniform_continuous -> HolderWith.uniformContinuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r) -> (UniformContinuous.{u1, u2} X Y (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} Y _inst_2) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r) -> (UniformContinuous.{u2, u1} X Y (PseudoEMetricSpace.toUniformSpace.{u2} X _inst_1) (PseudoEMetricSpace.toUniformSpace.{u1} Y _inst_2) f)
Case conversion may be inaccurate. Consider using '#align holder_with.uniform_continuous HolderWith.uniformContinuousₓ'. -/
/-- A Hölder continuous function is uniformly continuous -/
protected theorem uniformContinuous (hf : HolderWith C r f) (h0 : 0 < r) : UniformContinuous f :=
  uniformContinuousOn_univ.mp <| (hf.HolderOnWith univ).UniformContinuousOn h0
#align holder_with.uniform_continuous HolderWith.uniformContinuous

/- warning: holder_with.continuous -> HolderWith.continuous is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f) -> (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r) -> (Continuous.{u1, u2} X Y (UniformSpace.toTopologicalSpace.{u1} X (PseudoEMetricSpace.toUniformSpace.{u1} X _inst_1)) (UniformSpace.toTopologicalSpace.{u2} Y (PseudoEMetricSpace.toUniformSpace.{u2} Y _inst_2)) f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r) -> (Continuous.{u2, u1} X Y (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X _inst_1)) (UniformSpace.toTopologicalSpace.{u1} Y (PseudoEMetricSpace.toUniformSpace.{u1} Y _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align holder_with.continuous HolderWith.continuousₓ'. -/
protected theorem continuous (hf : HolderWith C r f) (h0 : 0 < r) : Continuous f :=
  (hf.UniformContinuous h0).Continuous
#align holder_with.continuous HolderWith.continuous

/- warning: holder_with.ediam_image_le -> HolderWith.ediam_image_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} X] [_inst_2 : PseudoEMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y _inst_1 _inst_2 C r f) -> (forall (s : Set.{u1} X), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} Y _inst_2 (Set.image.{u1, u2} X Y f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.Real.hasPow) (EMetric.diam.{u1} X _inst_1 s) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : PseudoEMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y _inst_1 _inst_2 C r f) -> (forall (s : Set.{u2} X), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} Y _inst_2 (Set.image.{u2, u1} X Y f s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (HPow.hPow.{0, 0, 0} ENNReal Real ENNReal (instHPow.{0, 0} ENNReal Real ENNReal.instPowENNRealReal) (EMetric.diam.{u2} X _inst_1 s) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_with.ediam_image_le HolderWith.ediam_image_leₓ'. -/
theorem ediam_image_le (hf : HolderWith C r f) (s : Set X) :
    EMetric.diam (f '' s) ≤ C * EMetric.diam s ^ (r : ℝ) :=
  EMetric.diam_image_le_iff.2 fun x hx y hy =>
    hf.edist_le_of_le <| EMetric.edist_le_diam_of_mem hx hy
#align holder_with.ediam_image_le HolderWith.ediam_image_le

end HolderWith

end Emetric

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] {C r : ℝ≥0} {f : X → Y}

namespace HolderWith

/- warning: holder_with.nndist_le_of_le -> HolderWith.nndist_le_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} X] [_inst_2 : PseudoMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u1} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} Y _inst_2) C r f) -> (forall {x : X} {y : X} {d : NNReal}, (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} X (PseudoMetricSpace.toNNDist.{u1} X _inst_1) x y) d) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u2} Y (PseudoMetricSpace.toNNDist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) C (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : PseudoMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} Y _inst_2) C r f) -> (forall {x : X} {y : X} {d : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u2} X (PseudoMetricSpace.toNNDist.{u2} X _inst_1) x y) d) -> (LE.le.{0} Real Real.instLEReal (NNReal.toReal (NNDist.nndist.{u1} Y (PseudoMetricSpace.toNNDist.{u1} Y _inst_2) (f x) (f y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal C) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (NNReal.toReal d) (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_with.nndist_le_of_le HolderWith.nndist_le_of_leₓ'. -/
theorem nndist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ≥0} (hd : nndist x y ≤ d) :
    nndist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  by
  rw [← ENNReal.coe_le_coe, ← edist_nndist, ENNReal.coe_mul, ←
    ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg]
  apply hf.edist_le_of_le
  rwa [edist_nndist, ENNReal.coe_le_coe]
#align holder_with.nndist_le_of_le HolderWith.nndist_le_of_le

/- warning: holder_with.nndist_le -> HolderWith.nndist_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} X] [_inst_2 : PseudoMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u1} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} Y _inst_2) C r f) -> (forall (x : X) (y : X), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u2} Y (PseudoMetricSpace.toNNDist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) C (HPow.hPow.{0, 0, 0} NNReal Real NNReal (instHPow.{0, 0} NNReal Real NNReal.Real.hasPow) (NNDist.nndist.{u1} X (PseudoMetricSpace.toNNDist.{u1} X _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : PseudoMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} Y _inst_2) C r f) -> (forall (x : X) (y : X), LE.le.{0} Real Real.instLEReal (NNReal.toReal (NNDist.nndist.{u1} Y (PseudoMetricSpace.toNNDist.{u1} Y _inst_2) (f x) (f y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal C) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (NNReal.toReal (NNDist.nndist.{u2} X (PseudoMetricSpace.toNNDist.{u2} X _inst_1) x y)) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_with.nndist_le HolderWith.nndist_leₓ'. -/
theorem nndist_le (hf : HolderWith C r f) (x y : X) :
    nndist (f x) (f y) ≤ C * nndist x y ^ (r : ℝ) :=
  hf.nndist_le_of_le le_rfl
#align holder_with.nndist_le HolderWith.nndist_le

/- warning: holder_with.dist_le_of_le -> HolderWith.dist_le_of_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} X] [_inst_2 : PseudoMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u1} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} Y _inst_2) C r f) -> (forall {x : X} {y : X} {d : Real}, (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} X (PseudoMetricSpace.toHasDist.{u1} X _inst_1) x y) d) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u2} Y (PseudoMetricSpace.toHasDist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) C) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) d ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : PseudoMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} Y _inst_2) C r f) -> (forall {x : X} {y : X} {d : Real}, (LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} X (PseudoMetricSpace.toDist.{u2} X _inst_1) x y) d) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} Y (PseudoMetricSpace.toDist.{u1} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal C) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) d (NNReal.toReal r)))))
Case conversion may be inaccurate. Consider using '#align holder_with.dist_le_of_le HolderWith.dist_le_of_leₓ'. -/
theorem dist_le_of_le (hf : HolderWith C r f) {x y : X} {d : ℝ} (hd : dist x y ≤ d) :
    dist (f x) (f y) ≤ C * d ^ (r : ℝ) :=
  by
  lift d to ℝ≥0 using dist_nonneg.trans hd
  rw [dist_nndist] at hd⊢
  norm_cast  at hd⊢
  exact hf.nndist_le_of_le hd
#align holder_with.dist_le_of_le HolderWith.dist_le_of_le

/- warning: holder_with.dist_le -> HolderWith.dist_le is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} X] [_inst_2 : PseudoMetricSpace.{u2} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u1, u2} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u1} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} Y _inst_2) C r f) -> (forall (x : X) (y : X), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} Y (PseudoMetricSpace.toHasDist.{u2} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) C) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) (Dist.dist.{u1} X (PseudoMetricSpace.toHasDist.{u1} X _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : PseudoMetricSpace.{u1} Y] {C : NNReal} {r : NNReal} {f : X -> Y}, (HolderWith.{u2, u1} X Y (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} Y _inst_2) C r f) -> (forall (x : X) (y : X), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} Y (PseudoMetricSpace.toDist.{u1} Y _inst_2) (f x) (f y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal C) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) (Dist.dist.{u2} X (PseudoMetricSpace.toDist.{u2} X _inst_1) x y) (NNReal.toReal r))))
Case conversion may be inaccurate. Consider using '#align holder_with.dist_le HolderWith.dist_leₓ'. -/
theorem dist_le (hf : HolderWith C r f) (x y : X) : dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ) :=
  hf.dist_le_of_le le_rfl
#align holder_with.dist_le HolderWith.dist_le

end HolderWith

end Metric

