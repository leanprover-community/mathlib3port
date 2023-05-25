/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.additive
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Partition.Split
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# Box additive functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a function `f : box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : with_top (box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' in π.boxes, f J'`. We use `I₀ : with_top (box ι)` instead of `I₀ : box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

### Tags

rectangular box, additive function
-/


noncomputable section

open Classical BigOperators

open Function Set

namespace BoxIntegral

variable {ι M : Type _} {n : ℕ}

#print BoxIntegral.BoxAdditiveMap /-
/-- A function on `box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji in π.boxes, f Ji`. A function is called box additive on subboxes of `I : box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the same definition
using `I : with_bot (box ι)`: the value `I = ⊤` corresponds to functions box additive on the whole
space.  -/
structure BoxAdditiveMap (ι M : Type _) [AddCommMonoid M] (I : WithTop (Box ι)) where
  toFun : Box ι → M
  sum_partition_boxes' :
    ∀ J : Box ι,
      ↑J ≤ I → ∀ π : Prepartition J, π.IsPartition → (∑ Ji in π.boxes, to_fun Ji) = to_fun J
#align box_integral.box_additive_map BoxIntegral.BoxAdditiveMap
-/

-- mathport name: box_integral.box_additive_map.top
scoped notation:25 ι " →ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤

-- mathport name: box_integral.box_additive_map
scoped notation:25 ι " →ᵇᵃ[" I "] " M => BoxIntegral.BoxAdditiveMap ι M I

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type _} [AddCommMonoid M] [AddCommMonoid N] {I₀ : WithTop (Box ι)} {I J : Box ι}
  {i : ι}

instance : CoeFun (ι →ᵇᵃ[I₀] M) fun _ => Box ι → M :=
  ⟨toFun⟩

initialize_simps_projections box_integral.box_additive_map (toFun → apply)

/- warning: box_integral.box_additive_map.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: box_integral.box_additive_map.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} (f : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀), Eq.{max (succ u1) (succ u2)} ((BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.toFun.{u1, u2} ι M _inst_1 I₀ f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f)
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}}, (Nat -> ι -> M) -> Nat -> (List.{u1} ι) -> (List.{u2} M)
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (f : ι →ᵇᵃ[I₀] M) : f.toFun = f :=
  rfl
#align box_integral.box_additive_map.to_fun_eq_coe [anonymous]

/- warning: box_integral.box_additive_map.coe_mk -> BoxIntegral.BoxAdditiveMap.coe_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} (f : (BoxIntegral.Box.{u1} ι) -> M) (h : forall (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) J) I₀) -> (forall (π : BoxIntegral.Prepartition.{u1} ι J), (BoxIntegral.Prepartition.IsPartition.{u1} ι J π) -> (Eq.{succ u2} M (Finset.sum.{u2, u1} M (BoxIntegral.Box.{u1} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u1} ι J π) (fun (Ji : BoxIntegral.Box.{u1} ι) => f Ji)) (f J)))), Eq.{max (succ u1) (succ u2)} ((BoxIntegral.Box.{u1} ι) -> M) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) (BoxIntegral.BoxAdditiveMap.mk.{u1, u2} ι M _inst_1 I₀ f h)) f
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} M] {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)} (f : (BoxIntegral.Box.{u2} ι) -> M) (h : forall (J : BoxIntegral.Box.{u2} ι), (LE.le.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (Preorder.toLE.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (WithTop.preorder.{u2} (BoxIntegral.Box.{u2} ι) (PartialOrder.toPreorder.{u2} (BoxIntegral.Box.{u2} ι) (BoxIntegral.Box.instPartialOrderBox.{u2} ι)))) (WithTop.some.{u2} (BoxIntegral.Box.{u2} ι) J) I₀) -> (forall (π : BoxIntegral.Prepartition.{u2} ι J), (BoxIntegral.Prepartition.IsPartition.{u2} ι J π) -> (Eq.{succ u1} M (Finset.sum.{u1, u2} M (BoxIntegral.Box.{u2} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u2} ι J π) (fun (Ji : BoxIntegral.Box.{u2} ι) => f Ji)) (f J)))), Eq.{max (succ u2) (succ u1)} ((BoxIntegral.Box.{u2} ι) -> M) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ (BoxIntegral.BoxAdditiveMap.mk.{u2, u1} ι M _inst_1 I₀ f h)) f
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.coe_mk BoxIntegral.BoxAdditiveMap.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f h) : ⇑(mk f h : ι →ᵇᵃ[I₀] M) = f :=
  rfl
#align box_integral.box_additive_map.coe_mk BoxIntegral.BoxAdditiveMap.coe_mk

/- warning: box_integral.box_additive_map.coe_injective -> BoxIntegral.BoxAdditiveMap.coe_injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)}, Function.Injective.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) ((BoxIntegral.Box.{u1} ι) -> M) (fun (f : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (x : BoxIntegral.Box.{u1} ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f x)
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} M] {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀) ((BoxIntegral.Box.{u2} ι) -> M) (fun (f : BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀) (x : BoxIntegral.Box.{u2} ι) => BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f x)
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.coe_injective BoxIntegral.BoxAdditiveMap.coe_injectiveₓ'. -/
theorem coe_injective : Injective fun (f : ι →ᵇᵃ[I₀] M) x => f x :=
  by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g)
  rfl
#align box_integral.box_additive_map.coe_injective BoxIntegral.BoxAdditiveMap.coe_injective

/- warning: box_integral.box_additive_map.coe_inj -> BoxIntegral.BoxAdditiveMap.coe_inj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} {f : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀} {g : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀}, Iff (Eq.{max (succ u1) (succ u2)} ((fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) g)) (Eq.{max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) f g)
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} M] {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)} {f : BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀} {g : BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀}, Iff (Eq.{max (succ u2) (succ u1)} ((BoxIntegral.Box.{u2} ι) -> M) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ g)) (Eq.{max (succ u2) (succ u1)} (BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀) f g)
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.coe_inj BoxIntegral.BoxAdditiveMap.coe_injₓ'. -/
@[simp]
theorem coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : Box ι → M) = g ↔ f = g :=
  coe_injective.eq_iff
#align box_integral.box_additive_map.coe_inj BoxIntegral.BoxAdditiveMap.coe_inj

/- warning: box_integral.box_additive_map.sum_partition_boxes -> BoxIntegral.BoxAdditiveMap.sum_partition_boxes is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} {I : BoxIntegral.Box.{u1} ι} (f : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I) I₀) -> (forall {π : BoxIntegral.Prepartition.{u1} ι I}, (BoxIntegral.Prepartition.IsPartition.{u1} ι I π) -> (Eq.{succ u2} M (Finset.sum.{u2, u1} M (BoxIntegral.Box.{u1} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u1} ι I π) (fun (J : BoxIntegral.Box.{u1} ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f J)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f I)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} M] {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)} {I : BoxIntegral.Box.{u2} ι} (f : BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀), (LE.le.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (Preorder.toLE.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (WithTop.preorder.{u2} (BoxIntegral.Box.{u2} ι) (PartialOrder.toPreorder.{u2} (BoxIntegral.Box.{u2} ι) (BoxIntegral.Box.instPartialOrderBox.{u2} ι)))) (WithTop.some.{u2} (BoxIntegral.Box.{u2} ι) I) I₀) -> (forall {π : BoxIntegral.Prepartition.{u2} ι I}, (BoxIntegral.Prepartition.IsPartition.{u2} ι I π) -> (Eq.{succ u1} M (Finset.sum.{u1, u2} M (BoxIntegral.Box.{u2} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u2} ι I π) (fun (J : BoxIntegral.Box.{u2} ι) => BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f J)) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f I)))
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.sum_partition_boxes BoxIntegral.BoxAdditiveMap.sum_partition_boxesₓ'. -/
theorem sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π : Prepartition I}
    (h : π.IsPartition) : (∑ J in π.boxes, f J) = f I :=
  f.sum_partition_boxes' I hI π h
#align box_integral.box_additive_map.sum_partition_boxes BoxIntegral.BoxAdditiveMap.sum_partition_boxes

@[simps (config := { fullyApplied := false })]
instance : Zero (ι →ᵇᵃ[I₀] M) :=
  ⟨⟨0, fun I hI π hπ => sum_const_zero⟩⟩

instance : Inhabited (ι →ᵇᵃ[I₀] M) :=
  ⟨0⟩

instance : Add (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance {R} [Monoid R] [DistribMulAction R M] : SMul R (ι →ᵇᵃ[I₀] M) :=
  ⟨fun r f =>
    ⟨r • f, fun I hI π hπ => by simp only [Pi.smul_apply, ← smul_sum, sum_partition_boxes _ hI hπ]⟩⟩

instance : AddCommMonoid (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

/- warning: box_integral.box_additive_map.map_split_add -> BoxIntegral.BoxAdditiveMap.map_split_add is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} {I : BoxIntegral.Box.{u1} ι} (f : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I) I₀) -> (forall (i : ι) (x : Real), Eq.{succ u2} M (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f) (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f) (BoxIntegral.Box.splitUpper.{u1} ι I i x))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f I))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} M] {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)} {I : BoxIntegral.Box.{u2} ι} (f : BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀), (LE.le.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (Preorder.toLE.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (WithTop.preorder.{u2} (BoxIntegral.Box.{u2} ι) (PartialOrder.toPreorder.{u2} (BoxIntegral.Box.{u2} ι) (BoxIntegral.Box.instPartialOrderBox.{u2} ι)))) (WithTop.some.{u2} (BoxIntegral.Box.{u2} ι) I) I₀) -> (forall (i : ι) (x : Real), Eq.{succ u1} M (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1)))) (Option.elim'.{u2, u1} (BoxIntegral.Box.{u2} ι) M (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1)))) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f) (BoxIntegral.Box.splitLower.{u2} ι I i x)) (Option.elim'.{u2, u1} (BoxIntegral.Box.{u2} ι) M (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1)))) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f) (BoxIntegral.Box.splitUpper.{u2} ι I i x))) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f I))
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.map_split_add BoxIntegral.BoxAdditiveMap.map_split_addₓ'. -/
@[simp]
theorem map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) (i : ι) (x : ℝ) :
    (I.splitLower i x).elim 0 f + (I.splitUpper i x).elim 0 f = f I := by
  rw [← f.sum_partition_boxes hI (is_partition_split I i x), sum_split_boxes]
#align box_integral.box_additive_map.map_split_add BoxIntegral.BoxAdditiveMap.map_split_add

/- warning: box_integral.box_additive_map.restrict -> BoxIntegral.BoxAdditiveMap.restrict is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)}, (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) -> (forall (I : WithTop.{u1} (BoxIntegral.Box.{u1} ι)), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) I I₀) -> (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)}, (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) -> (forall (I : WithTop.{u1} (BoxIntegral.Box.{u1} ι)), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toLE.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) I I₀) -> (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I))
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.restrict BoxIntegral.BoxAdditiveMap.restrictₓ'. -/
/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps]
def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩
#align box_integral.box_additive_map.restrict BoxIntegral.BoxAdditiveMap.restrict

/- warning: box_integral.box_additive_map.of_map_split_add -> BoxIntegral.BoxAdditiveMap.ofMapSplitAdd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_3 : Fintype.{u1} ι] (f : (BoxIntegral.Box.{u1} ι) -> M) (I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)), (forall (I : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I) I₀) -> (forall {i : ι} {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioo.{0} Real Real.preorder (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i))) -> (Eq.{succ u2} M (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))))) f (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))))) f (BoxIntegral.Box.splitUpper.{u1} ι I i x))) (f I)))) -> (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀)
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_3 : Fintype.{u1} ι] (f : (BoxIntegral.Box.{u1} ι) -> M) (I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)), (forall (I : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toLE.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) (WithTop.some.{u1} (BoxIntegral.Box.{u1} ι) I) I₀) -> (forall {i : ι} {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioo.{0} Real Real.instPreorderReal (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i))) -> (Eq.{succ u2} M (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) f (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) f (BoxIntegral.Box.splitUpper.{u1} ι I i x))) (f I)))) -> (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀)
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.of_map_split_add BoxIntegral.BoxAdditiveMap.ofMapSplitAddₓ'. -/
/-- If `f : box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
def ofMapSplitAdd [Fintype ι] (f : Box ι → M) (I₀ : WithTop (Box ι))
    (hf :
      ∀ I : Box ι,
        ↑I ≤ I₀ →
          ∀ {i x},
            x ∈ Ioo (I.lower i) (I.upper i) →
              (I.splitLower i x).elim 0 f + (I.splitUpper i x).elim 0 f = f I) :
    ι →ᵇᵃ[I₀] M := by
  refine' ⟨f, _⟩
  replace hf : ∀ I : box ι, ↑I ≤ I₀ → ∀ s, (∑ J in (split_many I s).boxes, f J) = f I
  · intro I hI s
    induction' s using Finset.induction_on with a s ha ihs
    · simp
    rw [split_many_insert, inf_split, ← ihs, bUnion_boxes, sum_bUnion_boxes]
    refine' Finset.sum_congr rfl fun J' hJ' => _
    by_cases h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1)
    · rw [sum_split_boxes]
      exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
    · rw [split_of_not_mem_Ioo h, top_boxes, Finset.sum_singleton]
  intro I hI π hπ
  have Hle : ∀ J ∈ π, ↑J ≤ I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  rcases hπ.exists_split_many_le with ⟨s, hs⟩
  rw [← hf _ hI, ← inf_of_le_right hs, inf_split_many, bUnion_boxes, sum_bUnion_boxes]
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm
#align box_integral.box_additive_map.of_map_split_add BoxIntegral.BoxAdditiveMap.ofMapSplitAdd

#print BoxIntegral.BoxAdditiveMap.map /-
/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps (config := { fullyApplied := false })]
def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) : ι →ᵇᵃ[I₀] N
    where
  toFun := g ∘ f
  sum_partition_boxes' I hI π hπ := by rw [← g.map_sum, f.sum_partition_boxes hI hπ]
#align box_integral.box_additive_map.map BoxIntegral.BoxAdditiveMap.map
-/

/- warning: box_integral.box_additive_map.sum_boxes_congr -> BoxIntegral.BoxAdditiveMap.sum_boxes_congr is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} {I : BoxIntegral.Box.{u1} ι} [_inst_3 : Finite.{succ u1} ι] (f : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀), (LE.le.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithTop.{u1} (BoxIntegral.Box.{u1} ι)) (WithTop.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I) I₀) -> (forall {π₁ : BoxIntegral.Prepartition.{u1} ι I} {π₂ : BoxIntegral.Prepartition.{u1} ι I}, (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₁) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂)) -> (Eq.{succ u2} M (Finset.sum.{u2, u1} M (BoxIntegral.Box.{u1} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u1} ι I π₁) (fun (J : BoxIntegral.Box.{u1} ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f J)) (Finset.sum.{u2, u1} M (BoxIntegral.Box.{u1} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u1} ι I π₂) (fun (J : BoxIntegral.Box.{u1} ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι M _inst_1 I₀) => (BoxIntegral.Box.{u1} ι) -> M) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι M _inst_1 I₀) f J))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} M] {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)} {I : BoxIntegral.Box.{u2} ι} [_inst_3 : Finite.{succ u2} ι] (f : BoxIntegral.BoxAdditiveMap.{u2, u1} ι M _inst_1 I₀), (LE.le.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (Preorder.toLE.{u2} (WithTop.{u2} (BoxIntegral.Box.{u2} ι)) (WithTop.preorder.{u2} (BoxIntegral.Box.{u2} ι) (PartialOrder.toPreorder.{u2} (BoxIntegral.Box.{u2} ι) (BoxIntegral.Box.instPartialOrderBox.{u2} ι)))) (WithTop.some.{u2} (BoxIntegral.Box.{u2} ι) I) I₀) -> (forall {π₁ : BoxIntegral.Prepartition.{u2} ι I} {π₂ : BoxIntegral.Prepartition.{u2} ι I}, (Eq.{succ u2} (Set.{u2} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u2} ι I π₁) (BoxIntegral.Prepartition.iUnion.{u2} ι I π₂)) -> (Eq.{succ u1} M (Finset.sum.{u1, u2} M (BoxIntegral.Box.{u2} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u2} ι I π₁) (fun (J : BoxIntegral.Box.{u2} ι) => BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f J)) (Finset.sum.{u1, u2} M (BoxIntegral.Box.{u2} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u2} ι I π₂) (fun (J : BoxIntegral.Box.{u2} ι) => BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι M _inst_1 I₀ f J))))
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.sum_boxes_congr BoxIntegral.BoxAdditiveMap.sum_boxes_congrₓ'. -/
/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J`. -/
theorem sum_boxes_congr [Finite ι] (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : (∑ J in π₁.boxes, f J) = ∑ J in π₂.boxes, f J :=
  by
  rcases exists_split_many_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with
    ⟨s, hs⟩
  simp only [inf_split_many] at hs
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩; clear hs
  rw [h] at h₁
  calc
    (∑ J in π₁.boxes, f J) = ∑ J in π₁.boxes, ∑ J' in (split_many J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ => (f.sum_partition_boxes _ (is_partition_split_many _ _)).symm
    _ = ∑ J in (π₁.bUnion fun J => split_many J s).boxes, f J := (sum_bUnion_boxes _ _ _).symm
    _ = ∑ J in (π₂.bUnion fun J => split_many J s).boxes, f J := by rw [h₁, h₂]
    _ = ∑ J in π₂.boxes, ∑ J' in (split_many J s).boxes, f J' := (sum_bUnion_boxes _ _ _)
    _ = ∑ J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes _ (is_partition_split_many _ _)
    
  exacts[(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI,
    (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]
#align box_integral.box_additive_map.sum_boxes_congr BoxIntegral.BoxAdditiveMap.sum_boxes_congr

section ToSmul

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

#print BoxIntegral.BoxAdditiveMap.toSmul /-
/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
def toSmul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] E →L[ℝ] E :=
  f.map (ContinuousLinearMap.lsmul ℝ ℝ).toLinearMap.toAddMonoidHom
#align box_integral.box_additive_map.to_smul BoxIntegral.BoxAdditiveMap.toSmul
-/

/- warning: box_integral.box_additive_map.to_smul_apply -> BoxIntegral.BoxAdditiveMap.toSmul_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I₀ : WithTop.{u1} (BoxIntegral.Box.{u1} ι)} {E : Type.{u2}} [_inst_3 : NormedAddCommGroup.{u2} E] [_inst_4 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)] (f : BoxIntegral.BoxAdditiveMap.{u1, 0} ι Real Real.addCommMonoid I₀) (I : BoxIntegral.Box.{u1} ι) (x : E), Eq.{succ u2} E (coeFn.{succ u2, succ u2} (ContinuousLinearMap.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4)) (fun (_x : ContinuousLinearMap.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4)) => E -> E) (ContinuousLinearMap.toFun.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (BoxIntegral.BoxAdditiveMap.{u1, u2} ι (ContinuousLinearMap.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4)) (ContinuousLinearMap.addCommMonoid.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (BoxIntegral.BoxAdditiveMap.toSmul._proof_1.{u2} E _inst_3)) I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, u2} ι (ContinuousLinearMap.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4)) (ContinuousLinearMap.addCommMonoid.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (BoxIntegral.BoxAdditiveMap.toSmul._proof_1.{u2} E _inst_3)) I₀) => (BoxIntegral.Box.{u1} ι) -> (ContinuousLinearMap.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4))) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, u2} ι (ContinuousLinearMap.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4)) (ContinuousLinearMap.addCommMonoid.{0, 0, u2, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4) (BoxIntegral.BoxAdditiveMap.toSmul._proof_1.{u2} E _inst_3)) I₀) (BoxIntegral.BoxAdditiveMap.toSmul.{u1, u2} ι I₀ E _inst_3 _inst_4 f) I) x) (SMul.smul.{0, u2} Real E (SMulZeroClass.toHasSmul.{0, u2} Real E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real E (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3)))))) (Module.toMulActionWithZero.{0, u2} Real E (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3))) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_3) _inst_4))))) (coeFn.{succ u1, succ u1} (BoxIntegral.BoxAdditiveMap.{u1, 0} ι Real Real.addCommMonoid I₀) (fun (_x : BoxIntegral.BoxAdditiveMap.{u1, 0} ι Real Real.addCommMonoid I₀) => (BoxIntegral.Box.{u1} ι) -> Real) (BoxIntegral.BoxAdditiveMap.hasCoeToFun.{u1, 0} ι Real Real.addCommMonoid I₀) f I) x)
but is expected to have type
  forall {ι : Type.{u2}} {I₀ : WithTop.{u2} (BoxIntegral.Box.{u2} ι)} {E : Type.{u1}} [_inst_3 : NormedAddCommGroup.{u1} E] [_inst_4 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)] (f : BoxIntegral.BoxAdditiveMap.{u2, 0} ι Real Real.instAddCommMonoidReal I₀) (I : BoxIntegral.Box.{u2} ι) (x : E), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : E) => E) x) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousLinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4)) E (fun (_x : E) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : E) => E) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousLinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4)) E E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (ContinuousSemilinearMapClass.toContinuousMapClass.{u1, 0, 0, u1, u1} (ContinuousLinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4)) Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (ContinuousLinearMap.continuousSemilinearMapClass.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4)))) (BoxIntegral.BoxAdditiveMap.toFun.{u2, u1} ι (ContinuousLinearMap.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4)) (ContinuousLinearMap.addCommMonoid.{0, 0, u1, u1} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4) (TopologicalAddGroup.toContinuousAdd.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_3)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3)))) I₀ (BoxIntegral.BoxAdditiveMap.toSmul.{u2, u1} ι I₀ E _inst_3 _inst_4 f) I) x) (HSMul.hSMul.{0, u1, u1} Real E E (instHSMul.{0, u1} Real E (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_3)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_3) _inst_4)))))) (BoxIntegral.BoxAdditiveMap.toFun.{u2, 0} ι Real Real.instAddCommMonoidReal I₀ f I) x)
Case conversion may be inaccurate. Consider using '#align box_integral.box_additive_map.to_smul_apply BoxIntegral.BoxAdditiveMap.toSmul_applyₓ'. -/
@[simp]
theorem toSmul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : Box ι) (x : E) : f.toSmul I x = f I • x :=
  rfl
#align box_integral.box_additive_map.to_smul_apply BoxIntegral.BoxAdditiveMap.toSmul_apply

end ToSmul

#print BoxIntegral.BoxAdditiveMap.upperSubLower /-
/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : box (fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `λ J, f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes of
`I₀`. -/
@[simps]
def upperSubLower.{u} {G : Type u} [AddCommGroup G] (I₀ : Box (Fin (n + 1))) (i : Fin (n + 1))
    (f : ℝ → Box (Fin n) → G) (fb : Icc (I₀.lower i) (I₀.upper i) → Fin n →ᵇᵃ[I₀.face i] G)
    (hf : ∀ (x) (hx : x ∈ Icc (I₀.lower i) (I₀.upper i)) (J), f x J = fb ⟨x, hx⟩ J) :
    Fin (n + 1) →ᵇᵃ[I₀] G :=
  ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j
      rw [WithTop.coe_le_coe] at hJ
      refine' i.succ_above_cases _ _ j
      · intro x hx
        simp only [box.split_lower_def hx, box.split_upper_def hx, update_same, ←
          WithBot.some_eq_coe, Option.elim', box.face, (· ∘ ·), update_noteq (Fin.succAbove_ne _ _)]
        abel
      · clear j
        intro j x hx
        have : (J.face i : WithTop (box (Fin n))) ≤ I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc, @box.Icc_eq_pi _ I₀] at hJ
        rw [hf _ (hJ J.upper_mem_Icc _ trivial), hf _ (hJ J.lower_mem_Icc _ trivial), ←
          (fb _).map_split_add this j x, ← (fb _).map_split_add this j x]
        have hx' : x ∈ Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        simp only [box.split_lower_def hx, box.split_upper_def hx, box.split_lower_def hx',
          box.split_upper_def hx', ← WithBot.some_eq_coe, Option.elim', box.face_mk,
          update_noteq (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ i.succ_above.injective j x, ← hf]
        simp only [box.face])
#align box_integral.box_additive_map.upper_sub_lower BoxIntegral.BoxAdditiveMap.upperSubLower
-/

end BoxAdditiveMap

end BoxIntegral

