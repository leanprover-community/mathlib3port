/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.subbox_induction
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Box.SubboxInduction
import Mathbin.Analysis.BoxIntegral.Partition.Tagged

/-!
# Induction on subboxes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove (see
`box_integral.tagged_partition.exists_is_Henstock_is_subordinate_homothetic`) that for every box `I`
in `ℝⁿ` and a function `r : ℝⁿ → ℝ` positive on `I` there exists a tagged partition `π` of `I` such
that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

Later we will use this lemma to prove that the Henstock filter is nontrivial, hence the Henstock
integral is well-defined.

## Tags

partition, tagged partition, Henstock integral
-/


namespace BoxIntegral

open Set Metric

open Classical Topology

noncomputable section

variable {ι : Type _} [Fintype ι] {I J : Box ι}

namespace Prepartition

#print BoxIntegral.Prepartition.splitCenter /-
/-- Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center. -/
def splitCenter (I : Box ι) : Prepartition I
    where
  boxes := Finset.univ.map (Box.splitCenterBoxEmb I)
  le_of_mem' := by simp [I.split_center_box_le]
  PairwiseDisjoint := by
    rw [Finset.coe_map, Finset.coe_univ, image_univ]
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne
    exact I.disjoint_split_center_box (mt (congr_arg _) Hne)
#align box_integral.prepartition.split_center BoxIntegral.Prepartition.splitCenter
-/

#print BoxIntegral.Prepartition.mem_splitCenter /-
@[simp]
theorem mem_splitCenter : J ∈ splitCenter I ↔ ∃ s, I.splitCenterBox s = J := by simp [split_center]
#align box_integral.prepartition.mem_split_center BoxIntegral.Prepartition.mem_splitCenter
-/

#print BoxIntegral.Prepartition.isPartition_splitCenter /-
theorem isPartition_splitCenter (I : Box ι) : IsPartition (splitCenter I) := fun x hx => by
  simp [hx]
#align box_integral.prepartition.is_partition_split_center BoxIntegral.Prepartition.isPartition_splitCenter
-/

/- warning: box_integral.prepartition.upper_sub_lower_of_mem_split_center -> BoxIntegral.Prepartition.upper_sub_lower_of_mem_splitCenter is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι}, (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J (BoxIntegral.Prepartition.splitCenter.{u1} ι _inst_1 I)) -> (forall (i : ι), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (BoxIntegral.Box.upper.{u1} ι J i) (BoxIntegral.Box.lower.{u1} ι J i)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (BoxIntegral.Box.upper.{u1} ι I i) (BoxIntegral.Box.lower.{u1} ι I i)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι}, (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J (BoxIntegral.Prepartition.splitCenter.{u1} ι _inst_1 I)) -> (forall (i : ι), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (BoxIntegral.Box.upper.{u1} ι J i) (BoxIntegral.Box.lower.{u1} ι J i)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (BoxIntegral.Box.upper.{u1} ι I i) (BoxIntegral.Box.lower.{u1} ι I i)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.upper_sub_lower_of_mem_split_center BoxIntegral.Prepartition.upper_sub_lower_of_mem_splitCenterₓ'. -/
theorem upper_sub_lower_of_mem_splitCenter (h : J ∈ splitCenter I) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
  let ⟨s, hs⟩ := mem_splitCenter.1 h
  hs ▸ I.upper_sub_lower_splitCenterBox s i
#align box_integral.prepartition.upper_sub_lower_of_mem_split_center BoxIntegral.Prepartition.upper_sub_lower_of_mem_splitCenter

end Prepartition

namespace Box

open Prepartition TaggedPrepartition

/- warning: box_integral.box.subbox_induction_on -> BoxIntegral.Box.subbox_induction_on is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {p : (BoxIntegral.Box.{u1} ι) -> Prop} (I : BoxIntegral.Box.{u1} ι), (forall (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) -> (forall (J' : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι J) (BoxIntegral.Prepartition.hasMem.{u1} ι J) J' (BoxIntegral.Prepartition.splitCenter.{u1} ι _inst_1 J)) -> (p J')) -> (p J)) -> (forall (z : ι -> Real), (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) z (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)) -> (Exists.{succ u1} (Set.{u1} (ι -> Real)) (fun (U : Set.{u1} (ι -> Real)) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} (ι -> Real)) (Filter.{u1} (ι -> Real)) (Filter.hasMem.{u1} (ι -> Real)) U (nhdsWithin.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) z (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} (ι -> Real)) (Filter.{u1} (ι -> Real)) (Filter.hasMem.{u1} (ι -> Real)) U (nhdsWithin.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) z (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I))) => forall (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) -> (forall (m : Nat), (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) z (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) J)) -> (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.hasSubset.{u1} (ι -> Real)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) J) U) -> (forall (i : ι), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (BoxIntegral.Box.upper.{u1} ι J i) (BoxIntegral.Box.lower.{u1} ι J i)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (BoxIntegral.Box.upper.{u1} ι I i) (BoxIntegral.Box.lower.{u1} ι I i)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) m))) -> (p J)))))) -> (p I)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {p : (BoxIntegral.Box.{u1} ι) -> Prop} (I : BoxIntegral.Box.{u1} ι), (forall (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) -> (forall (J' : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι J) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι J) J' (BoxIntegral.Prepartition.splitCenter.{u1} ι _inst_1 J)) -> (p J')) -> (p J)) -> (forall (z : ι -> Real), (Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) z (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (BoxIntegral.Box.Icc.{u1} ι) I)) -> (Exists.{succ u1} (Set.{u1} (ι -> Real)) (fun (U : Set.{u1} (ι -> Real)) => And (Membership.mem.{u1, u1} (Set.{u1} (ι -> Real)) (Filter.{u1} (ι -> Real)) (instMembershipSetFilter.{u1} (ι -> Real)) U (nhdsWithin.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) z (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (BoxIntegral.Box.Icc.{u1} ι) I))) (forall (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) -> (forall (m : Nat), (Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) J) (Set.instMembershipSet.{u1} (ι -> Real)) z (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (a : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) a) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (BoxIntegral.Box.Icc.{u1} ι) J)) -> (HasSubset.Subset.{u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) J) (Set.instHasSubsetSet.{u1} (ι -> Real)) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (a : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) a) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (BoxIntegral.Box.Icc.{u1} ι) J) U) -> (forall (i : ι), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (BoxIntegral.Box.upper.{u1} ι J i) (BoxIntegral.Box.lower.{u1} ι J i)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (BoxIntegral.Box.upper.{u1} ι I i) (BoxIntegral.Box.lower.{u1} ι I i)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) m))) -> (p J)))))) -> (p I)
Case conversion may be inaccurate. Consider using '#align box_integral.box.subbox_induction_on BoxIntegral.Box.subbox_induction_onₓ'. -/
/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `box_integral.box.subbox_induction_on'` for a version using
`box_integral.box.split_center_box` instead of `box_integral.prepartition.split_center`. -/
@[elab_as_elim]
theorem subbox_induction_on {p : Box ι → Prop} (I : Box ι)
    (H_ind : ∀ J ≤ I, (∀ J' ∈ splitCenter J, p J') → p J)
    (H_nhds :
      ∀ z ∈ I.Icc,
        ∃ U ∈ 𝓝[I.Icc] z,
          ∀ J ≤ I,
            ∀ (m : ℕ),
              z ∈ J.Icc →
                J.Icc ⊆ U → (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) → p J) :
    p I :=
  by
  refine' subbox_induction_on' I (fun J hle hs => H_ind J hle fun J' h' => _) H_nhds
  rcases mem_split_center.1 h' with ⟨s, rfl⟩
  exact hs s
#align box_integral.box.subbox_induction_on BoxIntegral.Box.subbox_induction_on

/- warning: box_integral.box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic -> BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] (I : BoxIntegral.Box.{u1} ι) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), Exists.{succ u1} (BoxIntegral.TaggedPrepartition.{u1} ι I) (fun (π : BoxIntegral.TaggedPrepartition.{u1} ι I) => And (BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I π) (And (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π) (And (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) (And (forall (J : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π) -> (Exists.{1} Nat (fun (m : Nat) => forall (i : ι), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (BoxIntegral.Box.upper.{u1} ι J i) (BoxIntegral.Box.lower.{u1} ι J i)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (BoxIntegral.Box.upper.{u1} ι I i) (BoxIntegral.Box.lower.{u1} ι I i)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) m))))) (Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1) (BoxIntegral.Box.distortion.{u1} ι _inst_1 I))))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] (I : BoxIntegral.Box.{u1} ι) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), Exists.{succ u1} (BoxIntegral.TaggedPrepartition.{u1} ι I) (fun (π : BoxIntegral.TaggedPrepartition.{u1} ι I) => And (BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I π) (And (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π) (And (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) (And (forall (J : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π) -> (Exists.{1} Nat (fun (m : Nat) => forall (i : ι), Eq.{1} Real (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (BoxIntegral.Box.upper.{u1} ι J i) (BoxIntegral.Box.lower.{u1} ι J i)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (BoxIntegral.Box.upper.{u1} ι I i) (BoxIntegral.Box.lower.{u1} ι I i)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) m))))) (Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1) (BoxIntegral.Box.distortion.{u1} ι _inst_1 I))))))
Case conversion may be inaccurate. Consider using '#align box_integral.box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homotheticₓ'. -/
/-- Given a box `I` in `ℝⁿ` and a function `r : ℝⁿ → (0, ∞)`, there exists a tagged partition `π` of
`I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ m`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock integral is
well-defined. -/
theorem exists_taggedPartition_isHenstock_isSubordinate_homothetic (I : Box ι)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π : TaggedPrepartition I,
      π.IsPartition ∧
        π.IsHenstock ∧
          π.IsSubordinate r ∧
            (∀ J ∈ π, ∃ m : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) ∧
              π.distortion = I.distortion :=
  by
  refine' subbox_induction_on I (fun J hle hJ => _) fun z hz => _
  · choose! πi hP hHen hr Hn Hd using hJ
    choose! n hn using Hn
    have hP : ((split_center J).biUnionTagged πi).IsPartition :=
      (is_partition_split_center _).biUnionTagged hP
    have hsub :
      ∀ J' ∈ (split_center J).biUnionTagged πi,
        ∃ n : ℕ, ∀ i, (J' : _).upper i - J'.lower i = (J.upper i - J.lower i) / 2 ^ n :=
      by
      intro J' hJ'
      rcases(split_center J).mem_biUnionTagged.1 hJ' with ⟨J₁, h₁, h₂⟩
      refine' ⟨n J₁ J' + 1, fun i => _⟩
      simp only [hn J₁ h₁ J' h₂, upper_sub_lower_of_mem_split_center h₁, pow_succ, div_div]
    refine' ⟨_, hP, is_Henstock_bUnion_tagged.2 hHen, is_subordinate_bUnion_tagged.2 hr, hsub, _⟩
    refine' tagged_prepartition.distortion_of_const _ hP.nonempty_boxes fun J' h' => _
    rcases hsub J' h' with ⟨n, hn⟩
    exact box.distortion_eq_of_sub_eq_div hn
  · refine'
      ⟨I.Icc ∩ closed_ball z (r z), inter_mem_nhdsWithin _ (closed_ball_mem_nhds _ (r z).coe_prop),
        _⟩
    intro J Hle n Hmem HIcc Hsub
    rw [Set.subset_inter_iff] at HIcc
    refine'
      ⟨single _ _ le_rfl _ Hmem, is_partition_single _, is_Henstock_single _,
        (is_subordinate_single _ _).2 HIcc.2, _, distortion_single _ _⟩
    simp only [tagged_prepartition.mem_single, forall_eq]
    refine' ⟨0, fun i => _⟩
    simp
#align box_integral.box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic BoxIntegral.Box.exists_taggedPartition_isHenstock_isSubordinate_homothetic

end Box

namespace Prepartition

open TaggedPrepartition Finset Function

/- warning: box_integral.prepartition.exists_tagged_le_is_Henstock_is_subordinate_Union_eq -> BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (π : BoxIntegral.Prepartition.{u1} ι I), Exists.{succ u1} (BoxIntegral.TaggedPrepartition.{u1} ι I) (fun (π' : BoxIntegral.TaggedPrepartition.{u1} ι I) => And (LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π') π) (And (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π') (And (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π' r) (And (Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π' _inst_1) (BoxIntegral.Prepartition.distortion.{u1} ι I π _inst_1)) (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π') (BoxIntegral.Prepartition.iUnion.{u1} ι I π))))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (π : BoxIntegral.Prepartition.{u1} ι I), Exists.{succ u1} (BoxIntegral.TaggedPrepartition.{u1} ι I) (fun (π' : BoxIntegral.TaggedPrepartition.{u1} ι I) => And (LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π') π) (And (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π') (And (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π' r) (And (Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π' _inst_1) (BoxIntegral.Prepartition.distortion.{u1} ι I π _inst_1)) (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π') (BoxIntegral.Prepartition.iUnion.{u1} ι I π))))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.exists_tagged_le_is_Henstock_is_subordinate_Union_eq BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnion_eqₓ'. -/
/-- Given a box `I` in `ℝⁿ`, a function `r : ℝⁿ → (0, ∞)`, and a prepartition `π` of `I`, there
exists a tagged prepartition `π'` of `I` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
theorem exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : Prepartition I) :
    ∃ π' : TaggedPrepartition I,
      π'.toPrepartition ≤ π ∧
        π'.IsHenstock ∧ π'.IsSubordinate r ∧ π'.distortion = π.distortion ∧ π'.iUnion = π.iUnion :=
  by
  have := fun J => box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic J r
  choose! πi πip πiH πir hsub πid; clear hsub
  refine'
    ⟨π.bUnion_tagged πi, bUnion_le _ _, is_Henstock_bUnion_tagged.2 fun J _ => πiH J,
      is_subordinate_bUnion_tagged.2 fun J _ => πir J, _, π.Union_bUnion_partition fun J _ => πip J⟩
  rw [distortion_bUnion_tagged]
  exact sup_congr rfl fun J _ => πid J
#align box_integral.prepartition.exists_tagged_le_is_Henstock_is_subordinate_Union_eq BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq

/- warning: box_integral.prepartition.to_subordinate -> BoxIntegral.Prepartition.toSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι}, (BoxIntegral.Prepartition.{u1} ι I) -> ((ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> (BoxIntegral.TaggedPrepartition.{u1} ι I)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι}, (BoxIntegral.Prepartition.{u1} ι I) -> ((ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> (BoxIntegral.TaggedPrepartition.{u1} ι I)
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.to_subordinate BoxIntegral.Prepartition.toSubordinateₓ'. -/
/-- Given a prepartition `π` of a box `I` and a function `r : ℝⁿ → (0, ∞)`, `π.to_subordinate r`
is a tagged partition `π'` such that

* each box of `π'` is included in some box of `π`;
* `π'` is a Henstock partition;
* `π'` is subordinate to `r`;
* `π'` covers exactly the same part of `I` as `π`;
* the distortion of `π'` is equal to the distortion of `π`.
-/
def toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).some
#align box_integral.prepartition.to_subordinate BoxIntegral.Prepartition.toSubordinate

/- warning: box_integral.prepartition.to_subordinate_to_prepartition_le -> BoxIntegral.Prepartition.toSubordinate_toPrepartition_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r)) π
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r)) π
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.to_subordinate_to_prepartition_le BoxIntegral.Prepartition.toSubordinate_toPrepartition_leₓ'. -/
theorem toSubordinate_toPrepartition_le (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).toPrepartition ≤ π :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.1
#align box_integral.prepartition.to_subordinate_to_prepartition_le BoxIntegral.Prepartition.toSubordinate_toPrepartition_le

/- warning: box_integral.prepartition.is_Henstock_to_subordinate -> BoxIntegral.Prepartition.isHenstock_toSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r)
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.is_Henstock_to_subordinate BoxIntegral.Prepartition.isHenstock_toSubordinateₓ'. -/
theorem isHenstock_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsHenstock :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.1
#align box_integral.prepartition.is_Henstock_to_subordinate BoxIntegral.Prepartition.isHenstock_toSubordinate

/- warning: box_integral.prepartition.is_subordinate_to_subordinate -> BoxIntegral.Prepartition.isSubordinate_toSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r) r
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r) r
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.is_subordinate_to_subordinate BoxIntegral.Prepartition.isSubordinate_toSubordinateₓ'. -/
theorem isSubordinate_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).IsSubordinate r :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.1
#align box_integral.prepartition.is_subordinate_to_subordinate BoxIntegral.Prepartition.isSubordinate_toSubordinate

/- warning: box_integral.prepartition.distortion_to_subordinate -> BoxIntegral.Prepartition.distortion_toSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r) _inst_1) (BoxIntegral.Prepartition.distortion.{u1} ι I π _inst_1)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r) _inst_1) (BoxIntegral.Prepartition.distortion.{u1} ι I π _inst_1)
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.distortion_to_subordinate BoxIntegral.Prepartition.distortion_toSubordinateₓ'. -/
@[simp]
theorem distortion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).distortion = π.distortion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.1
#align box_integral.prepartition.distortion_to_subordinate BoxIntegral.Prepartition.distortion_toSubordinate

/- warning: box_integral.prepartition.Union_to_subordinate -> BoxIntegral.Prepartition.iUnion_toSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π r)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π)
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.Union_to_subordinate BoxIntegral.Prepartition.iUnion_toSubordinateₓ'. -/
@[simp]
theorem iUnion_toSubordinate (π : Prepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π.toSubordinate r).iUnion = π.iUnion :=
  (π.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r).choose_spec.2.2.2.2
#align box_integral.prepartition.Union_to_subordinate BoxIntegral.Prepartition.iUnion_toSubordinate

end Prepartition

namespace TaggedPrepartition

/- warning: box_integral.tagged_prepartition.union_compl_to_subordinate -> BoxIntegral.TaggedPrepartition.unionComplToSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I), (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) -> ((ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> (BoxIntegral.TaggedPrepartition.{u1} ι I)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I), (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) -> ((ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> (BoxIntegral.TaggedPrepartition.{u1} ι I)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.union_compl_to_subordinate BoxIntegral.TaggedPrepartition.unionComplToSubordinateₓ'. -/
/-- Given a tagged prepartition `π₁`, a prepartition `π₂` that covers exactly `I \ π₁.Union`, and
a function `r : ℝⁿ → (0, ∞)`, returns the union of `π₁` and `π₂.to_subordinate r`. This partition
`π` has the following properties:

* `π` is a partition, i.e. it covers the whole `I`;
* `π₁.boxes ⊆ π.boxes`;
* `π.tag J = π₁.tag J` whenever `J ∈ π₁`;
* `π` is Henstock outside of `π₁`: `π.tag J ∈ J.Icc` whenever `J ∈ π`, `J ∉ π₁`;
* `π` is subordinate to `r` outside of `π₁`;
* the distortion of `π` is equal to the maximum of the distortions of `π₁` and `π₂`.
-/
def unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) : TaggedPrepartition I :=
  π₁.disjUnion (π₂.toSubordinate r)
    (((π₂.iUnion_toSubordinate r).trans hU).symm ▸ disjoint_sdiff_self_right)
#align box_integral.tagged_prepartition.union_compl_to_subordinate BoxIntegral.TaggedPrepartition.unionComplToSubordinate

/- warning: box_integral.tagged_prepartition.is_partition_union_compl_to_subordinate -> BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_partition_union_compl_to_subordinate BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinateₓ'. -/
theorem isPartition_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    IsPartition (π₁.unionComplToSubordinate π₂ hU r) :=
  Prepartition.isPartitionDisjUnionOfEqDiff ((π₂.iUnion_toSubordinate r).trans hU)
#align box_integral.tagged_prepartition.is_partition_union_compl_to_subordinate BoxIntegral.TaggedPrepartition.isPartition_unionComplToSubordinate

/- warning: box_integral.tagged_prepartition.union_compl_to_subordinate_boxes -> BoxIntegral.TaggedPrepartition.unionComplToSubordinate_boxes is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), Eq.{succ u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r))) (Union.union.{u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.hasUnion.{u1} (BoxIntegral.Box.{u1} ι) (fun (a : BoxIntegral.Box.{u1} ι) (b : BoxIntegral.Box.{u1} ι) => Classical.propDecidable (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) a b))) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π₁)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π₂ r))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), Eq.{succ u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r))) (Union.union.{u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.instUnionFinset.{u1} (BoxIntegral.Box.{u1} ι) (fun (a : BoxIntegral.Box.{u1} ι) (b : BoxIntegral.Box.{u1} ι) => Classical.propDecidable (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) a b))) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π₁)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.Prepartition.toSubordinate.{u1} ι _inst_1 I π₂ r))))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.union_compl_to_subordinate_boxes BoxIntegral.TaggedPrepartition.unionComplToSubordinate_boxesₓ'. -/
@[simp]
theorem unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).boxes = π₁.boxes ∪ (π₂.toSubordinate r).boxes :=
  rfl
#align box_integral.tagged_prepartition.union_compl_to_subordinate_boxes BoxIntegral.TaggedPrepartition.unionComplToSubordinate_boxes

/- warning: box_integral.tagged_prepartition.Union_union_compl_to_subordinate_boxes -> BoxIntegral.TaggedPrepartition.iUnion_unionComplToSubordinate_boxes is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I)
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r)) (BoxIntegral.Box.toSet.{u1} ι I)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.Union_union_compl_to_subordinate_boxes BoxIntegral.TaggedPrepartition.iUnion_unionComplToSubordinate_boxesₓ'. -/
@[simp]
theorem iUnion_unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).iUnion = I :=
  (isPartition_unionComplToSubordinate _ _ _ _).iUnion_eq
#align box_integral.tagged_prepartition.Union_union_compl_to_subordinate_boxes BoxIntegral.TaggedPrepartition.iUnion_unionComplToSubordinate_boxes

/- warning: box_integral.tagged_prepartition.distortion_union_compl_to_subordinate -> BoxIntegral.TaggedPrepartition.distortion_unionComplToSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r) _inst_1) (LinearOrder.max.{0} NNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot)) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π₁ _inst_1) (BoxIntegral.Prepartition.distortion.{u1} ι I π₂ _inst_1))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.Prepartition.{u1} ι I) (hU : Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π₂) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁))) (r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.unionComplToSubordinate.{u1} ι _inst_1 I π₁ π₂ hU r) _inst_1) (Max.max.{0} NNReal (CanonicallyLinearOrderedSemifield.toMax.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π₁ _inst_1) (BoxIntegral.Prepartition.distortion.{u1} ι I π₂ _inst_1))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_union_compl_to_subordinate BoxIntegral.TaggedPrepartition.distortion_unionComplToSubordinateₓ'. -/
@[simp]
theorem distortion_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I)
    (hU : π₂.iUnion = I \ π₁.iUnion) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    (π₁.unionComplToSubordinate π₂ hU r).distortion = max π₁.distortion π₂.distortion := by
  simp [union_compl_to_subordinate]
#align box_integral.tagged_prepartition.distortion_union_compl_to_subordinate BoxIntegral.TaggedPrepartition.distortion_unionComplToSubordinate

end TaggedPrepartition

end BoxIntegral

