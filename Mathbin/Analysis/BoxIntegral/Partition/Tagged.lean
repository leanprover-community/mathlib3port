/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.tagged
! leanprover-community/mathlib commit 2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Partition.Basic

/-!
# Tagged partitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A tagged (pre)partition is a (pre)partition `π` enriched with a tagged point for each box of
‵π`. For simplicity we require that the function `box_integral.tagged_prepartition.tag` is defined
on all boxes `J : box ι` but use its values only on boxes of the partition. Given `π :
box_integral.tagged_partition I`, we require that each `box_integral.tagged_partition π J` belongs
to `box_integral.box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is called
a *Henstock* partition. We do not include this assumption into the definition of a tagged
(pre)partition because McShane integral is defined as a limit along tagged partitions without this
requirement.

### Tags

rectangular box, box partition
-/


noncomputable section

open Classical ENNReal NNReal

open Set Function

namespace BoxIntegral

variable {ι : Type _}

#print BoxIntegral.TaggedPrepartition /-
/-- A tagged prepartition is a prepartition enriched with a tagged point for each box of the
prepartition. For simiplicity we require that `tag` is defined for all boxes in `ι → ℝ` but
we will use onle the values of `tag` on the boxes of the partition. -/
structure TaggedPrepartition (I : Box ι) extends Prepartition I where
  Tag : Box ι → ι → ℝ
  tag_mem_Icc : ∀ J, tag J ∈ I.Icc
#align box_integral.tagged_prepartition BoxIntegral.TaggedPrepartition
-/

namespace TaggedPrepartition

variable {I J J₁ J₂ : Box ι} (π : TaggedPrepartition I) {x : ι → ℝ}

instance : Membership (Box ι) (TaggedPrepartition I) :=
  ⟨fun J π => J ∈ π.boxes⟩

#print BoxIntegral.TaggedPrepartition.mem_toPrepartition /-
@[simp]
theorem mem_toPrepartition {π : TaggedPrepartition I} : J ∈ π.toPrepartition ↔ J ∈ π :=
  Iff.rfl
#align box_integral.tagged_prepartition.mem_to_prepartition BoxIntegral.TaggedPrepartition.mem_toPrepartition
-/

/- warning: box_integral.tagged_prepartition.mem_mk -> BoxIntegral.TaggedPrepartition.mem_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (f : (BoxIntegral.Box.{u1} ι) -> ι -> Real) (h : forall (J : BoxIntegral.Box.{u1} ι), Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) (f J) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J (BoxIntegral.TaggedPrepartition.mk.{u1} ι I π f h)) (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J π)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (f : (BoxIntegral.Box.{u1} ι) -> ι -> Real) (h : forall (J : BoxIntegral.Box.{u1} ι), Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) (f J) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J (BoxIntegral.TaggedPrepartition.mk.{u1} ι I π f h)) (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J π)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.mem_mk BoxIntegral.TaggedPrepartition.mem_mkₓ'. -/
@[simp]
theorem mem_mk (π : Prepartition I) (f h) : J ∈ mk π f h ↔ J ∈ π :=
  Iff.rfl
#align box_integral.tagged_prepartition.mem_mk BoxIntegral.TaggedPrepartition.mem_mk

#print BoxIntegral.TaggedPrepartition.iUnion /-
/-- Union of all boxes of a tagged prepartition. -/
def iUnion : Set (ι → ℝ) :=
  π.toPrepartition.iUnion
#align box_integral.tagged_prepartition.Union BoxIntegral.TaggedPrepartition.iUnion
-/

#print BoxIntegral.TaggedPrepartition.iUnion_def /-
theorem iUnion_def : π.iUnion = ⋃ J ∈ π, ↑J :=
  rfl
#align box_integral.tagged_prepartition.Union_def BoxIntegral.TaggedPrepartition.iUnion_def
-/

/- warning: box_integral.tagged_prepartition.Union_mk -> BoxIntegral.TaggedPrepartition.iUnion_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (f : (BoxIntegral.Box.{u1} ι) -> ι -> Real) (h : forall (J : BoxIntegral.Box.{u1} ι), Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) (f J) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.mk.{u1} ι I π f h)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) (f : (BoxIntegral.Box.{u1} ι) -> ι -> Real) (h : forall (J : BoxIntegral.Box.{u1} ι), Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) (f J) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.mk.{u1} ι I π f h)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.Union_mk BoxIntegral.TaggedPrepartition.iUnion_mkₓ'. -/
@[simp]
theorem iUnion_mk (π : Prepartition I) (f h) : (mk π f h).iUnion = π.iUnion :=
  rfl
#align box_integral.tagged_prepartition.Union_mk BoxIntegral.TaggedPrepartition.iUnion_mk

#print BoxIntegral.TaggedPrepartition.iUnion_toPrepartition /-
@[simp]
theorem iUnion_toPrepartition : π.toPrepartition.iUnion = π.iUnion :=
  rfl
#align box_integral.tagged_prepartition.Union_to_prepartition BoxIntegral.TaggedPrepartition.iUnion_toPrepartition
-/

/- warning: box_integral.tagged_prepartition.mem_Union -> BoxIntegral.TaggedPrepartition.mem_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) {x : ι -> Real}, Iff (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π)) (Exists.{succ u1} (BoxIntegral.Box.{u1} ι) (fun (J : BoxIntegral.Box.{u1} ι) => Exists.{0} (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π) (fun (H : Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π) => Membership.Mem.{u1, u1} (ι -> Real) (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasMem.{u1} ι) x J)))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) {x : ι -> Real}, Iff (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) x (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π)) (Exists.{succ u1} (BoxIntegral.Box.{u1} ι) (fun (J : BoxIntegral.Box.{u1} ι) => And (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π) (Membership.mem.{u1, u1} (ι -> Real) (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instMembershipForAllRealBox.{u1} ι) x J)))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.mem_Union BoxIntegral.TaggedPrepartition.mem_iUnionₓ'. -/
@[simp]
theorem mem_iUnion : x ∈ π.iUnion ↔ ∃ J ∈ π, x ∈ J :=
  Set.mem_iUnion₂
#align box_integral.tagged_prepartition.mem_Union BoxIntegral.TaggedPrepartition.mem_iUnion

#print BoxIntegral.TaggedPrepartition.subset_iUnion /-
theorem subset_iUnion (h : J ∈ π) : ↑J ⊆ π.iUnion :=
  subset_biUnion_of_mem h
#align box_integral.tagged_prepartition.subset_Union BoxIntegral.TaggedPrepartition.subset_iUnion
-/

#print BoxIntegral.TaggedPrepartition.iUnion_subset /-
theorem iUnion_subset : π.iUnion ⊆ I :=
  iUnion₂_subset π.le_of_mem'
#align box_integral.tagged_prepartition.Union_subset BoxIntegral.TaggedPrepartition.iUnion_subset
-/

#print BoxIntegral.TaggedPrepartition.IsPartition /-
/-- A tagged prepartition is a partition if it covers the whole box. -/
def IsPartition :=
  π.toPrepartition.IsPartition
#align box_integral.tagged_prepartition.is_partition BoxIntegral.TaggedPrepartition.IsPartition
-/

#print BoxIntegral.TaggedPrepartition.isPartition_iff_iUnion_eq /-
theorem isPartition_iff_iUnion_eq : IsPartition π ↔ π.iUnion = I :=
  Prepartition.isPartition_iff_iUnion_eq
#align box_integral.tagged_prepartition.is_partition_iff_Union_eq BoxIntegral.TaggedPrepartition.isPartition_iff_iUnion_eq
-/

#print BoxIntegral.TaggedPrepartition.filter /-
/-- The tagged partition made of boxes of `π` that satisfy predicate `p`. -/
@[simps (config := { fullyApplied := false })]
def filter (p : Box ι → Prop) : TaggedPrepartition I :=
  ⟨π.1.filterₓ p, π.2, π.3⟩
#align box_integral.tagged_prepartition.filter BoxIntegral.TaggedPrepartition.filter
-/

#print BoxIntegral.TaggedPrepartition.mem_filter /-
@[simp]
theorem mem_filter {p : Box ι → Prop} : J ∈ π.filterₓ p ↔ J ∈ π ∧ p J :=
  Finset.mem_filter
#align box_integral.tagged_prepartition.mem_filter BoxIntegral.TaggedPrepartition.mem_filter
-/

/- warning: box_integral.tagged_prepartition.Union_filter_not -> BoxIntegral.TaggedPrepartition.iUnion_filter_not is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) (p : (BoxIntegral.Box.{u1} ι) -> Prop), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.filter.{u1} ι I π (fun (J : BoxIntegral.Box.{u1} ι) => Not (p J)))) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.filter.{u1} ι I π p)))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) (p : (BoxIntegral.Box.{u1} ι) -> Prop), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.filter.{u1} ι I π (fun (J : BoxIntegral.Box.{u1} ι) => Not (p J)))) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.filter.{u1} ι I π p)))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.Union_filter_not BoxIntegral.TaggedPrepartition.iUnion_filter_notₓ'. -/
@[simp]
theorem iUnion_filter_not (π : TaggedPrepartition I) (p : Box ι → Prop) :
    (π.filterₓ fun J => ¬p J).iUnion = π.iUnion \ (π.filterₓ p).iUnion :=
  π.toPrepartition.iUnion_filter_not p
#align box_integral.tagged_prepartition.Union_filter_not BoxIntegral.TaggedPrepartition.iUnion_filter_not

end TaggedPrepartition

namespace Prepartition

variable {I J : Box ι}

#print BoxIntegral.Prepartition.biUnionTagged /-
/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def biUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) : TaggedPrepartition I
    where
  toPrepartition := π.biUnion fun J => (πi J).toPrepartition
  Tag J := (πi (π.biUnionIndex (fun J => (πi J).toPrepartition) J)).Tag J
  tag_mem_Icc J := Box.le_iff_Icc.1 (π.biUnionIndex_le _ _) ((πi _).tag_mem_Icc _)
#align box_integral.prepartition.bUnion_tagged BoxIntegral.Prepartition.biUnionTagged
-/

/- warning: box_integral.prepartition.mem_bUnion_tagged -> BoxIntegral.Prepartition.mem_biUnionTagged is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) {πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.TaggedPrepartition.{u1} ι J}, Iff (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J (BoxIntegral.Prepartition.biUnionTagged.{u1} ι I π πi)) (Exists.{succ u1} (BoxIntegral.Box.{u1} ι) (fun (J' : BoxIntegral.Box.{u1} ι) => Exists.{0} (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J' π) (fun (H : Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J' π) => Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι J') (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι J') J (πi J'))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.Prepartition.{u1} ι I) {πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.TaggedPrepartition.{u1} ι J}, Iff (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J (BoxIntegral.Prepartition.biUnionTagged.{u1} ι I π πi)) (Exists.{succ u1} (BoxIntegral.Box.{u1} ι) (fun (J' : BoxIntegral.Box.{u1} ι) => And (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J' π) (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι J') (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι J') J (πi J'))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.mem_bUnion_tagged BoxIntegral.Prepartition.mem_biUnionTaggedₓ'. -/
@[simp]
theorem mem_biUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} :
    J ∈ π.biUnionTagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
  π.mem_biUnion
#align box_integral.prepartition.mem_bUnion_tagged BoxIntegral.Prepartition.mem_biUnionTagged

#print BoxIntegral.Prepartition.tag_biUnionTagged /-
theorem tag_biUnionTagged (π : Prepartition I) {πi : ∀ J, TaggedPrepartition J} (hJ : J ∈ π) {J'}
    (hJ' : J' ∈ πi J) : (π.biUnionTagged πi).Tag J' = (πi J).Tag J' :=
  by
  have : J' ∈ π.bUnion_tagged πi := π.mem_bUnion.2 ⟨J, hJ, hJ'⟩
  obtain rfl := π.bUnion_index_of_mem hJ hJ'
  rfl
#align box_integral.prepartition.tag_bUnion_tagged BoxIntegral.Prepartition.tag_biUnionTagged
-/

#print BoxIntegral.Prepartition.iUnion_biUnionTagged /-
@[simp]
theorem iUnion_biUnionTagged (π : Prepartition I) (πi : ∀ J, TaggedPrepartition J) :
    (π.biUnionTagged πi).iUnion = ⋃ J ∈ π, (πi J).iUnion :=
  iUnion_biUnion _ _
#align box_integral.prepartition.Union_bUnion_tagged BoxIntegral.Prepartition.iUnion_biUnionTagged
-/

#print BoxIntegral.Prepartition.forall_biUnionTagged /-
theorem forall_biUnionTagged (p : (ι → ℝ) → Box ι → Prop) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (∀ J ∈ π.biUnionTagged πi, p ((π.biUnionTagged πi).Tag J) J) ↔
      ∀ J ∈ π, ∀ J' ∈ πi J, p ((πi J).Tag J') J' :=
  by
  simp only [bex_imp, mem_bUnion_tagged]
  refine' ⟨fun H J hJ J' hJ' => _, fun H J' J hJ hJ' => _⟩
  · rw [← π.tag_bUnion_tagged hJ hJ']
    exact H J' J hJ hJ'
  · rw [π.tag_bUnion_tagged hJ hJ']
    exact H J hJ J' hJ'
#align box_integral.prepartition.forall_bUnion_tagged BoxIntegral.Prepartition.forall_biUnionTagged
-/

#print BoxIntegral.Prepartition.IsPartition.biUnionTagged /-
theorem IsPartition.biUnionTagged {π : Prepartition I} (h : IsPartition π)
    {πi : ∀ J, TaggedPrepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnionTagged πi).IsPartition :=
  h.biUnion hi
#align box_integral.prepartition.is_partition.bUnion_tagged BoxIntegral.Prepartition.IsPartition.biUnionTagged
-/

end Prepartition

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}

#print BoxIntegral.TaggedPrepartition.biUnionPrepartition /-
/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps (config := { fullyApplied := false }) Tag]
def biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) : TaggedPrepartition I
    where
  toPrepartition := π.toPrepartition.biUnion πi
  Tag J := π.Tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc J := π.tag_mem_Icc _
#align box_integral.tagged_prepartition.bUnion_prepartition BoxIntegral.TaggedPrepartition.biUnionPrepartition
-/

#print BoxIntegral.TaggedPrepartition.IsPartition.biUnionPrepartition /-
theorem IsPartition.biUnionPrepartition {π : TaggedPrepartition I} (h : IsPartition π)
    {πi : ∀ J, Prepartition J} (hi : ∀ J ∈ π, (πi J).IsPartition) :
    (π.biUnionPrepartition πi).IsPartition :=
  h.biUnion hi
#align box_integral.tagged_prepartition.is_partition.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsPartition.biUnionPrepartition
-/

#print BoxIntegral.TaggedPrepartition.infPrepartition /-
/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def infPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) : TaggedPrepartition I :=
  π.biUnionPrepartition fun J => π'.restrict J
#align box_integral.tagged_prepartition.inf_prepartition BoxIntegral.TaggedPrepartition.infPrepartition
-/

#print BoxIntegral.TaggedPrepartition.infPrepartition_toPrepartition /-
@[simp]
theorem infPrepartition_toPrepartition (π : TaggedPrepartition I) (π' : Prepartition I) :
    (π.infPrepartition π').toPrepartition = π.toPrepartition ⊓ π' :=
  rfl
#align box_integral.tagged_prepartition.inf_prepartition_to_prepartition BoxIntegral.TaggedPrepartition.infPrepartition_toPrepartition
-/

#print BoxIntegral.TaggedPrepartition.mem_infPrepartition_comm /-
theorem mem_infPrepartition_comm :
    J ∈ π₁.infPrepartition π₂.toPrepartition ↔ J ∈ π₂.infPrepartition π₁.toPrepartition := by
  simp only [← mem_to_prepartition, inf_prepartition_to_prepartition, inf_comm]
#align box_integral.tagged_prepartition.mem_inf_prepartition_comm BoxIntegral.TaggedPrepartition.mem_infPrepartition_comm
-/

#print BoxIntegral.TaggedPrepartition.IsPartition.infPrepartition /-
theorem IsPartition.infPrepartition (h₁ : π₁.IsPartition) {π₂ : Prepartition I}
    (h₂ : π₂.IsPartition) : (π₁.infPrepartition π₂).IsPartition :=
  h₁.inf h₂
#align box_integral.tagged_prepartition.is_partition.inf_prepartition BoxIntegral.TaggedPrepartition.IsPartition.infPrepartition
-/

open Metric

#print BoxIntegral.TaggedPrepartition.IsHenstock /-
/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def IsHenstock (π : TaggedPrepartition I) : Prop :=
  ∀ J ∈ π, π.Tag J ∈ J.Icc
#align box_integral.tagged_prepartition.is_Henstock BoxIntegral.TaggedPrepartition.IsHenstock
-/

#print BoxIntegral.TaggedPrepartition.isHenstock_biUnionTagged /-
@[simp]
theorem isHenstock_biUnionTagged {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J} :
    IsHenstock (π.biUnionTagged πi) ↔ ∀ J ∈ π, (πi J).IsHenstock :=
  π.forall_biUnionTagged (fun x J => x ∈ J.Icc) πi
#align box_integral.tagged_prepartition.is_Henstock_bUnion_tagged BoxIntegral.TaggedPrepartition.isHenstock_biUnionTagged
-/

#print BoxIntegral.TaggedPrepartition.IsHenstock.card_filter_tag_eq_le /-
/-- In a Henstock prepartition, there are at most `2 ^ fintype.card ι` boxes with a given tag. -/
theorem IsHenstock.card_filter_tag_eq_le [Fintype ι] (h : π.IsHenstock) (x : ι → ℝ) :
    (π.boxes.filterₓ fun J => π.Tag J = x).card ≤ 2 ^ Fintype.card ι :=
  calc
    (π.boxes.filterₓ fun J => π.Tag J = x).card ≤
        (π.boxes.filterₓ fun J : Box ι => x ∈ J.Icc).card :=
      by
      refine' Finset.card_le_of_subset fun J hJ => _
      rw [Finset.mem_filter] at hJ⊢; rcases hJ with ⟨hJ, rfl⟩
      exact ⟨hJ, h J hJ⟩
    _ ≤ 2 ^ Fintype.card ι := π.toPrepartition.card_filter_mem_Icc_le x
    
#align box_integral.tagged_prepartition.is_Henstock.card_filter_tag_eq_le BoxIntegral.TaggedPrepartition.IsHenstock.card_filter_tag_eq_le
-/

/- warning: box_integral.tagged_prepartition.is_subordinate -> BoxIntegral.TaggedPrepartition.IsSubordinate is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.{u1} ι I) -> ((ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> Prop
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.{u1} ι I) -> ((ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> Prop
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate BoxIntegral.TaggedPrepartition.IsSubordinateₓ'. -/
/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included in
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def IsSubordinate [Fintype ι] (π : TaggedPrepartition I) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  ∀ J ∈ π, (J : _).Icc ⊆ closedBall (π.Tag J) (r <| π.Tag J)
#align box_integral.tagged_prepartition.is_subordinate BoxIntegral.TaggedPrepartition.IsSubordinate

variable {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}

/- warning: box_integral.tagged_prepartition.is_subordinate_bUnion_tagged -> BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTagged is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.Prepartition.{u1} ι I} {πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.TaggedPrepartition.{u1} ι J}, Iff (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.Prepartition.biUnionTagged.{u1} ι I π πi) r) (forall (J : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J π) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι J _inst_1 (πi J) r))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.Prepartition.{u1} ι I} {πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.TaggedPrepartition.{u1} ι J}, Iff (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.Prepartition.biUnionTagged.{u1} ι I π πi) r) (forall (J : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J π) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι J _inst_1 (πi J) r))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate_bUnion_tagged BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTaggedₓ'. -/
@[simp]
theorem isSubordinate_biUnionTagged [Fintype ι] {π : Prepartition I}
    {πi : ∀ J, TaggedPrepartition J} :
    IsSubordinate (π.biUnionTagged πi) r ↔ ∀ J ∈ π, (πi J).IsSubordinate r :=
  π.forall_biUnionTagged (fun x J => J.Icc ⊆ closedBall x (r x)) πi
#align box_integral.tagged_prepartition.is_subordinate_bUnion_tagged BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTagged

/- warning: box_integral.tagged_prepartition.is_subordinate.bUnion_prepartition -> BoxIntegral.TaggedPrepartition.IsSubordinate.biUnionPrepartition is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π : BoxIntegral.TaggedPrepartition.{u1} ι I} {r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) -> (forall (πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.Prepartition.{u1} ι J), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.biUnionPrepartition.{u1} ι I π πi) r)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π : BoxIntegral.TaggedPrepartition.{u1} ι I} {r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) -> (forall (πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.Prepartition.{u1} ι J), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.biUnionPrepartition.{u1} ι I π πi) r)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.biUnionPrepartitionₓ'. -/
theorem IsSubordinate.biUnionPrepartition [Fintype ι] (h : IsSubordinate π r)
    (πi : ∀ J, Prepartition J) : IsSubordinate (π.biUnionPrepartition πi) r := fun J hJ =>
  Subset.trans (Box.le_iff_Icc.1 <| π.toPrepartition.le_biUnionIndex hJ) <|
    h _ <| π.toPrepartition.biUnionIndex_mem hJ
#align box_integral.tagged_prepartition.is_subordinate.bUnion_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.biUnionPrepartition

/- warning: box_integral.tagged_prepartition.is_subordinate.inf_prepartition -> BoxIntegral.TaggedPrepartition.IsSubordinate.infPrepartition is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π : BoxIntegral.TaggedPrepartition.{u1} ι I} {r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) -> (forall (π' : BoxIntegral.Prepartition.{u1} ι I), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.infPrepartition.{u1} ι I π π') r)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π : BoxIntegral.TaggedPrepartition.{u1} ι I} {r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) -> (forall (π' : BoxIntegral.Prepartition.{u1} ι I), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.infPrepartition.{u1} ι I π π') r)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate.inf_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.infPrepartitionₓ'. -/
theorem IsSubordinate.infPrepartition [Fintype ι] (h : IsSubordinate π r) (π' : Prepartition I) :
    IsSubordinate (π.infPrepartition π') r :=
  h.biUnionPrepartition _
#align box_integral.tagged_prepartition.is_subordinate.inf_prepartition BoxIntegral.TaggedPrepartition.IsSubordinate.infPrepartition

/- warning: box_integral.tagged_prepartition.is_subordinate.mono' -> BoxIntegral.TaggedPrepartition.IsSubordinate.mono' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {r₁ : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} {r₂ : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₁) -> (forall (J : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π) -> (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (r₁ (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π J)) (r₂ (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π J)))) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₂)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {r₁ : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} {r₂ : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₁) -> (forall (J : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π) -> (LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (r₁ (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π J)) (r₂ (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π J)))) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₂)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate.mono' BoxIntegral.TaggedPrepartition.IsSubordinate.mono'ₓ'. -/
theorem IsSubordinate.mono' [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ J ∈ π, r₁ (π.Tag J) ≤ r₂ (π.Tag J)) : π.IsSubordinate r₂ := fun J hJ x hx =>
  closedBall_subset_closedBall (h _ hJ) (hr₁ _ hJ hx)
#align box_integral.tagged_prepartition.is_subordinate.mono' BoxIntegral.TaggedPrepartition.IsSubordinate.mono'

/- warning: box_integral.tagged_prepartition.is_subordinate.mono -> BoxIntegral.TaggedPrepartition.IsSubordinate.mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {r₁ : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} {r₂ : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₁) -> (forall (x : ι -> Real), (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)) -> (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (r₁ x) (r₂ x))) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₂)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {r₁ : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} {r₂ : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₁) -> (forall (x : ι -> Real), (Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)) -> (LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (r₁ x) (r₂ x))) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r₂)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate.mono BoxIntegral.TaggedPrepartition.IsSubordinate.monoₓ'. -/
theorem IsSubordinate.mono [Fintype ι] {π : TaggedPrepartition I} (hr₁ : π.IsSubordinate r₁)
    (h : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) : π.IsSubordinate r₂ :=
  hr₁.mono' fun J _ => h _ <| π.tag_mem_Icc J
#align box_integral.tagged_prepartition.is_subordinate.mono BoxIntegral.TaggedPrepartition.IsSubordinate.mono

/- warning: box_integral.tagged_prepartition.is_subordinate.diam_le -> BoxIntegral.TaggedPrepartition.IsSubordinate.diam_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) -> (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.hasMem.{u1} (BoxIntegral.Box.{u1} ι)) J (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π))) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (b : ι) => Real.pseudoMetricSpace)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) J)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))))) (r (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π J)))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι] {π : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π r) -> (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.instMembershipFinset.{u1} (BoxIntegral.Box.{u1} ι)) J (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π))) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (b : ι) => Real.pseudoMetricSpace)) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) J)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (r (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π J)))))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate.diam_le BoxIntegral.TaggedPrepartition.IsSubordinate.diam_leₓ'. -/
theorem IsSubordinate.diam_le [Fintype ι] {π : TaggedPrepartition I} (h : π.IsSubordinate r)
    (hJ : J ∈ π.boxes) : diam J.Icc ≤ 2 * r (π.Tag J) :=
  calc
    diam J.Icc ≤ diam (closedBall (π.Tag J) (r <| π.Tag J)) := diam_mono (h J hJ) bounded_closedBall
    _ ≤ 2 * r (π.Tag J) := diam_closedBall (le_of_lt (r _).2)
    
#align box_integral.tagged_prepartition.is_subordinate.diam_le BoxIntegral.TaggedPrepartition.IsSubordinate.diam_le

/- warning: box_integral.tagged_prepartition.single -> BoxIntegral.TaggedPrepartition.single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι) (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) -> (forall (x : ι -> Real), (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)) -> (BoxIntegral.TaggedPrepartition.{u1} ι I))
but is expected to have type
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι) (J : BoxIntegral.Box.{u1} ι), (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) -> (forall (x : ι -> Real), (Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)) -> (BoxIntegral.TaggedPrepartition.{u1} ι I))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.single BoxIntegral.TaggedPrepartition.singleₓ'. -/
/-- Tagged prepartition with single box and prescribed tag. -/
@[simps (config := { fullyApplied := false })]
def single (I J : Box ι) (hJ : J ≤ I) (x : ι → ℝ) (h : x ∈ I.Icc) : TaggedPrepartition I :=
  ⟨Prepartition.single I J hJ, fun J => x, fun J => h⟩
#align box_integral.tagged_prepartition.single BoxIntegral.TaggedPrepartition.single

/- warning: box_integral.tagged_prepartition.mem_single -> BoxIntegral.TaggedPrepartition.mem_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} {J' : BoxIntegral.Box.{u1} ι} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J' (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) J' J)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} {J' : BoxIntegral.Box.{u1} ι} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J' (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) J' J)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.mem_single BoxIntegral.TaggedPrepartition.mem_singleₓ'. -/
@[simp]
theorem mem_single {J'} (hJ : J ≤ I) (h : x ∈ I.Icc) : J' ∈ single I J hJ x h ↔ J' = J :=
  Finset.mem_singleton
#align box_integral.tagged_prepartition.mem_single BoxIntegral.TaggedPrepartition.mem_single

instance (I : Box ι) : Inhabited (TaggedPrepartition I) :=
  ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

/- warning: box_integral.tagged_prepartition.is_partition_single_iff -> BoxIntegral.TaggedPrepartition.isPartition_single_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) J I)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) J I)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_partition_single_iff BoxIntegral.TaggedPrepartition.isPartition_single_iffₓ'. -/
theorem isPartition_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
    (single I J hJ x h).IsPartition ↔ J = I :=
  Prepartition.isPartition_single_iff hJ
#align box_integral.tagged_prepartition.is_partition_single_iff BoxIntegral.TaggedPrepartition.isPartition_single_iff

/- warning: box_integral.tagged_prepartition.is_partition_single -> BoxIntegral.TaggedPrepartition.isPartition_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I I (le_rfl.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)) I) x h)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), BoxIntegral.TaggedPrepartition.IsPartition.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I I (le_rfl.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)) I) x h)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_partition_single BoxIntegral.TaggedPrepartition.isPartition_singleₓ'. -/
theorem isPartition_single (h : x ∈ I.Icc) : (single I I le_rfl x h).IsPartition :=
  Prepartition.isPartitionTop I
#align box_integral.tagged_prepartition.is_partition_single BoxIntegral.TaggedPrepartition.isPartition_single

/- warning: box_integral.tagged_prepartition.forall_mem_single -> BoxIntegral.TaggedPrepartition.forall_mem_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (p : (ι -> Real) -> (BoxIntegral.Box.{u1} ι) -> Prop) (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (forall (J' : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J' (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) -> (p (BoxIntegral.TaggedPrepartition.tag.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h) J') J')) (p x J)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (p : (ι -> Real) -> (BoxIntegral.Box.{u1} ι) -> Prop) (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (forall (J' : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J' (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) -> (p (BoxIntegral.TaggedPrepartition.tag.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h) J') J')) (p x J)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.forall_mem_single BoxIntegral.TaggedPrepartition.forall_mem_singleₓ'. -/
theorem forall_mem_single (p : (ι → ℝ) → Box ι → Prop) (hJ : J ≤ I) (h : x ∈ I.Icc) :
    (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).Tag J') J') ↔ p x J := by simp
#align box_integral.tagged_prepartition.forall_mem_single BoxIntegral.TaggedPrepartition.forall_mem_single

/- warning: box_integral.tagged_prepartition.is_Henstock_single_iff -> BoxIntegral.TaggedPrepartition.isHenstock_single_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) J))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) J) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) J))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_Henstock_single_iff BoxIntegral.TaggedPrepartition.isHenstock_single_iffₓ'. -/
@[simp]
theorem isHenstock_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
    IsHenstock (single I J hJ x h) ↔ x ∈ J.Icc :=
  forall_mem_single (fun x J => x ∈ J.Icc) hJ h
#align box_integral.tagged_prepartition.is_Henstock_single_iff BoxIntegral.TaggedPrepartition.isHenstock_single_iff

/- warning: box_integral.tagged_prepartition.is_Henstock_single -> BoxIntegral.TaggedPrepartition.isHenstock_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I I (le_rfl.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)) I) x h)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I I (le_rfl.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)) I) x h)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_Henstock_single BoxIntegral.TaggedPrepartition.isHenstock_singleₓ'. -/
@[simp]
theorem isHenstock_single (h : x ∈ I.Icc) : IsHenstock (single I I le_rfl x h) :=
  (isHenstock_single_iff (le_refl I) h).2 h
#align box_integral.tagged_prepartition.is_Henstock_single BoxIntegral.TaggedPrepartition.isHenstock_single

/- warning: box_integral.tagged_prepartition.is_subordinate_single -> BoxIntegral.TaggedPrepartition.isSubordinate_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} {r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι] (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h) r) (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.hasSubset.{u1} (ι -> Real)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) J) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (b : ι) => Real.pseudoMetricSpace)) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))))) (r x))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} {r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι] (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Iff (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h) r) (HasSubset.Subset.{u1} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) J) (Set.instHasSubsetSet.{u1} (ι -> Real)) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) J) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (b : ι) => Real.pseudoMetricSpace)) x (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (r x))))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate_single BoxIntegral.TaggedPrepartition.isSubordinate_singleₓ'. -/
@[simp]
theorem isSubordinate_single [Fintype ι] (hJ : J ≤ I) (h : x ∈ I.Icc) :
    IsSubordinate (single I J hJ x h) r ↔ J.Icc ⊆ closedBall x (r x) :=
  forall_mem_single (fun x J => J.Icc ⊆ closedBall x (r x)) hJ h
#align box_integral.tagged_prepartition.is_subordinate_single BoxIntegral.TaggedPrepartition.isSubordinate_single

/- warning: box_integral.tagged_prepartition.Union_single -> BoxIntegral.TaggedPrepartition.iUnion_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) J)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h)) (BoxIntegral.Box.toSet.{u1} ι J)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.Union_single BoxIntegral.TaggedPrepartition.iUnion_singleₓ'. -/
@[simp]
theorem iUnion_single (hJ : J ≤ I) (h : x ∈ I.Icc) : (single I J hJ x h).iUnion = J :=
  Prepartition.iUnion_single hJ
#align box_integral.tagged_prepartition.Union_single BoxIntegral.TaggedPrepartition.iUnion_single

/- warning: box_integral.tagged_prepartition.disj_union -> BoxIntegral.TaggedPrepartition.disjUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I), (Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)) -> (BoxIntegral.TaggedPrepartition.{u1} ι I)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I) (π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I), (Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)) -> (BoxIntegral.TaggedPrepartition.{u1} ι I)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.disj_union BoxIntegral.TaggedPrepartition.disjUnionₓ'. -/
/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disjUnion (π₁ π₂ : TaggedPrepartition I) (h : Disjoint π₁.iUnion π₂.iUnion) :
    TaggedPrepartition I
    where
  toPrepartition := π₁.toPrepartition.disjUnion π₂.toPrepartition h
  Tag := π₁.boxes.piecewise π₁.Tag π₂.Tag
  tag_mem_Icc J := by
    dsimp only [Finset.piecewise]
    split_ifs
    exacts[π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]
#align box_integral.tagged_prepartition.disj_union BoxIntegral.TaggedPrepartition.disjUnion

/- warning: box_integral.tagged_prepartition.disj_union_boxes -> BoxIntegral.TaggedPrepartition.disjUnion_boxes is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Eq.{succ u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h))) (Union.union.{u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.hasUnion.{u1} (BoxIntegral.Box.{u1} ι) (fun (a : BoxIntegral.Box.{u1} ι) (b : BoxIntegral.Box.{u1} ι) => Classical.propDecidable (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) a b))) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π₁)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π₂)))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Eq.{succ u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h))) (Union.union.{u1} (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.instUnionFinset.{u1} (BoxIntegral.Box.{u1} ι) (fun (a : BoxIntegral.Box.{u1} ι) (b : BoxIntegral.Box.{u1} ι) => Classical.propDecidable (Eq.{succ u1} (BoxIntegral.Box.{u1} ι) a b))) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π₁)) (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π₂)))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.disj_union_boxes BoxIntegral.TaggedPrepartition.disjUnion_boxesₓ'. -/
@[simp]
theorem disjUnion_boxes (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).boxes = π₁.boxes ∪ π₂.boxes :=
  rfl
#align box_integral.tagged_prepartition.disj_union_boxes BoxIntegral.TaggedPrepartition.disjUnion_boxes

/- warning: box_integral.tagged_prepartition.mem_disj_union -> BoxIntegral.TaggedPrepartition.mem_disjUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Iff (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h)) (Or (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π₁) (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π₂))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Iff (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h)) (Or (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π₁) (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π₂))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.mem_disj_union BoxIntegral.TaggedPrepartition.mem_disjUnionₓ'. -/
@[simp]
theorem mem_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    J ∈ π₁.disjUnion π₂ h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
  Finset.mem_union
#align box_integral.tagged_prepartition.mem_disj_union BoxIntegral.TaggedPrepartition.mem_disjUnion

/- warning: box_integral.tagged_prepartition.Union_disj_union -> BoxIntegral.TaggedPrepartition.iUnion_disjUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h)) (Union.union.{u1} (Set.{u1} (ι -> Real)) (Set.hasUnion.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h)) (Union.union.{u1} (Set.{u1} (ι -> Real)) (Set.instUnionSet.{u1} (ι -> Real)) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.Union_disj_union BoxIntegral.TaggedPrepartition.iUnion_disjUnionₓ'. -/
@[simp]
theorem iUnion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).iUnion = π₁.iUnion ∪ π₂.iUnion :=
  Prepartition.iUnion_disjUnion _
#align box_integral.tagged_prepartition.Union_disj_union BoxIntegral.TaggedPrepartition.iUnion_disjUnion

/- warning: box_integral.tagged_prepartition.disj_union_tag_of_mem_left -> BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π₁) -> (Eq.{succ u1} (ι -> Real) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) J) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π₁ J))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π₁) -> (Eq.{succ u1} (ι -> Real) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) J) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π₁ J))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.disj_union_tag_of_mem_left BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_leftₓ'. -/
theorem disjUnion_tag_of_mem_left (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J ∈ π₁) :
    (π₁.disjUnion π₂ h).Tag J = π₁.Tag J :=
  dif_pos hJ
#align box_integral.tagged_prepartition.disj_union_tag_of_mem_left BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_left

/- warning: box_integral.tagged_prepartition.disj_union_tag_of_mem_right -> BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π₂) -> (Eq.{succ u1} (ι -> Real) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) J) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π₂ J))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π₂) -> (Eq.{succ u1} (ι -> Real) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) J) (BoxIntegral.TaggedPrepartition.tag.{u1} ι I π₂ J))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.disj_union_tag_of_mem_right BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_rightₓ'. -/
theorem disjUnion_tag_of_mem_right (h : Disjoint π₁.iUnion π₂.iUnion) (hJ : J ∈ π₂) :
    (π₁.disjUnion π₂ h).Tag J = π₂.Tag J :=
  dif_neg fun h₁ => h.le_bot ⟨π₁.subset_iUnion h₁ J.upper_mem, π₂.subset_iUnion hJ J.upper_mem⟩
#align box_integral.tagged_prepartition.disj_union_tag_of_mem_right BoxIntegral.TaggedPrepartition.disjUnion_tag_of_mem_right

/- warning: box_integral.tagged_prepartition.is_subordinate.disj_union -> BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} {r : (ι -> Real) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π₁ r) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π₂ r) -> (forall (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) r)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} {r : (ι -> Real) -> (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))} [_inst_1 : Fintype.{u1} ι], (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π₁ r) -> (BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 π₂ r) -> (forall (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), BoxIntegral.TaggedPrepartition.IsSubordinate.{u1} ι I _inst_1 (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) r)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_subordinate.disj_union BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnionₓ'. -/
theorem IsSubordinate.disjUnion [Fintype ι] (h₁ : IsSubordinate π₁ r) (h₂ : IsSubordinate π₂ r)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsSubordinate (π₁.disjUnion π₂ h) r :=
  by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disj_union_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disj_union_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
#align box_integral.tagged_prepartition.is_subordinate.disj_union BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnion

/- warning: box_integral.tagged_prepartition.is_Henstock.disj_union -> BoxIntegral.TaggedPrepartition.IsHenstock.disjUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π₁) -> (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π₂) -> (forall (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I}, (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π₁) -> (BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I π₂) -> (forall (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), BoxIntegral.TaggedPrepartition.IsHenstock.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.is_Henstock.disj_union BoxIntegral.TaggedPrepartition.IsHenstock.disjUnionₓ'. -/
theorem IsHenstock.disjUnion (h₁ : IsHenstock π₁) (h₂ : IsHenstock π₂)
    (h : Disjoint π₁.iUnion π₂.iUnion) : IsHenstock (π₁.disjUnion π₂ h) :=
  by
  refine' fun J hJ => (Finset.mem_union.1 hJ).elim (fun hJ => _) fun hJ => _
  · rw [disj_union_tag_of_mem_left _ hJ]
    exact h₁ _ hJ
  · rw [disj_union_tag_of_mem_right _ hJ]
    exact h₂ _ hJ
#align box_integral.tagged_prepartition.is_Henstock.disj_union BoxIntegral.TaggedPrepartition.IsHenstock.disjUnion

#print BoxIntegral.TaggedPrepartition.embedBox /-
/-- If `I ≤ J`, then every tagged prepartition of `I` is a tagged prepartition of `J`. -/
def embedBox (I J : Box ι) (h : I ≤ J) : TaggedPrepartition I ↪ TaggedPrepartition J
    where
  toFun π :=
    { π with
      le_of_mem' := fun J' hJ' => (π.le_of_mem' J' hJ').trans h
      tag_mem_Icc := fun J => Box.le_iff_Icc.1 h (π.tag_mem_Icc J) }
  inj' := by
    rintro ⟨⟨b₁, h₁le, h₁d⟩, t₁, ht₁⟩ ⟨⟨b₂, h₂le, h₂d⟩, t₂, ht₂⟩ H
    simpa using H
#align box_integral.tagged_prepartition.embed_box BoxIntegral.TaggedPrepartition.embedBox
-/

section Distortion

variable [Fintype ι] (π)

open Finset

#print BoxIntegral.TaggedPrepartition.distortion /-
/-- The distortion of a tagged prepartition is the maximum of distortions of its boxes. -/
def distortion : ℝ≥0 :=
  π.toPrepartition.distortion
#align box_integral.tagged_prepartition.distortion BoxIntegral.TaggedPrepartition.distortion
-/

/- warning: box_integral.tagged_prepartition.distortion_le_of_mem -> BoxIntegral.TaggedPrepartition.distortion_le_of_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) [_inst_1 : Fintype.{u1} ι], (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (BoxIntegral.Box.distortion.{u1} ι _inst_1 J) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) [_inst_1 : Fintype.{u1} ι], (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (BoxIntegral.Box.distortion.{u1} ι _inst_1 J) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_le_of_mem BoxIntegral.TaggedPrepartition.distortion_le_of_memₓ'. -/
theorem distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
  le_sup h
#align box_integral.tagged_prepartition.distortion_le_of_mem BoxIntegral.TaggedPrepartition.distortion_le_of_mem

/- warning: box_integral.tagged_prepartition.distortion_le_iff -> BoxIntegral.TaggedPrepartition.distortion_le_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) [_inst_1 : Fintype.{u1} ι] {c : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1) c) (forall (J : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.hasMem.{u1} ι I) J π) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (BoxIntegral.Box.distortion.{u1} ι _inst_1 J) c))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) [_inst_1 : Fintype.{u1} ι] {c : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1) c) (forall (J : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.TaggedPrepartition.{u1} ι I) (BoxIntegral.TaggedPrepartition.instMembershipBoxTaggedPrepartition.{u1} ι I) J π) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (BoxIntegral.Box.distortion.{u1} ι _inst_1 J) c))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_le_iff BoxIntegral.TaggedPrepartition.distortion_le_iffₓ'. -/
theorem distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, Box.distortion J ≤ c :=
  Finset.sup_le_iff
#align box_integral.tagged_prepartition.distortion_le_iff BoxIntegral.TaggedPrepartition.distortion_le_iff

/- warning: box_integral.prepartition.distortion_bUnion_tagged -> BoxIntegral.Prepartition.distortion_biUnionTagged is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Fintype.{u1} ι] (π : BoxIntegral.Prepartition.{u1} ι I) (πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.TaggedPrepartition.{u1} ι J), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.Prepartition.biUnionTagged.{u1} ι I π πi) _inst_1) (Finset.sup.{0, u1} NNReal (BoxIntegral.Box.{u1} ι) NNReal.semilatticeSup NNReal.orderBot (BoxIntegral.Prepartition.boxes.{u1} ι I π) (fun (J : BoxIntegral.Box.{u1} ι) => BoxIntegral.TaggedPrepartition.distortion.{u1} ι J (πi J) _inst_1))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Fintype.{u1} ι] (π : BoxIntegral.Prepartition.{u1} ι I) (πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.TaggedPrepartition.{u1} ι J), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.Prepartition.biUnionTagged.{u1} ι I π πi) _inst_1) (Finset.sup.{0, u1} NNReal (BoxIntegral.Box.{u1} ι) instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring (BoxIntegral.Prepartition.boxes.{u1} ι I π) (fun (J : BoxIntegral.Box.{u1} ι) => BoxIntegral.TaggedPrepartition.distortion.{u1} ι J (πi J) _inst_1))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.distortion_bUnion_tagged BoxIntegral.Prepartition.distortion_biUnionTaggedₓ'. -/
@[simp]
theorem BoxIntegral.Prepartition.distortion_biUnionTagged (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    (π.biUnionTagged πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_biUnion _ _
#align box_integral.prepartition.distortion_bUnion_tagged BoxIntegral.Prepartition.distortion_biUnionTagged

/- warning: box_integral.tagged_prepartition.distortion_bUnion_prepartition -> BoxIntegral.TaggedPrepartition.distortion_biUnionPrepartition is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Fintype.{u1} ι] (π : BoxIntegral.TaggedPrepartition.{u1} ι I) (πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.Prepartition.{u1} ι J), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.biUnionPrepartition.{u1} ι I π πi) _inst_1) (Finset.sup.{0, u1} NNReal (BoxIntegral.Box.{u1} ι) NNReal.semilatticeSup NNReal.orderBot (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π)) (fun (J : BoxIntegral.Box.{u1} ι) => BoxIntegral.Prepartition.distortion.{u1} ι J (πi J) _inst_1))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Fintype.{u1} ι] (π : BoxIntegral.TaggedPrepartition.{u1} ι I) (πi : forall (J : BoxIntegral.Box.{u1} ι), BoxIntegral.Prepartition.{u1} ι J), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.biUnionPrepartition.{u1} ι I π πi) _inst_1) (Finset.sup.{0, u1} NNReal (BoxIntegral.Box.{u1} ι) instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.TaggedPrepartition.toPrepartition.{u1} ι I π)) (fun (J : BoxIntegral.Box.{u1} ι) => BoxIntegral.Prepartition.distortion.{u1} ι J (πi J) _inst_1))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_bUnion_prepartition BoxIntegral.TaggedPrepartition.distortion_biUnionPrepartitionₓ'. -/
@[simp]
theorem distortion_biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) :
    (π.biUnionPrepartition πi).distortion = π.boxes.sup fun J => (πi J).distortion :=
  sup_biUnion _ _
#align box_integral.tagged_prepartition.distortion_bUnion_prepartition BoxIntegral.TaggedPrepartition.distortion_biUnionPrepartition

/- warning: box_integral.tagged_prepartition.distortion_disj_union -> BoxIntegral.TaggedPrepartition.distortion_disjUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} [_inst_1 : Fintype.{u1} ι] (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.completeBooleanAlgebra.{u1} (ι -> Real))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real)))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) _inst_1) (LinearOrder.max.{0} NNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot)) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π₁ _inst_1) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π₂ _inst_1))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {π₁ : BoxIntegral.TaggedPrepartition.{u1} ι I} {π₂ : BoxIntegral.TaggedPrepartition.{u1} ι I} [_inst_1 : Fintype.{u1} ι] (h : Disjoint.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (ι -> Real)) (Preorder.toLE.{u1} (Set.{u1} (ι -> Real)) (PartialOrder.toPreorder.{u1} (Set.{u1} (ι -> Real)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (ι -> Real)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (ι -> Real)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (ι -> Real)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (ι -> Real)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (ι -> Real)) (Set.instCompleteBooleanAlgebraSet.{u1} (ι -> Real))))))) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₁) (BoxIntegral.TaggedPrepartition.iUnion.{u1} ι I π₂)), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.disjUnion.{u1} ι I π₁ π₂ h) _inst_1) (Max.max.{0} NNReal (CanonicallyLinearOrderedSemifield.toMax.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π₁ _inst_1) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π₂ _inst_1))
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_disj_union BoxIntegral.TaggedPrepartition.distortion_disjUnionₓ'. -/
@[simp]
theorem distortion_disjUnion (h : Disjoint π₁.iUnion π₂.iUnion) :
    (π₁.disjUnion π₂ h).distortion = max π₁.distortion π₂.distortion :=
  sup_union
#align box_integral.tagged_prepartition.distortion_disj_union BoxIntegral.TaggedPrepartition.distortion_disjUnion

#print BoxIntegral.TaggedPrepartition.distortion_of_const /-
theorem distortion_of_const {c} (h₁ : π.boxes.Nonempty) (h₂ : ∀ J ∈ π, Box.distortion J = c) :
    π.distortion = c :=
  (sup_congr rfl h₂).trans (sup_const h₁ _)
#align box_integral.tagged_prepartition.distortion_of_const BoxIntegral.TaggedPrepartition.distortion_of_const
-/

/- warning: box_integral.tagged_prepartition.distortion_single -> BoxIntegral.TaggedPrepartition.distortion_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} [_inst_1 : Fintype.{u1} ι] (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J I) (h : Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.hasLe.{u1} ι) (Set.hasLe.{u1} (ι -> Real))) (fun (_x : RelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) => (BoxIntegral.Box.{u1} ι) -> (Set.{u1} (ι -> Real))) (RelEmbedding.hasCoeToFun.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.hasLe.{u1} (ι -> Real)))) (BoxIntegral.Box.Icc.{u1} ι) I)), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h) _inst_1) (BoxIntegral.Box.distortion.{u1} ι _inst_1 J)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {x : ι -> Real} [_inst_1 : Fintype.{u1} ι] (hJ : LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J I) (h : Membership.mem.{u1, u1} (ι -> Real) ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) I) (Set.instMembershipSet.{u1} (ι -> Real)) x (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (fun (_x : BoxIntegral.Box.{u1} ι) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : BoxIntegral.Box.{u1} ι) => Set.{u1} (ι -> Real)) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.instLEBox.{u1} ι) (Set.instLESet.{u1} (ι -> Real))) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : BoxIntegral.Box.{u1} ι) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : BoxIntegral.Box.{u1} ι) => LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} (ι -> Real)) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} (ι -> Real)) => LE.le.{u1} (Set.{u1} (ι -> Real)) (Set.instLESet.{u1} (ι -> Real)) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (BoxIntegral.Box.Icc.{u1} ι) I)), Eq.{1} NNReal (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.single.{u1} ι I J hJ x h) _inst_1) (BoxIntegral.Box.distortion.{u1} ι _inst_1 J)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_single BoxIntegral.TaggedPrepartition.distortion_singleₓ'. -/
@[simp]
theorem distortion_single (hJ : J ≤ I) (h : x ∈ I.Icc) :
    distortion (single I J hJ x h) = J.distortion :=
  sup_singleton
#align box_integral.tagged_prepartition.distortion_single BoxIntegral.TaggedPrepartition.distortion_single

/- warning: box_integral.tagged_prepartition.distortion_filter_le -> BoxIntegral.TaggedPrepartition.distortion_filter_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) [_inst_1 : Fintype.{u1} ι] (p : (BoxIntegral.Box.{u1} ι) -> Prop), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.filter.{u1} ι I π p) _inst_1) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} (π : BoxIntegral.TaggedPrepartition.{u1} ι I) [_inst_1 : Fintype.{u1} ι] (p : (BoxIntegral.Box.{u1} ι) -> Prop), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I (BoxIntegral.TaggedPrepartition.filter.{u1} ι I π p) _inst_1) (BoxIntegral.TaggedPrepartition.distortion.{u1} ι I π _inst_1)
Case conversion may be inaccurate. Consider using '#align box_integral.tagged_prepartition.distortion_filter_le BoxIntegral.TaggedPrepartition.distortion_filter_leₓ'. -/
theorem distortion_filter_le (p : Box ι → Prop) : (π.filterₓ p).distortion ≤ π.distortion :=
  sup_mono (filter_subset _ _)
#align box_integral.tagged_prepartition.distortion_filter_le BoxIntegral.TaggedPrepartition.distortion_filter_le

end Distortion

end TaggedPrepartition

end BoxIntegral

