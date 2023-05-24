/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module analysis.normed.field.basic
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Instances.Ennreal

/-!
# Normed fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

open Filter Metric

open Topology BigOperators NNReal ENNReal uniformity Pointwise

#print NonUnitalSeminormedRing /-
/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalSeminormedRing (α : Type _) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align non_unital_semi_normed_ring NonUnitalSeminormedRing
-/

#print SeminormedRing /-
/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SeminormedRing (α : Type _) extends Norm α, Ring α, PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align semi_normed_ring SeminormedRing
-/

#print SeminormedRing.toNonUnitalSeminormedRing /-
-- see Note [lower instance priority]
/-- A seminormed ring is a non-unital seminormed ring. -/
instance (priority := 100) SeminormedRing.toNonUnitalSeminormedRing [β : SeminormedRing α] :
    NonUnitalSeminormedRing α :=
  { β with }
#align semi_normed_ring.to_non_unital_semi_normed_ring SeminormedRing.toNonUnitalSeminormedRing
-/

#print NonUnitalNormedRing /-
/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalNormedRing (α : Type _) extends Norm α, NonUnitalRing α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align non_unital_normed_ring NonUnitalNormedRing
-/

#print NonUnitalNormedRing.toNonUnitalSeminormedRing /-
-- see Note [lower instance priority]
/-- A non-unital normed ring is a non-unital seminormed ring. -/
instance (priority := 100) NonUnitalNormedRing.toNonUnitalSeminormedRing
    [β : NonUnitalNormedRing α] : NonUnitalSeminormedRing α :=
  { β with }
#align non_unital_normed_ring.to_non_unital_semi_normed_ring NonUnitalNormedRing.toNonUnitalSeminormedRing
-/

#print NormedRing /-
/-- A normed ring is a ring endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedRing (α : Type _) extends Norm α, Ring α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align normed_ring NormedRing
-/

#print NormedDivisionRing /-
/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`‖x y‖ = ‖x‖ ‖y‖`. -/
class NormedDivisionRing (α : Type _) extends Norm α, DivisionRing α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b
#align normed_division_ring NormedDivisionRing
-/

#print NormedDivisionRing.toNormedRing /-
-- see Note [lower instance priority]
/-- A normed division ring is a normed ring. -/
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul := fun a b => (NormedDivisionRing.norm_mul' a b).le }
#align normed_division_ring.to_normed_ring NormedDivisionRing.toNormedRing
-/

#print NormedRing.toSeminormedRing /-
-- see Note [lower instance priority]
/-- A normed ring is a seminormed ring. -/
instance (priority := 100) NormedRing.toSeminormedRing [β : NormedRing α] : SeminormedRing α :=
  { β with }
#align normed_ring.to_semi_normed_ring NormedRing.toSeminormedRing
-/

#print NormedRing.toNonUnitalNormedRing /-
-- see Note [lower instance priority]
/-- A normed ring is a non-unital normed ring. -/
instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] :
    NonUnitalNormedRing α :=
  { β with }
#align normed_ring.to_non_unital_normed_ring NormedRing.toNonUnitalNormedRing
-/

#print SeminormedCommRing /-
/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SeminormedCommRing (α : Type _) extends SeminormedRing α where
  mul_comm : ∀ x y : α, x * y = y * x
#align semi_normed_comm_ring SeminormedCommRing
-/

#print NormedCommRing /-
/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedCommRing (α : Type _) extends NormedRing α where
  mul_comm : ∀ x y : α, x * y = y * x
#align normed_comm_ring NormedCommRing
-/

#print NormedCommRing.toSeminormedCommRing /-
-- see Note [lower instance priority]
/-- A normed commutative ring is a seminormed commutative ring. -/
instance (priority := 100) NormedCommRing.toSeminormedCommRing [β : NormedCommRing α] :
    SeminormedCommRing α :=
  { β with }
#align normed_comm_ring.to_semi_normed_comm_ring NormedCommRing.toSeminormedCommRing
-/

instance : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with norm_mul := fun _ _ => by simp }

#print NormOneClass /-
/-- A mixin class with the axiom `‖1‖ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class NormOneClass (α : Type _) [Norm α] [One α] : Prop where
  norm_one : ‖(1 : α)‖ = 1
#align norm_one_class NormOneClass
-/

export NormOneClass (norm_one)

attribute [simp] norm_one

#print nnnorm_one /-
@[simp]
theorem nnnorm_one [SeminormedAddCommGroup α] [One α] [NormOneClass α] : ‖(1 : α)‖₊ = 1 :=
  NNReal.eq norm_one
#align nnnorm_one nnnorm_one
-/

#print NormOneClass.nontrivial /-
theorem NormOneClass.nontrivial (α : Type _) [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    Nontrivial α :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp
#align norm_one_class.nontrivial NormOneClass.nontrivial
-/

#print SeminormedCommRing.toCommRing /-
-- see Note [lower instance priority]
instance (priority := 100) SeminormedCommRing.toCommRing [β : SeminormedCommRing α] : CommRing α :=
  { β with }
#align semi_normed_comm_ring.to_comm_ring SeminormedCommRing.toCommRing
-/

#print NonUnitalNormedRing.toNormedAddCommGroup /-
-- see Note [lower instance priority]
instance (priority := 100) NonUnitalNormedRing.toNormedAddCommGroup [β : NonUnitalNormedRing α] :
    NormedAddCommGroup α :=
  { β with }
#align non_unital_normed_ring.to_normed_add_comm_group NonUnitalNormedRing.toNormedAddCommGroup
-/

#print NonUnitalSeminormedRing.toSeminormedAddCommGroup /-
-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedRing.toSeminormedAddCommGroup
    [NonUnitalSeminormedRing α] : SeminormedAddCommGroup α :=
  { ‹NonUnitalSeminormedRing α› with }
#align non_unital_semi_normed_ring.to_seminormed_add_comm_group NonUnitalSeminormedRing.toSeminormedAddCommGroup
-/

instance [SeminormedAddCommGroup α] [One α] [NormOneClass α] : NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

/- warning: prod.norm_one_class -> Prod.normOneClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : NormOneClass.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) _inst_2] [_inst_4 : SeminormedAddCommGroup.{u2} β] [_inst_5 : One.{u2} β] [_inst_6 : NormOneClass.{u2} β (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_4) _inst_5], NormOneClass.{max u1 u2} (Prod.{u1, u2} α β) (Prod.hasNorm.{u1, u2} α β (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_4)) (Prod.hasOne.{u1, u2} α β _inst_2 _inst_5)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : NormOneClass.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) _inst_2] [_inst_4 : SeminormedAddCommGroup.{u2} β] [_inst_5 : One.{u2} β] [_inst_6 : NormOneClass.{u2} β (SeminormedAddCommGroup.toNorm.{u2} β _inst_4) _inst_5], NormOneClass.{max u2 u1} (Prod.{u1, u2} α β) (Prod.toNorm.{u1, u2} α β (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) (SeminormedAddCommGroup.toNorm.{u2} β _inst_4)) (Prod.instOneProd.{u1, u2} α β _inst_2 _inst_5)
Case conversion may be inaccurate. Consider using '#align prod.norm_one_class Prod.normOneClassₓ'. -/
instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩
#align prod.norm_one_class Prod.normOneClass

#print Pi.normOneClass /-
instance Pi.normOneClass {ι : Type _} {α : ι → Type _} [Nonempty ι] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (α i)] [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simp [Pi.norm_def, Finset.sup_const Finset.univ_nonempty]⟩
#align pi.norm_one_class Pi.normOneClass
-/

#print MulOpposite.normOneClass /-
instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩
#align mul_opposite.norm_one_class MulOpposite.normOneClass
-/

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

/- warning: norm_mul_le -> norm_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (a : α) (b : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) a b)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) a) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (a : α) (b : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))) a b)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) a) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align norm_mul_le norm_mul_leₓ'. -/
theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  NonUnitalSeminormedRing.norm_mul _ _
#align norm_mul_le norm_mul_le

/- warning: nnnorm_mul_le -> nnnorm_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (a : α) (b : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) a b)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α _inst_1))) a) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (a : α) (b : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))) a b)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α _inst_1))) a) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align nnnorm_mul_le nnnorm_mul_leₓ'. -/
theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := by
  simpa only [← norm_toNNReal, ← Real.toNNReal_mul (norm_nonneg _)] using
    Real.toNNReal_mono (norm_mul_le _ _)
#align nnnorm_mul_le nnnorm_mul_le

/- warning: one_le_norm_one -> one_le_norm_one is a dubious translation:
lean 3 declaration is
  forall (β : Type.{u1}) [_inst_2 : NormedRing.{u1} β] [_inst_3 : Nontrivial.{u1} β], LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u1} β (NormedRing.toHasNorm.{u1} β _inst_2) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (AddMonoidWithOne.toOne.{u1} β (AddGroupWithOne.toAddMonoidWithOne.{u1} β (AddCommGroupWithOne.toAddGroupWithOne.{u1} β (Ring.toAddCommGroupWithOne.{u1} β (NormedRing.toRing.{u1} β _inst_2)))))))))
but is expected to have type
  forall (β : Type.{u1}) [_inst_2 : NormedRing.{u1} β] [_inst_3 : Nontrivial.{u1} β], LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u1} β (NormedRing.toNorm.{u1} β _inst_2) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (Ring.toSemiring.{u1} β (NormedRing.toRing.{u1} β _inst_2))))))
Case conversion may be inaccurate. Consider using '#align one_le_norm_one one_le_norm_oneₓ'. -/
theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)
#align one_le_norm_one one_le_norm_one

/- warning: one_le_nnnorm_one -> one_le_nnnorm_one is a dubious translation:
lean 3 declaration is
  forall (β : Type.{u1}) [_inst_2 : NormedRing.{u1} β] [_inst_3 : Nontrivial.{u1} β], LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (NNNorm.nnnorm.{u1} β (SeminormedAddGroup.toNNNorm.{u1} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} β (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} β (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β _inst_2))))) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (AddMonoidWithOne.toOne.{u1} β (AddGroupWithOne.toAddMonoidWithOne.{u1} β (AddCommGroupWithOne.toAddGroupWithOne.{u1} β (Ring.toAddCommGroupWithOne.{u1} β (NormedRing.toRing.{u1} β _inst_2)))))))))
but is expected to have type
  forall (β : Type.{u1}) [_inst_2 : NormedRing.{u1} β] [_inst_3 : Nontrivial.{u1} β], LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (NNNorm.nnnorm.{u1} β (SeminormedAddGroup.toNNNorm.{u1} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} β (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} β (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β _inst_2))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (Ring.toSemiring.{u1} β (NormedRing.toRing.{u1} β _inst_2))))))
Case conversion may be inaccurate. Consider using '#align one_le_nnnorm_one one_le_nnnorm_oneₓ'. -/
theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
  one_le_norm_one β
#align one_le_nnnorm_one one_le_nnnorm_one

/- warning: filter.tendsto.zero_mul_is_bounded_under_le -> Filter.Tendsto.zero_mul_isBoundedUnder_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] {f : ι -> α} {g : ι -> α} {l : Filter.{u2} ι}, (Filter.Tendsto.{u2, u1} ι α f l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))))))) -> (Filter.IsBoundedUnder.{0, u2} Real ι (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u2, succ u1, 1} ι α Real (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1)) g)) -> (Filter.Tendsto.{u2, u1} ι α (fun (x : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (f x) (g x)) l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] {f : ι -> α} {g : ι -> α} {l : Filter.{u2} ι}, (Filter.Tendsto.{u2, u1} ι α f l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))))) -> (Filter.IsBoundedUnder.{0, u2} Real ι (fun (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1131 : Real) (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1133 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1131 x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1133) l (Function.comp.{succ u2, succ u1, 1} ι α Real (fun (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1152 : α) => Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1152) g)) -> (Filter.Tendsto.{u2, u1} ι α (fun (x : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))) (f x) (g x)) l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.zero_mul_is_bounded_under_le Filter.Tendsto.zero_mul_isBoundedUnder_leₓ'. -/
theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι → α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le
#align filter.tendsto.zero_mul_is_bounded_under_le Filter.Tendsto.zero_mul_isBoundedUnder_le

/- warning: filter.is_bounded_under_le.mul_tendsto_zero -> Filter.isBoundedUnder_le_mul_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] {f : ι -> α} {g : ι -> α} {l : Filter.{u2} ι}, (Filter.IsBoundedUnder.{0, u2} Real ι (LE.le.{0} Real Real.hasLe) l (Function.comp.{succ u2, succ u1, 1} ι α Real (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1)) f)) -> (Filter.Tendsto.{u2, u1} ι α g l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))))))) -> (Filter.Tendsto.{u2, u1} ι α (fun (x : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (f x) (g x)) l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] {f : ι -> α} {g : ι -> α} {l : Filter.{u2} ι}, (Filter.IsBoundedUnder.{0, u2} Real ι (fun (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1225 : Real) (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1227 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1225 x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.1227) l (Function.comp.{succ u2, succ u1, 1} ι α Real (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1)) f)) -> (Filter.Tendsto.{u2, u1} ι α g l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))))) -> (Filter.Tendsto.{u2, u1} ι α (fun (x : ι) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))) (f x) (g x)) l (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (SemigroupWithZero.toZero.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_le.mul_tendsto_zero Filter.isBoundedUnder_le_mul_tendsto_zeroₓ'. -/
theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)
#align filter.is_bounded_under_le.mul_tendsto_zero Filter.isBoundedUnder_le_mul_tendsto_zero

/- warning: mul_left_bound -> mulLeft_bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (fun (_x : AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) => α -> α) (AddMonoidHom.hasCoeToFun.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (AddMonoidHom.mulLeft.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))) x) y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) x) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) y) (NonUnitalSeminormedRing.toNorm.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) y) _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) α α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoidHom.addMonoidHomClass.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))))) (AddMonoidHom.mulLeft.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))) x) y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) x) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) y))
Case conversion may be inaccurate. Consider using '#align mul_left_bound mulLeft_boundₓ'. -/
/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
theorem mulLeft_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulLeft x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x
#align mul_left_bound mulLeft_bound

/- warning: mul_right_bound -> mulRight_bound is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (fun (_x : AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) => α -> α) (AddMonoidHom.hasCoeToFun.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (AddMonoidHom.mulRight.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))) x) y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) x) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toHasNorm.{u1} α _inst_1) y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) y) (NonUnitalSeminormedRing.toNorm.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) y) _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : α) => α) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) α α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))) α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoidHom.addMonoidHomClass.{u1, u1} α α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))))))))) (AddMonoidHom.mulRight.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1))) x) y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) x) (Norm.norm.{u1} α (NonUnitalSeminormedRing.toNorm.{u1} α _inst_1) y))
Case conversion may be inaccurate. Consider using '#align mul_right_bound mulRight_boundₓ'. -/
/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
theorem mulRight_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulRight x y‖ ≤ ‖x‖ * ‖y‖ := fun y =>
  by
  rw [mul_comm]
  convert norm_mul_le y x
#align mul_right_bound mulRight_bound

instance : NonUnitalSeminormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup with norm_mul := fun x y => (norm_mul_le x.down y.down : _) }

#print Prod.nonUnitalSeminormedRing /-
/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing (α × β) :=
  { Prod.seminormedAddCommGroup with
    norm_mul := fun x y =>
      calc
        ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
        _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
        _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
          (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
        _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
        _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
          apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
        _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
        _ = ‖x‖ * ‖y‖ := rfl
         }
#align prod.non_unital_semi_normed_ring Prod.nonUnitalSeminormedRing
-/

#print Pi.nonUnitalSeminormedRing /-
/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedRing {π : ι → Type _} [Fintype ι]
    [∀ i, NonUnitalSeminormedRing (π i)] : NonUnitalSeminormedRing (∀ i, π i) :=
  { Pi.seminormedAddCommGroup with
    norm_mul := fun x y =>
      NNReal.coe_mono <|
        calc
          (Finset.univ.sup fun i => ‖x i * y i‖₊) ≤
              Finset.univ.sup ((fun i => ‖x i‖₊) * fun i => ‖y i‖₊) :=
            Finset.sup_mono_fun fun b hb => norm_mul_le _ _
          _ ≤ (Finset.univ.sup fun i => ‖x i‖₊) * Finset.univ.sup fun i => ‖y i‖₊ :=
            Finset.sup_mul_le_mul_sup_of_nonneg _ (fun i _ => zero_le _) fun i _ => zero_le _
           }
#align pi.non_unital_semi_normed_ring Pi.nonUnitalSeminormedRing
-/

#print MulOpposite.nonUnitalSeminormedRing /-
instance MulOpposite.nonUnitalSeminormedRing : NonUnitalSeminormedRing αᵐᵒᵖ :=
  { MulOpposite.seminormedAddCommGroup with
    norm_mul :=
      MulOpposite.rec' fun x =>
        MulOpposite.rec' fun y => (norm_mul_le y x).trans_eq (mul_comm _ _) }
#align mul_opposite.non_unital_semi_normed_ring MulOpposite.nonUnitalSeminormedRing
-/

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/- warning: subalgebra.semi_normed_ring -> Subalgebra.seminormedRing is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {_x : CommRing.{u1} 𝕜} {E : Type.{u2}} [_inst_2 : SeminormedRing.{u2} E] {_x_1 : Algebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2))} (s : Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1), SeminormedRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1) E (Subalgebra.setLike.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1)) s)
but is expected to have type
  forall {𝕜 : Type.{u1}} [_x : CommRing.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : SeminormedRing.{u2} E] [_x_1 : Algebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2))] (s : Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1), SeminormedRing.{u2} (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1) E (Subalgebra.instSetLikeSubalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (SeminormedRing.toRing.{u2} E _inst_2)) _x_1)) x s))
Case conversion may be inaccurate. Consider using '#align subalgebra.semi_normed_ring Subalgebra.seminormedRingₓ'. -/
/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.seminormedRing {𝕜 : Type _} {_ : CommRing 𝕜} {E : Type _} [SeminormedRing E]
    {_ : Algebra 𝕜 E} (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.SeminormedAddCommGroup with norm_mul := fun a b => norm_mul_le a.1 b.1 }
#align subalgebra.semi_normed_ring Subalgebra.seminormedRing

/- warning: subalgebra.normed_ring -> Subalgebra.normedRing is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {_x : CommRing.{u1} 𝕜} {E : Type.{u2}} [_inst_2 : NormedRing.{u2} E] {_x_1 : Algebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2))} (s : Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1), NormedRing.{u2} (coeSort.{succ u2, succ (succ u2)} (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1) E (Subalgebra.setLike.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1)) s)
but is expected to have type
  forall {𝕜 : Type.{u1}} [_x : CommRing.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedRing.{u2} E] [_x_1 : Algebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2))] (s : Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1), NormedRing.{u2} (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1) (SetLike.instMembership.{u2, u2} (Subalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1) E (Subalgebra.instSetLikeSubalgebra.{u1, u2} 𝕜 E (CommRing.toCommSemiring.{u1} 𝕜 _x) (Ring.toSemiring.{u2} E (NormedRing.toRing.{u2} E _inst_2)) _x_1)) x s))
Case conversion may be inaccurate. Consider using '#align subalgebra.normed_ring Subalgebra.normedRingₓ'. -/
/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.normedRing {𝕜 : Type _} {_ : CommRing 𝕜} {E : Type _} [NormedRing E]
    {_ : Algebra 𝕜 E} (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.SeminormedRing with }
#align subalgebra.normed_ring Subalgebra.normedRing

/- warning: nat.norm_cast_le -> Nat.norm_cast_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat α (HasLiftT.mk.{1, succ u1} Nat α (CoeTCₓ.coe.{1, succ u1} Nat α (Nat.castCoe.{u1} α (AddMonoidWithOne.toNatCast.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))))) n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (Nat.cast.{u1} α (Semiring.toNatCast.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align nat.norm_cast_le Nat.norm_cast_leₓ'. -/
theorem Nat.norm_cast_le : ∀ n : ℕ, ‖(n : α)‖ ≤ n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mul, one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl
#align nat.norm_cast_le Nat.norm_cast_le

/- warning: list.norm_prod_le' -> List.norm_prod_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))))) l)) (List.prod.{0} Real Real.hasMul Real.hasOne (List.map.{u1, 0} α Real (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1)) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) l)) (List.prod.{0} Real Real.instMulReal Real.instOneReal (List.map.{u1, 0} α Real (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1)) l)))
Case conversion may be inaccurate. Consider using '#align list.norm_prod_le' List.norm_prod_le'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ‖l.Prod‖ ≤ (l.map norm).Prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons, List.prod_cons, @List.prod_cons _ _ _ ‖a‖]
    refine' le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)
#align list.norm_prod_le' List.norm_prod_le'

/- warning: list.nnnorm_prod_le' -> List.nnnorm_prod_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))))) l)) (List.prod.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (List.map.{u1, 0} α NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1))))) l)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) l)) (List.prod.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) instNNRealOne (List.map.{u1, 0} α NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1))))) l)))
Case conversion may be inaccurate. Consider using '#align list.nnnorm_prod_le' List.nnnorm_prod_le'ₓ'. -/
theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ‖l.Prod‖₊ ≤ (l.map nnnorm).Prod :=
  (List.norm_prod_le' hl).trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]
#align list.nnnorm_prod_le' List.nnnorm_prod_le'

/- warning: list.norm_prod_le -> List.norm_prod_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))] (l : List.{u1} α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))))) l)) (List.prod.{0} Real Real.hasMul Real.hasOne (List.map.{u1, 0} α Real (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1)) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))] (l : List.{u1} α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) l)) (List.prod.{0} Real Real.instMulReal Real.instOneReal (List.map.{u1, 0} α Real (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.norm_prod_le List.norm_prod_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ‖l.Prod‖ ≤ (l.map norm).Prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)
#align list.norm_prod_le List.norm_prod_le

/- warning: list.nnnorm_prod_le -> List.nnnorm_prod_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))] (l : List.{u1} α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))))) l)) (List.prod.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (List.map.{u1, 0} α NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1))))) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))] (l : List.{u1} α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1))) l)) (List.prod.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) instNNRealOne (List.map.{u1, 0} α NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1))))) l))
Case conversion may be inaccurate. Consider using '#align list.nnnorm_prod_le List.nnnorm_prod_leₓ'. -/
theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.Prod‖₊ ≤ (l.map nnnorm).Prod :=
  l.norm_prod_le.trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]
#align list.nnnorm_prod_le List.nnnorm_prod_le

/- warning: finset.norm_prod_le' -> Finset.norm_prod_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (f : ι -> α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} α (NormedRing.toHasNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} Real ι Real.commMonoid s (fun (i : ι) => Norm.norm.{u2} α (NormedRing.toHasNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (f i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (f : ι -> α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} α (NormedRing.toNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} Real ι Real.instCommMonoidReal s (fun (i : ι) => Norm.norm.{u2} α (NormedRing.toNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (f i))))
Case conversion may be inaccurate. Consider using '#align finset.norm_prod_le' Finset.norm_prod_le'ₓ'. -/
theorem Finset.norm_prod_le' {α : Type _} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i in s, f i‖ ≤ ∏ i in s, ‖f i‖ :=
  by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by simpa using hs
  simpa using List.norm_prod_le' this
#align finset.norm_prod_le' Finset.norm_prod_le'

/- warning: finset.nnnorm_prod_le' -> Finset.nnnorm_prod_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (f : ι -> α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} NNReal ι (OrderedCommMonoid.toCommMonoid.{0} NNReal (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} NNReal NNReal.canonicallyOrderedCommSemiring)) s (fun (i : ι) => NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (f i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (f : ι -> α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} NNReal ι (LinearOrderedCommMonoid.toCommMonoid.{0} NNReal (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} NNReal (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)))) s (fun (i : ι) => NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (f i))))
Case conversion may be inaccurate. Consider using '#align finset.nnnorm_prod_le' Finset.nnnorm_prod_le'ₓ'. -/
theorem Finset.nnnorm_prod_le' {α : Type _} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i in s, f i‖₊ ≤ ∏ i in s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]
#align finset.nnnorm_prod_le' Finset.nnnorm_prod_le'

/- warning: finset.norm_prod_le -> Finset.norm_prod_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] [_inst_3 : NormOneClass.{u2} α (NormedRing.toHasNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (AddMonoidWithOne.toOne.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (NormedRing.toRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2))))))] (s : Finset.{u1} ι) (f : ι -> α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} α (NormedRing.toHasNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} Real ι Real.commMonoid s (fun (i : ι) => Norm.norm.{u2} α (NormedRing.toHasNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] [_inst_3 : NormOneClass.{u2} α (NormedRing.toNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (Semiring.toOne.{u2} α (CommSemiring.toSemiring.{u2} α (CommRing.toCommSemiring.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2)))))] (s : Finset.{u1} ι) (f : ι -> α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} α (NormedRing.toNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} Real ι Real.instCommMonoidReal s (fun (i : ι) => Norm.norm.{u2} α (NormedRing.toNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (f i)))
Case conversion may be inaccurate. Consider using '#align finset.norm_prod_le Finset.norm_prod_leₓ'. -/
theorem Finset.norm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i in s, f i‖ ≤ ∏ i in s, ‖f i‖ :=
  by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le
#align finset.norm_prod_le Finset.norm_prod_le

/- warning: finset.nnnorm_prod_le -> Finset.nnnorm_prod_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] [_inst_3 : NormOneClass.{u2} α (NormedRing.toHasNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (AddMonoidWithOne.toOne.{u2} α (AddGroupWithOne.toAddMonoidWithOne.{u2} α (AddCommGroupWithOne.toAddGroupWithOne.{u2} α (Ring.toAddCommGroupWithOne.{u2} α (NormedRing.toRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2))))))] (s : Finset.{u1} ι) (f : ι -> α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} NNReal ι (OrderedCommMonoid.toCommMonoid.{0} NNReal (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} NNReal NNReal.canonicallyOrderedCommSemiring)) s (fun (i : ι) => NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : NormedCommRing.{u2} α] [_inst_3 : NormOneClass.{u2} α (NormedRing.toNorm.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)) (Semiring.toOne.{u2} α (CommSemiring.toSemiring.{u2} α (CommRing.toCommSemiring.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2)))))] (s : Finset.{u1} ι) (f : ι -> α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (Finset.prod.{u2, u1} α ι (CommRing.toCommMonoid.{u2} α (SeminormedCommRing.toCommRing.{u2} α (NormedCommRing.toSeminormedCommRing.{u2} α _inst_2))) s (fun (i : ι) => f i))) (Finset.prod.{0, u1} NNReal ι (LinearOrderedCommMonoid.toCommMonoid.{0} NNReal (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} NNReal (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)))) s (fun (i : ι) => NNNorm.nnnorm.{u2} α (SeminormedAddGroup.toNNNorm.{u2} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} α (NormedRing.toNonUnitalNormedRing.{u2} α (NormedCommRing.toNormedRing.{u2} α _inst_2)))))) (f i)))
Case conversion may be inaccurate. Consider using '#align finset.nnnorm_prod_le Finset.nnnorm_prod_leₓ'. -/
theorem Finset.nnnorm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i in s, f i‖₊ ≤ ∏ i in s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]
#align finset.nnnorm_prod_le Finset.nnnorm_prod_le

/- warning: nnnorm_pow_le' -> nnnorm_pow_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (a : α) {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) a) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (a : α) {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))) a n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) a) n))
Case conversion may be inaccurate. Consider using '#align nnnorm_pow_le' nnnorm_pow_le'ₓ'. -/
/-- If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, h => by simp only [pow_one]
  | n + 2, h => by
    simpa only [pow_succ _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' n.succ_pos) _)
#align nnnorm_pow_le' nnnorm_pow_le'

/- warning: nnnorm_pow_le -> nnnorm_pow_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))] (a : α) (n : Nat), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) a) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))] (a : α) (n : Nat), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))) a n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (SeminormedRing.toNonUnitalSeminormedRing.{u1} α _inst_1)))) a) n)
Case conversion may be inaccurate. Consider using '#align nnnorm_pow_le nnnorm_pow_leₓ'. -/
/-- If `α` is a seminormed ring with `‖1‖₊ = 1`, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n`.
See also `nnnorm_pow_le'`.-/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n :=
  Nat.recOn n (by simp only [pow_zero, nnnorm_one]) fun k hk => nnnorm_pow_le' a k.succ_pos
#align nnnorm_pow_le nnnorm_pow_le

/- warning: norm_pow_le' -> norm_pow_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (a : α) {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) a) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (a : α) {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) a) n))
Case conversion may be inaccurate. Consider using '#align norm_pow_le' norm_pow_le'ₓ'. -/
/-- If `α` is a seminormed ring, then `‖a ^ n‖ ≤ ‖a‖ ^ n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)
#align norm_pow_le' norm_pow_le'

/- warning: norm_pow_le -> norm_pow_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))] (a : α) (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) a) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] [_inst_2 : NormOneClass.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (Semiring.toOne.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))] (a : α) (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) a) n)
Case conversion may be inaccurate. Consider using '#align norm_pow_le norm_pow_leₓ'. -/
/-- If `α` is a seminormed ring with `‖1‖ = 1`, then `‖a ^ n‖ ≤ ‖a‖ ^ n`. See also `norm_pow_le'`.-/
theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  Nat.recOn n (by simp only [pow_zero, norm_one]) fun n hn => norm_pow_le' a n.succ_pos
#align norm_pow_le norm_pow_le

/- warning: eventually_norm_pow_le -> eventually_norm_pow_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (a : α), Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} α (SeminormedRing.toHasNorm.{u1} α _inst_1) a) n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedRing.{u1} α] (a : α), Filter.Eventually.{0} Nat (fun (n : Nat) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (SeminormedRing.toRing.{u1} α _inst_1)))))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} α (SeminormedRing.toNorm.{u1} α _inst_1) a) n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))
Case conversion may be inaccurate. Consider using '#align eventually_norm_pow_le eventually_norm_pow_leₓ'. -/
theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩
#align eventually_norm_pow_le eventually_norm_pow_le

instance : SeminormedRing (ULift α) :=
  { ULift.nonUnitalSemiNormedRing, ULift.seminormedAddCommGroup with }

#print Prod.seminormedRing /-
/-- Seminormed ring structure on the product of two seminormed rings,
  using the sup norm. -/
instance Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β) :=
  { Prod.nonUnitalSeminormedRing, Prod.seminormedAddCommGroup with }
#align prod.semi_normed_ring Prod.seminormedRing
-/

#print Pi.seminormedRing /-
/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.seminormedRing {π : ι → Type _} [Fintype ι] [∀ i, SeminormedRing (π i)] :
    SeminormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.seminormedAddCommGroup with }
#align pi.semi_normed_ring Pi.seminormedRing
-/

#print MulOpposite.seminormedRing /-
instance MulOpposite.seminormedRing : SeminormedRing αᵐᵒᵖ :=
  { MulOpposite.nonUnitalSeminormedRing, MulOpposite.seminormedAddCommGroup with }
#align mul_opposite.semi_normed_ring MulOpposite.seminormedRing
-/

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

instance : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSemiNormedRing, ULift.seminormedAddCommGroup with }

#print Prod.nonUnitalNormedRing /-
/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.seminormedAddCommGroup with norm_mul := norm_mul_le }
#align prod.non_unital_normed_ring Prod.nonUnitalNormedRing
-/

#print Pi.nonUnitalNormedRing /-
/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {π : ι → Type _} [Fintype ι] [∀ i, NonUnitalNormedRing (π i)] :
    NonUnitalNormedRing (∀ i, π i) :=
  { Pi.normedAddCommGroup with norm_mul := norm_mul_le }
#align pi.non_unital_normed_ring Pi.nonUnitalNormedRing
-/

#print MulOpposite.nonUnitalNormedRing /-
instance MulOpposite.nonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ :=
  { MulOpposite.normedAddCommGroup with norm_mul := norm_mul_le }
#align mul_opposite.non_unital_normed_ring MulOpposite.nonUnitalNormedRing
-/

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/- warning: units.norm_pos -> Units.norm_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (x : Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (coeBase.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (Units.hasCoe.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1)))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (x : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (NormedRing.toRing.{u1} α _inst_1))))), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align units.norm_pos Units.norm_posₓ'. -/
theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)
#align units.norm_pos Units.norm_pos

/- warning: units.nnnorm_pos -> Units.nnnorm_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (x : Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))), LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (coeBase.{succ u1, succ u1} (Units.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1))) α (Units.hasCoe.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α _inst_1)))))) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : Nontrivial.{u1} α] (x : Units.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (NormedRing.toRing.{u1} α _inst_1))))), LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1))))) (Units.val.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align units.nnnorm_pos Units.nnnorm_posₓ'. -/
theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos
#align units.nnnorm_pos Units.nnnorm_pos

instance : NormedRing (ULift α) :=
  { ULift.semiNormedRing, ULift.normedAddCommGroup with }

#print Prod.normedRing /-
/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { Prod.normedAddCommGroup with norm_mul := norm_mul_le }
#align prod.normed_ring Prod.normedRing
-/

#print Pi.normedRing /-
/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {π : ι → Type _} [Fintype ι] [∀ i, NormedRing (π i)] :
    NormedRing (∀ i, π i) :=
  { Pi.normedAddCommGroup with norm_mul := norm_mul_le }
#align pi.normed_ring Pi.normedRing
-/

#print MulOpposite.normedRing /-
instance MulOpposite.normedRing : NormedRing αᵐᵒᵖ :=
  { MulOpposite.normedAddCommGroup with norm_mul := norm_mul_le }
#align mul_opposite.normed_ring MulOpposite.normedRing
-/

end NormedRing

/- warning: semi_normed_ring_top_monoid -> semi_normed_ring_top_monoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α], ContinuousMul.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalSeminormedRing.{u1} α], ContinuousMul.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (NonUnitalSeminormedRing.toPseudoMetricSpace.{u1} α _inst_1))) (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalSeminormedRing.toNonUnitalRing.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align semi_normed_ring_top_monoid semi_normed_ring_top_monoidₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) semi_normed_ring_top_monoid [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_tendsto_zero.2 <|
        by
        have : ∀ e : α × α, ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
          by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [mul_sub, sub_mul, sub_add_sub_cancel]
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
            
        refine' squeeze_zero (fun e => norm_nonneg _) this _
        convert((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        show tendsto _ _ _
        exact tendsto_const_nhds
        simp⟩
#align semi_normed_ring_top_monoid semi_normed_ring_top_monoid

#print semi_normed_top_ring /-
-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) semi_normed_top_ring [NonUnitalSeminormedRing α] : TopologicalRing α
    where
#align semi_normed_top_ring semi_normed_top_ring
-/

section NormedDivisionRing

variable [NormedDivisionRing α]

/- warning: norm_mul -> norm_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) a b)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) a) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a b)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) a) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align norm_mul norm_mulₓ'. -/
@[simp]
theorem norm_mul (a b : α) : ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormedDivisionRing.norm_mul' a b
#align norm_mul norm_mul

/- warning: normed_division_ring.to_norm_one_class -> NormedDivisionRing.to_normOneClass is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α], NormOneClass.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α], NormOneClass.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) (Semiring.toOne.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align normed_division_ring.to_norm_one_class NormedDivisionRing.to_normOneClassₓ'. -/
instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) <| by rw [← norm_mul, mul_one, mul_one]⟩
#align normed_division_ring.to_norm_one_class NormedDivisionRing.to_normOneClass

#print isAbsoluteValue_norm /-
instance isAbsoluteValue_norm : IsAbsoluteValue (norm : α → ℝ)
    where
  abv_nonneg := norm_nonneg
  abv_eq_zero _ := norm_eq_zero
  abv_add := norm_add_le
  abv_mul := norm_mul
#align is_absolute_value_norm isAbsoluteValue_norm
-/

/- warning: nnnorm_mul -> nnnorm_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) a b)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a b)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) b))
Case conversion may be inaccurate. Consider using '#align nnnorm_mul nnnorm_mulₓ'. -/
@[simp]
theorem nnnorm_mul (a b : α) : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ :=
  NNReal.eq <| norm_mul a b
#align nnnorm_mul nnnorm_mul

#print normHom /-
/-- `norm` as a `monoid_with_zero_hom`. -/
@[simps]
def normHom : α →*₀ ℝ :=
  ⟨norm, norm_zero, norm_one, norm_mul⟩
#align norm_hom normHom
-/

#print nnnormHom /-
/-- `nnnorm` as a `monoid_with_zero_hom`. -/
@[simps]
def nnnormHom : α →*₀ ℝ≥0 :=
  ⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩
#align nnnorm_hom nnnormHom
-/

/- warning: norm_pow -> norm_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (n : Nat), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) a) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (n : Nat), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) a n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) a) n)
Case conversion may be inaccurate. Consider using '#align norm_pow norm_powₓ'. -/
@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a
#align norm_pow norm_pow

/- warning: nnnorm_pow -> nnnorm_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (n : Nat), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) a n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (n : Nat), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) a n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) n)
Case conversion may be inaccurate. Consider using '#align nnnorm_pow nnnorm_powₓ'. -/
@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_pow a n
#align nnnorm_pow nnnorm_pow

/- warning: list.norm_prod -> List.norm_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (l : List.{u1} α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) l)) (List.prod.{0} Real Real.hasMul Real.hasOne (List.map.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1)) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (l : List.{u1} α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) (Semiring.toOne.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))) l)) (List.prod.{0} Real Real.instMulReal Real.instOneReal (List.map.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.norm_prod List.norm_prodₓ'. -/
protected theorem List.norm_prod (l : List α) : ‖l.Prod‖ = (l.map norm).Prod :=
  (normHom.toMonoidHom : α →* ℝ).map_list_prod _
#align list.norm_prod List.norm_prod

/- warning: list.nnnorm_prod -> List.nnnorm_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (l : List.{u1} α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (List.prod.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) l)) (List.prod.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (List.map.{u1, 0} α NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (l : List.{u1} α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (List.prod.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) (Semiring.toOne.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))) l)) (List.prod.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) instNNRealOne (List.map.{u1, 0} α NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) l))
Case conversion may be inaccurate. Consider using '#align list.nnnorm_prod List.nnnorm_prodₓ'. -/
protected theorem List.nnnorm_prod (l : List α) : ‖l.Prod‖₊ = (l.map nnnorm).Prod :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_list_prod _
#align list.nnnorm_prod List.nnnorm_prod

/- warning: norm_div -> norm_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))) a b)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) a) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivisionRing.toDiv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) a b)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) a) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) b))
Case conversion may be inaccurate. Consider using '#align norm_div norm_divₓ'. -/
@[simp]
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α →*₀ ℝ) a b
#align norm_div norm_div

/- warning: nnnorm_div -> nnnorm_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))) a b)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (b : α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivisionRing.toDiv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) a b)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) b))
Case conversion may be inaccurate. Consider using '#align nnnorm_div nnnorm_divₓ'. -/
@[simp]
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α →*₀ ℝ≥0) a b
#align nnnorm_div nnnorm_div

/- warning: norm_inv -> norm_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) a)) (Inv.inv.{0} Real Real.hasInv (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α), Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) a)) (Inv.inv.{0} Real Real.instInvReal (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align norm_inv norm_invₓ'. -/
@[simp]
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α →*₀ ℝ) a
#align norm_inv norm_inv

/- warning: nnnorm_inv -> nnnorm_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) a)) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) a)) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a))
Case conversion may be inaccurate. Consider using '#align nnnorm_inv nnnorm_invₓ'. -/
@[simp]
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
  NNReal.eq <| by simp
#align nnnorm_inv nnnorm_inv

#print norm_zpow /-
@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α →*₀ ℝ)
#align norm_zpow norm_zpow
-/

/- warning: nnnorm_zpow -> nnnorm_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (n : Int), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] (a : α) (n : Int), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))) a n)) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) a) n)
Case conversion may be inaccurate. Consider using '#align nnnorm_zpow nnnorm_zpowₓ'. -/
@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α →*₀ ℝ≥0)
#align nnnorm_zpow nnnorm_zpow

/- warning: dist_inv_inv₀ -> dist_inv_inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {z : α} {w : α}, (Ne.{succ u1} α z (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))))))) -> (Ne.{succ u1} α w (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))))))) -> (Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) z) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) w)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) z w) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) z) (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) w))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {z : α} {w : α}, (Ne.{succ u1} α z (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))))) -> (Ne.{succ u1} α w (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))))) -> (Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) z) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) w)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) z w) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) z) (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) w))))
Case conversion may be inaccurate. Consider using '#align dist_inv_inv₀ dist_inv_inv₀ₓ'. -/
theorem dist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) : dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) :=
  by
  rw [dist_eq_norm, inv_sub_inv' hz hw, norm_mul, norm_mul, norm_inv, norm_inv, mul_comm ‖z‖⁻¹,
    mul_assoc, dist_eq_norm', div_eq_mul_inv, mul_inv]
#align dist_inv_inv₀ dist_inv_inv₀

/- warning: nndist_inv_inv₀ -> nndist_inv_inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {z : α} {w : α}, (Ne.{succ u1} α z (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))))))) -> (Ne.{succ u1} α w (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))))))) -> (Eq.{1} NNReal (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) z) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) w)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) z w) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) z) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) w))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {z : α} {w : α}, (Ne.{succ u1} α z (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))))) -> (Ne.{succ u1} α w (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))))) -> (Eq.{1} NNReal (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) z) (Inv.inv.{u1} α (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) w)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))) z w) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) z) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) w))))
Case conversion may be inaccurate. Consider using '#align nndist_inv_inv₀ nndist_inv_inv₀ₓ'. -/
theorem nndist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
  by
  rw [← NNReal.coe_eq]
  simp [-NNReal.coe_eq, dist_inv_inv₀ hz hw]
#align nndist_inv_inv₀ nndist_inv_inv₀

/- warning: filter.tendsto_mul_left_cobounded -> Filter.tendsto_mul_left_cobounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))))))) -> (Filter.Tendsto.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) a) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.preorder)) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.preorder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))))) -> (Filter.Tendsto.{u1, u1} α α ((fun (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.5145 : α) (x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.5147 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.5145 x._@.Mathlib.Analysis.Normed.Field.Basic._hyg.5147) a) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.instPreorderReal)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_mul_left_cobounded Filter.tendsto_mul_left_coboundedₓ'. -/
/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto ((· * ·) a) (comap norm atTop) (comap norm atTop) := by
  simpa only [tendsto_comap_iff, (· ∘ ·), norm_mul] using
    tendsto_const_nhds.mul_at_top (norm_pos_iff.2 ha) tendsto_comap
#align filter.tendsto_mul_left_cobounded Filter.tendsto_mul_left_cobounded

/- warning: filter.tendsto_mul_right_cobounded -> Filter.tendsto_mul_right_cobounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))))))) -> (Filter.Tendsto.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) x a) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.preorder)) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.preorder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))))) -> (Filter.Tendsto.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))) x a) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.comap.{u1, 0} α Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1)) (Filter.atTop.{0} Real Real.instPreorderReal)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_mul_right_cobounded Filter.tendsto_mul_right_coboundedₓ'. -/
/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (fun x => x * a) (comap norm atTop) (comap norm atTop) := by
  simpa only [tendsto_comap_iff, (· ∘ ·), norm_mul] using
    tendsto_comap.at_top_mul (norm_pos_iff.2 ha) tendsto_const_nhds
#align filter.tendsto_mul_right_cobounded Filter.tendsto_mul_right_cobounded

/- warning: normed_division_ring.to_has_continuous_inv₀ -> NormedDivisionRing.to_hasContinuousInv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α], HasContinuousInv₀.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α], HasContinuousInv₀.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))) (DivisionRing.toInv.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align normed_division_ring.to_has_continuous_inv₀ NormedDivisionRing.to_hasContinuousInv₀ₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_hasContinuousInv₀ : HasContinuousInv₀ α :=
  by
  refine' ⟨fun r r0 => tendsto_iff_norm_tendsto_zero.2 _⟩
  have r0' : 0 < ‖r‖ := norm_pos_iff.2 r0
  rcases exists_between r0' with ⟨ε, ε0, εr⟩
  have : ∀ᶠ e in 𝓝 r, ‖e⁻¹ - r⁻¹‖ ≤ ‖r - e‖ / ‖r‖ / ε :=
    by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).eventually_mem εr]with e he
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he)
    calc
      ‖e⁻¹ - r⁻¹‖ = ‖r‖⁻¹ * ‖r - e‖ * ‖e‖⁻¹ := by
        rw [← norm_inv, ← norm_inv, ← norm_mul, ← norm_mul, mul_sub, sub_mul, mul_assoc _ e,
          inv_mul_cancel r0, mul_inv_cancel e0, one_mul, mul_one]
      _ = ‖r - e‖ / ‖r‖ / ‖e‖ := by field_simp [mul_comm]
      _ ≤ ‖r - e‖ / ‖r‖ / ε :=
        div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le
      
  refine' squeeze_zero' (eventually_of_forall fun _ => norm_nonneg _) this _
  refine' (((continuous_const.sub continuous_id).norm.div_const _).div_const _).tendsto' _ _ _
  simp
#align normed_division_ring.to_has_continuous_inv₀ NormedDivisionRing.to_hasContinuousInv₀

#print NormedDivisionRing.to_topologicalDivisionRing /-
-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_topologicalDivisionRing : TopologicalDivisionRing α
    where
#align normed_division_ring.to_topological_division_ring NormedDivisionRing.to_topologicalDivisionRing
-/

/- warning: norm_map_one_of_pow_eq_one -> norm_map_one_of_pow_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedDivisionRing.{u1} α] [_inst_2 : Monoid.{u2} β] (φ : MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) {x : β} {k : PNat}, (Eq.{succ u2} β (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β _inst_2)) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) k)) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)))))) -> (Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) (fun (_x : MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) => β -> α) (MonoidHom.hasCoeToFun.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (NonAssocRing.toNonAssocSemiring.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))))) φ x)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedDivisionRing.{u1} α] [_inst_2 : Monoid.{u2} β] (φ : MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) {x : β} {k : PNat}, (Eq.{succ u2} β (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β _inst_2)) x (PNat.val k)) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (Monoid.toOne.{u2} β _inst_2)))) -> (Eq.{1} Real (Norm.norm.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : β) => α) x) (NormedDivisionRing.toNorm.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : β) => α) x) _inst_1) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : β) => α) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) β α (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MulOneClass.toMul.{u1} α (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1)))))) (MonoidHom.monoidHomClass.{u2, u1} β α (Monoid.toMulOneClass.{u2} β _inst_2) (MulZeroOneClass.toMulOneClass.{u1} α (NonAssocSemiring.toMulZeroOneClass.{u1} α (Semiring.toNonAssocSemiring.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))))) φ x)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align norm_map_one_of_pow_eq_one norm_map_one_of_pow_eq_oneₓ'. -/
theorem norm_map_one_of_pow_eq_one [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :
    ‖φ x‖ = 1 :=
  by
  rw [← pow_left_inj, ← norm_pow, ← map_pow, h, map_one, norm_one, one_pow]
  exacts[norm_nonneg _, zero_le_one, k.pos]
#align norm_map_one_of_pow_eq_one norm_map_one_of_pow_eq_one

/- warning: norm_one_of_pow_eq_one -> norm_one_of_pow_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {x : α} {k : PNat}, (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) k)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (NormedRing.toRing.{u1} α (NormedDivisionRing.toNormedRing.{u1} α _inst_1)))))))))) -> (Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toHasNorm.{u1} α _inst_1) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedDivisionRing.{u1} α] {x : α} {k : PNat}, (Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) x (PNat.val k)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (DivisionSemiring.toSemiring.{u1} α (DivisionRing.toDivisionSemiring.{u1} α (NormedDivisionRing.toDivisionRing.{u1} α _inst_1))))))) -> (Eq.{1} Real (Norm.norm.{u1} α (NormedDivisionRing.toNorm.{u1} α _inst_1) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align norm_one_of_pow_eq_one norm_one_of_pow_eq_oneₓ'. -/
theorem norm_one_of_pow_eq_one {x : α} {k : ℕ+} (h : x ^ (k : ℕ) = 1) : ‖x‖ = 1 :=
  norm_map_one_of_pow_eq_one (MonoidHom.id α) h
#align norm_one_of_pow_eq_one norm_one_of_pow_eq_one

end NormedDivisionRing

#print NormedField /-
/-- A normed field is a field with a norm satisfying ‖x y‖ = ‖x‖ ‖y‖. -/
class NormedField (α : Type _) extends Norm α, Field α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b
#align normed_field NormedField
-/

#print NontriviallyNormedField /-
/-- A nontrivially normed field is a normed field in which there is an element of norm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by
multiplication by the powers of any element, and thus to relate algebra and topology. -/
class NontriviallyNormedField (α : Type _) extends NormedField α where
  non_trivial : ∃ x : α, 1 < ‖x‖
#align nontrivially_normed_field NontriviallyNormedField
-/

#print DenselyNormedField /-
/-- A densely normed field is a normed field for which the image of the norm is dense in `ℝ≥0`,
which means it is also nontrivially normed. However, not all nontrivally normed fields are densely
normed; in particular, the `padic`s exhibit this fact. -/
class DenselyNormedField (α : Type _) extends NormedField α where
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y
#align densely_normed_field DenselyNormedField
-/

section NormedField

#print DenselyNormedField.toNontriviallyNormedField /-
/-- A densely normed field is always a nontrivially normed field.
See note [lower instance priority]. -/
instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α
    where non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩
#align densely_normed_field.to_nontrivially_normed_field DenselyNormedField.toNontriviallyNormedField
-/

variable [NormedField α]

#print NormedField.toNormedDivisionRing /-
-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }
#align normed_field.to_normed_division_ring NormedField.toNormedDivisionRing
-/

#print NormedField.toNormedCommRing /-
-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }
#align normed_field.to_normed_comm_ring NormedField.toNormedCommRing
-/

#print norm_prod /-
@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b in s, f b‖ = ∏ b in s, ‖f b‖ :=
  (normHom.toMonoidHom : α →* ℝ).map_prod f s
#align norm_prod norm_prod
-/

/- warning: nnnorm_prod -> nnnorm_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u1} α] (s : Finset.{u2} β) (f : β -> α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α _inst_1))))))) (Finset.prod.{u1, u2} α β (CommRing.toCommMonoid.{u1} α (SeminormedCommRing.toCommRing.{u1} α (NormedCommRing.toSeminormedCommRing.{u1} α (NormedField.toNormedCommRing.{u1} α _inst_1)))) s (fun (b : β) => f b))) (Finset.prod.{0, u2} NNReal β (OrderedCommMonoid.toCommMonoid.{0} NNReal (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{0} NNReal NNReal.canonicallyOrderedCommSemiring)) s (fun (b : β) => NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α _inst_1))))))) (f b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u1} α] (s : Finset.{u2} β) (f : β -> α), Eq.{1} NNReal (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α _inst_1))))))) (Finset.prod.{u1, u2} α β (CommRing.toCommMonoid.{u1} α (EuclideanDomain.toCommRing.{u1} α (Field.toEuclideanDomain.{u1} α (NormedField.toField.{u1} α _inst_1)))) s (fun (b : β) => f b))) (Finset.prod.{0, u2} NNReal β (LinearOrderedCommMonoid.toCommMonoid.{0} NNReal (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{0} NNReal (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)))) s (fun (b : β) => NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α _inst_1))))))) (f b)))
Case conversion may be inaccurate. Consider using '#align nnnorm_prod nnnorm_prodₓ'. -/
@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b in s, f b‖₊ = ∏ b in s, ‖f b‖₊ :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_prod f s
#align nnnorm_prod nnnorm_prod

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

/- warning: normed_field.exists_one_lt_norm -> NormedField.exists_one_lt_norm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α], Exists.{succ u1} α (fun (x : α) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α], Exists.{succ u1} α (fun (x : α) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align normed_field.exists_one_lt_norm NormedField.exists_one_lt_normₓ'. -/
theorem exists_one_lt_norm : ∃ x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial
#align normed_field.exists_one_lt_norm NormedField.exists_one_lt_norm

/- warning: normed_field.exists_lt_norm -> NormedField.exists_lt_norm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α] (r : Real), Exists.{succ u1} α (fun (x : α) => LT.lt.{0} Real Real.hasLt r (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α] (r : Real), Exists.{succ u1} α (fun (x : α) => LT.lt.{0} Real Real.instLTReal r (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align normed_field.exists_lt_norm NormedField.exists_lt_normₓ'. -/
theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩
#align normed_field.exists_lt_norm NormedField.exists_lt_norm

/- warning: normed_field.exists_norm_lt -> NormedField.exists_norm_lt is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x)) (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x) r)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x)) (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x) r)))
Case conversion may be inaccurate. Consider using '#align normed_field.exists_norm_lt NormedField.exists_norm_ltₓ'. -/
theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩
#align normed_field.exists_norm_lt NormedField.exists_norm_lt

/- warning: normed_field.exists_norm_lt_one -> NormedField.exists_norm_lt_one is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α], Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x)) (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} α], Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x)) (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align normed_field.exists_norm_lt_one NormedField.exists_norm_lt_oneₓ'. -/
theorem exists_norm_lt_one : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos
#align normed_field.exists_norm_lt_one NormedField.exists_norm_lt_one

variable {α}

/- warning: normed_field.punctured_nhds_ne_bot -> NormedField.punctured_nhds_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} α] (x : α), Filter.NeBot.{u1} α (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (SeminormedCommRing.toSemiNormedRing.{u1} α (NormedCommRing.toSeminormedCommRing.{u1} α (NormedField.toNormedCommRing.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1))))))) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} α] (x : α), Filter.NeBot.{u1} α (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (SeminormedCommRing.toSeminormedRing.{u1} α (NormedCommRing.toSeminormedCommRing.{u1} α (NormedField.toNormedCommRing.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1))))))) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align normed_field.punctured_nhds_ne_bot NormedField.punctured_nhds_neBotₓ'. -/
@[instance]
theorem punctured_nhds_neBot (x : α) : NeBot (𝓝[≠] x) :=
  by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine' ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_self).1 <| norm_pos_iff.1 hb0, _⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel']
#align normed_field.punctured_nhds_ne_bot NormedField.punctured_nhds_neBot

/- warning: normed_field.nhds_within_is_unit_ne_bot -> NormedField.nhdsWithin_isUnit_neBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} α], Filter.NeBot.{u1} α (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (SeminormedCommRing.toSemiNormedRing.{u1} α (NormedCommRing.toSeminormedCommRing.{u1} α (NormedField.toNormedCommRing.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)))))))))))) (setOf.{u1} α (fun (x : α) => IsUnit.{u1} α (Ring.toMonoid.{u1} α (NormedRing.toRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1))))) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} α], Filter.NeBot.{u1} α (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (SeminormedCommRing.toSeminormedRing.{u1} α (NormedCommRing.toSeminormedCommRing.{u1} α (NormedField.toNormedCommRing.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommGroupWithZero.toCommMonoidWithZero.{u1} α (Semifield.toCommGroupWithZero.{u1} α (Field.toSemifield.{u1} α (NormedField.toField.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1)))))))) (setOf.{u1} α (fun (x : α) => IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (DivisionSemiring.toSemiring.{u1} α (Semifield.toDivisionSemiring.{u1} α (Field.toSemifield.{u1} α (NormedField.toField.{u1} α (NontriviallyNormedField.toNormedField.{u1} α _inst_1))))))) x)))
Case conversion may be inaccurate. Consider using '#align normed_field.nhds_within_is_unit_ne_bot NormedField.nhdsWithin_isUnit_neBotₓ'. -/
@[instance]
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using punctured_nhds_ne_bot (0 : α)
#align normed_field.nhds_within_is_unit_ne_bot NormedField.nhdsWithin_isUnit_neBot

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

/- warning: normed_field.exists_lt_norm_lt -> NormedField.exists_lt_norm_lt is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α] {r₁ : Real} {r₂ : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r₁) -> (LT.lt.{0} Real Real.hasLt r₁ r₂) -> (Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} Real Real.hasLt r₁ (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)) x)) (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)) x) r₂)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α] {r₁ : Real} {r₂ : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r₁) -> (LT.lt.{0} Real Real.instLTReal r₁ r₂) -> (Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} Real Real.instLTReal r₁ (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)) x)) (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)) x) r₂)))
Case conversion may be inaccurate. Consider using '#align normed_field.exists_lt_norm_lt NormedField.exists_lt_norm_ltₓ'. -/
theorem exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h
#align normed_field.exists_lt_norm_lt NormedField.exists_lt_norm_lt

/- warning: normed_field.exists_lt_nnnorm_lt -> NormedField.exists_lt_nnnorm_lt is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α] {r₁ : NNReal} {r₂ : NNReal}, (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r₁ r₂) -> (Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r₁ (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)))))))) x)) (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)))))))) x) r₂)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α] {r₁ : NNReal} {r₂ : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r₁ r₂) -> (Exists.{succ u1} α (fun (x : α) => And (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r₁ (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)))))))) x)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)))))))) x) r₂)))
Case conversion may be inaccurate. Consider using '#align normed_field.exists_lt_nnnorm_lt NormedField.exists_lt_nnnorm_ltₓ'. -/
theorem exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ := by
  exact_mod_cast exists_lt_norm_lt α r₁.prop h
#align normed_field.exists_lt_nnnorm_lt NormedField.exists_lt_nnnorm_lt

/- warning: normed_field.densely_ordered_range_norm -> NormedField.denselyOrdered_range_norm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α], DenselyOrdered.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.range.{0, succ u1} Real α (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))) (Subtype.hasLt.{0} Real Real.hasLt (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.range.{0, succ u1} Real α (Norm.norm.{u1} α (NormedField.toHasNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α], DenselyOrdered.{0} (Set.Elem.{0} Real (Set.range.{0, succ u1} Real α (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))) (Subtype.lt.{0} Real Real.instLTReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.range.{0, succ u1} Real α (Norm.norm.{u1} α (NormedField.toNorm.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align normed_field.densely_ordered_range_norm NormedField.denselyOrdered_range_normₓ'. -/
instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α → ℝ))
    where dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    exact
      let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
      ⟨⟨‖z‖, z, rfl⟩, h⟩
#align normed_field.densely_ordered_range_norm NormedField.denselyOrdered_range_norm

/- warning: normed_field.densely_ordered_range_nnnorm -> NormedField.denselyOrdered_range_nnnorm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α], DenselyOrdered.{0} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.range.{0, succ u1} NNReal α (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))))))))) (Subtype.hasLt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.range.{0, succ u1} NNReal α (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))))))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α], DenselyOrdered.{0} (Set.Elem.{0} NNReal (Set.range.{0, succ u1} NNReal α (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))))))))) (Subtype.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (fun (x : NNReal) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.range.{0, succ u1} NNReal α (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1))))))))))))
Case conversion may be inaccurate. Consider using '#align normed_field.densely_ordered_range_nnnorm NormedField.denselyOrdered_range_nnnormₓ'. -/
instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α → ℝ≥0))
    where dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    exact
      let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
      ⟨⟨‖z‖₊, z, rfl⟩, h⟩
#align normed_field.densely_ordered_range_nnnorm NormedField.denselyOrdered_range_nnnorm

/- warning: normed_field.dense_range_nnnorm -> NormedField.denseRange_nnnorm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α], DenseRange.{0, u1} NNReal NNReal.topologicalSpace α (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)))))))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : DenselyNormedField.{u1} α], DenseRange.{0, u1} NNReal NNReal.instTopologicalSpaceNNReal α (NNNorm.nnnorm.{u1} α (SeminormedAddGroup.toNNNorm.{u1} α (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} α (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} α (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α (NormedCommRing.toNormedRing.{u1} α (NormedField.toNormedCommRing.{u1} α (DenselyNormedField.toNormedField.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align normed_field.dense_range_nnnorm NormedField.denseRange_nnnormₓ'. -/
theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩
#align normed_field.dense_range_nnnorm NormedField.denseRange_nnnorm

end Densely

end NormedField

instance : NormedCommRing ℝ :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul := fun x y => (abs_mul x y).le }

noncomputable instance : NormedField ℝ :=
  { Real.normedAddCommGroup with norm_mul' := abs_mul }

noncomputable instance : DenselyNormedField ℝ
    where lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

/- warning: real.to_nnreal_mul_nnnorm -> Real.toNNReal_mul_nnnorm is a dubious translation:
lean 3 declaration is
  forall {x : Real} (y : Real), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Real.toNNReal x) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) y)) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)))
but is expected to have type
  forall {x : Real} (y : Real), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (Real.toNNReal x) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) y)) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_mul_nnnorm Real.toNNReal_mul_nnnormₓ'. -/
theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  simp [Real.toNNReal_of_nonneg, nnnorm, norm_of_nonneg, hx]
#align real.to_nnreal_mul_nnnorm Real.toNNReal_mul_nnnorm

/- warning: real.nnnorm_mul_to_nnreal -> Real.nnnorm_mul_toNNReal is a dubious translation:
lean 3 declaration is
  forall (x : Real) {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) x) (Real.toNNReal y)) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)))
but is expected to have type
  forall (x : Real) {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) x) (Real.toNNReal y)) (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)))
Case conversion may be inaccurate. Consider using '#align real.nnnorm_mul_to_nnreal Real.nnnorm_mul_toNNRealₓ'. -/
theorem nnnorm_mul_toNNReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  simp [Real.toNNReal_of_nonneg, nnnorm, norm_of_nonneg, hy]
#align real.nnnorm_mul_to_nnreal Real.nnnorm_mul_toNNReal

end Real

namespace NNReal

open NNReal

/- warning: nnreal.norm_eq -> NNReal.norm_eq is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} Real (Norm.norm.{0} Real Real.hasNorm ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x)
but is expected to have type
  forall (x : NNReal), Eq.{1} Real (Norm.norm.{0} Real Real.norm (NNReal.toReal x)) (NNReal.toReal x)
Case conversion may be inaccurate. Consider using '#align nnreal.norm_eq NNReal.norm_eqₓ'. -/
@[simp]
theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]
#align nnreal.norm_eq NNReal.norm_eq

/- warning: nnreal.nnnorm_eq -> NNReal.nnnorm_eq is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x)) x
but is expected to have type
  forall (x : NNReal), Eq.{1} NNReal (NNNorm.nnnorm.{0} Real (SeminormedAddGroup.toNNNorm.{0} Real (SeminormedAddCommGroup.toSeminormedAddGroup.{0} Real (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Real (NonUnitalNormedRing.toNonUnitalSeminormedRing.{0} Real (NormedRing.toNonUnitalNormedRing.{0} Real (NormedCommRing.toNormedRing.{0} Real Real.normedCommRing)))))) (NNReal.toReal x)) x
Case conversion may be inaccurate. Consider using '#align nnreal.nnnorm_eq NNReal.nnnorm_eqₓ'. -/
@[simp]
theorem nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x :=
  NNReal.eq <| Real.norm_of_nonneg x.2
#align nnreal.nnnorm_eq NNReal.nnnorm_eq

end NNReal

/- warning: norm_norm -> norm_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] (x : α), Eq.{1} Real (Norm.norm.{0} Real Real.hasNorm (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) x)) (Norm.norm.{u1} α (SeminormedAddCommGroup.toHasNorm.{u1} α _inst_1) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} α] (x : α), Eq.{1} Real (Norm.norm.{0} Real Real.norm (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) x)) (Norm.norm.{u1} α (SeminormedAddCommGroup.toNorm.{u1} α _inst_1) x)
Case conversion may be inaccurate. Consider using '#align norm_norm norm_normₓ'. -/
@[simp]
theorem norm_norm [SeminormedAddCommGroup α] (x : α) : ‖‖x‖‖ = ‖x‖ :=
  Real.norm_of_nonneg (norm_nonneg _)
#align norm_norm norm_norm

#print nnnorm_norm /-
@[simp]
theorem nnnorm_norm [SeminormedAddCommGroup α] (a : α) : ‖‖a‖‖₊ = ‖a‖₊ := by
  simpa [Real.nnnorm_of_nonneg (norm_nonneg a)]
#align nnnorm_norm nnnorm_norm
-/

/- warning: normed_add_comm_group.tendsto_at_top -> NormedAddCommGroup.tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] {β : Type.{u2}} [_inst_3 : SeminormedAddCommGroup.{u2} β] {f : α -> β} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_3))) b)) (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{succ u1} α (fun (N : α) => forall (n : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) N n) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{u2} β (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_3) (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (SeminormedAddGroup.toAddGroup.{u2} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} β _inst_3))))) (f n) b)) ε))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Nonempty.{succ u2} α] [_inst_2 : SemilatticeSup.{u2} α] {β : Type.{u1}} [_inst_3 : SeminormedAddCommGroup.{u1} β] {f : α -> β} {b : β}, Iff (Filter.Tendsto.{u2, u1} α β f (Filter.atTop.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_2))) (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β _inst_3))) b)) (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{succ u2} α (fun (N : α) => forall (n : α), (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_2))) N n) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} β (SeminormedAddCommGroup.toNorm.{u1} β _inst_3) (HSub.hSub.{u1, u1, u1} β β β (instHSub.{u1} β (SubNegMonoid.toSub.{u1} β (AddGroup.toSubNegMonoid.{u1} β (SeminormedAddGroup.toAddGroup.{u1} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} β _inst_3))))) (f n) b)) ε))))
Case conversion may be inaccurate. Consider using '#align normed_add_comm_group.tendsto_at_top NormedAddCommGroup.tendsto_atTopₓ'. -/
/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [SemilatticeSup α] {β : Type _}
    [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iffₓ Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])
#align normed_add_comm_group.tendsto_at_top NormedAddCommGroup.tendsto_atTop

/- warning: normed_add_comm_group.tendsto_at_top' -> NormedAddCommGroup.tendsto_atTop' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : SemilatticeSup.{u1} α] [_inst_3 : NoMaxOrder.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)))] {β : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} β] {f : α -> β} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (Filter.atTop.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_4))) b)) (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{succ u1} α (fun (N : α) => forall (n : α), (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) N n) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{u2} β (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_4) (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (SeminormedAddGroup.toAddGroup.{u2} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} β _inst_4))))) (f n) b)) ε))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Nonempty.{succ u2} α] [_inst_2 : SemilatticeSup.{u2} α] [_inst_3 : NoMaxOrder.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_2)))] {β : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} β] {f : α -> β} {b : β}, Iff (Filter.Tendsto.{u2, u1} α β f (Filter.atTop.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_2))) (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β _inst_4))) b)) (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{succ u2} α (fun (N : α) => forall (n : α), (LT.lt.{u2} α (Preorder.toLT.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_2))) N n) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} β (SeminormedAddCommGroup.toNorm.{u1} β _inst_4) (HSub.hSub.{u1, u1, u1} β β β (instHSub.{u1} β (SubNegMonoid.toSub.{u1} β (AddGroup.toSubNegMonoid.{u1} β (SeminormedAddGroup.toAddGroup.{u1} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} β _inst_4))))) (f n) b)) ε))))
Case conversion may be inaccurate. Consider using '#align normed_add_comm_group.tendsto_at_top' NormedAddCommGroup.tendsto_atTop'ₓ'. -/
/-- A variant of `normed_add_comm_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [SemilatticeSup α] [NoMaxOrder α]
    {β : Type _} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iffₓ Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])
#align normed_add_comm_group.tendsto_at_top' NormedAddCommGroup.tendsto_atTop'

instance : NormedCommRing ℤ :=
  {
    Int.normedAddCommGroup with
    norm_mul := fun m n => le_of_eq <| by simp only [norm, Int.cast_mul, abs_mul]
    mul_comm := mul_comm }

instance : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩

instance : NormedField ℚ :=
  { Rat.normedAddCommGroup with
    norm_mul' := fun r₁ r₂ => by simp only [norm, Rat.cast_mul, abs_mul] }

instance : DenselyNormedField ℚ
    where lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by
      unfold norm
      rwa [abs_of_pos (h₀.trans_lt h.1)]⟩

section RingHomIsometric

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

#print RingHomIsometric /-
/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  is_iso : ∀ {x : R₁}, ‖σ x‖ = ‖x‖
#align ring_hom_isometric RingHomIsometric
-/

attribute [simp] RingHomIsometric.is_iso

variable [SeminormedRing R₁] [SeminormedRing R₂] [SeminormedRing R₃]

#print RingHomIsometric.ids /-
instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨fun x => rfl⟩
#align ring_hom_isometric.ids RingHomIsometric.ids
-/

end RingHomIsometric

/-! ### Induced normed structures -/


section Induced

variable {F : Type _} (R S : Type _)

#print NonUnitalSeminormedRing.induced /-
/-- A non-unital ring homomorphism from an `non_unital_ring` to a `non_unital_semi_normed_ring`
induces a `non_unital_semi_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R :=
  { SeminormedAddCommGroup.induced R S f with
    norm_mul := fun x y => by
      unfold norm
      exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }
#align non_unital_semi_normed_ring.induced NonUnitalSeminormedRing.induced
-/

#print NonUnitalNormedRing.induced /-
/-- An injective non-unital ring homomorphism from an `non_unital_ring` to a
`non_unital_normed_ring` induces a `non_unital_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align non_unital_normed_ring.induced NonUnitalNormedRing.induced
-/

#print SeminormedRing.induced /-
/-- A non-unital ring homomorphism from an `ring` to a `semi_normed_ring` induces a
`semi_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f with }
#align semi_normed_ring.induced SeminormedRing.induced
-/

#print NormedRing.induced /-
/-- An injective non-unital ring homomorphism from an `ring` to a `normed_ring` induces a
`normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align normed_ring.induced NormedRing.induced
-/

#print SeminormedCommRing.induced /-
/-- A non-unital ring homomorphism from a `comm_ring` to a `semi_normed_ring` induces a
`semi_normed_comm_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f with
    mul_comm := mul_comm }
#align semi_normed_comm_ring.induced SeminormedCommRing.induced
-/

#print NormedCommRing.induced /-
/-- An injective non-unital ring homomorphism from an `comm_ring` to a `normed_ring` induces a
`normed_comm_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R :=
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align normed_comm_ring.induced NormedCommRing.induced
-/

#print NormedDivisionRing.induced /-
/-- An injective non-unital ring homomorphism from an `division_ring` to a `normed_ring` induces a
`normed_division_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S] [NonUnitalRingHomClass F R S]
    (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf with
    norm_mul' := fun x y => by
      unfold norm
      exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) }
#align normed_division_ring.induced NormedDivisionRing.induced
-/

#print NormedField.induced /-
/-- An injective non-unital ring homomorphism from an `field` to a `normed_ring` induces a
`normed_field` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with }
#align normed_field.induced NormedField.induced
-/

/- warning: norm_one_class.induced -> NormOneClass.induced is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} (R : Type.{u2}) (S : Type.{u3}) [_inst_1 : Ring.{u2} R] [_inst_2 : SeminormedRing.{u3} S] [_inst_3 : NormOneClass.{u3} S (SeminormedRing.toHasNorm.{u3} S _inst_2) (AddMonoidWithOne.toOne.{u3} S (AddGroupWithOne.toAddMonoidWithOne.{u3} S (AddCommGroupWithOne.toAddGroupWithOne.{u3} S (Ring.toAddCommGroupWithOne.{u3} S (SeminormedRing.toRing.{u3} S _inst_2)))))] [_inst_4 : RingHomClass.{u1, u2, u3} F R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u3} S (Ring.toNonAssocRing.{u3} S (SeminormedRing.toRing.{u3} S _inst_2)))] (f : F), NormOneClass.{u2} R (SeminormedRing.toHasNorm.{u2} R (SeminormedRing.induced.{u1, u2, u3} F R S _inst_1 _inst_2 (RingHomClass.toNonUnitalRingHomClass.{u1, u2, u3} F R S (NonAssocRing.toNonAssocSemiring.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1)) (NonAssocRing.toNonAssocSemiring.{u3} S (Ring.toNonAssocRing.{u3} S (SeminormedRing.toRing.{u3} S _inst_2))) _inst_4) f)) (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R _inst_1))))
but is expected to have type
  forall {F : Type.{u3}} (R : Type.{u2}) (S : Type.{u1}) [_inst_1 : Ring.{u2} R] [_inst_2 : SeminormedRing.{u1} S] [_inst_3 : NormOneClass.{u1} S (SeminormedRing.toNorm.{u1} S _inst_2) (Semiring.toOne.{u1} S (Ring.toSemiring.{u1} S (SeminormedRing.toRing.{u1} S _inst_2)))] [_inst_4 : RingHomClass.{u3, u2, u1} F R S (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (Ring.toSemiring.{u1} S (SeminormedRing.toRing.{u1} S _inst_2)))] (f : F), NormOneClass.{u2} R (SeminormedRing.toNorm.{u2} R (SeminormedRing.induced.{u3, u2, u1} F R S _inst_1 _inst_2 (RingHomClass.toNonUnitalRingHomClass.{u3, u2, u1} F R S (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} S (Ring.toSemiring.{u1} S (SeminormedRing.toRing.{u1} S _inst_2))) _inst_4) f)) (Semiring.toOne.{u2} R (Ring.toSemiring.{u2} R _inst_1))
Case conversion may be inaccurate. Consider using '#align norm_one_class.induced NormOneClass.inducedₓ'. -/
/-- A ring homomorphism from a `ring R` to a `semi_normed_ring S` which induces the norm structure
`semi_normed_ring.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormOneClass.induced {F : Type _} (R S : Type _) [Ring R] [SeminormedRing S]
    [NormOneClass S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toHasNorm _ :=
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }
#align norm_one_class.induced NormOneClass.induced

end Induced

namespace SubringClass

variable {S R : Type _} [SetLike S R]

#print SubringClass.toSeminormedRing /-
instance toSeminormedRing [SeminormedRing R] [SubringClass S R] (s : S) : SeminormedRing s :=
  SeminormedRing.induced s R (SubringClass.subtype s)
#align subring_class.to_semi_normed_ring SubringClass.toSeminormedRing
-/

#print SubringClass.toNormedRing /-
instance toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective
#align subring_class.to_normed_ring SubringClass.toNormedRing
-/

#print SubringClass.toSeminormedCommRing /-
instance toSeminormedCommRing [SeminormedCommRing R] [h : SubringClass S R] (s : S) :
    SeminormedCommRing s :=
  { SubringClass.toSeminormedRing s with mul_comm := mul_comm }
#align subring_class.to_semi_normed_comm_ring SubringClass.toSeminormedCommRing
-/

#print SubringClass.toNormedCommRing /-
instance toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCommRing s :=
  { SubringClass.toNormedRing s with mul_comm := mul_comm }
#align subring_class.to_normed_comm_ring SubringClass.toNormedCommRing
-/

end SubringClass

-- Guard again import creep.
assert_not_exists RestrictScalars

