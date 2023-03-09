/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module topology.metric_space.algebra
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Topology.MetricSpace.Lipschitz

/-!
# Compatibility of algebraic operations with metric space structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define mixin typeclasses `has_lipschitz_mul`, `has_lipschitz_add`,
`has_bounded_smul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `has_continuous_mul` instance from `has_lipschitz_mul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`uniform_group`) is structured differently.

-/


open NNReal

noncomputable section

variable (α β : Type _) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

#print LipschitzAdd /-
/-- Class `has_lipschitz_add M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2
#align has_lipschitz_add LipschitzAdd
-/

#print LipschitzMul /-
/-- Class `has_lipschitz_mul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive]
class LipschitzMul [Monoid β] : Prop where
  lipschitz_mul : ∃ C, LipschitzWith C fun p : β × β => p.1 * p.2
#align has_lipschitz_mul LipschitzMul
#align has_lipschitz_add LipschitzAdd
-/

variable [Monoid β]

#print LipschitzMul.C /-
/-- The Lipschitz constant of a monoid `β` satisfying `has_lipschitz_mul` -/
@[to_additive "The Lipschitz constant of an `add_monoid` `β` satisfying `has_lipschitz_add`"]
def LipschitzMul.C [_i : LipschitzMul β] : ℝ≥0 :=
  Classical.choose _i.lipschitz_mul
#align has_lipschitz_mul.C LipschitzMul.C
#align has_lipschitz_add.C LipschitzAdd.C
-/

variable {β}

/- warning: lipschitz_with_lipschitz_const_mul_edist -> lipschitzWith_lipschitz_const_mul_edist is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_i : LipschitzMul.{u1} β _inst_2 _inst_3], LipschitzWith.{u1, u1} (Prod.{u1, u1} β β) β (Prod.pseudoEMetricSpaceMax.{u1, u1} β β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2)) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) (LipschitzMul.C.{u1} β _inst_2 _inst_3 _i) (fun (p : Prod.{u1, u1} β β) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) (Prod.fst.{u1, u1} β β p) (Prod.snd.{u1, u1} β β p))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_i : LipschitzMul.{u1} β _inst_2 _inst_3], LipschitzWith.{u1, u1} (Prod.{u1, u1} β β) β (Prod.pseudoEMetricSpaceMax.{u1, u1} β β (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2)) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} β _inst_2) (LipschitzMul.C.{u1} β _inst_2 _inst_3 _i) (fun (p : Prod.{u1, u1} β β) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) (Prod.fst.{u1, u1} β β p) (Prod.snd.{u1, u1} β β p))
Case conversion may be inaccurate. Consider using '#align lipschitz_with_lipschitz_const_mul_edist lipschitzWith_lipschitz_const_mul_edistₓ'. -/
@[to_additive]
theorem lipschitzWith_lipschitz_const_mul_edist [_i : LipschitzMul β] :
    LipschitzWith (LipschitzMul.C β) fun p : β × β => p.1 * p.2 :=
  Classical.choose_spec _i.lipschitz_mul
#align lipschitz_with_lipschitz_const_mul_edist lipschitzWith_lipschitz_const_mul_edist
#align lipschitz_with_lipschitz_const_add_edist lipschitzWith_lipschitz_const_add_edist

variable [LipschitzMul β]

/- warning: lipschitz_with_lipschitz_const_mul -> lipschitz_with_lipschitz_const_mul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3] (p : Prod.{u1, u1} β β) (q : Prod.{u1, u1} β β), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} β (PseudoMetricSpace.toHasDist.{u1} β _inst_2) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) (Prod.fst.{u1, u1} β β p) (Prod.snd.{u1, u1} β β p)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) (Prod.fst.{u1, u1} β β q) (Prod.snd.{u1, u1} β β q))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (LipschitzMul.C.{u1} β _inst_2 _inst_3 _inst_4)) (Dist.dist.{u1} (Prod.{u1, u1} β β) (PseudoMetricSpace.toHasDist.{u1} (Prod.{u1, u1} β β) (Prod.pseudoMetricSpaceMax.{u1, u1} β β _inst_2 _inst_2)) p q))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3] (p : Prod.{u1, u1} β β) (q : Prod.{u1, u1} β β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β _inst_2) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) (Prod.fst.{u1, u1} β β p) (Prod.snd.{u1, u1} β β p)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) (Prod.fst.{u1, u1} β β q) (Prod.snd.{u1, u1} β β q))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal (LipschitzMul.C.{u1} β _inst_2 _inst_3 _inst_4)) (Dist.dist.{u1} (Prod.{u1, u1} β β) (PseudoMetricSpace.toDist.{u1} (Prod.{u1, u1} β β) (Prod.pseudoMetricSpaceMax.{u1, u1} β β _inst_2 _inst_2)) p q))
Case conversion may be inaccurate. Consider using '#align lipschitz_with_lipschitz_const_mul lipschitz_with_lipschitz_const_mulₓ'. -/
@[to_additive]
theorem lipschitz_with_lipschitz_const_mul :
    ∀ p q : β × β, dist (p.1 * p.2) (q.1 * q.2) ≤ LipschitzMul.C β * dist p q :=
  by
  rw [← lipschitzWith_iff_dist_le_mul]
  exact lipschitzWith_lipschitz_const_mul_edist
#align lipschitz_with_lipschitz_const_mul lipschitz_with_lipschitz_const_mul
#align lipschitz_with_lipschitz_const_add lipschitz_with_lipschitz_const_add

/- warning: has_lipschitz_mul.has_continuous_mul -> LipschitzMul.continuousMul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3], ContinuousMul.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β _inst_2)) (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3], ContinuousMul.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β _inst_2)) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))
Case conversion may be inaccurate. Consider using '#align has_lipschitz_mul.has_continuous_mul LipschitzMul.continuousMulₓ'. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LipschitzMul.continuousMul : ContinuousMul β :=
  ⟨lipschitzWith_lipschitz_const_mul_edist.Continuous⟩
#align has_lipschitz_mul.has_continuous_mul LipschitzMul.continuousMul
#align has_lipschitz_add.has_continuous_add LipschitzAdd.continuousAdd

/- warning: submonoid.has_lipschitz_mul -> Submonoid.lipschitzMul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3] (s : Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)), LipschitzMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) β (Submonoid.setLike.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) s) (Subtype.pseudoMetricSpace.{u1} β _inst_2 (fun (x : β) => Membership.Mem.{u1, u1} β (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) β (Submonoid.setLike.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) x s)) (Submonoid.toMonoid.{u1} β _inst_3 s)
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3] (s : Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)), LipschitzMul.{u1} (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) β (Submonoid.instSetLikeSubmonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) x s)) (Subtype.pseudoMetricSpace.{u1} β _inst_2 (fun (x : β) => Membership.mem.{u1, u1} β (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3)) β (Submonoid.instSetLikeSubmonoid.{u1} β (Monoid.toMulOneClass.{u1} β _inst_3))) x s)) (Submonoid.toMonoid.{u1} β _inst_3 s)
Case conversion may be inaccurate. Consider using '#align submonoid.has_lipschitz_mul Submonoid.lipschitzMulₓ'. -/
@[to_additive]
instance Submonoid.lipschitzMul (s : Submonoid β) : LipschitzMul s
    where lipschitz_mul :=
    ⟨LipschitzMul.C β, by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
      convert lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩
#align submonoid.has_lipschitz_mul Submonoid.lipschitzMul
#align add_submonoid.has_lipschitz_add AddSubmonoid.lipschitzAdd

/- warning: mul_opposite.has_lipschitz_mul -> MulOpposite.lipschitzMul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3], LipschitzMul.{u1} (MulOpposite.{u1} β) (MulOpposite.pseudoMetricSpace.{u1} β _inst_2) (MulOpposite.monoid.{u1} β _inst_3)
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] [_inst_3 : Monoid.{u1} β] [_inst_4 : LipschitzMul.{u1} β _inst_2 _inst_3], LipschitzMul.{u1} (MulOpposite.{u1} β) (MulOpposite.instPseudoMetricSpaceMulOpposite.{u1} β _inst_2) (MulOpposite.instMonoidMulOpposite.{u1} β _inst_3)
Case conversion may be inaccurate. Consider using '#align mul_opposite.has_lipschitz_mul MulOpposite.lipschitzMulₓ'. -/
@[to_additive]
instance MulOpposite.lipschitzMul : LipschitzMul βᵐᵒᵖ
    where lipschitz_mul :=
    ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
      (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
        (congr_arg _ <| max_comm _ _)⟩
#align mul_opposite.has_lipschitz_mul MulOpposite.lipschitzMul
#align add_opposite.has_lipschitz_add AddOpposite.lipschitzAdd

#print Real.hasLipschitzAdd /-
-- this instance could be deduced from `normed_add_comm_group.has_lipschitz_add`, but we prove it
-- separately here so that it is available earlier in the hierarchy
instance Real.hasLipschitzAdd : LipschitzAdd ℝ
    where lipschitz_add :=
    ⟨2, by
      rw [lipschitzWith_iff_dist_le_mul]
      intro p q
      simp only [Real.dist_eq, Prod.dist_eq, Prod.fst_sub, Prod.snd_sub, NNReal.coe_one,
        [anonymous]]
      convert le_trans (abs_add (p.1 - q.1) (p.2 - q.2)) _ using 2
      · abel
      have := le_max_left (|p.1 - q.1|) (|p.2 - q.2|)
      have := le_max_right (|p.1 - q.1|) (|p.2 - q.2|)
      linarith⟩
#align real.has_lipschitz_add Real.hasLipschitzAdd
-/

/- warning: nnreal.has_lipschitz_add -> NNReal.hasLipschitzAdd is a dubious translation:
lean 3 declaration is
  LipschitzAdd.{0} NNReal NNReal.pseudoMetricSpace (AddMonoidWithOne.toAddMonoid.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))
but is expected to have type
  LipschitzAdd.{0} NNReal instPseudoMetricSpaceNNReal (AddMonoidWithOne.toAddMonoid.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))
Case conversion may be inaccurate. Consider using '#align nnreal.has_lipschitz_add NNReal.hasLipschitzAddₓ'. -/
-- this instance has the same proof as `add_submonoid.has_lipschitz_add`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
instance NNReal.hasLipschitzAdd : LipschitzAdd ℝ≥0
    where lipschitz_add :=
    ⟨LipschitzAdd.C ℝ, by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
      convert lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : ℝ), x₂⟩ ⟨y₁, y₂⟩ using 1⟩
#align nnreal.has_lipschitz_add NNReal.hasLipschitzAdd

end LipschitzMul

section BoundedSmul

variable [Zero α] [Zero β] [SMul α β]

#print BoundedSmul /-
/-- Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` both with
distinguished points `0`, requiring compatibility of the action in the sense that
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`. -/
class BoundedSmul : Prop where
  dist_smul_pair' : ∀ x : α, ∀ y₁ y₂ : β, dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂
  dist_pair_smul' : ∀ x₁ x₂ : α, ∀ y : β, dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0
#align has_bounded_smul BoundedSmul
-/

variable {α β} [BoundedSmul α β]

/- warning: dist_smul_pair -> dist_smul_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] [_inst_3 : Zero.{u1} α] [_inst_4 : Zero.{u2} β] [_inst_5 : SMul.{u1, u2} α β] [_inst_6 : BoundedSmul.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] (x : α) (y₁ : β) (y₂ : β), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (SMul.smul.{u1, u2} α β _inst_5 x y₁) (SMul.smul.{u1, u2} α β _inst_5 x y₂)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_3)))) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) y₁ y₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] [_inst_3 : Zero.{u1} α] [_inst_4 : Zero.{u2} β] [_inst_5 : SMul.{u1, u2} α β] [_inst_6 : BoundedSmul.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] (x : α) (y₁ : β) (y₂ : β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_5) x y₁) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_5) x y₂)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α _inst_3))) (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) y₁ y₂))
Case conversion may be inaccurate. Consider using '#align dist_smul_pair dist_smul_pairₓ'. -/
theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂ :=
  BoundedSmul.dist_smul_pair' x y₁ y₂
#align dist_smul_pair dist_smul_pair

/- warning: dist_pair_smul -> dist_pair_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] [_inst_3 : Zero.{u1} α] [_inst_4 : Zero.{u2} β] [_inst_5 : SMul.{u1, u2} α β] [_inst_6 : BoundedSmul.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] (x₁ : α) (x₂ : α) (y : β), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (SMul.smul.{u1, u2} α β _inst_5 x₁ y) (SMul.smul.{u1, u2} α β _inst_5 x₂ y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₁ x₂) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_4)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] [_inst_3 : Zero.{u1} α] [_inst_4 : Zero.{u2} β] [_inst_5 : SMul.{u1, u2} α β] [_inst_6 : BoundedSmul.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 _inst_5] (x₁ : α) (x₂ : α) (y : β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_5) x₁ y) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_5) x₂ y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₁ x₂) (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_4))))
Case conversion may be inaccurate. Consider using '#align dist_pair_smul dist_pair_smulₓ'. -/
theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0 :=
  BoundedSmul.dist_pair_smul' x₁ x₂ y
#align dist_pair_smul dist_pair_smul

#print BoundedSmul.continuousSMul /-
-- see Note [lower instance priority]
/-- The typeclass `has_bounded_smul` on a metric-space scalar action implies continuity of the
action. -/
instance (priority := 100) BoundedSmul.continuousSMul : ContinuousSMul α β
    where continuous_smul := by
    rw [Metric.continuous_iff]
    rintro ⟨a, b⟩ ε hε
    have : 0 ≤ dist a 0 := dist_nonneg
    have : 0 ≤ dist b 0 := dist_nonneg
    let δ : ℝ := min 1 ((dist a 0 + dist b 0 + 2)⁻¹ * ε)
    have hδ_pos : 0 < δ :=
      by
      refine' lt_min_iff.mpr ⟨by norm_num, mul_pos _ hε⟩
      rw [inv_pos]
      linarith
    refine' ⟨δ, hδ_pos, _⟩
    rintro ⟨a', b'⟩ hab'
    calc
      _ ≤ _ := dist_triangle _ (a • b') _
      _ ≤ δ * (dist a 0 + dist b 0 + δ) := _
      _ < ε := _
      
    · have : 0 ≤ dist a' a := dist_nonneg
      have := dist_triangle b' b 0
      have := dist_comm (a • b') (a' • b')
      have := dist_comm a a'
      have : dist a' a ≤ dist (a', b') (a, b) := le_max_left _ _
      have : dist b' b ≤ dist (a', b') (a, b) := le_max_right _ _
      have := dist_smul_pair a b' b
      have := dist_pair_smul a a' b'
      nlinarith
    · have : δ ≤ _ := min_le_right _ _
      have : δ ≤ _ := min_le_left _ _
      have : (dist a 0 + dist b 0 + 2)⁻¹ * (ε * (dist a 0 + dist b 0 + δ)) < ε := by
        rw [inv_mul_lt_iff] <;> nlinarith
      nlinarith
#align has_bounded_smul.has_continuous_smul BoundedSmul.continuousSMul
-/

/- warning: real.has_bounded_smul -> Real.hasBoundedSmul is a dubious translation:
lean 3 declaration is
  BoundedSmul.{0, 0} Real Real Real.pseudoMetricSpace Real.pseudoMetricSpace Real.hasZero Real.hasZero (Mul.toSMul.{0} Real Real.hasMul)
but is expected to have type
  BoundedSmul.{0, 0} Real Real Real.pseudoMetricSpace Real.pseudoMetricSpace Real.instZeroReal Real.instZeroReal (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))
Case conversion may be inaccurate. Consider using '#align real.has_bounded_smul Real.hasBoundedSmulₓ'. -/
-- this instance could be deduced from `normed_space.has_bounded_smul`, but we prove it separately
-- here so that it is available earlier in the hierarchy
instance Real.hasBoundedSmul : BoundedSmul ℝ ℝ
    where
  dist_smul_pair' x y₁ y₂ := by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le
#align real.has_bounded_smul Real.hasBoundedSmul

/- warning: nnreal.has_bounded_smul -> NNReal.hasBoundedSmul is a dubious translation:
lean 3 declaration is
  BoundedSmul.{0, 0} NNReal NNReal NNReal.pseudoMetricSpace NNReal.pseudoMetricSpace (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (Mul.toSMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))
but is expected to have type
  BoundedSmul.{0, 0} NNReal NNReal instPseudoMetricSpaceNNReal instPseudoMetricSpaceNNReal instNNRealZero instNNRealZero (Algebra.toSMul.{0, 0} NNReal NNReal instNNRealCommSemiring instNNRealSemiring (Algebra.id.{0} NNReal instNNRealCommSemiring))
Case conversion may be inaccurate. Consider using '#align nnreal.has_bounded_smul NNReal.hasBoundedSmulₓ'. -/
instance NNReal.hasBoundedSmul : BoundedSmul ℝ≥0 ℝ≥0
    where
  dist_smul_pair' x y₁ y₂ := by convert dist_smul_pair (x : ℝ) (y₁ : ℝ) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert dist_pair_smul (x₁ : ℝ) x₂ (y : ℝ) using 1
#align nnreal.has_bounded_smul NNReal.hasBoundedSmul

#print BoundedSmul.op /-
/-- If a scalar is central, then its right action is bounded when its left action is. -/
instance BoundedSmul.op [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : BoundedSmul αᵐᵒᵖ β
    where
  dist_smul_pair' :=
    MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using dist_pair_smul x₁ x₂ y
#align has_bounded_smul.op BoundedSmul.op
-/

end BoundedSmul

instance [Monoid α] [LipschitzMul α] : LipschitzAdd (Additive α) :=
  ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩

instance [AddMonoid α] [LipschitzAdd α] : LipschitzMul (Multiplicative α) :=
  ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]
instance [Monoid α] [LipschitzMul α] : LipschitzMul αᵒᵈ :=
  ‹LipschitzMul α›

