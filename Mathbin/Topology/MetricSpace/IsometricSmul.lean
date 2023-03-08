/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.isometric_smul
! leanprover-community/mathlib commit 832a8ba8f10f11fea99367c469ff802e69a5b8ec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Isometry

/-!
# Group actions by isometries

In this file we define two typeclasses:

- `has_isometric_smul M X` says that `M` multiplicatively acts on a (pseudo extended) metric space
  `X` by isometries;
- `has_isometric_vadd` is an additive version of `has_isometric_smul`.

We also prove basic facts about isometric actions and define bundled isometries
`isometry_equiv.const_mul`, `isometry_equiv.mul_left`, `isometry_equiv.mul_right`,
`isometry_equiv.div_left`, `isometry_equiv.div_right`, and `isometry_equiv.inv`, as well as their
additive versions.

If `G` is a group, then `has_isometric_smul G G` means that `G` has a left-invariant metric while
`has_isometric_smul Gᵐᵒᵖ G` means that `G` has a right-invariant metric. For a commutative group,
these two notions are equivalent. A group with a right-invariant metric can be also represented as a
`normed_group`.
-/


open Set

open ENNReal Pointwise

universe u v w

variable (M : Type u) (G : Type v) (X : Type w)

#print IsometricVAdd /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`isometry_vadd] [] -/
/-- An additive action is isometric if each map `x ↦ c +ᵥ x` is an isometry. -/
class IsometricVAdd [PseudoEMetricSpace X] [VAdd M X] : Prop where
  isometry_vadd : ∀ c : M, Isometry ((· +ᵥ ·) c : X → X)
#align has_isometric_vadd IsometricVAdd
-/

#print IsometricSMul /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`isometry_smul] [] -/
/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive]
class IsometricSMul [PseudoEMetricSpace X] [SMul M X] : Prop where
  isometry_smul : ∀ c : M, Isometry ((· • ·) c : X → X)
#align has_isometric_smul IsometricSMul
#align has_isometric_vadd IsometricVAdd
-/

export IsometricVAdd (isometry_vadd)

export IsometricSMul (isometry_smul)

#print IsometricSMul.to_continuousConstSMul /-
@[to_additive]
instance (priority := 100) IsometricSMul.to_continuousConstSMul [PseudoEMetricSpace X] [SMul M X]
    [IsometricSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (isometry_smul X c).Continuous⟩
#align has_isometric_smul.to_has_continuous_const_smul IsometricSMul.to_continuousConstSMul
#align has_isometric_vadd.to_has_continuous_const_vadd IsometricVAdd.to_continuousConstVAdd
-/

#print IsometricSMul.opposite_of_comm /-
@[to_additive]
instance (priority := 100) IsometricSMul.opposite_of_comm [PseudoEMetricSpace X] [SMul M X]
    [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] [IsometricSMul M X] : IsometricSMul Mᵐᵒᵖ X :=
  ⟨fun c x y => by simpa only [← op_smul_eq_smul] using isometry_smul X c.unop x y⟩
#align has_isometric_smul.opposite_of_comm IsometricSMul.opposite_of_comm
#align has_isometric_vadd.opposite_of_comm IsometricVAdd.opposite_of_comm
-/

variable {M G X}

section Emetric

variable [PseudoEMetricSpace X] [Group G] [MulAction G X] [IsometricSMul G X]

#print edist_smul_left /-
@[simp, to_additive]
theorem edist_smul_left [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    edist (c • x) (c • y) = edist x y :=
  isometry_smul X c x y
#align edist_smul_left edist_smul_left
#align edist_vadd_left edist_vadd_left
-/

#print isometry_mul_left /-
@[to_additive]
theorem isometry_mul_left [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] (a : M) :
    Isometry ((· * ·) a) :=
  isometry_smul M a
#align isometry_mul_left isometry_mul_left
#align isometry_add_left isometry_add_left
-/

#print edist_mul_left /-
@[simp, to_additive]
theorem edist_mul_left [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] (a b c : M) :
    edist (a * b) (a * c) = edist b c :=
  isometry_mul_left a b c
#align edist_mul_left edist_mul_left
#align edist_add_left edist_add_left
-/

#print isometry_mul_right /-
@[to_additive]
theorem isometry_mul_right [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a : M) :
    Isometry fun x => x * a :=
  isometry_smul M (MulOpposite.op a)
#align isometry_mul_right isometry_mul_right
#align isometry_add_right isometry_add_right
-/

#print edist_mul_right /-
@[simp, to_additive]
theorem edist_mul_right [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    edist (a * c) (b * c) = edist a b :=
  isometry_mul_right c a b
#align edist_mul_right edist_mul_right
#align edist_add_right edist_add_right
-/

/- warning: edist_div_right -> edist_div_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : DivInvMonoid.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M _inst_6 (Mul.toHasOppositeSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_5))))] (a : M) (b : M) (c : M), Eq.{1} ENNReal (EDist.edist.{u1} M (PseudoEMetricSpace.toHasEdist.{u1} M _inst_6) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M _inst_5)) a c) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M _inst_5)) b c)) (EDist.edist.{u1} M (PseudoEMetricSpace.toHasEdist.{u1} M _inst_6) a b)
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : DivInvMonoid.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M _inst_6 (Mul.toHasOppositeSMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_5))))] (a : M) (b : M) (c : M), Eq.{1} ENNReal (EDist.edist.{u1} M (PseudoEMetricSpace.toEDist.{u1} M _inst_6) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M _inst_5)) a c) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M _inst_5)) b c)) (EDist.edist.{u1} M (PseudoEMetricSpace.toEDist.{u1} M _inst_6) a b)
Case conversion may be inaccurate. Consider using '#align edist_div_right edist_div_rightₓ'. -/
@[simp, to_additive]
theorem edist_div_right [DivInvMonoid M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    edist (a / c) (b / c) = edist a b := by simp only [div_eq_mul_inv, edist_mul_right]
#align edist_div_right edist_div_right
#align edist_sub_right edist_sub_right

/- warning: edist_inv_inv -> edist_inv_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G), Eq.{1} ENNReal (EDist.edist.{u1} G (PseudoEMetricSpace.toHasEdist.{u1} G _inst_5) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) b)) (EDist.edist.{u1} G (PseudoEMetricSpace.toHasEdist.{u1} G _inst_5) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G), Eq.{1} ENNReal (EDist.edist.{u1} G (PseudoEMetricSpace.toEDist.{u1} G _inst_5) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) b)) (EDist.edist.{u1} G (PseudoEMetricSpace.toEDist.{u1} G _inst_5) a b)
Case conversion may be inaccurate. Consider using '#align edist_inv_inv edist_inv_invₓ'. -/
@[simp, to_additive]
theorem edist_inv_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G] (a b : G) :
    edist a⁻¹ b⁻¹ = edist a b := by
  rw [← edist_mul_left a, ← edist_mul_right _ _ b, mul_right_inv, one_mul, inv_mul_cancel_right,
    edist_comm]
#align edist_inv_inv edist_inv_inv
#align edist_neg_neg edist_neg_neg

/- warning: isometry_inv -> isometry_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], Isometry.{u1, u1} G G _inst_5 _inst_5 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], Isometry.{u1, u1} G G _inst_5 _inst_5 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))))
Case conversion may be inaccurate. Consider using '#align isometry_inv isometry_invₓ'. -/
@[to_additive]
theorem isometry_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G] :
    Isometry (Inv.inv : G → G) :=
  edist_inv_inv
#align isometry_inv isometry_inv
#align isometry_neg isometry_neg

/- warning: edist_inv -> edist_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (x : G) (y : G), Eq.{1} ENNReal (EDist.edist.{u1} G (PseudoEMetricSpace.toHasEdist.{u1} G _inst_5) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) x) y) (EDist.edist.{u1} G (PseudoEMetricSpace.toHasEdist.{u1} G _inst_5) x (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) y))
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (x : G) (y : G), Eq.{1} ENNReal (EDist.edist.{u1} G (PseudoEMetricSpace.toEDist.{u1} G _inst_5) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) x) y) (EDist.edist.{u1} G (PseudoEMetricSpace.toEDist.{u1} G _inst_5) x (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) y))
Case conversion may be inaccurate. Consider using '#align edist_inv edist_invₓ'. -/
@[to_additive]
theorem edist_inv [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G] (x y : G) :
    edist x⁻¹ y = edist x y⁻¹ := by rw [← edist_inv_inv, inv_inv]
#align edist_inv edist_inv
#align edist_neg edist_neg

/- warning: edist_div_left -> edist_div_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (c : G), Eq.{1} ENNReal (EDist.edist.{u1} G (PseudoEMetricSpace.toHasEdist.{u1} G _inst_5) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) a c)) (EDist.edist.{u1} G (PseudoEMetricSpace.toHasEdist.{u1} G _inst_5) b c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (c : G), Eq.{1} ENNReal (EDist.edist.{u1} G (PseudoEMetricSpace.toEDist.{u1} G _inst_5) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) a c)) (EDist.edist.{u1} G (PseudoEMetricSpace.toEDist.{u1} G _inst_5) b c)
Case conversion may be inaccurate. Consider using '#align edist_div_left edist_div_leftₓ'. -/
@[simp, to_additive]
theorem edist_div_left [PseudoEMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : edist (a / b) (a / c) = edist b c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, edist_mul_left, edist_inv_inv]
#align edist_div_left edist_div_left
#align edist_sub_left edist_sub_left

namespace IsometryEquiv

#print IsometryEquiv.constSMul /-
/-- If a group `G` acts on `X` by isometries, then `isometry_equiv.const_smul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive
      "If an additive group `G` acts on `X` by isometries, then `isometry_equiv.const_vadd`\nis the isometry of `X` given by addition of a constant element of the group.",
  simps toEquiv apply]
def constSMul (c : G) : X ≃ᵢ X where
  toEquiv := MulAction.toPerm c
  isometry_toFun := isometry_smul X c
#align isometry_equiv.const_smul IsometryEquiv.constSMul
#align isometry_equiv.const_vadd IsometryEquiv.constVAdd
-/

/- warning: isometry_equiv.const_smul_symm -> IsometryEquiv.constSMul_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X _inst_1 (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G), Eq.{succ u2} (IsometryEquiv.{u2, u2} X X _inst_1 _inst_1) (IsometryEquiv.symm.{u2, u2} X X _inst_1 _inst_1 (IsometryEquiv.constSMul.{u1, u2} G X _inst_1 _inst_2 _inst_3 _inst_4 c)) (IsometryEquiv.constSMul.{u1, u2} G X _inst_1 _inst_2 _inst_3 _inst_4 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) c))
but is expected to have type
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X _inst_1 (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G), Eq.{succ u2} (IsometryEquiv.{u2, u2} X X _inst_1 _inst_1) (IsometryEquiv.symm.{u2, u2} X X _inst_1 _inst_1 (IsometryEquiv.constSMul.{u1, u2} G X _inst_1 _inst_2 _inst_3 _inst_4 c)) (IsometryEquiv.constSMul.{u1, u2} G X _inst_1 _inst_2 _inst_3 _inst_4 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) c))
Case conversion may be inaccurate. Consider using '#align isometry_equiv.const_smul_symm IsometryEquiv.constSMul_symmₓ'. -/
@[simp, to_additive]
theorem constSMul_symm (c : G) : (constSMul c : X ≃ᵢ X).symm = constSMul c⁻¹ :=
  ext fun _ => rfl
#align isometry_equiv.const_smul_symm IsometryEquiv.constSMul_symm
#align isometry_equiv.const_vadd_symm IsometryEquiv.constVAdd_symm

variable [PseudoEMetricSpace G]

/- warning: isometry_equiv.mul_left -> IsometryEquiv.mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
Case conversion may be inaccurate. Consider using '#align isometry_equiv.mul_left IsometryEquiv.mulLeftₓ'. -/
/-- Multiplication `y ↦ x * y` as an `isometry_equiv`. -/
@[to_additive "Addition `y ↦ x + y` as an `isometry_equiv`.", simps apply toEquiv]
def mulLeft [IsometricSMul G G] (c : G) : G ≃ᵢ G
    where
  toEquiv := Equiv.mulLeft c
  isometry_toFun := edist_mul_left c
#align isometry_equiv.mul_left IsometryEquiv.mulLeft
#align isometry_equiv.add_left IsometryEquiv.addLeft

/- warning: isometry_equiv.mul_left_symm -> IsometryEquiv.mulLeft_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (x : G), Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.mulLeft.{u1} G _inst_2 _inst_5 _inst_6 x)) (IsometryEquiv.mulLeft.{u1} G _inst_2 _inst_5 _inst_6 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) x))
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (x : G), Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.mulLeft.{u1} G _inst_2 _inst_5 _inst_6 x)) (IsometryEquiv.mulLeft.{u1} G _inst_2 _inst_5 _inst_6 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) x))
Case conversion may be inaccurate. Consider using '#align isometry_equiv.mul_left_symm IsometryEquiv.mulLeft_symmₓ'. -/
@[simp, to_additive]
theorem mulLeft_symm [IsometricSMul G G] (x : G) : (mulLeft x).symm = IsometryEquiv.mulLeft x⁻¹ :=
  constSMul_symm x
#align isometry_equiv.mul_left_symm IsometryEquiv.mulLeft_symm
#align isometry_equiv.add_left_symm IsometryEquiv.addLeft_symm

/- warning: isometry_equiv.mul_right -> IsometryEquiv.mulRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
Case conversion may be inaccurate. Consider using '#align isometry_equiv.mul_right IsometryEquiv.mulRightₓ'. -/
--ext $ λ y, rfl
/-- Multiplication `y ↦ y * x` as an `isometry_equiv`. -/
@[to_additive "Addition `y ↦ y + x` as an `isometry_equiv`.", simps apply toEquiv]
def mulRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G
    where
  toEquiv := Equiv.mulRight c
  isometry_toFun a b := edist_mul_right a b c
#align isometry_equiv.mul_right IsometryEquiv.mulRight
#align isometry_equiv.add_right IsometryEquiv.addRight

/- warning: isometry_equiv.mul_right_symm -> IsometryEquiv.mulRight_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (x : G), Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.mulRight.{u1} G _inst_2 _inst_5 _inst_6 x)) (IsometryEquiv.mulRight.{u1} G _inst_2 _inst_5 _inst_6 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) x))
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (x : G), Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.mulRight.{u1} G _inst_2 _inst_5 _inst_6 x)) (IsometryEquiv.mulRight.{u1} G _inst_2 _inst_5 _inst_6 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) x))
Case conversion may be inaccurate. Consider using '#align isometry_equiv.mul_right_symm IsometryEquiv.mulRight_symmₓ'. -/
@[simp, to_additive]
theorem mulRight_symm [IsometricSMul Gᵐᵒᵖ G] (x : G) : (mulRight x).symm = mulRight x⁻¹ :=
  ext fun y => rfl
#align isometry_equiv.mul_right_symm IsometryEquiv.mulRight_symm
#align isometry_equiv.add_right_symm IsometryEquiv.addRight_symm

/- warning: isometry_equiv.div_right -> IsometryEquiv.divRight is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
Case conversion may be inaccurate. Consider using '#align isometry_equiv.div_right IsometryEquiv.divRightₓ'. -/
/-- Division `y ↦ y / x` as an `isometry_equiv`. -/
@[to_additive "Subtraction `y ↦ y - x` as an `isometry_equiv`.", simps apply toEquiv]
def divRight [IsometricSMul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G
    where
  toEquiv := Equiv.divRight c
  isometry_toFun a b := edist_div_right a b c
#align isometry_equiv.div_right IsometryEquiv.divRight
#align isometry_equiv.sub_right IsometryEquiv.subRight

/- warning: isometry_equiv.div_right_symm -> IsometryEquiv.divRight_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (c : G), Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.divRight.{u1} G _inst_2 _inst_5 _inst_6 c)) (IsometryEquiv.mulRight.{u1} G _inst_2 _inst_5 _inst_6 c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (c : G), Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.divRight.{u1} G _inst_2 _inst_5 _inst_6 c)) (IsometryEquiv.mulRight.{u1} G _inst_2 _inst_5 _inst_6 c)
Case conversion may be inaccurate. Consider using '#align isometry_equiv.div_right_symm IsometryEquiv.divRight_symmₓ'. -/
@[simp, to_additive]
theorem divRight_symm [IsometricSMul Gᵐᵒᵖ G] (c : G) : (divRight c).symm = mulRight c :=
  ext fun y => rfl
#align isometry_equiv.div_right_symm IsometryEquiv.divRight_symm
#align isometry_equiv.sub_right_symm IsometryEquiv.subRight_symm

variable [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]

/- warning: isometry_equiv.div_left -> IsometryEquiv.divLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], G -> (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5)
Case conversion may be inaccurate. Consider using '#align isometry_equiv.div_left IsometryEquiv.divLeftₓ'. -/
/-- Division `y ↦ x / y` as an `isometry_equiv`. -/
@[to_additive "Subtraction `y ↦ x - y` as an `isometry_equiv`.", simps apply symm_apply toEquiv]
def divLeft (c : G) : G ≃ᵢ G where
  toEquiv := Equiv.divLeft c
  isometry_toFun := edist_div_left c
#align isometry_equiv.div_left IsometryEquiv.divLeft
#align isometry_equiv.sub_left IsometryEquiv.subLeft

variable (G)

/- warning: isometry_equiv.inv -> IsometryEquiv.inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], IsometryEquiv.{u1, u1} G G _inst_5 _inst_5
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], IsometryEquiv.{u1, u1} G G _inst_5 _inst_5
Case conversion may be inaccurate. Consider using '#align isometry_equiv.inv IsometryEquiv.invₓ'. -/
/-- Inversion `x ↦ x⁻¹` as an `isometry_equiv`. -/
@[to_additive "Negation `x ↦ -x` as an `isometry_equiv`.", simps apply toEquiv]
def inv : G ≃ᵢ G where
  toEquiv := Equiv.inv G
  isometry_toFun := edist_inv_inv
#align isometry_equiv.inv IsometryEquiv.inv
#align isometry_equiv.neg IsometryEquiv.neg

/- warning: isometry_equiv.inv_symm -> IsometryEquiv.inv_symm is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.inv.{u1} G _inst_2 _inst_5 _inst_6 _inst_7)) (IsometryEquiv.inv.{u1} G _inst_2 _inst_5 _inst_6 _inst_7)
but is expected to have type
  forall (G : Type.{u1}) [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))], Eq.{succ u1} (IsometryEquiv.{u1, u1} G G _inst_5 _inst_5) (IsometryEquiv.symm.{u1, u1} G G _inst_5 _inst_5 (IsometryEquiv.inv.{u1} G _inst_2 _inst_5 _inst_6 _inst_7)) (IsometryEquiv.inv.{u1} G _inst_2 _inst_5 _inst_6 _inst_7)
Case conversion may be inaccurate. Consider using '#align isometry_equiv.inv_symm IsometryEquiv.inv_symmₓ'. -/
@[simp, to_additive]
theorem inv_symm : (inv G).symm = inv G :=
  rfl
#align isometry_equiv.inv_symm IsometryEquiv.inv_symm
#align isometry_equiv.neg_symm IsometryEquiv.neg_symm

end IsometryEquiv

namespace Emetric

#print EMetric.smul_ball /-
@[simp, to_additive]
theorem smul_ball (c : G) (x : X) (r : ℝ≥0∞) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_emetric_ball _ _
#align emetric.smul_ball EMetric.smul_ball
#align emetric.vadd_ball EMetric.vadd_ball
-/

/- warning: emetric.preimage_smul_ball -> EMetric.preimage_smul_ball is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X _inst_1 (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : ENNReal), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) c) (EMetric.ball.{u2} X _inst_1 x r)) (EMetric.ball.{u2} X _inst_1 (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) c) x) r)
but is expected to have type
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X _inst_1 (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : ENNReal), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1599 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1601 : X) => HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1599 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1601) c) (EMetric.ball.{u2} X _inst_1 x r)) (EMetric.ball.{u2} X _inst_1 (HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) c) x) r)
Case conversion may be inaccurate. Consider using '#align emetric.preimage_smul_ball EMetric.preimage_smul_ballₓ'. -/
@[simp, to_additive]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ≥0∞) : (· • ·) c ⁻¹' ball x r = ball (c⁻¹ • x) r :=
  by rw [preimage_smul, smul_ball]
#align emetric.preimage_smul_ball EMetric.preimage_smul_ball
#align emetric.preimage_vadd_ball EMetric.preimage_vadd_ball

#print EMetric.smul_closedBall /-
@[simp, to_additive]
theorem smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_emetric_closedBall _ _
#align emetric.smul_closed_ball EMetric.smul_closedBall
#align emetric.vadd_closed_ball EMetric.vadd_closedBall
-/

/- warning: emetric.preimage_smul_closed_ball -> EMetric.preimage_smul_closedBall is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X _inst_1 (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : ENNReal), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) c) (EMetric.closedBall.{u2} X _inst_1 x r)) (EMetric.closedBall.{u2} X _inst_1 (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) c) x) r)
but is expected to have type
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X _inst_1 (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : ENNReal), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1741 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1743 : X) => HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1741 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1743) c) (EMetric.closedBall.{u2} X _inst_1 x r)) (EMetric.closedBall.{u2} X _inst_1 (HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) c) x) r)
Case conversion may be inaccurate. Consider using '#align emetric.preimage_smul_closed_ball EMetric.preimage_smul_closedBallₓ'. -/
@[simp, to_additive]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ≥0∞) :
    (· • ·) c ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closed_ball]
#align emetric.preimage_smul_closed_ball EMetric.preimage_smul_closedBall
#align emetric.preimage_vadd_closed_ball EMetric.preimage_vadd_closedBall

variable [PseudoEMetricSpace G]

/- warning: emetric.preimage_mul_left_ball -> EMetric.preimage_mul_left_ball is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a) (EMetric.ball.{u1} G _inst_5 b r)) (EMetric.ball.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a) b) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1862 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1864 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1862 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.1864) a) (EMetric.ball.{u1} G _inst_5 b r)) (EMetric.ball.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a) b) r)
Case conversion may be inaccurate. Consider using '#align emetric.preimage_mul_left_ball EMetric.preimage_mul_left_ballₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_ball [IsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (· * ·) a ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r
#align emetric.preimage_mul_left_ball EMetric.preimage_mul_left_ball
#align emetric.preimage_add_left_ball EMetric.preimage_add_left_ball

/- warning: emetric.preimage_mul_right_ball -> EMetric.preimage_mul_right_ball is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (EMetric.ball.{u1} G _inst_5 b r)) (EMetric.ball.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (EMetric.ball.{u1} G _inst_5 b r)) (EMetric.ball.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
Case conversion may be inaccurate. Consider using '#align emetric.preimage_mul_right_ball EMetric.preimage_mul_right_ballₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_ball [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r
#align emetric.preimage_mul_right_ball EMetric.preimage_mul_right_ball
#align emetric.preimage_add_right_ball EMetric.preimage_add_right_ball

/- warning: emetric.preimage_mul_left_closed_ball -> EMetric.preimage_mul_left_closedBall is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a) (EMetric.closedBall.{u1} G _inst_5 b r)) (EMetric.closedBall.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a) b) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G _inst_5 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2036 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2038 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2036 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2038) a) (EMetric.closedBall.{u1} G _inst_5 b r)) (EMetric.closedBall.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a) b) r)
Case conversion may be inaccurate. Consider using '#align emetric.preimage_mul_left_closed_ball EMetric.preimage_mul_left_closedBallₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_closedBall [IsometricSMul G G] (a b : G) (r : ℝ≥0∞) :
    (· * ·) a ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r
#align emetric.preimage_mul_left_closed_ball EMetric.preimage_mul_left_closedBall
#align emetric.preimage_add_left_closed_ball EMetric.preimage_add_left_closedBall

/- warning: emetric.preimage_mul_right_closed_ball -> EMetric.preimage_mul_right_closedBall is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (EMetric.closedBall.{u1} G _inst_5 b r)) (EMetric.closedBall.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoEMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G _inst_5 (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : ENNReal), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (EMetric.closedBall.{u1} G _inst_5 b r)) (EMetric.closedBall.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
Case conversion may be inaccurate. Consider using '#align emetric.preimage_mul_right_closed_ball EMetric.preimage_mul_right_closedBallₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_closedBall [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_closed_ball (MulOpposite.op a) b r
#align emetric.preimage_mul_right_closed_ball EMetric.preimage_mul_right_closedBall
#align emetric.preimage_add_right_closed_ball EMetric.preimage_add_right_closedBall

end Emetric

end Emetric

#print dist_smul /-
@[simp, to_additive]
theorem dist_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    dist (c • x) (c • y) = dist x y :=
  (isometry_smul X c).dist_eq x y
#align dist_smul dist_smul
#align dist_vadd dist_vadd
-/

#print nndist_smul /-
@[simp, to_additive]
theorem nndist_smul [PseudoMetricSpace X] [SMul M X] [IsometricSMul M X] (c : M) (x y : X) :
    nndist (c • x) (c • y) = nndist x y :=
  (isometry_smul X c).nndist_eq x y
#align nndist_smul nndist_smul
#align nndist_vadd nndist_vadd
-/

#print dist_mul_left /-
@[simp, to_additive]
theorem dist_mul_left [PseudoMetricSpace M] [Mul M] [IsometricSMul M M] (a b c : M) :
    dist (a * b) (a * c) = dist b c :=
  dist_smul a b c
#align dist_mul_left dist_mul_left
#align dist_add_left dist_add_left
-/

#print nndist_mul_left /-
@[simp, to_additive]
theorem nndist_mul_left [PseudoMetricSpace M] [Mul M] [IsometricSMul M M] (a b c : M) :
    nndist (a * b) (a * c) = nndist b c :=
  nndist_smul a b c
#align nndist_mul_left nndist_mul_left
#align nndist_add_left nndist_add_left
-/

#print dist_mul_right /-
@[simp, to_additive]
theorem dist_mul_right [Mul M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    dist (a * c) (b * c) = dist a b :=
  dist_smul (MulOpposite.op c) a b
#align dist_mul_right dist_mul_right
#align dist_add_right dist_add_right
-/

#print nndist_mul_right /-
@[simp, to_additive]
theorem nndist_mul_right [PseudoMetricSpace M] [Mul M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a * c) (b * c) = nndist a b :=
  nndist_smul (MulOpposite.op c) a b
#align nndist_mul_right nndist_mul_right
#align nndist_add_right nndist_add_right
-/

/- warning: dist_div_right -> dist_div_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} M] [_inst_2 : PseudoMetricSpace.{u1} M] [_inst_3 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M (PseudoMetricSpace.toPseudoEMetricSpace.{u1} M _inst_2) (Mul.toHasOppositeSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1))))] (a : M) (b : M) (c : M), Eq.{1} Real (Dist.dist.{u1} M (PseudoMetricSpace.toHasDist.{u1} M _inst_2) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M _inst_1)) b c)) (Dist.dist.{u1} M (PseudoMetricSpace.toHasDist.{u1} M _inst_2) a b)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} M] [_inst_2 : PseudoMetricSpace.{u1} M] [_inst_3 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M (PseudoMetricSpace.toPseudoEMetricSpace.{u1} M _inst_2) (Mul.toHasOppositeSMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1))))] (a : M) (b : M) (c : M), Eq.{1} Real (Dist.dist.{u1} M (PseudoMetricSpace.toDist.{u1} M _inst_2) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M _inst_1)) b c)) (Dist.dist.{u1} M (PseudoMetricSpace.toDist.{u1} M _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align dist_div_right dist_div_rightₓ'. -/
@[simp, to_additive]
theorem dist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    dist (a / c) (b / c) = dist a b := by simp only [div_eq_mul_inv, dist_mul_right]
#align dist_div_right dist_div_right
#align dist_sub_right dist_sub_right

/- warning: nndist_div_right -> nndist_div_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} M] [_inst_2 : PseudoMetricSpace.{u1} M] [_inst_3 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M (PseudoMetricSpace.toPseudoEMetricSpace.{u1} M _inst_2) (Mul.toHasOppositeSMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1))))] (a : M) (b : M) (c : M), Eq.{1} NNReal (NNDist.nndist.{u1} M (PseudoMetricSpace.toNNDist.{u1} M _inst_2) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M _inst_1)) b c)) (NNDist.nndist.{u1} M (PseudoMetricSpace.toNNDist.{u1} M _inst_2) a b)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} M] [_inst_2 : PseudoMetricSpace.{u1} M] [_inst_3 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M (PseudoMetricSpace.toPseudoEMetricSpace.{u1} M _inst_2) (Mul.toHasOppositeSMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M _inst_1))))] (a : M) (b : M) (c : M), Eq.{1} NNReal (NNDist.nndist.{u1} M (PseudoMetricSpace.toNNDist.{u1} M _inst_2) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M _inst_1)) b c)) (NNDist.nndist.{u1} M (PseudoMetricSpace.toNNDist.{u1} M _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align nndist_div_right nndist_div_rightₓ'. -/
@[simp, to_additive]
theorem nndist_div_right [DivInvMonoid M] [PseudoMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] (a b c : M) :
    nndist (a / c) (b / c) = nndist a b := by simp only [div_eq_mul_inv, nndist_mul_right]
#align nndist_div_right nndist_div_right
#align nndist_sub_right nndist_sub_right

/- warning: dist_inv_inv -> dist_inv_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G), Eq.{1} Real (Dist.dist.{u1} G (PseudoMetricSpace.toHasDist.{u1} G _inst_2) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) (Dist.dist.{u1} G (PseudoMetricSpace.toHasDist.{u1} G _inst_2) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G), Eq.{1} Real (Dist.dist.{u1} G (PseudoMetricSpace.toDist.{u1} G _inst_2) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) (Dist.dist.{u1} G (PseudoMetricSpace.toDist.{u1} G _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align dist_inv_inv dist_inv_invₓ'. -/
@[simp, to_additive]
theorem dist_inv_inv [Group G] [PseudoMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
  (IsometryEquiv.inv G).dist_eq a b
#align dist_inv_inv dist_inv_inv
#align dist_neg_neg dist_neg_neg

/- warning: nndist_inv_inv -> nndist_inv_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G), Eq.{1} NNReal (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G), Eq.{1} NNReal (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align nndist_inv_inv nndist_inv_invₓ'. -/
@[simp, to_additive]
theorem nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
  (IsometryEquiv.inv G).nndist_eq a b
#align nndist_inv_inv nndist_inv_inv
#align nndist_neg_neg nndist_neg_neg

/- warning: dist_div_left -> dist_div_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G) (c : G), Eq.{1} Real (Dist.dist.{u1} G (PseudoMetricSpace.toHasDist.{u1} G _inst_2) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)) (Dist.dist.{u1} G (PseudoMetricSpace.toHasDist.{u1} G _inst_2) b c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G) (c : G), Eq.{1} Real (Dist.dist.{u1} G (PseudoMetricSpace.toDist.{u1} G _inst_2) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)) (Dist.dist.{u1} G (PseudoMetricSpace.toDist.{u1} G _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align dist_div_left dist_div_leftₓ'. -/
@[simp, to_additive]
theorem dist_div_left [Group G] [PseudoMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : dist (a / b) (a / c) = dist b c := by simp [div_eq_mul_inv]
#align dist_div_left dist_div_left
#align dist_sub_left dist_sub_left

/- warning: nndist_div_left -> nndist_div_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G) (c : G), Eq.{1} NNReal (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)) (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) b c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : PseudoMetricSpace.{u1} G] [_inst_3 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] [_inst_4 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_2) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))] (a : G) (b : G) (c : G), Eq.{1} NNReal (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)) (NNDist.nndist.{u1} G (PseudoMetricSpace.toNNDist.{u1} G _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align nndist_div_left nndist_div_leftₓ'. -/
@[simp, to_additive]
theorem nndist_div_left [Group G] [PseudoMetricSpace G] [IsometricSMul G G] [IsometricSMul Gᵐᵒᵖ G]
    (a b c : G) : nndist (a / b) (a / c) = nndist b c := by simp [div_eq_mul_inv]
#align nndist_div_left nndist_div_left
#align nndist_sub_left nndist_sub_left

namespace Metric

variable [PseudoMetricSpace X] [Group G] [MulAction G X] [IsometricSMul G X]

#print Metric.smul_ball /-
@[simp, to_additive]
theorem smul_ball (c : G) (x : X) (r : ℝ) : c • ball x r = ball (c • x) r :=
  (IsometryEquiv.constSMul c).image_ball _ _
#align metric.smul_ball Metric.smul_ball
#align metric.vadd_ball Metric.vadd_ball
-/

/- warning: metric.preimage_smul_ball -> Metric.preimage_smul_ball is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : Real), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) c) (Metric.ball.{u2} X _inst_1 x r)) (Metric.ball.{u2} X _inst_1 (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) c) x) r)
but is expected to have type
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : Real), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2854 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2856 : X) => HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2854 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2856) c) (Metric.ball.{u2} X _inst_1 x r)) (Metric.ball.{u2} X _inst_1 (HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) c) x) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_smul_ball Metric.preimage_smul_ballₓ'. -/
@[simp, to_additive]
theorem preimage_smul_ball (c : G) (x : X) (r : ℝ) : (· • ·) c ⁻¹' ball x r = ball (c⁻¹ • x) r := by
  rw [preimage_smul, smul_ball]
#align metric.preimage_smul_ball Metric.preimage_smul_ball
#align metric.preimage_vadd_ball Metric.preimage_vadd_ball

#print Metric.smul_closedBall /-
@[simp, to_additive]
theorem smul_closedBall (c : G) (x : X) (r : ℝ) : c • closedBall x r = closedBall (c • x) r :=
  (IsometryEquiv.constSMul c).image_closedBall _ _
#align metric.smul_closed_ball Metric.smul_closedBall
#align metric.vadd_closed_ball Metric.vadd_closedBall
-/

/- warning: metric.preimage_smul_closed_ball -> Metric.preimage_smul_closedBall is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : Real), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) c) (Metric.closedBall.{u2} X _inst_1 x r)) (Metric.closedBall.{u2} X _inst_1 (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) c) x) r)
but is expected to have type
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : Real), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2996 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2998 : X) => HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2996 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.2998) c) (Metric.closedBall.{u2} X _inst_1 x r)) (Metric.closedBall.{u2} X _inst_1 (HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) c) x) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_smul_closed_ball Metric.preimage_smul_closedBallₓ'. -/
@[simp, to_additive]
theorem preimage_smul_closedBall (c : G) (x : X) (r : ℝ) :
    (· • ·) c ⁻¹' closedBall x r = closedBall (c⁻¹ • x) r := by rw [preimage_smul, smul_closed_ball]
#align metric.preimage_smul_closed_ball Metric.preimage_smul_closedBall
#align metric.preimage_vadd_closed_ball Metric.preimage_vadd_closedBall

#print Metric.smul_sphere /-
@[simp, to_additive]
theorem smul_sphere (c : G) (x : X) (r : ℝ) : c • sphere x r = sphere (c • x) r :=
  (IsometryEquiv.constSMul c).image_sphere _ _
#align metric.smul_sphere Metric.smul_sphere
#align metric.vadd_sphere Metric.vadd_sphere
-/

/- warning: metric.preimage_smul_sphere -> Metric.preimage_smul_sphere is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : Real), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) c) (Metric.sphere.{u2} X _inst_1 x r)) (Metric.sphere.{u2} X _inst_1 (SMul.smul.{u1, u2} G X (MulAction.toHasSmul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) c) x) r)
but is expected to have type
  forall {G : Type.{u1}} {X : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} X] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : IsometricSMul.{u1, u2} G X (PseudoMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (x : X) (r : Real), Eq.{succ u2} (Set.{u2} X) (Set.preimage.{u2, u2} X X ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3138 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3140 : X) => HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3138 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3140) c) (Metric.sphere.{u2} X _inst_1 x r)) (Metric.sphere.{u2} X _inst_1 (HSMul.hSMul.{u1, u2, u2} G X X (instHSMul.{u1, u2} G X (MulAction.toSMul.{u1, u2} G X (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) c) x) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_smul_sphere Metric.preimage_smul_sphereₓ'. -/
@[simp, to_additive]
theorem preimage_smul_sphere (c : G) (x : X) (r : ℝ) :
    (· • ·) c ⁻¹' sphere x r = sphere (c⁻¹ • x) r := by rw [preimage_smul, smul_sphere]
#align metric.preimage_smul_sphere Metric.preimage_smul_sphere
#align metric.preimage_vadd_sphere Metric.preimage_vadd_sphere

variable [PseudoMetricSpace G]

/- warning: metric.preimage_mul_left_ball -> Metric.preimage_mul_left_ball is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a) (Metric.ball.{u1} G _inst_5 b r)) (Metric.ball.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a) b) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3259 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3261 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3259 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3261) a) (Metric.ball.{u1} G _inst_5 b r)) (Metric.ball.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a) b) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_mul_left_ball Metric.preimage_mul_left_ballₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_ball [IsometricSMul G G] (a b : G) (r : ℝ) :
    (· * ·) a ⁻¹' ball b r = ball (a⁻¹ * b) r :=
  preimage_smul_ball a b r
#align metric.preimage_mul_left_ball Metric.preimage_mul_left_ball
#align metric.preimage_add_left_ball Metric.preimage_add_left_ball

/- warning: metric.preimage_mul_right_ball -> Metric.preimage_mul_right_ball is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (Metric.ball.{u1} G _inst_5 b r)) (Metric.ball.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (Metric.ball.{u1} G _inst_5 b r)) (Metric.ball.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_mul_right_ball Metric.preimage_mul_right_ballₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_ball [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' ball b r = ball (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_ball (MulOpposite.op a) b r
#align metric.preimage_mul_right_ball Metric.preimage_mul_right_ball
#align metric.preimage_add_right_ball Metric.preimage_add_right_ball

/- warning: metric.preimage_mul_left_closed_ball -> Metric.preimage_mul_left_closedBall is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) a) (Metric.closedBall.{u1} G _inst_5 b r)) (Metric.closedBall.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) a) b) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} G G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G ((fun (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3433 : G) (x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3435 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3433 x._@.Mathlib.Topology.MetricSpace.IsometricSMul._hyg.3435) a) (Metric.closedBall.{u1} G _inst_5 b r)) (Metric.closedBall.{u1} G _inst_5 (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_2)))) a) b) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_mul_left_closed_ball Metric.preimage_mul_left_closedBallₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_closedBall [IsometricSMul G G] (a b : G) (r : ℝ) :
    (· * ·) a ⁻¹' closedBall b r = closedBall (a⁻¹ * b) r :=
  preimage_smul_closedBall a b r
#align metric.preimage_mul_left_closed_ball Metric.preimage_mul_left_closedBall
#align metric.preimage_add_left_closed_ball Metric.preimage_add_left_closedBall

/- warning: metric.preimage_mul_right_closed_ball -> Metric.preimage_mul_right_closedBall is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (Metric.closedBall.{u1} G _inst_5 b r)) (Metric.closedBall.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : Group.{u1} G] [_inst_5 : PseudoMetricSpace.{u1} G] [_inst_6 : IsometricSMul.{u1, u1} (MulOpposite.{u1} G) G (PseudoMetricSpace.toPseudoEMetricSpace.{u1} G _inst_5) (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)))))] (a : G) (b : G) (r : Real), Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))))) x a) (Metric.closedBall.{u1} G _inst_5 b r)) (Metric.closedBall.{u1} G _inst_5 (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) b a) r)
Case conversion may be inaccurate. Consider using '#align metric.preimage_mul_right_closed_ball Metric.preimage_mul_right_closedBallₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_closedBall [IsometricSMul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
    (fun x => x * a) ⁻¹' closedBall b r = closedBall (b / a) r :=
  by
  rw [div_eq_mul_inv]
  exact preimage_smul_closed_ball (MulOpposite.op a) b r
#align metric.preimage_mul_right_closed_ball Metric.preimage_mul_right_closedBall
#align metric.preimage_add_right_closed_ball Metric.preimage_add_right_closedBall

end Metric

section Instances

variable {Y : Type _} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [SMul M X] [IsometricSMul M X]

@[to_additive]
instance [SMul M Y] [IsometricSMul M Y] : IsometricSMul M (X × Y) :=
  ⟨fun c => (isometry_smul X c).Prod_map (isometry_smul Y c)⟩

#print Prod.isometricSMul' /-
@[to_additive]
instance Prod.isometricSMul' {N} [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] [Mul N]
    [PseudoEMetricSpace N] [IsometricSMul N N] : IsometricSMul (M × N) (M × N) :=
  ⟨fun c => (isometry_smul M c.1).Prod_map (isometry_smul N c.2)⟩
#align prod.has_isometric_smul' Prod.isometricSMul'
#align prod.has_isometric_vadd' Prod.isometricVAdd'
-/

#print Prod.isometricSMul'' /-
@[to_additive]
instance Prod.isometricSMul'' {N} [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] [Mul N]
    [PseudoEMetricSpace N] [IsometricSMul Nᵐᵒᵖ N] : IsometricSMul (M × N)ᵐᵒᵖ (M × N) :=
  ⟨fun c => (isometry_mul_right c.unop.1).Prod_map (isometry_mul_right c.unop.2)⟩
#align prod.has_isometric_smul'' Prod.isometricSMul''
#align prod.has_isometric_vadd'' Prod.isometricVAdd''
-/

#print Units.isometricSMul /-
@[to_additive]
instance Units.isometricSMul [Monoid M] : IsometricSMul Mˣ X :=
  ⟨fun c => by convert isometry_smul X (c : M)⟩
#align units.has_isometric_smul Units.isometricSMul
#align add_units.has_isometric_vadd AddUnits.isometricVAdd
-/

@[to_additive]
instance : IsometricSMul M Xᵐᵒᵖ :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.unop y.unop⟩

#print ULift.isometricSMul /-
@[to_additive]
instance ULift.isometricSMul : IsometricSMul (ULift M) X :=
  ⟨fun c => by simpa only using isometry_smul X c.down⟩
#align ulift.has_isometric_smul ULift.isometricSMul
#align ulift.has_isometric_vadd ULift.isometricVAdd
-/

#print ULift.isometricSMul' /-
@[to_additive]
instance ULift.isometricSMul' : IsometricSMul M (ULift X) :=
  ⟨fun c x y => by simpa only using edist_smul_left c x.1 y.1⟩
#align ulift.has_isometric_smul' ULift.isometricSMul'
#align ulift.has_isometric_vadd' ULift.isometricVAdd'
-/

@[to_additive]
instance {ι} {X : ι → Type _} [Fintype ι] [∀ i, SMul M (X i)] [∀ i, PseudoEMetricSpace (X i)]
    [∀ i, IsometricSMul M (X i)] : IsometricSMul M (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun i => (· • ·) c) fun i => isometry_smul (X i) c⟩

#print Pi.isometricSMul' /-
@[to_additive]
instance Pi.isometricSMul' {ι} {M X : ι → Type _} [Fintype ι] [∀ i, SMul (M i) (X i)]
    [∀ i, PseudoEMetricSpace (X i)] [∀ i, IsometricSMul (M i) (X i)] :
    IsometricSMul (∀ i, M i) (∀ i, X i) :=
  ⟨fun c => isometry_dcomp (fun i => (· • ·) (c i)) fun i => isometry_smul _ _⟩
#align pi.has_isometric_smul' Pi.isometricSMul'
#align pi.has_isometric_vadd' Pi.isometricVAdd'
-/

#print Pi.isometricSMul'' /-
@[to_additive]
instance Pi.isometricSMul'' {ι} {M : ι → Type _} [Fintype ι] [∀ i, Mul (M i)]
    [∀ i, PseudoEMetricSpace (M i)] [∀ i, IsometricSMul (M i)ᵐᵒᵖ (M i)] :
    IsometricSMul (∀ i, M i)ᵐᵒᵖ (∀ i, M i) :=
  ⟨fun c => isometry_dcomp (fun i (x : M i) => x * c.unop i) fun i => isometry_mul_right _⟩
#align pi.has_isometric_smul'' Pi.isometricSMul''
#align pi.has_isometric_vadd'' Pi.isometricVAdd''
-/

#print Additive.isometricVAdd /-
instance Additive.isometricVAdd : IsometricVAdd (Additive M) X :=
  ⟨fun c => isometry_smul X c.toMul⟩
#align additive.has_isometric_vadd Additive.isometricVAdd
-/

/- warning: additive.has_isometric_vadd' -> Additive.isometricVAdd' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Mul.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricSMul.{u1, u1} M M _inst_6 (Mul.toSMul.{u1} M _inst_5)], IsometricVAdd.{u1, u1} (Additive.{u1} M) (Additive.{u1} M) (Additive.pseudoEmetricSpace.{u1} M _inst_6) (Add.toVAdd.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_5))
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : Mul.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricSMul.{u1, u1} M M _inst_6 (Mul.toSMul.{u1} M _inst_5)], IsometricVAdd.{u1, u1} (Additive.{u1} M) (Additive.{u1} M) (instPseudoEMetricSpaceAdditive.{u1} M _inst_6) (Add.toVAdd.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_5))
Case conversion may be inaccurate. Consider using '#align additive.has_isometric_vadd' Additive.isometricVAdd'ₓ'. -/
instance Additive.isometricVAdd' [Mul M] [PseudoEMetricSpace M] [IsometricSMul M M] :
    IsometricVAdd (Additive M) (Additive M) :=
  ⟨fun c x y => edist_smul_left c.toMul x.toMul y.toMul⟩
#align additive.has_isometric_vadd' Additive.isometricVAdd'

/- warning: additive.has_isometric_vadd'' -> Additive.isometricVAdd'' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Mul.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M _inst_6 (Mul.toHasOppositeSMul.{u1} M _inst_5)], IsometricVAdd.{u1, u1} (AddOpposite.{u1} (Additive.{u1} M)) (Additive.{u1} M) (Additive.pseudoEmetricSpace.{u1} M _inst_6) (Add.toHasOppositeVAdd.{u1} (Additive.{u1} M) (Additive.hasAdd.{u1} M _inst_5))
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : Mul.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricSMul.{u1, u1} (MulOpposite.{u1} M) M _inst_6 (Mul.toHasOppositeSMul.{u1} M _inst_5)], IsometricVAdd.{u1, u1} (AddOpposite.{u1} (Additive.{u1} M)) (Additive.{u1} M) (instPseudoEMetricSpaceAdditive.{u1} M _inst_6) (Add.toHasOppositeVAdd.{u1} (Additive.{u1} M) (Additive.add.{u1} M _inst_5))
Case conversion may be inaccurate. Consider using '#align additive.has_isometric_vadd'' Additive.isometricVAdd''ₓ'. -/
instance Additive.isometricVAdd'' [Mul M] [PseudoEMetricSpace M] [IsometricSMul Mᵐᵒᵖ M] :
    IsometricVAdd (Additive M)ᵃᵒᵖ (Additive M) :=
  ⟨fun c x y => edist_smul_left (MulOpposite.op c.unop.toMul) x.toMul y.toMul⟩
#align additive.has_isometric_vadd'' Additive.isometricVAdd''

#print Multiplicative.isometricSMul /-
instance Multiplicative.isometricSMul {M X} [VAdd M X] [PseudoEMetricSpace X] [IsometricVAdd M X] :
    IsometricSMul (Multiplicative M) X :=
  ⟨fun c => isometry_vadd X c.toAdd⟩
#align multiplicative.has_isometric_smul Multiplicative.isometricSMul
-/

/- warning: multiplicative.has_isometric_smul' -> Multiplicative.isometricSMul' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Add.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricVAdd.{u1, u1} M M _inst_6 (Add.toVAdd.{u1} M _inst_5)], IsometricSMul.{u1, u1} (Multiplicative.{u1} M) (Multiplicative.{u1} M) (Multiplicative.pseudoEmetricSpace.{u1} M _inst_6) (Mul.toSMul.{u1} (Multiplicative.{u1} M) (Multiplicative.hasMul.{u1} M _inst_5))
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : Add.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricVAdd.{u1, u1} M M _inst_6 (Add.toVAdd.{u1} M _inst_5)], IsometricSMul.{u1, u1} (Multiplicative.{u1} M) (Multiplicative.{u1} M) (instPseudoEMetricSpaceMultiplicative.{u1} M _inst_6) (Mul.toSMul.{u1} (Multiplicative.{u1} M) (Multiplicative.mul.{u1} M _inst_5))
Case conversion may be inaccurate. Consider using '#align multiplicative.has_isometric_smul' Multiplicative.isometricSMul'ₓ'. -/
instance Multiplicative.isometricSMul' [Add M] [PseudoEMetricSpace M] [IsometricVAdd M M] :
    IsometricSMul (Multiplicative M) (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left c.toAdd x.toAdd y.toAdd⟩
#align multiplicative.has_isometric_smul' Multiplicative.isometricSMul'

/- warning: multiplicative.has_isometric_vadd'' -> Multiplicative.isometricVAdd'' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Add.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricVAdd.{u1, u1} (AddOpposite.{u1} M) M _inst_6 (Add.toHasOppositeVAdd.{u1} M _inst_5)], IsometricSMul.{u1, u1} (MulOpposite.{u1} (Multiplicative.{u1} M)) (Multiplicative.{u1} M) (Multiplicative.pseudoEmetricSpace.{u1} M _inst_6) (Mul.toHasOppositeSMul.{u1} (Multiplicative.{u1} M) (Multiplicative.hasMul.{u1} M _inst_5))
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : Add.{u1} M] [_inst_6 : PseudoEMetricSpace.{u1} M] [_inst_7 : IsometricVAdd.{u1, u1} (AddOpposite.{u1} M) M _inst_6 (Add.toHasOppositeVAdd.{u1} M _inst_5)], IsometricSMul.{u1, u1} (MulOpposite.{u1} (Multiplicative.{u1} M)) (Multiplicative.{u1} M) (instPseudoEMetricSpaceMultiplicative.{u1} M _inst_6) (Mul.toHasOppositeSMul.{u1} (Multiplicative.{u1} M) (Multiplicative.mul.{u1} M _inst_5))
Case conversion may be inaccurate. Consider using '#align multiplicative.has_isometric_vadd'' Multiplicative.isometricVAdd''ₓ'. -/
instance Multiplicative.isometricVAdd'' [Add M] [PseudoEMetricSpace M] [IsometricVAdd Mᵃᵒᵖ M] :
    IsometricSMul (Multiplicative M)ᵐᵒᵖ (Multiplicative M) :=
  ⟨fun c x y => edist_vadd_left (AddOpposite.op c.unop.toAdd) x.toAdd y.toAdd⟩
#align multiplicative.has_isometric_vadd'' Multiplicative.isometricVAdd''

end Instances

