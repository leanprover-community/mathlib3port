/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.algebra.uniform_mul_action
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.UniformSpace.Completion

/-!
# Multiplicative action on the completion of a uniform space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define typeclasses `has_uniform_continuous_const_vadd` and
`has_uniform_continuous_const_smul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `uniform_space.completion X`.

In later files once the additive group structure is set up, we provide
* `uniform_space.completion.distrib_mul_action`
* `uniform_space.completion.mul_action_with_zero`
* `uniform_space.completion.module`

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/


universe u v w x y z

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X]
  [UniformSpace Y]

#print UniformContinuousConstVAdd /-
/-- An additive action such that for all `c`, the map `λ x, c +ᵥ x` is uniformly continuous. -/
class UniformContinuousConstVAdd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : ∀ c : M, UniformContinuous ((· +ᵥ ·) c : X → X)
#align has_uniform_continuous_const_vadd UniformContinuousConstVAdd
-/

#print UniformContinuousConstSMul /-
/-- A multiplicative action such that for all `c`, the map `λ x, c • x` is uniformly continuous. -/
@[to_additive]
class UniformContinuousConstSMul [SMul M X] : Prop where
  uniformContinuous_const_smul : ∀ c : M, UniformContinuous ((· • ·) c : X → X)
#align has_uniform_continuous_const_smul UniformContinuousConstSMul
#align has_uniform_continuous_const_vadd UniformContinuousConstVAdd
-/

export UniformContinuousConstVAdd (uniformContinuous_const_vadd)

export UniformContinuousConstSMul (uniformContinuous_const_smul)

#print AddMonoid.uniformContinuousConstSMul_nat /-
instance AddMonoid.uniformContinuousConstSMul_nat [AddGroup X] [UniformAddGroup X] :
    UniformContinuousConstSMul ℕ X :=
  ⟨uniformContinuous_const_nsmul⟩
#align add_monoid.has_uniform_continuous_const_smul_nat AddMonoid.uniformContinuousConstSMul_nat
-/

#print AddGroup.uniformContinuousConstSMul_int /-
instance AddGroup.uniformContinuousConstSMul_int [AddGroup X] [UniformAddGroup X] :
    UniformContinuousConstSMul ℤ X :=
  ⟨uniformContinuous_const_zsmul⟩
#align add_group.has_uniform_continuous_const_smul_int AddGroup.uniformContinuousConstSMul_int
-/

/- warning: has_uniform_continuous_const_smul_of_continuous_const_smul -> uniformContinuousConstSMul_of_continuousConstSMul is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_3 : Monoid.{u1} R] [_inst_4 : AddCommGroup.{u2} M] [_inst_5 : DistribMulAction.{u1, u2} R M _inst_3 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))] [_inst_6 : UniformSpace.{u2} M] [_inst_7 : UniformAddGroup.{u2} M _inst_6 (AddCommGroup.toAddGroup.{u2} M _inst_4)] [_inst_8 : ContinuousConstSMul.{u1, u2} R M (UniformSpace.toTopologicalSpace.{u2} M _inst_6) (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))))) (DistribSMul.toSmulZeroClass.{u1, u2} R M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (DistribMulAction.toDistribSMul.{u1, u2} R M _inst_3 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) _inst_5)))], UniformContinuousConstSMul.{u1, u2} R M _inst_6 (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))))) (DistribSMul.toSmulZeroClass.{u1, u2} R M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (DistribMulAction.toDistribSMul.{u1, u2} R M _inst_3 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) _inst_5)))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_3 : Monoid.{u1} R] [_inst_4 : AddCommGroup.{u2} M] [_inst_5 : DistribMulAction.{u1, u2} R M _inst_3 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))] [_inst_6 : UniformSpace.{u2} M] [_inst_7 : UniformAddGroup.{u2} M _inst_6 (AddCommGroup.toAddGroup.{u2} M _inst_4)] [_inst_8 : ContinuousConstSMul.{u1, u2} R M (UniformSpace.toTopologicalSpace.{u2} M _inst_6) (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (DistribSMul.toSMulZeroClass.{u1, u2} R M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (DistribMulAction.toDistribSMul.{u1, u2} R M _inst_3 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) _inst_5)))], UniformContinuousConstSMul.{u1, u2} R M _inst_6 (SMulZeroClass.toSMul.{u1, u2} R M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (DistribSMul.toSMulZeroClass.{u1, u2} R M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (DistribMulAction.toDistribSMul.{u1, u2} R M _inst_3 (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) _inst_5)))
Case conversion may be inaccurate. Consider using '#align has_uniform_continuous_const_smul_of_continuous_const_smul uniformContinuousConstSMul_of_continuousConstSMulₓ'. -/
/-- A `distrib_mul_action` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`has_uniform_continuous_const_smul.to_has_continuous_const_smul` -/
theorem uniformContinuousConstSMul_of_continuousConstSMul [Monoid R] [AddCommGroup M]
    [DistribMulAction R M] [UniformSpace M] [UniformAddGroup M] [ContinuousConstSMul R M] :
    UniformContinuousConstSMul R M :=
  ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribMulAction.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩
#align has_uniform_continuous_const_smul_of_continuous_const_smul uniformContinuousConstSMul_of_continuousConstSMul

/- warning: ring.has_uniform_continuous_const_smul -> Ring.uniformContinuousConstSMul is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_3 : Ring.{u1} R] [_inst_4 : UniformSpace.{u1} R] [_inst_5 : UniformAddGroup.{u1} R _inst_4 (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_3)))] [_inst_6 : ContinuousMul.{u1} R (UniformSpace.toTopologicalSpace.{u1} R _inst_4) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_3))], UniformContinuousConstSMul.{u1, u1} R R _inst_4 (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_3)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_3 : Ring.{u1} R] [_inst_4 : UniformSpace.{u1} R] [_inst_5 : UniformAddGroup.{u1} R _inst_4 (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_3))] [_inst_6 : ContinuousMul.{u1} R (UniformSpace.toTopologicalSpace.{u1} R _inst_4) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_3)))], UniformContinuousConstSMul.{u1, u1} R R _inst_4 (SMulZeroClass.toSMul.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_3))) (SMulWithZero.toSMulZeroClass.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_3))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_3))) (MulZeroClass.toSMulWithZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_3)))))))
Case conversion may be inaccurate. Consider using '#align ring.has_uniform_continuous_const_smul Ring.uniformContinuousConstSMulₓ'. -/
/-- The action of `semiring.to_module` is uniformly continuous. -/
instance Ring.uniformContinuousConstSMul [Ring R] [UniformSpace R] [UniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul R R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _
#align ring.has_uniform_continuous_const_smul Ring.uniformContinuousConstSMul

/- warning: ring.has_uniform_continuous_const_op_smul -> Ring.uniformContinuousConstSMul_op is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_3 : Ring.{u1} R] [_inst_4 : UniformSpace.{u1} R] [_inst_5 : UniformAddGroup.{u1} R _inst_4 (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_3)))] [_inst_6 : ContinuousMul.{u1} R (UniformSpace.toTopologicalSpace.{u1} R _inst_4) (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_3))], UniformContinuousConstSMul.{u1, u1} (MulOpposite.{u1} R) R _inst_4 (Mul.toHasOppositeSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_3)))
but is expected to have type
  forall (R : Type.{u1}) [_inst_3 : Ring.{u1} R] [_inst_4 : UniformSpace.{u1} R] [_inst_5 : UniformAddGroup.{u1} R _inst_4 (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_3))] [_inst_6 : ContinuousMul.{u1} R (UniformSpace.toTopologicalSpace.{u1} R _inst_4) (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_3)))], UniformContinuousConstSMul.{u1, u1} (MulOpposite.{u1} R) R _inst_4 (Mul.toHasOppositeSMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_3))))
Case conversion may be inaccurate. Consider using '#align ring.has_uniform_continuous_const_op_smul Ring.uniformContinuousConstSMul_opₓ'. -/
/-- The action of `semiring.to_opposite_module` is uniformly continuous. -/
instance Ring.uniformContinuousConstSMul_op [Ring R] [UniformSpace R] [UniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul Rᵐᵒᵖ R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _
#align ring.has_uniform_continuous_const_op_smul Ring.uniformContinuousConstSMul_op

section SMul

variable [SMul M X]

#print UniformContinuousConstSMul.to_continuousConstSMul /-
@[to_additive]
instance (priority := 100) UniformContinuousConstSMul.to_continuousConstSMul
    [UniformContinuousConstSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (uniformContinuous_const_smul c).Continuous⟩
#align has_uniform_continuous_const_smul.to_has_continuous_const_smul UniformContinuousConstSMul.to_continuousConstSMul
#align has_uniform_continuous_const_vadd.to_has_continuous_const_vadd UniformContinuousConstVAdd.to_continuousConstVAdd
-/

variable {M X Y}

#print UniformContinuous.const_smul /-
@[to_additive]
theorem UniformContinuous.const_smul [UniformContinuousConstSMul M X] {f : Y → X}
    (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f) :=
  (uniformContinuous_const_smul c).comp hf
#align uniform_continuous.const_smul UniformContinuous.const_smul
#align uniform_continuous.const_vadd UniformContinuous.const_vadd
-/

#print UniformContinuousConstSMul.op /-
/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[to_additive
      "If an additive action is central, then its right action is uniform\ncontinuous when its left action,is."]
instance (priority := 100) UniformContinuousConstSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
    [UniformContinuousConstSMul M X] : UniformContinuousConstSMul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec' fun c =>
      by
      change UniformContinuous fun m => MulOpposite.op c • m
      simp_rw [op_smul_eq_smul]
      exact uniform_continuous_const_smul c⟩
#align has_uniform_continuous_const_smul.op UniformContinuousConstSMul.op
#align has_uniform_continuous_const_vadd.op UniformContinuousConstVAdd.op
-/

#print MulOpposite.uniformContinuousConstSMul /-
@[to_additive]
instance MulOpposite.uniformContinuousConstSMul [UniformContinuousConstSMul M X] :
    UniformContinuousConstSMul M Xᵐᵒᵖ :=
  ⟨fun c =>
    MulOpposite.uniformContinuous_op.comp <| MulOpposite.uniformContinuous_unop.const_smul c⟩
#align mul_opposite.has_uniform_continuous_const_smul MulOpposite.uniformContinuousConstSMul
#align add_opposite.has_uniform_continuous_const_vadd AddOpposite.uniformContinuousConstVAdd
-/

end SMul

/- warning: uniform_group.to_has_uniform_continuous_const_smul -> UniformGroup.to_uniformContinuousConstSMul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] [_inst_4 : UniformSpace.{u1} G] [_inst_5 : UniformGroup.{u1} G _inst_4 _inst_3], UniformContinuousConstSMul.{u1, u1} G G _inst_4 (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : Group.{u1} G] [_inst_4 : UniformSpace.{u1} G] [_inst_5 : UniformGroup.{u1} G _inst_4 _inst_3], UniformContinuousConstSMul.{u1, u1} G G _inst_4 (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))))
Case conversion may be inaccurate. Consider using '#align uniform_group.to_has_uniform_continuous_const_smul UniformGroup.to_uniformContinuousConstSMulₓ'. -/
@[to_additive]
instance UniformGroup.to_uniformContinuousConstSMul {G : Type u} [Group G] [UniformSpace G]
    [UniformGroup G] : UniformContinuousConstSMul G G :=
  ⟨fun c => uniformContinuous_const.mul uniformContinuous_id⟩
#align uniform_group.to_has_uniform_continuous_const_smul UniformGroup.to_uniformContinuousConstSMul
#align uniform_add_group.to_has_uniform_continuous_const_vadd UniformAddGroup.to_uniformContinuousConstVAdd

namespace UniformSpace

namespace Completion

section SMul

variable [SMul M X]

@[to_additive]
instance : SMul M (Completion X) :=
  ⟨fun c => Completion.map ((· • ·) c)⟩

#print UniformSpace.Completion.smul_def /-
@[to_additive]
theorem smul_def (c : M) (x : Completion X) : c • x = Completion.map ((· • ·) c) x :=
  rfl
#align uniform_space.completion.smul_def UniformSpace.Completion.smul_def
#align uniform_space.completion.vadd_def UniformSpace.Completion.vadd_def
-/

@[to_additive]
instance : UniformContinuousConstSMul M (Completion X) :=
  ⟨fun c => uniformContinuous_map⟩

@[to_additive]
instance [SMul N X] [SMul M N] [UniformContinuousConstSMul M X] [UniformContinuousConstSMul N X]
    [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x =>
    by
    have : _ = (_ : completion X → completion X) :=
      map_comp (uniform_continuous_const_smul m) (uniform_continuous_const_smul n)
    refine' Eq.trans _ (congr_fun this.symm x)
    exact congr_arg (fun f => completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]
instance [SMul N X] [SMulCommClass M N X] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] : SMulCommClass M N (Completion X) :=
  ⟨fun m n x =>
    by
    have hmn : m • n • x = (completion.map (SMul.smul m) ∘ completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (completion.map (SMul.smul n) ∘ completion.map (SMul.smul m)) x := rfl
    rw [hmn, hnm, map_comp, map_comp]
    exact congr_arg (fun f => completion.map f x) (funext (smul_comm _ _))
    repeat' exact uniform_continuous_const_smul _⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
  ⟨fun c a => (congr_arg fun f => Completion.map f a) <| funext (op_smul_eq_smul c)⟩

variable {M X} [UniformContinuousConstSMul M X]

/- warning: uniform_space.completion.coe_smul -> UniformSpace.Completion.coe_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : UniformSpace.{u2} X] [_inst_3 : SMul.{u1, u2} M X] [_inst_4 : UniformContinuousConstSMul.{u1, u2} M X _inst_1 _inst_3] (c : M) (x : X), Eq.{succ u2} (UniformSpace.Completion.{u2} X _inst_1) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) X (UniformSpace.Completion.{u2} X _inst_1) (HasLiftT.mk.{succ u2, succ u2} X (UniformSpace.Completion.{u2} X _inst_1) (CoeTCₓ.coe.{succ u2, succ u2} X (UniformSpace.Completion.{u2} X _inst_1) (UniformSpace.Completion.hasCoeT.{u2} X _inst_1))) (SMul.smul.{u1, u2} M X _inst_3 c x)) (SMul.smul.{u1, u2} M (UniformSpace.Completion.{u2} X _inst_1) (UniformSpace.Completion.hasSmul.{u1, u2} M X _inst_1 _inst_3) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) X (UniformSpace.Completion.{u2} X _inst_1) (HasLiftT.mk.{succ u2, succ u2} X (UniformSpace.Completion.{u2} X _inst_1) (CoeTCₓ.coe.{succ u2, succ u2} X (UniformSpace.Completion.{u2} X _inst_1) (UniformSpace.Completion.hasCoeT.{u2} X _inst_1))) x))
but is expected to have type
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : UniformSpace.{u2} X] [_inst_3 : SMul.{u1, u2} M X] [_inst_4 : UniformContinuousConstSMul.{u1, u2} M X _inst_1 _inst_3] (c : M) (x : X), Eq.{succ u2} (UniformSpace.Completion.{u2} X _inst_1) (UniformSpace.Completion.coe'.{u2} X _inst_1 (HSMul.hSMul.{u1, u2, u2} M X X (instHSMul.{u1, u2} M X _inst_3) c x)) (HSMul.hSMul.{u1, u2, u2} M (UniformSpace.Completion.{u2} X _inst_1) (UniformSpace.Completion.{u2} X _inst_1) (instHSMul.{u1, u2} M (UniformSpace.Completion.{u2} X _inst_1) (UniformSpace.Completion.instSMulCompletion.{u1, u2} M X _inst_1 _inst_3)) c (UniformSpace.Completion.coe'.{u2} X _inst_1 x))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.coe_smul UniformSpace.Completion.coe_smulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_smul (c : M) (x : X) : ↑(c • x) = (c • x : Completion X) :=
  (map_coe (uniformContinuous_const_smul c) x).symm
#align uniform_space.completion.coe_smul UniformSpace.Completion.coe_smul
#align uniform_space.completion.coe_vadd UniformSpace.Completion.coe_vadd

end SMul

@[to_additive]
instance [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] : MulAction M (Completion X)
    where
  smul := (· • ·)
  one_smul := ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

end Completion

end UniformSpace

