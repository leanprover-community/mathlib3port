/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.UniformSpace.Completion

/-!
# Multiplicative action on the completion of a uniform space

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

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X] [UniformSpace Y]

/-- An additive action such that for all `c`, the map `λ x, c +ᵥ x` is uniformly continuous. -/
class HasUniformContinuousConstVadd [HasVadd M X] : Prop where
  uniform_continuous_const_vadd : ∀ c : M, UniformContinuous ((· +ᵥ ·) c : X → X)
#align has_uniform_continuous_const_vadd HasUniformContinuousConstVadd

/-- A multiplicative action such that for all `c`, the map `λ x, c • x` is uniformly continuous. -/
@[to_additive]
class HasUniformContinuousConstSmul [HasSmul M X] : Prop where
  uniform_continuous_const_smul : ∀ c : M, UniformContinuous ((· • ·) c : X → X)
#align has_uniform_continuous_const_smul HasUniformContinuousConstSmul

export HasUniformContinuousConstVadd (uniform_continuous_const_vadd)

export HasUniformContinuousConstSmul (uniform_continuous_const_smul)

instance AddMonoid.has_uniform_continuous_const_smul_nat [AddGroup X] [UniformAddGroup X] :
    HasUniformContinuousConstSmul ℕ X :=
  ⟨uniform_continuous_const_nsmul⟩
#align add_monoid.has_uniform_continuous_const_smul_nat AddMonoid.has_uniform_continuous_const_smul_nat

instance AddGroup.has_uniform_continuous_const_smul_int [AddGroup X] [UniformAddGroup X] :
    HasUniformContinuousConstSmul ℤ X :=
  ⟨uniform_continuous_const_zsmul⟩
#align add_group.has_uniform_continuous_const_smul_int AddGroup.has_uniform_continuous_const_smul_int

/-- A `distrib_mul_action` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`has_uniform_continuous_const_smul.to_has_continuous_const_smul` -/
theorem has_uniform_continuous_const_smul_of_continuous_const_smul [Monoid R] [AddCommGroup M] [DistribMulAction R M]
    [UniformSpace M] [UniformAddGroup M] [HasContinuousConstSmul R M] : HasUniformContinuousConstSmul R M :=
  ⟨fun r =>
    uniform_continuous_of_continuous_at_zero (DistribMulAction.toAddMonoidHom M r)
      (Continuous.continuous_at (continuous_const_smul r))⟩
#align
  has_uniform_continuous_const_smul_of_continuous_const_smul has_uniform_continuous_const_smul_of_continuous_const_smul

/-- The action of `semiring.to_module` is uniformly continuous. -/
instance Ring.has_uniform_continuous_const_smul [Ring R] [UniformSpace R] [UniformAddGroup R] [HasContinuousMul R] :
    HasUniformContinuousConstSmul R R :=
  has_uniform_continuous_const_smul_of_continuous_const_smul _ _
#align ring.has_uniform_continuous_const_smul Ring.has_uniform_continuous_const_smul

/-- The action of `semiring.to_opposite_module` is uniformly continuous. -/
instance Ring.has_uniform_continuous_const_op_smul [Ring R] [UniformSpace R] [UniformAddGroup R] [HasContinuousMul R] :
    HasUniformContinuousConstSmul Rᵐᵒᵖ R :=
  has_uniform_continuous_const_smul_of_continuous_const_smul _ _
#align ring.has_uniform_continuous_const_op_smul Ring.has_uniform_continuous_const_op_smul

section HasSmul

variable [HasSmul M X]

@[to_additive]
instance (priority := 100) HasUniformContinuousConstSmul.to_has_continuous_const_smul
    [HasUniformContinuousConstSmul M X] : HasContinuousConstSmul M X :=
  ⟨fun c => (uniform_continuous_const_smul c).Continuous⟩
#align
  has_uniform_continuous_const_smul.to_has_continuous_const_smul HasUniformContinuousConstSmul.to_has_continuous_const_smul

variable {M X Y}

@[to_additive]
theorem UniformContinuous.const_smul [HasUniformContinuousConstSmul M X] {f : Y → X} (hf : UniformContinuous f)
    (c : M) : UniformContinuous (c • f) :=
  (uniform_continuous_const_smul c).comp hf
#align uniform_continuous.const_smul UniformContinuous.const_smul

/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[to_additive "If an additive action is central, then its right action is uniform\ncontinuous when its left action,is."]
instance (priority := 100) HasUniformContinuousConstSmul.op [HasSmul Mᵐᵒᵖ X] [IsCentralScalar M X]
    [HasUniformContinuousConstSmul M X] : HasUniformContinuousConstSmul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec fun c => by
      change UniformContinuous fun m => MulOpposite.op c • m
      simp_rw [op_smul_eq_smul]
      exact uniform_continuous_const_smul c⟩
#align has_uniform_continuous_const_smul.op HasUniformContinuousConstSmul.op

@[to_additive]
instance MulOpposite.has_uniform_continuous_const_smul [HasUniformContinuousConstSmul M X] :
    HasUniformContinuousConstSmul M Xᵐᵒᵖ :=
  ⟨fun c => MulOpposite.uniform_continuous_op.comp <| MulOpposite.uniform_continuous_unop.const_smul c⟩
#align mul_opposite.has_uniform_continuous_const_smul MulOpposite.has_uniform_continuous_const_smul

end HasSmul

@[to_additive]
instance UniformGroup.to_has_uniform_continuous_const_smul {G : Type u} [Group G] [UniformSpace G] [UniformGroup G] :
    HasUniformContinuousConstSmul G G :=
  ⟨fun c => uniform_continuous_const.mul uniform_continuous_id⟩
#align uniform_group.to_has_uniform_continuous_const_smul UniformGroup.to_has_uniform_continuous_const_smul

namespace UniformSpace

namespace Completion

section HasSmul

variable [HasSmul M X]

@[to_additive]
instance : HasSmul M (Completion X) :=
  ⟨fun c => Completion.map ((· • ·) c)⟩

@[to_additive]
theorem smul_def (c : M) (x : Completion X) : c • x = Completion.map ((· • ·) c) x :=
  rfl
#align uniform_space.completion.smul_def UniformSpace.Completion.smul_def

@[to_additive]
instance : HasUniformContinuousConstSmul M (Completion X) :=
  ⟨fun c => uniform_continuous_map⟩

@[to_additive]
instance [HasSmul N X] [HasSmul M N] [HasUniformContinuousConstSmul M X] [HasUniformContinuousConstSmul N X]
    [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x => by
    have : _ = (_ : completion X → completion X) :=
      map_comp (uniform_continuous_const_smul m) (uniform_continuous_const_smul n)
    refine' Eq.trans _ (congr_fun this.symm x)
    exact congr_arg (fun f => completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]
instance [HasSmul N X] [SmulCommClass M N X] [HasUniformContinuousConstSmul M X] [HasUniformContinuousConstSmul N X] :
    SmulCommClass M N (Completion X) :=
  ⟨fun m n x => by
    have hmn : m • n • x = (completion.map (HasSmul.smul m) ∘ completion.map (HasSmul.smul n)) x := rfl
    have hnm : n • m • x = (completion.map (HasSmul.smul n) ∘ completion.map (HasSmul.smul m)) x := rfl
    rw [hmn, hnm, map_comp, map_comp]
    exact congr_arg (fun f => completion.map f x) (funext (smul_comm _ _))
    repeat' exact uniform_continuous_const_smul _⟩

@[to_additive]
instance [HasSmul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
  ⟨fun c a => (congr_arg fun f => Completion.map f a) <| funext (op_smul_eq_smul c)⟩

variable {M X} [HasUniformContinuousConstSmul M X]

@[simp, norm_cast, to_additive]
theorem coe_smul (c : M) (x : X) : ↑(c • x) = (c • x : Completion X) :=
  (map_coe (uniform_continuous_const_smul c) x).symm
#align uniform_space.completion.coe_smul UniformSpace.Completion.coe_smul

end HasSmul

@[to_additive]
instance [Monoid M] [MulAction M X] [HasUniformContinuousConstSmul M X] : MulAction M (Completion X) where
  smul := (· • ·)
  one_smul := (ext' (continuous_const_smul _) continuous_id) fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    (ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _)) fun a => by
      simp only [← coe_smul, mul_smul]

end Completion

end UniformSpace

