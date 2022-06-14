/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Topology.Algebra.GroupCompletion

/-!
# Multiplicative action on the completion of a uniform space

In this file we define typeclasses `has_uniform_continuous_const_vadd` and
`has_uniform_continuous_const_smul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `uniform_space.completion X`. We
also provide similar instances `distrib_mul_action`, `mul_action_with_zero`, and `module`.
-/


universe u v w x y z

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X] [UniformSpace Y]

/-- An additive action such that for all `c`, the map `λ x, c +ᵥ x` is uniformly continuous. -/
class HasUniformContinuousConstVadd [UniformSpace X] [HasVadd M X] : Prop where
  uniform_continuous_const_vadd : ∀ c : M, UniformContinuous ((· +ᵥ ·) c : X → X)

/-- A multiplicative action such that for all `c`, the map `λ x, c • x` is uniformly continuous. -/
@[to_additive]
class HasUniformContinuousConstSmul [UniformSpace X] [HasScalar M X] : Prop where
  uniform_continuous_const_smul : ∀ c : M, UniformContinuous ((· • ·) c : X → X)

export HasUniformContinuousConstVadd (uniform_continuous_const_vadd)

export HasUniformContinuousConstSmul (uniform_continuous_const_smul)

section HasScalar

variable [HasScalar M X]

@[to_additive]
instance (priority := 100) HasUniformContinuousConstSmul.to_has_continuous_const_smul
    [HasUniformContinuousConstSmul M X] : HasContinuousConstSmul M X :=
  ⟨fun c => (uniform_continuous_const_smul c).Continuous⟩

variable {M X Y}

@[to_additive]
theorem UniformContinuous.const_smul [HasUniformContinuousConstSmul M X] {f : Y → X} (hf : UniformContinuous f)
    (c : M) : UniformContinuous (c • f) :=
  (uniform_continuous_const_smul c).comp hf

/-- If a scalar is central, then its right action is uniform continuous when its left action is. -/
instance (priority := 100) HasUniformContinuousConstSmul.op [HasScalar Mᵐᵒᵖ X] [IsCentralScalar M X]
    [HasUniformContinuousConstSmul M X] : HasUniformContinuousConstSmul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec fun c => by
      change UniformContinuous fun m => MulOpposite.op c • m
      simp_rw [op_smul_eq_smul]
      exact uniform_continuous_const_smul c⟩

@[to_additive]
instance MulOpposite.has_uniform_continuous_const_smul [HasUniformContinuousConstSmul M X] :
    HasUniformContinuousConstSmul M Xᵐᵒᵖ :=
  ⟨fun c => MulOpposite.uniform_continuous_op.comp <| MulOpposite.uniform_continuous_unop.const_smul c⟩

end HasScalar

@[to_additive]
instance UniformGroup.to_has_uniform_continuous_const_smul {G : Type u} [Groupₓ G] [UniformSpace G] [UniformGroup G] :
    HasUniformContinuousConstSmul G G :=
  ⟨fun c => uniform_continuous_const.mul uniform_continuous_id⟩

namespace UniformSpace

namespace Completion

section HasScalar

variable [HasScalar M X]

@[to_additive HasVadd]
instance : HasScalar M (Completion X) :=
  ⟨fun c => Completion.map ((· • ·) c)⟩

@[to_additive]
instance : HasUniformContinuousConstSmul M (Completion X) :=
  ⟨fun c => uniform_continuous_map⟩

instance [HasScalar Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
  ⟨fun c a => (congr_arg fun f => Completion.map f a) <| funext (op_smul_eq_smul c)⟩

variable {M X} [HasUniformContinuousConstSmul M X]

@[simp, norm_cast, to_additive]
theorem coe_smul (c : M) (x : X) : ↑(c • x) = (c • x : Completion X) :=
  (map_coe (uniform_continuous_const_smul c) x).symm

end HasScalar

@[to_additive]
instance [Monoidₓ M] [MulAction M X] [HasUniformContinuousConstSmul M X] : MulAction M (Completion X) where
  smul := (· • ·)
  one_smul :=
    (ext' (continuous_const_smul _) continuous_id) fun a => by
      rw [← coe_smul, one_smul]
  mul_smul := fun x y =>
    (ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _)) fun a => by
      simp only [← coe_smul, mul_smul]

instance [MonoidWithZeroₓ M] [Zero X] [MulActionWithZero M X] [HasUniformContinuousConstSmul M X] :
    MulActionWithZero M (Completion X) :=
  { Completion.mulAction M X with smul := (· • ·),
    smul_zero := fun r => by
      rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r],
    zero_smul :=
      (ext' (continuous_const_smul _) continuous_const) fun a => by
        rw [← coe_smul, zero_smul, coe_zero] }

instance [Monoidₓ M] [AddGroupₓ N] [DistribMulAction M N] [UniformSpace N] [UniformAddGroup N]
    [HasUniformContinuousConstSmul M N] : DistribMulAction M (Completion N) :=
  { Completion.mulAction M N with smul := (· • ·),
    smul_add := fun r x y =>
      induction_on₂ x y
        (is_closed_eq ((continuous_fst.add continuous_snd).const_smul _)
          ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)))
        fun a b => by
        simp only [← coe_add, ← coe_smul, smul_add],
    smul_zero := fun r => by
      rw [← coe_zero, ← coe_smul, smul_zero r] }

instance [Semiringₓ R] [AddCommGroupₓ M] [Module R M] [UniformSpace M] [UniformAddGroup M]
    [HasUniformContinuousConstSmul R M] : Module R (Completion M) :=
  { Completion.distribMulAction R M, Completion.mulActionWithZero R M with smul := (· • ·),
    add_smul := fun a b =>
      (ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))) fun x => by
        norm_cast
        rw [add_smul] }

end Completion

end UniformSpace

