/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.continuous_function.algebra
! leanprover-community/mathlib commit 7d34004e19699895c13c86b78ae62bbaea0bc893
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Pi
import Mathbin.Algebra.Periodic
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.Star.StarAlgHom
import Mathbin.Tactic.FieldSimp
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Star
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.ContinuousFunction.Ordered
import Mathbin.Topology.UniformSpace.CompactConvergence

/-!
# Algebraic structures over continuous functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define instances of algebraic structures over the type `continuous_map α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | continuous f }`. For example, when `β` is a group, a subgroup
`continuous_subgroup α β` of `α → β` is constructed with carrier `{ f : α → β | continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuous_subgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/


attribute [local elab_without_expected_type] Continuous.comp

namespace ContinuousFunctions

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {f g : { f : α → β | Continuous f }}

instance : CoeFun { f : α → β | Continuous f } fun _ => α → β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

#print ContinuousMap.instMul /-
-- ### "mul" and "add"
@[to_additive]
instance instMul [Mul β] [ContinuousMul β] : Mul C(α, β) :=
  ⟨fun f g => ⟨f * g, continuous_mul.comp (f.Continuous.prod_mk g.Continuous : _)⟩⟩
#align continuous_map.has_mul ContinuousMap.instMul
#align continuous_map.has_add ContinuousMap.instAdd
-/

/- warning: continuous_map.coe_mul -> ContinuousMap.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Mul.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHMul.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instMul.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_4))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Mul.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHMul.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instMul.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (instHMul.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => _inst_4))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_mul ContinuousMap.coe_mulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_mul [Mul β] [ContinuousMul β] (f g : C(α, β)) : ⇑(f * g) = f * g :=
  rfl
#align continuous_map.coe_mul ContinuousMap.coe_mul
#align continuous_map.coe_add ContinuousMap.coe_add

/- warning: continuous_map.mul_apply -> ContinuousMap.mul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Mul.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHMul.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instMul.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g) x) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_4) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Mul.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHMul.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instMul.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g) x) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (instHMul.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align continuous_map.mul_apply ContinuousMap.mul_applyₓ'. -/
@[simp, to_additive]
theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
  rfl
#align continuous_map.mul_apply ContinuousMap.mul_apply
#align continuous_map.add_apply ContinuousMap.add_apply

#print ContinuousMap.mul_comp /-
@[simp, to_additive]
theorem mul_comp [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl
#align continuous_map.mul_comp ContinuousMap.mul_comp
#align continuous_map.add_comp ContinuousMap.add_comp
-/

-- ### "one"
@[to_additive]
instance [One β] : One C(α, β) :=
  ⟨const α 1⟩

/- warning: continuous_map.coe_one -> ContinuousMap.coe_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : One.{u2} β], Eq.{succ (max u1 u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (OfNat.ofNat.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) 1 (OfNat.mk.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) 1 (One.one.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasOne.{u1, u2} α β _inst_1 _inst_2 _inst_4))))) (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_4)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : One.{u2} β], Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (OfNat.ofNat.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) 1 (One.toOfNat1.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instOneContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) (OfNat.ofNat.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) 1 (One.toOfNat1.{max u1 u2} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (Pi.instOne.{u1, u2} α (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (fun (i : α) => _inst_4))))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_one ContinuousMap.coe_oneₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_one [One β] : ⇑(1 : C(α, β)) = 1 :=
  rfl
#align continuous_map.coe_one ContinuousMap.coe_one
#align continuous_map.coe_zero ContinuousMap.coe_zero

/- warning: continuous_map.one_apply -> ContinuousMap.one_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : One.{u2} β] (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (OfNat.ofNat.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) 1 (OfNat.mk.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) 1 (One.one.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasOne.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) x) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_4)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : One.{u2} β] (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (OfNat.ofNat.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) 1 (One.toOfNat1.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instOneContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4))) x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4))
Case conversion may be inaccurate. Consider using '#align continuous_map.one_apply ContinuousMap.one_applyₓ'. -/
@[simp, to_additive]
theorem one_apply [One β] (x : α) : (1 : C(α, β)) x = 1 :=
  rfl
#align continuous_map.one_apply ContinuousMap.one_apply
#align continuous_map.zero_apply ContinuousMap.zero_apply

/- warning: continuous_map.one_comp -> ContinuousMap.one_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : One.{u3} γ] (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) 1 (OfNat.mk.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) 1 (One.one.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.hasOne.{u2, u3} β γ _inst_2 _inst_3 _inst_4)))) g) (OfNat.ofNat.{max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) 1 (OfNat.mk.{max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) 1 (One.one.{max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.hasOne.{u1, u3} α γ _inst_1 _inst_3 _inst_4))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : One.{u3} γ] (g : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u3)} (ContinuousMap.{u2, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u2, u1, u3} α β γ _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{max u1 u3} (ContinuousMap.{u1, u3} β γ _inst_2 _inst_3) 1 (One.toOfNat1.{max u1 u3} (ContinuousMap.{u1, u3} β γ _inst_2 _inst_3) (ContinuousMap.instOneContinuousMap.{u1, u3} β γ _inst_2 _inst_3 _inst_4))) g) (OfNat.ofNat.{max u2 u3} (ContinuousMap.{u2, u3} α γ _inst_1 _inst_3) 1 (One.toOfNat1.{max u2 u3} (ContinuousMap.{u2, u3} α γ _inst_1 _inst_3) (ContinuousMap.instOneContinuousMap.{u2, u3} α γ _inst_1 _inst_3 _inst_4)))
Case conversion may be inaccurate. Consider using '#align continuous_map.one_comp ContinuousMap.one_compₓ'. -/
@[simp, to_additive]
theorem one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 :=
  rfl
#align continuous_map.one_comp ContinuousMap.one_comp
#align continuous_map.zero_comp ContinuousMap.zero_comp

-- ### "nat_cast"
instance [NatCast β] : NatCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

/- warning: continuous_map.coe_nat_cast -> ContinuousMap.coe_nat_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : NatCast.{u2} β] (n : Nat), Eq.{max (succ u1) (succ u2)} ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (Nat.castCoe.{max u1 u2} ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (Pi.hasNatCast.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) => _inst_4))))) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : NatCast.{u2} β] (n : Nat), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Nat.cast.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instNatCastContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4) n)) (Nat.cast.{max u1 u2} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (Pi.natCast.{u1, u2} α (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (fun (a : α) => _inst_4)) n)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_nat_cast ContinuousMap.coe_nat_castₓ'. -/
@[simp, norm_cast]
theorem coe_nat_cast [NatCast β] (n : ℕ) : ((n : C(α, β)) : α → β) = n :=
  rfl
#align continuous_map.coe_nat_cast ContinuousMap.coe_nat_cast

/- warning: continuous_map.nat_cast_apply -> ContinuousMap.nat_cast_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : NatCast.{u2} β] (n : Nat) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Nat.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasNatCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n) x) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u2} Nat β (CoeTCₓ.coe.{1, succ u2} Nat β (Nat.castCoe.{u2} β _inst_4))) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : NatCast.{u2} β] (n : Nat) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Nat.cast.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instNatCastContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4) n) x) (Nat.cast.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4 n)
Case conversion may be inaccurate. Consider using '#align continuous_map.nat_cast_apply ContinuousMap.nat_cast_applyₓ'. -/
@[simp]
theorem nat_cast_apply [NatCast β] (n : ℕ) (x : α) : (n : C(α, β)) x = n :=
  rfl
#align continuous_map.nat_cast_apply ContinuousMap.nat_cast_apply

-- ### "int_cast"
instance [IntCast β] : IntCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

/- warning: continuous_map.coe_int_cast -> ContinuousMap.coe_int_cast is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : IntCast.{u2} β] (n : Int), Eq.{max (succ u1) (succ u2)} ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (Int.castCoe.{max u1 u2} ((fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n)) (Pi.hasIntCast.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_4))))) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : IntCast.{u2} β] (n : Int), Eq.{max (succ u1) (succ u2)} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Int.cast.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instIntCastContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4) n)) (Int.cast.{max u1 u2} (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (Pi.intCast.{u1, u2} α (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (fun (i : α) => _inst_4)) n)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_int_cast ContinuousMap.coe_int_castₓ'. -/
@[simp, norm_cast]
theorem coe_int_cast [IntCast β] (n : ℤ) : ((n : C(α, β)) : α → β) = n :=
  rfl
#align continuous_map.coe_int_cast ContinuousMap.coe_int_cast

/- warning: continuous_map.int_cast_apply -> ContinuousMap.int_cast_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : IntCast.{u2} β] (n : Int) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) ((fun (a : Type) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{1, max (succ u1) (succ u2)} a b] => self.0) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (HasLiftT.mk.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (CoeTCₓ.coe.{1, max (succ u1) (succ u2)} Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (Int.castCoe.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasIntCast.{u1, u2} α β _inst_1 _inst_2 _inst_4)))) n) x) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int β (HasLiftT.mk.{1, succ u2} Int β (CoeTCₓ.coe.{1, succ u2} Int β (Int.castCoe.{u2} β _inst_4))) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : IntCast.{u2} β] (n : Int) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Int.cast.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instIntCastContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4) n) x) (Int.cast.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4 n)
Case conversion may be inaccurate. Consider using '#align continuous_map.int_cast_apply ContinuousMap.int_cast_applyₓ'. -/
@[simp]
theorem int_cast_apply [IntCast β] (n : ℤ) (x : α) : (n : C(α, β)) x = n :=
  rfl
#align continuous_map.int_cast_apply ContinuousMap.int_cast_apply

/- warning: continuous_map.has_nsmul -> ContinuousMap.instNSMul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : AddMonoid.{u2} β] [_inst_5 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4))], SMul.{0, max u1 u2} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : AddMonoid.{u2} β] [_inst_5 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4))], SMul.{0, max u2 u1} Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align continuous_map.has_nsmul ContinuousMap.instNSMulₓ'. -/
-- ### "nsmul" and "pow"
instance instNSMul [AddMonoid β] [ContinuousAdd β] : SMul ℕ C(α, β) :=
  ⟨fun n f => ⟨n • f, f.Continuous.nsmul n⟩⟩
#align continuous_map.has_nsmul ContinuousMap.instNSMul

/- warning: continuous_map.has_pow -> ContinuousMap.instPow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Monoid.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_4))], Pow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Monoid.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_4))], Pow.{max u2 u1, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat
Case conversion may be inaccurate. Consider using '#align continuous_map.has_pow ContinuousMap.instPowₓ'. -/
@[to_additive]
instance instPow [Monoid β] [ContinuousMul β] : Pow C(α, β) ℕ :=
  ⟨fun f n => ⟨f ^ n, f.Continuous.pow n⟩⟩
#align continuous_map.has_pow ContinuousMap.instPow
#align continuous_map.has_nsmul ContinuousMap.instNSMul

/- warning: continuous_map.coe_pow -> ContinuousMap.coe_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Monoid.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_4))] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (n : Nat), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.instPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> β) Nat (α -> β) (instHPow.{max u1 u2, 0} (α -> β) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => β) (fun (i : α) => Monoid.Pow.{u2} β _inst_4))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Monoid.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_4))] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (n : Nat), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.instPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) Nat (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (instHPow.{max u1 u2, 0} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) Nat (Pi.instPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => Monoid.Pow.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) _inst_4))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f) n)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_pow ContinuousMap.coe_powₓ'. -/
@[norm_cast, to_additive]
theorem coe_pow [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) : ⇑(f ^ n) = f ^ n :=
  rfl
#align continuous_map.coe_pow ContinuousMap.coe_pow
#align continuous_map.coe_nsmul ContinuousMap.coe_nsmul

/- warning: continuous_map.pow_apply -> ContinuousMap.pow_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Monoid.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_4))] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (n : Nat) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.instPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f n) x) (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat (Monoid.Pow.{u2} β _inst_4)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Monoid.{u2} β] [_inst_5 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_4))] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (n : Nat) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Nat (ContinuousMap.instPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f n) x) (HPow.hPow.{u2, 0, u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) Nat ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (instHPow.{u2, 0} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) Nat (Monoid.Pow.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x) n)
Case conversion may be inaccurate. Consider using '#align continuous_map.pow_apply ContinuousMap.pow_applyₓ'. -/
@[to_additive]
theorem pow_apply [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) (x : α) :
    (f ^ n) x = f x ^ n :=
  rfl
#align continuous_map.pow_apply ContinuousMap.pow_apply
#align continuous_map.nsmul_apply ContinuousMap.nsmul_apply

-- don't make auto-generated `coe_nsmul` and `nsmul_apply` simp, as the linter complains they're
-- redundant WRT `coe_smul`
attribute [simp] coe_pow pow_apply

/- warning: continuous_map.pow_comp -> ContinuousMap.pow_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : Monoid.{u3} γ] [_inst_5 : ContinuousMul.{u3} γ _inst_3 (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ _inst_4))] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (n : Nat) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (HPow.hPow.{max u2 u3, 0, max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) Nat (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (instHPow.{max u2 u3, 0} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) Nat (ContinuousMap.instPow.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5)) f n) g) (HPow.hPow.{max u1 u3, 0, max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) Nat (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (instHPow.{max u1 u3, 0} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) Nat (ContinuousMap.instPow.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5)) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : Monoid.{u3} γ] [_inst_5 : ContinuousMul.{u3} γ _inst_3 (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ _inst_4))] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (n : Nat) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (HPow.hPow.{max u2 u3, 0, max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) Nat (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (instHPow.{max u2 u3, 0} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) Nat (ContinuousMap.instPow.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5)) f n) g) (HPow.hPow.{max u1 u3, 0, max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) Nat (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (instHPow.{max u1 u3, 0} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) Nat (ContinuousMap.instPow.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5)) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) n)
Case conversion may be inaccurate. Consider using '#align continuous_map.pow_comp ContinuousMap.pow_compₓ'. -/
@[to_additive]
theorem pow_comp [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
    (f ^ n).comp g = f.comp g ^ n :=
  rfl
#align continuous_map.pow_comp ContinuousMap.pow_comp
#align continuous_map.nsmul_comp ContinuousMap.nsmul_comp

-- don't make `nsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] pow_comp

-- ### "inv" and "neg"
@[to_additive]
instance [Group β] [TopologicalGroup β] : Inv C(α, β) where inv f := ⟨f⁻¹, f.Continuous.inv⟩

/- warning: continuous_map.coe_inv -> ContinuousMap.coe_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Inv.inv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasInv.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) f)) (Inv.inv.{max u1 u2} (α -> β) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Inv.inv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instInvContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) f)) (Inv.inv.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => InvOneClass.toInv.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) (DivInvOneMonoid.toInvOneClass.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) (DivisionMonoid.toDivInvOneMonoid.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) (Group.toDivisionMonoid.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) _inst_4))))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_inv ContinuousMap.coe_invₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_inv [Group β] [TopologicalGroup β] (f : C(α, β)) : ⇑f⁻¹ = f⁻¹ :=
  rfl
#align continuous_map.coe_inv ContinuousMap.coe_inv
#align continuous_map.coe_neg ContinuousMap.coe_neg

/- warning: continuous_map.inv_apply -> ContinuousMap.inv_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Inv.inv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasInv.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) f) x) (Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (Inv.inv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instInvContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) f) x) (Inv.inv.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (InvOneClass.toInv.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (DivInvOneMonoid.toInvOneClass.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (DivisionMonoid.toDivInvOneMonoid.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (Group.toDivisionMonoid.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4)))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align continuous_map.inv_apply ContinuousMap.inv_applyₓ'. -/
@[simp, to_additive]
theorem inv_apply [Group β] [TopologicalGroup β] (f : C(α, β)) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align continuous_map.inv_apply ContinuousMap.inv_apply
#align continuous_map.neg_apply ContinuousMap.neg_apply

/- warning: continuous_map.inv_comp -> ContinuousMap.inv_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : Group.{u3} γ] [_inst_5 : TopologicalGroup.{u3} γ _inst_3 _inst_4] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Inv.inv.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.hasInv.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5) f) g) (Inv.inv.{max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.hasInv.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : Group.{u3} γ] [_inst_5 : TopologicalGroup.{u3} γ _inst_3 _inst_4] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (Inv.inv.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.instInvContinuousMap.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5) f) g) (Inv.inv.{max u3 u1} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.instInvContinuousMap.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g))
Case conversion may be inaccurate. Consider using '#align continuous_map.inv_comp ContinuousMap.inv_compₓ'. -/
@[simp, to_additive]
theorem inv_comp [Group γ] [TopologicalGroup γ] (f : C(β, γ)) (g : C(α, β)) :
    f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl
#align continuous_map.inv_comp ContinuousMap.inv_comp
#align continuous_map.neg_comp ContinuousMap.neg_comp

-- ### "div" and "sub"
@[to_additive]
instance [Div β] [ContinuousDiv β] : Div C(α, β)
    where div f g := ⟨f / g, f.Continuous.div' g.Continuous⟩

/- warning: continuous_map.coe_div -> ContinuousMap.coe_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Div.{u2} β] [_inst_5 : ContinuousDiv.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHDiv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasDiv.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_4))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Div.{u2} β] [_inst_5 : ContinuousDiv.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHDiv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instDivContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (instHDiv.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => _inst_4))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_div ContinuousMap.coe_divₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_div [Div β] [ContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
  rfl
#align continuous_map.coe_div ContinuousMap.coe_div
#align continuous_map.coe_sub ContinuousMap.coe_sub

/- warning: continuous_map.div_apply -> ContinuousMap.div_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Div.{u2} β] [_inst_5 : ContinuousDiv.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHDiv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasDiv.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g) x) (HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β _inst_4) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Div.{u2} β] [_inst_5 : ContinuousDiv.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHDiv.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.instDivContinuousMap.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f g) x) (HDiv.hDiv.{u2, u2, u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (instHDiv.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align continuous_map.div_apply ContinuousMap.div_applyₓ'. -/
@[simp, to_additive]
theorem div_apply [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α) : (f / g) x = f x / g x :=
  rfl
#align continuous_map.div_apply ContinuousMap.div_apply
#align continuous_map.sub_apply ContinuousMap.sub_apply

/- warning: continuous_map.div_comp -> ContinuousMap.div_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : Div.{u3} γ] [_inst_5 : ContinuousDiv.{u3} γ _inst_3 _inst_4] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (h : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (instHDiv.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.hasDiv.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5)) f g) h) (HDiv.hDiv.{max u1 u3, max u1 u3, max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (instHDiv.{max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.hasDiv.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5)) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f h) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : Div.{u3} γ] [_inst_5 : ContinuousDiv.{u3} γ _inst_3 _inst_4] (f : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (g : ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (h : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (instHDiv.{max u2 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.instDivContinuousMap.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5)) f g) h) (HDiv.hDiv.{max u1 u3, max u1 u3, max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (instHDiv.{max u1 u3} (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.instDivContinuousMap.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5)) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f h) (ContinuousMap.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align continuous_map.div_comp ContinuousMap.div_compₓ'. -/
@[simp, to_additive]
theorem div_comp [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) :
    (f / g).comp h = f.comp h / g.comp h :=
  rfl
#align continuous_map.div_comp ContinuousMap.div_comp
#align continuous_map.sub_comp ContinuousMap.sub_comp

#print ContinuousMap.instZSMul /-
-- ### "zpow" and "zsmul"
instance instZSMul [AddGroup β] [TopologicalAddGroup β] : SMul ℤ C(α, β)
    where smul z f := ⟨z • f, f.Continuous.zsmul z⟩
#align continuous_map.has_zsmul ContinuousMap.instZSMul
-/

#print ContinuousMap.instZPow /-
@[to_additive]
instance instZPow [Group β] [TopologicalGroup β] : Pow C(α, β) ℤ
    where pow f z := ⟨f ^ z, f.Continuous.zpow z⟩
#align continuous_map.has_zpow ContinuousMap.instZPow
#align continuous_map.has_zsmul ContinuousMap.instZSMul
-/

/- warning: continuous_map.coe_zpow -> ContinuousMap.coe_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (z : Int), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.instZPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f z)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> β) Int (α -> β) (instHPow.{max u1 u2, 0} (α -> β) Int (Pi.hasPow.{u1, u2, 0} α Int (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.Pow.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f) z)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (z : Int), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.instZPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f z)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) Int (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (instHPow.{max u1 u2, 0} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) Int (Pi.instPow.{u1, u2, 0} α Int (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => DivInvMonoid.Pow.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) (Group.toDivInvMonoid.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) i) _inst_4)))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f) z)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_zpow ContinuousMap.coe_zpowₓ'. -/
@[norm_cast, to_additive]
theorem coe_zpow [Group β] [TopologicalGroup β] (f : C(α, β)) (z : ℤ) : ⇑(f ^ z) = f ^ z :=
  rfl
#align continuous_map.coe_zpow ContinuousMap.coe_zpow
#align continuous_map.coe_zsmul ContinuousMap.coe_zsmul

/- warning: continuous_map.zpow_apply -> ContinuousMap.zpow_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (z : Int) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.instZPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f z) x) (HPow.hPow.{u2, 0, u2} β Int β (instHPow.{u2, 0} β Int (DivInvMonoid.Pow.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x) z)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (z : Int) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (instHPow.{max u1 u2, 0} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) Int (ContinuousMap.instZPow.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5)) f z) x) (HPow.hPow.{u2, 0, u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) Int ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (instHPow.{u2, 0} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) Int (DivInvMonoid.Pow.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (Group.toDivInvMonoid.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_4))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α β _inst_1 _inst_2)) f x) z)
Case conversion may be inaccurate. Consider using '#align continuous_map.zpow_apply ContinuousMap.zpow_applyₓ'. -/
@[to_additive]
theorem zpow_apply [Group β] [TopologicalGroup β] (f : C(α, β)) (z : ℤ) (x : α) :
    (f ^ z) x = f x ^ z :=
  rfl
#align continuous_map.zpow_apply ContinuousMap.zpow_apply
#align continuous_map.zsmul_apply ContinuousMap.zsmul_apply

-- don't make auto-generated `coe_zsmul` and `zsmul_apply` simp as the linter complains they're
-- redundant WRT `coe_smul`
attribute [simp] coe_zpow zpow_apply

#print ContinuousMap.zpow_comp /-
@[to_additive]
theorem zpow_comp [Group γ] [TopologicalGroup γ] (f : C(β, γ)) (z : ℤ) (g : C(α, β)) :
    (f ^ z).comp g = f.comp g ^ z :=
  rfl
#align continuous_map.zpow_comp ContinuousMap.zpow_comp
#align continuous_map.zsmul_comp ContinuousMap.zsmul_comp
-/

-- don't make `zsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] zpow_comp

end ContinuousMap

section GroupStructure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/


section Subtype

/- warning: continuous_submonoid -> continuousSubmonoid is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : MulOneClass.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β _inst_3)], Submonoid.{max u1 u2} (α -> β) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : MulOneClass.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toMul.{u2} β _inst_3)], Submonoid.{max u1 u2} (α -> β) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3))
Case conversion may be inaccurate. Consider using '#align continuous_submonoid continuousSubmonoidₓ'. -/
/-- The `submonoid` of continuous maps `α → β`. -/
@[to_additive "The `add_submonoid` of continuous maps `α → β`. "]
def continuousSubmonoid (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α → β)
    where
  carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' f g fc gc := fc.mul gc
#align continuous_submonoid continuousSubmonoid
#align continuous_add_submonoid continuousAddSubmonoid

#print continuousSubgroup /-
/-- The subgroup of continuous maps `α → β`. -/
@[to_additive "The `add_subgroup` of continuous maps `α → β`. "]
def continuousSubgroup (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [TopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun f fc => Continuous.inv fc }
#align continuous_subgroup continuousSubgroup
#align continuous_add_subgroup continuousAddSubgroup
-/

end Subtype

namespace ContinuousMap

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

@[to_additive]
instance [Semigroup β] [ContinuousMul β] : Semigroup C(α, β) :=
  coe_injective.Semigroup _ coe_mul

@[to_additive]
instance [CommSemigroup β] [ContinuousMul β] : CommSemigroup C(α, β) :=
  coe_injective.CommSemigroup _ coe_mul

@[to_additive]
instance [MulOneClass β] [ContinuousMul β] : MulOneClass C(α, β) :=
  coe_injective.MulOneClass _ coe_one coe_mul

instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C(α, β) :=
  coe_injective.MulZeroClass _ coe_zero coe_mul

instance [SemigroupWithZero β] [ContinuousMul β] : SemigroupWithZero C(α, β) :=
  coe_injective.SemigroupWithZero _ coe_zero coe_mul

@[to_additive]
instance [Monoid β] [ContinuousMul β] : Monoid C(α, β) :=
  coe_injective.Monoid _ coe_one coe_mul coe_pow

instance [MonoidWithZero β] [ContinuousMul β] : MonoidWithZero C(α, β) :=
  coe_injective.MonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [CommMonoid β] [ContinuousMul β] : CommMonoid C(α, β) :=
  coe_injective.CommMonoid _ coe_one coe_mul coe_pow

instance [CommMonoidWithZero β] [ContinuousMul β] : CommMonoidWithZero C(α, β) :=
  coe_injective.CommMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [LocallyCompactSpace α] [Mul β] [ContinuousMul β] : ContinuousMul C(α, β) :=
  ⟨by
    refine' continuous_of_continuous_uncurry _ _
    have h1 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.fst x.snd :=
      continuous_eval'.comp (continuous_fst.prod_map continuous_id)
    have h2 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.snd x.snd :=
      continuous_eval'.comp (continuous_snd.prod_map continuous_id)
    exact h1.mul h2⟩

/- warning: continuous_map.coe_fn_monoid_hom -> ContinuousMap.coeFnMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Monoid.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_3))], MonoidHom.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (ContinuousMap.mulOneClass.{u1, u2} α β _inst_1 _inst_2 (Monoid.toMulOneClass.{u2} β _inst_3) _inst_4) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Monoid.toMulOneClass.{u2} β _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Monoid.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_3))], MonoidHom.{max u2 u1, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (ContinuousMap.instMulOneClassContinuousMap.{u1, u2} α β _inst_1 _inst_2 (Monoid.toMulOneClass.{u2} β _inst_3) _inst_4) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Monoid.toMulOneClass.{u2} β _inst_3))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_fn_monoid_hom ContinuousMap.coeFnMonoidHomₓ'. -/
/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.",
  simps]
def coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) →* α → β
    where
  toFun := coeFn
  map_one' := coe_one
  map_mul' := coe_mul
#align continuous_map.coe_fn_monoid_hom ContinuousMap.coeFnMonoidHom
#align continuous_map.coe_fn_add_monoid_hom ContinuousMap.coeFnAddMonoidHom

variable (α)

/- warning: monoid_hom.comp_left_continuous -> MonoidHom.compLeftContinuous is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : Monoid.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_3))] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Monoid.{u3} γ] [_inst_7 : ContinuousMul.{u3} γ _inst_5 (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ _inst_6))] (g : MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)), (Continuous.{u2, u3} β γ _inst_2 _inst_5 (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)) (fun (_x : MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)) => β -> γ) (MonoidHom.hasCoeToFun.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)) g)) -> (MonoidHom.{max u1 u2, max u1 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_5) (ContinuousMap.mulOneClass.{u1, u2} α β _inst_1 _inst_2 (Monoid.toMulOneClass.{u2} β _inst_3) _inst_4) (ContinuousMap.mulOneClass.{u1, u3} α γ _inst_1 _inst_5 (Monoid.toMulOneClass.{u3} γ _inst_6) _inst_7))
but is expected to have type
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : Monoid.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_3))] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Monoid.{u3} γ] [_inst_7 : ContinuousMul.{u3} γ _inst_5 (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ _inst_6))] (g : MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)), (Continuous.{u2, u3} β γ _inst_2 _inst_5 (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : β) => γ) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)) β γ (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_3)) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ _inst_6)) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)) β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6) (MonoidHom.monoidHomClass.{u2, u3} β γ (Monoid.toMulOneClass.{u2} β _inst_3) (Monoid.toMulOneClass.{u3} γ _inst_6)))) g)) -> (MonoidHom.{max u2 u1, max u3 u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_5) (ContinuousMap.instMulOneClassContinuousMap.{u1, u2} α β _inst_1 _inst_2 (Monoid.toMulOneClass.{u2} β _inst_3) _inst_4) (ContinuousMap.instMulOneClassContinuousMap.{u1, u3} α γ _inst_1 _inst_5 (Monoid.toMulOneClass.{u3} γ _inst_6) _inst_7))
Case conversion may be inaccurate. Consider using '#align monoid_hom.comp_left_continuous MonoidHom.compLeftContinuousₓ'. -/
/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`monoid_hom`. Similar to `monoid_hom.comp_left`. -/
@[to_additive
      "Composition on the left by a (continuous) homomorphism of topological `add_monoid`s,\nas an `add_monoid_hom`. Similar to `add_monoid_hom.comp_left`.",
  simps]
protected def MonoidHom.compLeftContinuous {γ : Type _} [Monoid β] [ContinuousMul β]
    [TopologicalSpace γ] [Monoid γ] [ContinuousMul γ] (g : β →* γ) (hg : Continuous g) :
    C(α, β) →* C(α, γ) where
  toFun f := (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun x => g.map_one
  map_mul' f₁ f₂ := ext fun x => g.map_mul _ _
#align monoid_hom.comp_left_continuous MonoidHom.compLeftContinuous
#align add_monoid_hom.comp_left_continuous AddMonoidHom.compLeftContinuous

variable {α}

/- warning: continuous_map.comp_monoid_hom' -> ContinuousMap.compMonoidHom' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : MulOneClass.{u3} γ] [_inst_5 : ContinuousMul.{u3} γ _inst_3 (MulOneClass.toHasMul.{u3} γ _inst_4)], (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) -> (MonoidHom.{max u2 u3, max u1 u3} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.mulOneClass.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5) (ContinuousMap.mulOneClass.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : MulOneClass.{u3} γ] [_inst_5 : ContinuousMul.{u3} γ _inst_3 (MulOneClass.toMul.{u3} γ _inst_4)], (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) -> (MonoidHom.{max u3 u2, max u3 u1} (ContinuousMap.{u2, u3} β γ _inst_2 _inst_3) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_3) (ContinuousMap.instMulOneClassContinuousMap.{u2, u3} β γ _inst_2 _inst_3 _inst_4 _inst_5) (ContinuousMap.instMulOneClassContinuousMap.{u1, u3} α γ _inst_1 _inst_3 _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_monoid_hom' ContinuousMap.compMonoidHom'ₓ'. -/
/-- Composition on the right as a `monoid_hom`. Similar to `monoid_hom.comp_hom'`. -/
@[to_additive
      "Composition on the right as an `add_monoid_hom`. Similar to\n`add_monoid_hom.comp_hom'`.",
  simps]
def compMonoidHom' {γ : Type _} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
    (g : C(α, β)) : C(β, γ) →* C(α, γ)
    where
  toFun f := f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g
#align continuous_map.comp_monoid_hom' ContinuousMap.compMonoidHom'
#align continuous_map.comp_add_monoid_hom' ContinuousMap.compAddMonoidHom'

open BigOperators

/- warning: continuous_map.coe_prod -> ContinuousMap.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3)))] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Finset.prod.{max u1 u2, u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) ι (ContinuousMap.commMonoid.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) s (fun (i : ι) => f i))) (Finset.prod.{max u1 u2, u3} (α -> β) ι (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3)) s (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : CommMonoid.{u3} β] [_inst_4 : ContinuousMul.{u3} β _inst_2 (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_3)))] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (ContinuousMap.{u1, u3} α β _inst_1 _inst_2)), Eq.{max (succ u1) (succ u3)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) (Finset.prod.{max u1 u3, u2} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) ι (ContinuousMap.instCommMonoidContinuousMap.{u1, u3} α β _inst_1 _inst_2 _inst_3 _inst_4) s (fun (i : ι) => f i))) (Finset.prod.{max u1 u3, u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) ι (Pi.commMonoid.{u1, u3} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => _inst_3)) s (fun (i : ι) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) (f i)))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_prod ContinuousMap.coe_prodₓ'. -/
@[simp, to_additive]
theorem coe_prod [CommMonoid β] [ContinuousMul β] {ι : Type _} (s : Finset ι) (f : ι → C(α, β)) :
    ⇑(∏ i in s, f i) = ∏ i in s, (f i : α → β) :=
  (coeFnMonoidHom : C(α, β) →* _).map_prod f s
#align continuous_map.coe_prod ContinuousMap.coe_prod
#align continuous_map.coe_sum ContinuousMap.coe_sum

/- warning: continuous_map.prod_apply -> ContinuousMap.prod_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : CommMonoid.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3)))] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Finset.prod.{max u1 u2, u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) ι (ContinuousMap.commMonoid.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) s (fun (i : ι) => f i)) a) (Finset.prod.{u2, u3} β ι _inst_3 s (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (f i) a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : CommMonoid.{u3} β] [_inst_4 : ContinuousMul.{u3} β _inst_2 (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_3)))] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> (ContinuousMap.{u1, u3} α β _inst_1 _inst_2)) (a : α), Eq.{succ u3} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) (Finset.prod.{max u1 u3, u2} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) ι (ContinuousMap.instCommMonoidContinuousMap.{u1, u3} α β _inst_1 _inst_2 _inst_3 _inst_4) s (fun (i : ι) => f i)) a) (Finset.prod.{u3, u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) a) ι _inst_3 s (fun (i : ι) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u1 u3, u1, u3} (ContinuousMap.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u3} α β _inst_1 _inst_2)) (f i) a))
Case conversion may be inaccurate. Consider using '#align continuous_map.prod_apply ContinuousMap.prod_applyₓ'. -/
@[to_additive]
theorem prod_apply [CommMonoid β] [ContinuousMul β] {ι : Type _} (s : Finset ι) (f : ι → C(α, β))
    (a : α) : (∏ i in s, f i) a = ∏ i in s, f i a := by simp
#align continuous_map.prod_apply ContinuousMap.prod_apply
#align continuous_map.sum_apply ContinuousMap.sum_apply

@[to_additive]
instance [Group β] [TopologicalGroup β] : Group C(α, β) :=
  coe_injective.Group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup β] [TopologicalGroup β] : CommGroup C(α, β) :=
  coe_injective.CommGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup β] [TopologicalGroup β] : TopologicalGroup C(α, β)
    where
  continuous_mul := by
    letI : UniformSpace β := TopologicalGroup.toUniformSpace β
    have : UniformGroup β := comm_topologicalGroup_is_uniform
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt, tendsto_iff_forall_compact_tendsto_uniformly_on, nhds_prod_eq]
    exact fun K hK =>
      uniform_continuous_mul.comp_tendsto_uniformly_on
        ((tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK).Prod
          (tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK))
  continuous_inv := by
    letI : UniformSpace β := TopologicalGroup.toUniformSpace β
    have : UniformGroup β := comm_topologicalGroup_is_uniform
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, tendsto_iff_forall_compact_tendsto_uniformly_on]
    exact fun K hK =>
      uniform_continuous_inv.comp_tendsto_uniformly_on
        (tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK)

/- warning: continuous_map.has_sum_apply -> ContinuousMap.hasSum_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : LocallyCompactSpace.{u1} α _inst_1] [_inst_4 : AddCommMonoid.{u2} β] [_inst_5 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_4)))] {f : γ -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)} {g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2}, (HasSum.{max u1 u2, u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) γ (ContinuousMap.addCommMonoid.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f g) -> (forall (x : α), HasSum.{u2, u3} β γ _inst_4 _inst_2 (fun (i : γ) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (f i) x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {γ : Type.{u3}} [_inst_3 : LocallyCompactSpace.{u2} α _inst_1] [_inst_4 : AddCommMonoid.{u1} β] [_inst_5 : ContinuousAdd.{u1} β _inst_2 (AddZeroClass.toAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddCommMonoid.toAddMonoid.{u1} β _inst_4)))] {f : γ -> (ContinuousMap.{u2, u1} α β _inst_1 _inst_2)} {g : ContinuousMap.{u2, u1} α β _inst_1 _inst_2}, (HasSum.{max u2 u1, u3} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) γ (ContinuousMap.instAddCommMonoidContinuousMap.{u2, u1} α β _inst_1 _inst_2 _inst_4 _inst_5) (ContinuousMap.compactOpen.{u2, u1} α β _inst_1 _inst_2) f g) -> (forall (x : α), HasSum.{u1, u3} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) γ _inst_4 _inst_2 (fun (i : γ) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (f i) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) g x))
Case conversion may be inaccurate. Consider using '#align continuous_map.has_sum_apply ContinuousMap.hasSum_applyₓ'. -/
-- TODO: rewrite the next three lemmas for products and deduce sum case via `to_additive`, once
-- definition of `tprod` is in place
/-- If `α` is locally compact, and an infinite sum of functions in `C(α, β)`
converges to `g` (for the compact-open topology), then the pointwise sum converges to `g x` for
all `x ∈ α`. -/
theorem hasSum_apply {γ : Type _} [LocallyCompactSpace α] [AddCommMonoid β] [ContinuousAdd β]
    {f : γ → C(α, β)} {g : C(α, β)} (hf : HasSum f g) (x : α) : HasSum (fun i : γ => f i x) (g x) :=
  by
  let evₓ : AddMonoidHom C(α, β) β := (Pi.evalAddMonoidHom _ x).comp coe_fn_add_monoid_hom
  exact hf.map evₓ (ContinuousMap.continuous_eval_const' x)
#align continuous_map.has_sum_apply ContinuousMap.hasSum_apply

/- warning: continuous_map.summable_apply -> ContinuousMap.summable_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : LocallyCompactSpace.{u1} α _inst_1] [_inst_4 : AddCommMonoid.{u2} β] [_inst_5 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_4)))] {γ : Type.{u3}} {f : γ -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)}, (Summable.{max u1 u2, u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) γ (ContinuousMap.addCommMonoid.{u1, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f) -> (forall (x : α), Summable.{u2, u3} β γ _inst_4 _inst_2 (fun (i : γ) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (f i) x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : LocallyCompactSpace.{u3} α _inst_1] [_inst_4 : AddCommMonoid.{u2} β] [_inst_5 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_4)))] {γ : Type.{u1}} {f : γ -> (ContinuousMap.{u3, u2} α β _inst_1 _inst_2)}, (Summable.{max u3 u2, u1} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) γ (ContinuousMap.instAddCommMonoidContinuousMap.{u3, u2} α β _inst_1 _inst_2 _inst_4 _inst_5) (ContinuousMap.compactOpen.{u3, u2} α β _inst_1 _inst_2) f) -> (forall (x : α), Summable.{u2, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) γ _inst_4 _inst_2 (fun (i : γ) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} α β _inst_1 _inst_2)) (f i) x))
Case conversion may be inaccurate. Consider using '#align continuous_map.summable_apply ContinuousMap.summable_applyₓ'. -/
theorem summable_apply [LocallyCompactSpace α] [AddCommMonoid β] [ContinuousAdd β] {γ : Type _}
    {f : γ → C(α, β)} (hf : Summable f) (x : α) : Summable fun i : γ => f i x :=
  (hasSum_apply hf.HasSum x).Summable
#align continuous_map.summable_apply ContinuousMap.summable_apply

/- warning: continuous_map.tsum_apply -> ContinuousMap.tsum_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : LocallyCompactSpace.{u1} α _inst_1] [_inst_4 : T2Space.{u2} β _inst_2] [_inst_5 : AddCommMonoid.{u2} β] [_inst_6 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_5)))] {γ : Type.{u3}} {f : γ -> (ContinuousMap.{u1, u2} α β _inst_1 _inst_2)}, (Summable.{max u1 u2, u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) γ (ContinuousMap.addCommMonoid.{u1, u2} α β _inst_1 _inst_2 _inst_5 _inst_6) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) f) -> (forall (x : α), Eq.{succ u2} β (tsum.{u2, u3} β _inst_5 _inst_2 γ (fun (i : γ) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (f i) x)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (tsum.{max u1 u2, u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.addCommMonoid.{u1, u2} α β _inst_1 _inst_2 _inst_5 _inst_6) (ContinuousMap.compactOpen.{u1, u2} α β _inst_1 _inst_2) γ (fun (i : γ) => f i)) x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : LocallyCompactSpace.{u3} α _inst_1] [_inst_4 : T2Space.{u2} β _inst_2] [_inst_5 : AddCommMonoid.{u2} β] [_inst_6 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_5)))] {γ : Type.{u1}} {f : γ -> (ContinuousMap.{u3, u2} α β _inst_1 _inst_2)}, (Summable.{max u3 u2, u1} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) γ (ContinuousMap.instAddCommMonoidContinuousMap.{u3, u2} α β _inst_1 _inst_2 _inst_5 _inst_6) (ContinuousMap.compactOpen.{u3, u2} α β _inst_1 _inst_2) f) -> (forall (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (tsum.{u2, u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_5 _inst_2 γ (fun (i : γ) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} α β _inst_1 _inst_2)) (f i) x)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u3 u2, u3, u2} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u3, u2} α β _inst_1 _inst_2)) (tsum.{max u3 u2, u1} (ContinuousMap.{u3, u2} α β _inst_1 _inst_2) (ContinuousMap.instAddCommMonoidContinuousMap.{u3, u2} α β _inst_1 _inst_2 _inst_5 _inst_6) (ContinuousMap.compactOpen.{u3, u2} α β _inst_1 _inst_2) γ (fun (i : γ) => f i)) x))
Case conversion may be inaccurate. Consider using '#align continuous_map.tsum_apply ContinuousMap.tsum_applyₓ'. -/
theorem tsum_apply [LocallyCompactSpace α] [T2Space β] [AddCommMonoid β] [ContinuousAdd β]
    {γ : Type _} {f : γ → C(α, β)} (hf : Summable f) (x : α) :
    (∑' i : γ, f i x) = (∑' i : γ, f i) x :=
  (hasSum_apply hf.HasSum x).tsum_eq
#align continuous_map.tsum_apply ContinuousMap.tsum_apply

end ContinuousMap

end GroupStructure

section RingStructure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological semiring `R` inherit
the structure of a ring.
-/


section Subtype

#print continuousSubsemiring /-
/-- The subsemiring of continuous maps `α → β`. -/
def continuousSubsemiring (α : Type _) (R : Type _) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [TopologicalSemiring R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }
#align continuous_subsemiring continuousSubsemiring
-/

#print continuousSubring /-
/-- The subring of continuous maps `α → β`. -/
def continuousSubring (α : Type _) (R : Type _) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
    [TopologicalRing R] : Subring (α → R) :=
  { continuousSubsemiring α R, continuousAddSubgroup α R with }
#align continuous_subring continuousSubring
-/

end Subtype

namespace ContinuousMap

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocSemiring β] [TopologicalSemiring β] : NonUnitalNonAssocSemiring C(α, β) :=
  coe_injective.NonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalSemiring β]
    [TopologicalSemiring β] : NonUnitalSemiring C(α, β) :=
  coe_injective.NonUnitalSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [AddMonoidWithOne β]
    [ContinuousAdd β] : AddMonoidWithOne C(α, β) :=
  coe_injective.AddMonoidWithOne _ coe_zero coe_one coe_add coe_nsmul coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonAssocSemiring β]
    [TopologicalSemiring β] : NonAssocSemiring C(α, β) :=
  coe_injective.NonAssocSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [TopologicalSemiring β] : Semiring C(α, β) :=
  coe_injective.Semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocRing β] [TopologicalRing β] : NonUnitalNonAssocRing C(α, β) :=
  coe_injective.NonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalRing β]
    [TopologicalRing β] : NonUnitalRing C(α, β) :=
  coe_injective.NonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonAssocRing β]
    [TopologicalRing β] : NonAssocRing C(α, β) :=
  coe_injective.NonAssocRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_nat_cast coe_int_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
    [TopologicalRing β] : Ring C(α, β) :=
  coe_injective.Ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_nat_cast coe_int_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalCommSemiring β] [TopologicalSemiring β] : NonUnitalCommSemiring C(α, β) :=
  coe_injective.NonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommSemiring β]
    [TopologicalSemiring β] : CommSemiring C(α, β) :=
  coe_injective.CommSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalCommRing β]
    [TopologicalRing β] : NonUnitalCommRing C(α, β) :=
  coe_injective.NonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommRing β]
    [TopologicalRing β] : CommRing C(α, β) :=
  coe_injective.CommRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_pow coe_nat_cast coe_int_cast

/- warning: ring_hom.comp_left_continuous -> RingHom.compLeftContinuous is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Semiring.{u2} β] [_inst_4 : TopologicalSemiring.{u2} β _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_3))] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Semiring.{u3} γ] [_inst_7 : TopologicalSemiring.{u3} γ _inst_5 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_6))] (g : RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)), (Continuous.{u2, u3} β γ _inst_2 _inst_5 (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) (fun (_x : RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) => β -> γ) (RingHom.hasCoeToFun.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) g)) -> (RingHom.{max u1 u2, max u1 u3} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_5) (ContinuousMap.nonAssocSemiring.{u1, u2} α β _inst_1 _inst_2 (Semiring.toNonAssocSemiring.{u2} β _inst_3) _inst_4) (ContinuousMap.nonAssocSemiring.{u1, u3} α γ _inst_1 _inst_5 (Semiring.toNonAssocSemiring.{u3} γ _inst_6) _inst_7))
but is expected to have type
  forall (α : Type.{u1}) {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Semiring.{u2} β] [_inst_4 : TopologicalSemiring.{u2} β _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_3))] [_inst_5 : TopologicalSpace.{u3} γ] [_inst_6 : Semiring.{u3} γ] [_inst_7 : TopologicalSemiring.{u3} γ _inst_5 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_6))] (g : RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)), (Continuous.{u2, u3} β γ _inst_2 _inst_5 (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : β) => γ) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) β γ (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_3))) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_6))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_3)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6)) β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6) (RingHom.instRingHomClassRingHom.{u2, u3} β γ (Semiring.toNonAssocSemiring.{u2} β _inst_3) (Semiring.toNonAssocSemiring.{u3} γ _inst_6))))) g)) -> (RingHom.{max u2 u1, max u3 u1} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.{u1, u3} α γ _inst_1 _inst_5) (ContinuousMap.instNonAssocSemiringContinuousMap.{u1, u2} α β _inst_1 _inst_2 (Semiring.toNonAssocSemiring.{u2} β _inst_3) _inst_4) (ContinuousMap.instNonAssocSemiringContinuousMap.{u1, u3} α γ _inst_1 _inst_5 (Semiring.toNonAssocSemiring.{u3} γ _inst_6) _inst_7))
Case conversion may be inaccurate. Consider using '#align ring_hom.comp_left_continuous RingHom.compLeftContinuousₓ'. -/
/-- Composition on the left by a (continuous) homomorphism of topological semirings, as a
`ring_hom`.  Similar to `ring_hom.comp_left`. -/
@[simps]
protected def RingHom.compLeftContinuous (α : Type _) {β : Type _} {γ : Type _} [TopologicalSpace α]
    [TopologicalSpace β] [Semiring β] [TopologicalSemiring β] [TopologicalSpace γ] [Semiring γ]
    [TopologicalSemiring γ] (g : β →+* γ) (hg : Continuous g) : C(α, β) →+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }
#align ring_hom.comp_left_continuous RingHom.compLeftContinuous

/- warning: continuous_map.coe_fn_ring_hom -> ContinuousMap.coeFnRingHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Semiring.{u2} β] [_inst_4 : TopologicalSemiring.{u2} β _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_3))], RingHom.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (ContinuousMap.nonAssocSemiring.{u1, u2} α β _inst_1 _inst_2 (Semiring.toNonAssocSemiring.{u2} β _inst_3) _inst_4) (Pi.nonAssocSemiring.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} β _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Semiring.{u2} β] [_inst_4 : TopologicalSemiring.{u2} β _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_3))], RingHom.{max u2 u1, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (α -> β) (ContinuousMap.instNonAssocSemiringContinuousMap.{u1, u2} α β _inst_1 _inst_2 (Semiring.toNonAssocSemiring.{u2} β _inst_3) _inst_4) (Pi.nonAssocSemiring.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} β _inst_3))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_fn_ring_hom ContinuousMap.coeFnRingHomₓ'. -/
/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coeFnRingHom {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [TopologicalSemiring β] : C(α, β) →+* α → β :=
  { (coeFnMonoidHom : C(α, β) →* _), (coeFnAddMonoidHom : C(α, β) →+ _) with toFun := coeFn }
#align continuous_map.coe_fn_ring_hom ContinuousMap.coeFnRingHom

end ContinuousMap

end RingStructure

attribute [local ext] Subtype.eq

section ModuleStructure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/


section Subtype

variable (α : Type _) [TopologicalSpace α]

variable (R : Type _) [Semiring R]

variable (M : Type _) [TopologicalSpace M] [AddCommGroup M]

variable [Module R M] [ContinuousConstSMul R M] [TopologicalAddGroup M]

#print continuousSubmodule /-
/-- The `R`-submodule of continuous maps `α → M`. -/
def continuousSubmodule : Submodule R (α → M) :=
  {
    continuousAddSubgroup α
      M with
    carrier := { f : α → M | Continuous f }
    smul_mem' := fun c f hf => hf.const_smul c }
#align continuous_submodule continuousSubmodule
-/

end Subtype

namespace ContinuousMap

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {R R₁ : Type _} {M : Type _}
  [TopologicalSpace M] {M₂ : Type _} [TopologicalSpace M₂]

@[to_additive ContinuousMap.instVAdd]
instance [SMul R M] [ContinuousConstSMul R M] : SMul R C(α, M) :=
  ⟨fun r f => ⟨r • f, f.Continuous.const_smul r⟩⟩

@[to_additive]
instance [LocallyCompactSpace α] [SMul R M] [ContinuousConstSMul R M] :
    ContinuousConstSMul R C(α, M) :=
  ⟨fun γ => continuous_of_continuous_uncurry _ (continuous_eval'.const_smul γ)⟩

@[to_additive]
instance [LocallyCompactSpace α] [TopologicalSpace R] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul R C(α, M) :=
  ⟨by
    refine' continuous_of_continuous_uncurry _ _
    have h : Continuous fun x : (R × C(α, M)) × α => x.fst.snd x.snd :=
      continuous_eval'.comp (continuous_snd.prod_map continuous_id)
    exact (continuous_fst.comp continuous_fst).smul h⟩

/- warning: continuous_map.coe_smul -> ContinuousMap.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : SMul.{u2, u3} R M] [_inst_6 : ContinuousConstSMul.{u2, u3} R M _inst_3 _inst_5] (c : R) (f : ContinuousMap.{u1, u3} α M _inst_1 _inst_3), Eq.{succ (max u1 u3)} (α -> M) (coeFn.{succ (max u1 u3), succ (max u1 u3)} (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (fun (_x : ContinuousMap.{u1, u3} α M _inst_1 _inst_3) => α -> M) (ContinuousMap.hasCoeToFun.{u1, u3} α M _inst_1 _inst_3) (SMul.smul.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (ContinuousMap.instSMul.{u1, u2, u3} α _inst_1 R M _inst_3 _inst_5 _inst_6) c f)) (SMul.smul.{u2, max u1 u3} R (α -> M) (Function.hasSMul.{u1, u2, u3} α R M _inst_5) c (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (fun (_x : ContinuousMap.{u1, u3} α M _inst_1 _inst_3) => α -> M) (ContinuousMap.hasCoeToFun.{u1, u3} α M _inst_1 _inst_3) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u3}} {M : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} M] [_inst_5 : SMul.{u3, u2} R M] [_inst_6 : ContinuousConstSMul.{u3, u2} R M _inst_3 _inst_5] (c : R) (f : ContinuousMap.{u1, u2} α M _inst_1 _inst_3), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α M _inst_1 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α M _inst_1 _inst_3)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} R (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (instHSMul.{u3, max u1 u2} R (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (ContinuousMap.instSMul.{u1, u3, u2} α _inst_1 R M _inst_3 _inst_5 _inst_6)) c f)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} R (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) ᾰ) (instHSMul.{u3, max u1 u2} R (forall (a : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) (Pi.instSMul.{u1, u2, u3} α R (fun (a : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) (fun (i : α) => _inst_5))) c (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α M _inst_1 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α M _inst_1 _inst_3)) f))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_smul ContinuousMap.coe_smulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_smul [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) : ⇑(c • f) = c • f :=
  rfl
#align continuous_map.coe_smul ContinuousMap.coe_smul
#align continuous_map.coe_vadd ContinuousMap.coe_vadd

/- warning: continuous_map.smul_apply -> ContinuousMap.smul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : SMul.{u2, u3} R M] [_inst_6 : ContinuousConstSMul.{u2, u3} R M _inst_3 _inst_5] (c : R) (f : ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (a : α), Eq.{succ u3} M (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (fun (_x : ContinuousMap.{u1, u3} α M _inst_1 _inst_3) => α -> M) (ContinuousMap.hasCoeToFun.{u1, u3} α M _inst_1 _inst_3) (SMul.smul.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (ContinuousMap.instSMul.{u1, u2, u3} α _inst_1 R M _inst_3 _inst_5 _inst_6) c f) a) (SMul.smul.{u2, u3} R M _inst_5 c (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (fun (_x : ContinuousMap.{u1, u3} α M _inst_1 _inst_3) => α -> M) (ContinuousMap.hasCoeToFun.{u1, u3} α M _inst_1 _inst_3) f a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u3}} {M : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} M] [_inst_5 : SMul.{u3, u2} R M] [_inst_6 : ContinuousConstSMul.{u3, u2} R M _inst_3 _inst_5] (c : R) (f : ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α M _inst_1 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α M _inst_1 _inst_3)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} R (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (instHSMul.{u3, max u1 u2} R (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) (ContinuousMap.instSMul.{u1, u3, u2} α _inst_1 R M _inst_3 _inst_5 _inst_6)) c f) a) (HSMul.hSMul.{u3, u2, u2} R ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) (instHSMul.{u3, u2} R ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) a) _inst_5) c (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => M) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u1, u2} (ContinuousMap.{u1, u2} α M _inst_1 _inst_3) α M _inst_1 _inst_3 (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u2} α M _inst_1 _inst_3)) f a))
Case conversion may be inaccurate. Consider using '#align continuous_map.smul_apply ContinuousMap.smul_applyₓ'. -/
@[to_additive]
theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
    (c • f) a = c • f a :=
  rfl
#align continuous_map.smul_apply ContinuousMap.smul_apply
#align continuous_map.vadd_apply ContinuousMap.vadd_apply

/- warning: continuous_map.smul_comp -> ContinuousMap.smul_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {R : Type.{u3}} {M : Type.{u4}} [_inst_3 : TopologicalSpace.{u4} M] [_inst_5 : SMul.{u3, u4} R M] [_inst_6 : ContinuousConstSMul.{u3, u4} R M _inst_3 _inst_5] (r : R) (f : ContinuousMap.{u2, u4} β M _inst_2 _inst_3) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (ContinuousMap.{u1, u4} α M _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u4} α β M _inst_1 _inst_2 _inst_3 (SMul.smul.{u3, max u2 u4} R (ContinuousMap.{u2, u4} β M _inst_2 _inst_3) (ContinuousMap.instSMul.{u2, u3, u4} β _inst_2 R M _inst_3 _inst_5 _inst_6) r f) g) (SMul.smul.{u3, max u1 u4} R (ContinuousMap.{u1, u4} α M _inst_1 _inst_3) (ContinuousMap.instSMul.{u1, u3, u4} α _inst_1 R M _inst_3 _inst_5 _inst_6) r (ContinuousMap.comp.{u1, u2, u4} α β M _inst_1 _inst_2 _inst_3 f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {R : Type.{u4}} {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : SMul.{u4, u3} R M] [_inst_6 : ContinuousConstSMul.{u4, u3} R M _inst_3 _inst_5] (r : R) (f : ContinuousMap.{u2, u3} β M _inst_2 _inst_3) (g : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (ContinuousMap.comp.{u1, u2, u3} α β M _inst_1 _inst_2 _inst_3 (HSMul.hSMul.{u4, max u2 u3, max u2 u3} R (ContinuousMap.{u2, u3} β M _inst_2 _inst_3) (ContinuousMap.{u2, u3} β M _inst_2 _inst_3) (instHSMul.{u4, max u2 u3} R (ContinuousMap.{u2, u3} β M _inst_2 _inst_3) (ContinuousMap.instSMul.{u2, u4, u3} β _inst_2 R M _inst_3 _inst_5 _inst_6)) r f) g) (HSMul.hSMul.{u4, max u3 u1, max u1 u3} R (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (instHSMul.{u4, max u1 u3} R (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (ContinuousMap.instSMul.{u1, u4, u3} α _inst_1 R M _inst_3 _inst_5 _inst_6)) r (ContinuousMap.comp.{u1, u2, u3} α β M _inst_1 _inst_2 _inst_3 f g))
Case conversion may be inaccurate. Consider using '#align continuous_map.smul_comp ContinuousMap.smul_compₓ'. -/
@[simp, to_additive]
theorem smul_comp [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
    (r • f).comp g = r • f.comp g :=
  rfl
#align continuous_map.smul_comp ContinuousMap.smul_comp
#align continuous_map.vadd_comp ContinuousMap.vadd_comp

@[to_additive]
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
    [SMulCommClass R R₁ M] : SMulCommClass R R₁ C(α, M)
    where smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
    [IsScalarTower R R₁ M] : IsScalarTower R R₁ C(α, M)
    where smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
    IsCentralScalar R C(α, M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance [Monoid R] [MulAction R M] [ContinuousConstSMul R M] : MulAction R C(α, M) :=
  Function.Injective.mulAction _ coe_injective coe_smul

instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [ContinuousAdd M]
    [ContinuousConstSMul R M] : DistribMulAction R C(α, M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [ContinuousAdd M] [Module R M] [ContinuousConstSMul R M]

variable [ContinuousAdd M₂] [Module R M₂] [ContinuousConstSMul R M₂]

/- warning: continuous_map.module -> ContinuousMap.module is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : Semiring.{u2} R] [_inst_6 : AddCommMonoid.{u3} M] [_inst_8 : ContinuousAdd.{u3} M _inst_3 (AddZeroClass.toHasAdd.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)))] [_inst_9 : Module.{u2, u3} R M _inst_5 _inst_6] [_inst_10 : ContinuousConstSMul.{u2, u3} R M _inst_3 (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_5)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_5) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (Module.toMulActionWithZero.{u2, u3} R M _inst_5 _inst_6 _inst_9))))], Module.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) _inst_5 (ContinuousMap.addCommMonoid.{u1, u3} α M _inst_1 _inst_3 _inst_6 _inst_8)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : Semiring.{u2} R] [_inst_6 : AddCommMonoid.{u3} M] [_inst_8 : ContinuousAdd.{u3} M _inst_3 (AddZeroClass.toAdd.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)))] [_inst_9 : Module.{u2, u3} R M _inst_5 _inst_6] [_inst_10 : ContinuousConstSMul.{u2, u3} R M _inst_3 (SMulZeroClass.toSMul.{u2, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u2, u3} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_5)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_5) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (Module.toMulActionWithZero.{u2, u3} R M _inst_5 _inst_6 _inst_9))))], Module.{u2, max u3 u1} R (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) _inst_5 (ContinuousMap.instAddCommMonoidContinuousMap.{u1, u3} α M _inst_1 _inst_3 _inst_6 _inst_8)
Case conversion may be inaccurate. Consider using '#align continuous_map.module ContinuousMap.moduleₓ'. -/
instance module : Module R C(α, M) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul
#align continuous_map.module ContinuousMap.module

variable (R)

/- warning: continuous_linear_map.comp_left_continuous -> ContinuousLinearMap.compLeftContinuous is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} M] {M₂ : Type.{u3}} [_inst_4 : TopologicalSpace.{u3} M₂] [_inst_5 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_7 : AddCommMonoid.{u3} M₂] [_inst_8 : ContinuousAdd.{u2} M _inst_3 (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)))] [_inst_9 : Module.{u1, u2} R M _inst_5 _inst_6] [_inst_10 : ContinuousConstSMul.{u1, u2} R M _inst_3 (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_5)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_5) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6))) (Module.toMulActionWithZero.{u1, u2} R M _inst_5 _inst_6 _inst_9))))] [_inst_11 : ContinuousAdd.{u3} M₂ _inst_4 (AddZeroClass.toHasAdd.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7)))] [_inst_12 : Module.{u1, u3} R M₂ _inst_5 _inst_7] [_inst_13 : ContinuousConstSMul.{u1, u3} R M₂ _inst_4 (SMulZeroClass.toHasSmul.{u1, u3} R M₂ (AddZeroClass.toHasZero.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7))) (SMulWithZero.toSmulZeroClass.{u1, u3} R M₂ (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_5)))) (AddZeroClass.toHasZero.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7))) (MulActionWithZero.toSMulWithZero.{u1, u3} R M₂ (Semiring.toMonoidWithZero.{u1} R _inst_5) (AddZeroClass.toHasZero.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7))) (Module.toMulActionWithZero.{u1, u3} R M₂ _inst_5 _inst_7 _inst_12))))] (α : Type.{u4}) [_inst_14 : TopologicalSpace.{u4} α], (ContinuousLinearMap.{u1, u1, u2, u3} R R _inst_5 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)) M _inst_3 _inst_6 M₂ _inst_4 _inst_7 _inst_9 _inst_12) -> (LinearMap.{u1, u1, max u4 u2, max u4 u3} R R _inst_5 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)) (ContinuousMap.{u4, u2} α M _inst_14 _inst_3) (ContinuousMap.{u4, u3} α M₂ _inst_14 _inst_4) (ContinuousMap.addCommMonoid.{u4, u2} α M _inst_14 _inst_3 _inst_6 _inst_8) (ContinuousMap.addCommMonoid.{u4, u3} α M₂ _inst_14 _inst_4 _inst_7 _inst_11) (ContinuousMap.module.{u4, u1, u2} α _inst_14 R M _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 _inst_10) (ContinuousMap.module.{u4, u1, u3} α _inst_14 R M₂ _inst_4 _inst_5 _inst_7 _inst_11 _inst_12 _inst_13))
but is expected to have type
  forall (R : Type.{u1}) {M : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} M] {M₂ : Type.{u3}} [_inst_4 : TopologicalSpace.{u3} M₂] [_inst_5 : Semiring.{u1} R] [_inst_6 : AddCommMonoid.{u2} M] [_inst_7 : AddCommMonoid.{u3} M₂] [_inst_8 : ContinuousAdd.{u2} M _inst_3 (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)))] [_inst_9 : Module.{u1, u2} R M _inst_5 _inst_6] [_inst_10 : ContinuousConstSMul.{u1, u2} R M _inst_3 (SMulZeroClass.toSMul.{u1, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_5)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_5) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_6)) (Module.toMulActionWithZero.{u1, u2} R M _inst_5 _inst_6 _inst_9))))] [_inst_11 : ContinuousAdd.{u3} M₂ _inst_4 (AddZeroClass.toAdd.{u3} M₂ (AddMonoid.toAddZeroClass.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7)))] [_inst_12 : Module.{u1, u3} R M₂ _inst_5 _inst_7] [_inst_13 : ContinuousConstSMul.{u1, u3} R M₂ _inst_4 (SMulZeroClass.toSMul.{u1, u3} R M₂ (AddMonoid.toZero.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7)) (SMulWithZero.toSMulZeroClass.{u1, u3} R M₂ (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_5)) (AddMonoid.toZero.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7)) (MulActionWithZero.toSMulWithZero.{u1, u3} R M₂ (Semiring.toMonoidWithZero.{u1} R _inst_5) (AddMonoid.toZero.{u3} M₂ (AddCommMonoid.toAddMonoid.{u3} M₂ _inst_7)) (Module.toMulActionWithZero.{u1, u3} R M₂ _inst_5 _inst_7 _inst_12))))] (α : Type.{u4}) [_inst_14 : TopologicalSpace.{u4} α], (ContinuousLinearMap.{u1, u1, u2, u3} R R _inst_5 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)) M _inst_3 _inst_6 M₂ _inst_4 _inst_7 _inst_9 _inst_12) -> (LinearMap.{u1, u1, max u2 u4, max u3 u4} R R _inst_5 _inst_5 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_5)) (ContinuousMap.{u4, u2} α M _inst_14 _inst_3) (ContinuousMap.{u4, u3} α M₂ _inst_14 _inst_4) (ContinuousMap.instAddCommMonoidContinuousMap.{u4, u2} α M _inst_14 _inst_3 _inst_6 _inst_8) (ContinuousMap.instAddCommMonoidContinuousMap.{u4, u3} α M₂ _inst_14 _inst_4 _inst_7 _inst_11) (ContinuousMap.module.{u4, u1, u2} α _inst_14 R M _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 _inst_10) (ContinuousMap.module.{u4, u1, u3} α _inst_14 R M₂ _inst_4 _inst_5 _inst_7 _inst_11 _inst_12 _inst_13))
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.comp_left_continuous ContinuousLinearMap.compLeftContinuousₓ'. -/
/-- Composition on the left by a continuous linear map, as a `linear_map`.
Similar to `linear_map.comp_left`. -/
@[simps]
protected def ContinuousLinearMap.compLeftContinuous (α : Type _) [TopologicalSpace α]
    (g : M →L[R] M₂) : C(α, M) →ₗ[R] C(α, M₂) :=
  { g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.Continuous with
    map_smul' := fun c f => ext fun x => g.map_smul' c _ }
#align continuous_linear_map.comp_left_continuous ContinuousLinearMap.compLeftContinuous

/- warning: continuous_map.coe_fn_linear_map -> ContinuousMap.coeFnLinearMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : Semiring.{u2} R] [_inst_6 : AddCommMonoid.{u3} M] [_inst_8 : ContinuousAdd.{u3} M _inst_3 (AddZeroClass.toHasAdd.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)))] [_inst_9 : Module.{u2, u3} R M _inst_5 _inst_6] [_inst_10 : ContinuousConstSMul.{u2, u3} R M _inst_3 (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_5)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_5) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (Module.toMulActionWithZero.{u2, u3} R M _inst_5 _inst_6 _inst_9))))], LinearMap.{u2, u2, max u1 u3, max u1 u3} R R _inst_5 _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_5)) (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (α -> M) (ContinuousMap.addCommMonoid.{u1, u3} α M _inst_1 _inst_3 _inst_6 _inst_8) (Pi.addCommMonoid.{u1, u3} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_6)) (ContinuousMap.module.{u1, u2, u3} α _inst_1 R M _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 _inst_10) (Pi.Function.module.{u1, u2, u3} α R M _inst_5 _inst_6 _inst_9)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) {M : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} M] [_inst_5 : Semiring.{u2} R] [_inst_6 : AddCommMonoid.{u3} M] [_inst_8 : ContinuousAdd.{u3} M _inst_3 (AddZeroClass.toAdd.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)))] [_inst_9 : Module.{u2, u3} R M _inst_5 _inst_6] [_inst_10 : ContinuousConstSMul.{u2, u3} R M _inst_3 (SMulZeroClass.toSMul.{u2, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u2, u3} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_5)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_5) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (Module.toMulActionWithZero.{u2, u3} R M _inst_5 _inst_6 _inst_9))))], LinearMap.{u2, u2, max u3 u1, max u1 u3} R R _inst_5 _inst_5 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_5)) (ContinuousMap.{u1, u3} α M _inst_1 _inst_3) (α -> M) (ContinuousMap.instAddCommMonoidContinuousMap.{u1, u3} α M _inst_1 _inst_3 _inst_6 _inst_8) (Pi.addCommMonoid.{u1, u3} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_6)) (ContinuousMap.module.{u1, u2, u3} α _inst_1 R M _inst_3 _inst_5 _inst_6 _inst_8 _inst_9 _inst_10) (Pi.module.{u1, u3, u2} α (fun (a._@.Mathlib.Topology.ContinuousFunction.Algebra._hyg.4968 : α) => M) R _inst_5 (fun (i : α) => _inst_6) (fun (i : α) => _inst_9))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_fn_linear_map ContinuousMap.coeFnLinearMapₓ'. -/
/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coeFnLinearMap : C(α, M) →ₗ[R] α → M :=
  { (coeFnAddMonoidHom : C(α, M) →+ _) with
    toFun := coeFn
    map_smul' := coe_smul }
#align continuous_map.coe_fn_linear_map ContinuousMap.coeFnLinearMap

end ContinuousMap

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `has_continuous_smul` and a `topological_semiring`.-/


section Subtype

variable {α : Type _} [TopologicalSpace α] {R : Type _} [CommSemiring R] {A : Type _}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [TopologicalSemiring A]

#print continuousSubalgebra /-
/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuousSubalgebra : Subalgebra R (α → A) :=
  {
    continuousSubsemiring α
      A with
    carrier := { f : α → A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun x : α => algebraMap R A r) }
#align continuous_subalgebra continuousSubalgebra
-/

end Subtype

section ContinuousMap

variable {α : Type _} [TopologicalSpace α] {R : Type _} [CommSemiring R] {A : Type _}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [TopologicalSemiring A] {A₂ : Type _}
  [TopologicalSpace A₂] [Semiring A₂] [Algebra R A₂] [TopologicalSemiring A₂]

/- warning: continuous_map.C -> ContinuousMap.C is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], RingHom.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)) (ContinuousMap.nonAssocSemiring.{u1, u3} α A _inst_1 _inst_3 (Semiring.toNonAssocSemiring.{u3} A _inst_4) _inst_6)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], RingHom.{u2, max u3 u1} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)) (ContinuousMap.instNonAssocSemiringContinuousMap.{u1, u3} α A _inst_1 _inst_3 (Semiring.toNonAssocSemiring.{u3} A _inst_4) _inst_6)
Case conversion may be inaccurate. Consider using '#align continuous_map.C ContinuousMap.Cₓ'. -/
/-- Continuous constant functions as a `ring_hom`. -/
def ContinuousMap.C : R →+* C(α, A)
    where
  toFun := fun c : R => ⟨fun x : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext x <;> exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext x <;> exact (algebraMap R A).map_mul _ _
  map_zero' := by ext x <;> exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext x <;> exact (algebraMap R A).map_add _ _
#align continuous_map.C ContinuousMap.C

/- warning: continuous_map.C_apply -> ContinuousMap.C_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_map.C_apply ContinuousMap.C_applyₓ'. -/
@[simp]
theorem ContinuousMap.C_apply (r : R) (a : α) : ContinuousMap.C r a = algebraMap R A r :=
  rfl
#align continuous_map.C_apply ContinuousMap.C_apply

/- warning: continuous_map.algebra -> ContinuousMap.algebra is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], Algebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], Algebra.{u2, max u3 u1} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6)
Case conversion may be inaccurate. Consider using '#align continuous_map.algebra ContinuousMap.algebraₓ'. -/
instance ContinuousMap.algebra : Algebra R C(α, A)
    where
  toRingHom := ContinuousMap.C
  commutes' c f := by ext x <;> exact Algebra.commutes' _ _
  smul_def' c f := by ext x <;> exact Algebra.smul_def' _ _
#align continuous_map.algebra ContinuousMap.algebra

variable (R)

#print AlgHom.compLeftContinuous /-
/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`alg_hom`. Similar to `alg_hom.comp_left`. -/
@[simps]
protected def AlgHom.compLeftContinuous {α : Type _} [TopologicalSpace α] (g : A →ₐ[R] A₂)
    (hg : Continuous g) : C(α, A) →ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun c => ContinuousMap.ext fun _ => g.commutes' _ }
#align alg_hom.comp_left_continuous AlgHom.compLeftContinuous
-/

variable (A)

/- warning: continuous_map.comp_right_alg_hom -> ContinuousMap.compRightAlgHom is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_2 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_3 : TopologicalSpace.{u2} A] [_inst_4 : Semiring.{u2} A] [_inst_5 : Algebra.{u1, u2} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u2} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))] {α : Type.{u3}} {β : Type.{u4}} [_inst_11 : TopologicalSpace.{u3} α] [_inst_12 : TopologicalSpace.{u4} β], (ContinuousMap.{u3, u4} α β _inst_11 _inst_12) -> (AlgHom.{u1, max u4 u2, max u3 u2} R (ContinuousMap.{u4, u2} β A _inst_12 _inst_3) (ContinuousMap.{u3, u2} α A _inst_11 _inst_3) _inst_2 (ContinuousMap.semiring.{u4, u2} β A _inst_12 _inst_3 _inst_4 _inst_6) (ContinuousMap.semiring.{u3, u2} α A _inst_11 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u4, u1, u2} β _inst_12 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_11 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6))
but is expected to have type
  forall (R : Type.{u1}) [_inst_2 : CommSemiring.{u1} R] (A : Type.{u2}) [_inst_3 : TopologicalSpace.{u2} A] [_inst_4 : Semiring.{u2} A] [_inst_5 : Algebra.{u1, u2} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u2} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))] {α : Type.{u3}} {β : Type.{u4}} [_inst_11 : TopologicalSpace.{u3} α] [_inst_12 : TopologicalSpace.{u4} β], (ContinuousMap.{u3, u4} α β _inst_11 _inst_12) -> (AlgHom.{u1, max u2 u4, max u2 u3} R (ContinuousMap.{u4, u2} β A _inst_12 _inst_3) (ContinuousMap.{u3, u2} α A _inst_11 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u4, u2} β A _inst_12 _inst_3 _inst_4 _inst_6) (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_11 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u4, u1, u2} β _inst_12 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_11 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_right_alg_hom ContinuousMap.compRightAlgHomₓ'. -/
/-- Precomposition of functions into a normed ring by a continuous map is an algebra homomorphism.
-/
@[simps]
def ContinuousMap.compRightAlgHom {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : C(α, β)) : C(β, A) →ₐ[R] C(α, A)
    where
  toFun g := g.comp f
  map_zero' := by
    ext
    rfl
  map_add' g₁ g₂ := by
    ext
    rfl
  map_one' := by
    ext
    rfl
  map_mul' g₁ g₂ := by
    ext
    rfl
  commutes' r := by
    ext
    rfl
#align continuous_map.comp_right_alg_hom ContinuousMap.compRightAlgHom

variable {A}

/- warning: continuous_map.coe_fn_alg_hom -> ContinuousMap.coeFnAlgHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], AlgHom.{u2, max u1 u3, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) (α -> A) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (Pi.semiring.{u1, u3} α (fun (ᾰ : α) => A) (fun (i : α) => _inst_4)) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6) (Function.algebra.{u2, u1, u3} R α A _inst_2 _inst_4 _inst_5)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], AlgHom.{u2, max u3 u1, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) (α -> A) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (Pi.semiring.{u1, u3} α (fun (ᾰ : α) => A) (fun (i : α) => _inst_4)) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6) (Pi.algebra.{u1, u3, u2} α R (fun (a._@.Mathlib.Topology.ContinuousFunction.Algebra._hyg.5862 : α) => A) _inst_2 (fun (i : α) => _inst_4) (fun (i : α) => _inst_5))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_fn_alg_hom ContinuousMap.coeFnAlgHomₓ'. -/
/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def ContinuousMap.coeFnAlgHom : C(α, A) →ₐ[R] α → A :=
  {
    (ContinuousMap.coeFnRingHom :
      C(α, A) →+* _) with
    toFun := coeFn
    commutes' := fun r => rfl }
#align continuous_map.coe_fn_alg_hom ContinuousMap.coeFnAlgHom

variable {R}

/- warning: subalgebra.separates_points -> Subalgebra.SeparatesPoints is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], (Subalgebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) -> Prop
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], (Subalgebra.{u2, max u3 u1} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) -> Prop
Case conversion may be inaccurate. Consider using '#align subalgebra.separates_points Subalgebra.SeparatesPointsₓ'. -/
/-- A version of `separates_points` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbrev Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop :=
  Set.SeparatesPoints ((fun f : C(α, A) => (f : α → A)) '' (s : Set C(α, A)))
#align subalgebra.separates_points Subalgebra.SeparatesPoints

/- warning: subalgebra.separates_points_monotone -> Subalgebra.separatesPoints_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] {A : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} A] [_inst_4 : Semiring.{u3} A] [_inst_5 : Algebra.{u2, u3} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u3} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_4))], Monotone.{max u1 u3, 0} (Subalgebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) Prop (PartialOrder.toPreorder.{max u1 u3} (Subalgebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u3} (Subalgebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u3} (Subalgebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) (Algebra.Subalgebra.completeLattice.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (s : Subalgebra.{u2, max u1 u3} R (ContinuousMap.{u1, u3} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u3} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) => Subalgebra.SeparatesPoints.{u1, u2, u3} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6 s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {R : Type.{u1}} [_inst_2 : CommSemiring.{u1} R] {A : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} A] [_inst_4 : Semiring.{u2} A] [_inst_5 : Algebra.{u1, u2} R A _inst_2 _inst_4] [_inst_6 : TopologicalSemiring.{u2} A _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_4))], Monotone.{max u3 u2, 0} (Subalgebra.{u1, max u2 u3} R (ContinuousMap.{u3, u2} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) Prop (PartialOrder.toPreorder.{max u3 u2} (Subalgebra.{u1, max u2 u3} R (ContinuousMap.{u3, u2} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) (OmegaCompletePartialOrder.toPartialOrder.{max u3 u2} (Subalgebra.{u1, max u2 u3} R (ContinuousMap.{u3, u2} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) (CompleteLattice.instOmegaCompletePartialOrder.{max u3 u2} (Subalgebra.{u1, max u2 u3} R (ContinuousMap.{u3, u2} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) (Algebra.instCompleteLatticeSubalgebra.{u1, max u3 u2} R (ContinuousMap.{u3, u2} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (s : Subalgebra.{u1, max u2 u3} R (ContinuousMap.{u3, u2} α A _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u3, u2} α A _inst_1 _inst_3 _inst_4 _inst_6) (ContinuousMap.algebra.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6)) => Subalgebra.SeparatesPoints.{u3, u1, u2} α _inst_1 R _inst_2 A _inst_3 _inst_4 _inst_5 _inst_6 s)
Case conversion may be inaccurate. Consider using '#align subalgebra.separates_points_monotone Subalgebra.separatesPoints_monotoneₓ'. -/
theorem Subalgebra.separatesPoints_monotone :
    Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints := fun s s' r h x y n =>
  by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩
#align subalgebra.separates_points_monotone Subalgebra.separatesPoints_monotone

/- warning: algebra_map_apply -> algebraMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra_map_apply algebraMap_applyₓ'. -/
@[simp]
theorem algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • 1 :=
  by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl
#align algebra_map_apply algebraMap_apply

variable {𝕜 : Type _} [TopologicalSpace 𝕜]

#print Set.SeparatesPointsStrongly /-
/-- A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on them.

We give a slightly unusual formulation, where the specified values are given by some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothesis `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous functions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
def Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop :=
  ∀ (v : α → 𝕜) (x y : α), ∃ f ∈ s, (f x : 𝕜) = v x ∧ f y = v y
#align set.separates_points_strongly Set.SeparatesPointsStrongly
-/

variable [Field 𝕜] [TopologicalRing 𝕜]

/- warning: subalgebra.separates_points.strongly -> Subalgebra.SeparatesPoints.strongly is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align subalgebra.separates_points.strongly Subalgebra.SeparatesPoints.stronglyₓ'. -/
/-- Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
theorem Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) :
    (s : Set C(α, 𝕜)).SeparatesPointsStrongly := fun v x y =>
  by
  by_cases n : x = y
  · subst n
    refine' ⟨_, (v x • 1 : s).Prop, mul_one _, mul_one _⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hxy⟩ := h n
  replace hxy : f x - f y ≠ 0 := sub_ne_zero_of_ne hxy
  let a := v x
  let b := v y
  let f' : s := ((b - a) * (f x - f y)⁻¹) • (algebraMap _ _ (f x) - ⟨f, hf⟩) + algebraMap _ _ a
  refine' ⟨f', f'.prop, _, _⟩
  · simp [f']
  · simp [f', inv_mul_cancel_right₀ hxy]
#align subalgebra.separates_points.strongly Subalgebra.SeparatesPoints.strongly

end ContinuousMap

/- warning: continuous_map.subsingleton_subalgebra -> ContinuousMap.subsingleton_subalgebra is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) [_inst_2 : CommSemiring.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : TopologicalSemiring.{u2} R _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))] [_inst_5 : Subsingleton.{succ u1} α], Subsingleton.{succ (max u1 u2)} (Subalgebra.{u2, max u1 u2} R (ContinuousMap.{u1, u2} α R _inst_1 _inst_3) _inst_2 (ContinuousMap.semiring.{u1, u2} α R _inst_1 _inst_3 (CommSemiring.toSemiring.{u2} R _inst_2) _inst_4) (ContinuousMap.algebra.{u1, u2, u2} α _inst_1 R _inst_2 R _inst_3 (CommSemiring.toSemiring.{u2} R _inst_2) (Algebra.id.{u2} R _inst_2) _inst_4))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) [_inst_2 : CommSemiring.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : TopologicalSemiring.{u2} R _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))] [_inst_5 : Subsingleton.{succ u1} α], Subsingleton.{succ (max u2 u1)} (Subalgebra.{u2, max u2 u1} R (ContinuousMap.{u1, u2} α R _inst_1 _inst_3) _inst_2 (ContinuousMap.instSemiringContinuousMap.{u1, u2} α R _inst_1 _inst_3 (CommSemiring.toSemiring.{u2} R _inst_2) _inst_4) (ContinuousMap.algebra.{u1, u2, u2} α _inst_1 R _inst_2 R _inst_3 (CommSemiring.toSemiring.{u2} R _inst_2) (Algebra.id.{u2} R _inst_2) _inst_4))
Case conversion may be inaccurate. Consider using '#align continuous_map.subsingleton_subalgebra ContinuousMap.subsingleton_subalgebraₓ'. -/
instance ContinuousMap.subsingleton_subalgebra (α : Type _) [TopologicalSpace α] (R : Type _)
    [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R] [Subsingleton α] :
    Subsingleton (Subalgebra R C(α, R)) :=
  ⟨fun s₁ s₂ => by
    cases isEmpty_or_nonempty α
    · haveI : Subsingleton C(α, R) := fun_like.coe_injective.subsingleton
      exact Subsingleton.elim _ _
    · inhabit α
      ext f
      have h : f = algebraMap R C(α, R) (f default) :=
        by
        ext x'
        simp only [mul_one, Algebra.id.smul_eq_mul, algebraMap_apply]
        congr
      rw [h]
      simp only [Subalgebra.algebraMap_mem]⟩
#align continuous_map.subsingleton_subalgebra ContinuousMap.subsingleton_subalgebra

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/


namespace ContinuousMap

#print ContinuousMap.instSMul' /-
instance instSMul' {α : Type _} [TopologicalSpace α] {R : Type _} [Semiring R] [TopologicalSpace R]
    {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousSMul R M] :
    SMul C(α, R) C(α, M) :=
  ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩
#align continuous_map.has_smul' ContinuousMap.instSMul'
-/

/- warning: continuous_map.module' -> ContinuousMap.module' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) [_inst_2 : Semiring.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : TopologicalSemiring.{u2} R _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))] (M : Type.{u3}) [_inst_5 : TopologicalSpace.{u3} M] [_inst_6 : AddCommMonoid.{u3} M] [_inst_7 : ContinuousAdd.{u3} M _inst_5 (AddZeroClass.toHasAdd.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)))] [_inst_8 : Module.{u2, u3} R M _inst_2 _inst_6] [_inst_9 : ContinuousSMul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_2)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_2) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6))) (Module.toMulActionWithZero.{u2, u3} R M _inst_2 _inst_6 _inst_8)))) _inst_3 _inst_5], Module.{max u1 u2, max u1 u3} (ContinuousMap.{u1, u2} α R _inst_1 _inst_3) (ContinuousMap.{u1, u3} α M _inst_1 _inst_5) (ContinuousMap.semiring.{u1, u2} α R _inst_1 _inst_3 _inst_2 _inst_4) (ContinuousMap.addCommMonoid.{u1, u3} α M _inst_1 _inst_5 _inst_6 _inst_7)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] (R : Type.{u2}) [_inst_2 : Semiring.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_4 : TopologicalSemiring.{u2} R _inst_3 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))] (M : Type.{u3}) [_inst_5 : TopologicalSpace.{u3} M] [_inst_6 : AddCommMonoid.{u3} M] [_inst_7 : ContinuousAdd.{u3} M _inst_5 (AddZeroClass.toAdd.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)))] [_inst_8 : Module.{u2, u3} R M _inst_2 _inst_6] [_inst_9 : ContinuousSMul.{u2, u3} R M (SMulZeroClass.toSMul.{u2, u3} R M (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (SMulWithZero.toSMulZeroClass.{u2, u3} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_2)) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_2) (AddMonoid.toZero.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_6)) (Module.toMulActionWithZero.{u2, u3} R M _inst_2 _inst_6 _inst_8)))) _inst_3 _inst_5], Module.{max u2 u1, max u3 u1} (ContinuousMap.{u1, u2} α R _inst_1 _inst_3) (ContinuousMap.{u1, u3} α M _inst_1 _inst_5) (ContinuousMap.instSemiringContinuousMap.{u1, u2} α R _inst_1 _inst_3 _inst_2 _inst_4) (ContinuousMap.instAddCommMonoidContinuousMap.{u1, u3} α M _inst_1 _inst_5 _inst_6 _inst_7)
Case conversion may be inaccurate. Consider using '#align continuous_map.module' ContinuousMap.module'ₓ'. -/
instance module' {α : Type _} [TopologicalSpace α] (R : Type _) [Semiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (M : Type _) [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
    [Module R M] [ContinuousSMul R M] : Module C(α, R) C(α, M)
    where
  smul := (· • ·)
  smul_add c f g := by ext x <;> exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x <;> exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x <;> exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x <;> exact one_smul R (f x)
  zero_smul f := by ext x <;> exact zero_smul _ _
  smul_zero r := by ext x <;> exact smul_zero _
#align continuous_map.module' ContinuousMap.module'

end ContinuousMap

end ModuleOverContinuousFunctions

/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `continuous_map.abs`.
-/


section

variable {R : Type _} [LinearOrderedField R]

/- warning: min_eq_half_add_sub_abs_sub -> min_eq_half_add_sub_abs_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] {x : R} {y : R}, Eq.{succ u1} R (LinearOrder.min.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))) x y) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))) x y) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))))) (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (LinearOrder.toLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))))))) x y))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] {x : R} {y : R}, Eq.{succ u1} R (Min.min.{u1} R (LinearOrderedRing.toMin.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))) x y) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))) (Inv.inv.{u1} R (LinearOrderedField.toInv.{u1} R _inst_1) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (Semiring.toNatCast.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} R (LinearOrderedField.toLinearOrderedSemifield.{u1} R _inst_1)))))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))))) x y) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (Ring.toNeg.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))) (SemilatticeSup.toSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))) x y))))
Case conversion may be inaccurate. Consider using '#align min_eq_half_add_sub_abs_sub min_eq_half_add_sub_abs_subₓ'. -/
-- TODO:
-- This lemma (and the next) could go all the way back in `algebra.order.field`,
-- except that it is tedious to prove without tactics.
-- Rather than stranding it at some intermediate location,
-- it's here, immediately prior to the point of use.
theorem min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - |x - y|) := by
  cases' le_total x y with h h <;> field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two] <;> abel
#align min_eq_half_add_sub_abs_sub min_eq_half_add_sub_abs_sub

/- warning: max_eq_half_add_add_abs_sub -> max_eq_half_add_add_abs_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] {x : R} {y : R}, Eq.{succ u1} R (LinearOrder.max.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))) x y) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))) (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))) x y) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))))))) (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (LinearOrder.toLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))))))))) x y))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} R] {x : R} {y : R}, Eq.{succ u1} R (Max.max.{u1} R (LinearOrderedRing.toMax.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))) x y) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))) (Inv.inv.{u1} R (LinearOrderedField.toInv.{u1} R _inst_1) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (Semiring.toNatCast.{u1} R (StrictOrderedSemiring.toSemiring.{u1} R (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} R (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} R (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} R (LinearOrderedField.toLinearOrderedSemifield.{u1} R _inst_1)))))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))))) x y) (Abs.abs.{u1} R (Neg.toHasAbs.{u1} R (Ring.toNeg.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1))))) (SemilatticeSup.toSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R (LinearOrderedRing.toLinearOrder.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (StrictOrderedRing.toRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))))) x y))))
Case conversion may be inaccurate. Consider using '#align max_eq_half_add_add_abs_sub max_eq_half_add_add_abs_subₓ'. -/
theorem max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + |x - y|) := by
  cases' le_total x y with h h <;> field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two] <;> abel
#align max_eq_half_add_add_abs_sub max_eq_half_add_add_abs_sub

end

namespace ContinuousMap

section Lattice

variable {α : Type _} [TopologicalSpace α]

variable {β : Type _} [LinearOrderedField β] [TopologicalSpace β] [OrderTopology β]
  [TopologicalRing β]

/- warning: continuous_map.inf_eq -> ContinuousMap.inf_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_map.inf_eq ContinuousMap.inf_eqₓ'. -/
theorem inf_eq (f g : C(α, β)) : f ⊓ g = (2⁻¹ : β) • (f + g - |f - g|) :=
  ext fun x => by simpa using min_eq_half_add_sub_abs_sub
#align continuous_map.inf_eq ContinuousMap.inf_eq

/- warning: continuous_map.sup_eq -> ContinuousMap.sup_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_map.sup_eq ContinuousMap.sup_eqₓ'. -/
-- Not sure why this is grosser than `inf_eq`:
theorem sup_eq (f g : C(α, β)) : f ⊔ g = (2⁻¹ : β) • (f + g + |f - g|) :=
  ext fun x => by simpa [mul_add] using @max_eq_half_add_add_abs_sub _ _ (f x) (g x)
#align continuous_map.sup_eq ContinuousMap.sup_eq

end Lattice

/-!
### Star structure

If `β` has a continuous star operation, we put a star structure on `C(α, β)` by using the
star operation pointwise.

If `β` is a ⋆-ring, then `C(α, β)` inherits a ⋆-ring structure.

If `β` is a ⋆-ring and a ⋆-module over `R`, then the space of continuous functions from `α` to `β`
is a ⋆-module over `R`.

-/


section StarStructure

variable {R α β : Type _}

variable [TopologicalSpace α] [TopologicalSpace β]

section Star

variable [Star β] [ContinuousStar β]

instance : Star C(α, β) where unit f := starContinuousMap.comp f

/- warning: continuous_map.coe_star -> ContinuousMap.coe_star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Star.{u2} β] [_inst_4 : ContinuousStar.{u2} β _inst_2 _inst_3] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Star.star.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasStar.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f)) (Star.star.{max u1 u2} (α -> β) (Pi.hasStar.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Star.{u1} β] [_inst_4 : ContinuousStar.{u1} β _inst_2 _inst_3] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Star.star.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.instStarContinuousMap.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) f)) (Star.star.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (Pi.instStarForAll.{u2, u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) ᾰ) (fun (i : α) => _inst_3)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_star ContinuousMap.coe_starₓ'. -/
@[simp]
theorem coe_star (f : C(α, β)) : ⇑(star f) = star f :=
  rfl
#align continuous_map.coe_star ContinuousMap.coe_star

/- warning: continuous_map.star_apply -> ContinuousMap.star_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Star.{u2} β] [_inst_4 : ContinuousStar.{u2} β _inst_2 _inst_3] (f : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Star.star.{max u1 u2} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (ContinuousMap.hasStar.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4) f) x) (Star.star.{u2} β _inst_3 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} α β _inst_1 _inst_2) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Star.{u1} β] [_inst_4 : ContinuousStar.{u1} β _inst_2 _inst_3] (f : ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) (Star.star.{max u2 u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) (ContinuousMap.instStarContinuousMap.{u2, u1} α β _inst_1 _inst_2 _inst_3 _inst_4) f) x) (Star.star.{u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) x) _inst_3 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_1 _inst_2)) f x))
Case conversion may be inaccurate. Consider using '#align continuous_map.star_apply ContinuousMap.star_applyₓ'. -/
@[simp]
theorem star_apply (f : C(α, β)) (x : α) : star f x = star (f x) :=
  rfl
#align continuous_map.star_apply ContinuousMap.star_apply

end Star

instance [InvolutiveStar β] [ContinuousStar β] : InvolutiveStar C(α, β)
    where star_involutive f := ext fun x => star_star _

instance [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β] :
    StarAddMonoid C(α, β) where star_add f g := ext fun x => star_add _ _

instance [Semigroup β] [ContinuousMul β] [StarSemigroup β] [ContinuousStar β] :
    StarSemigroup C(α, β) where star_mul f g := ext fun x => star_mul _ _

instance [NonUnitalSemiring β] [TopologicalSemiring β] [StarRing β] [ContinuousStar β] :
    StarRing C(α, β) :=
  { ContinuousMap.starAddMonoid with }

instance [Star R] [Star β] [SMul R β] [StarModule R β] [ContinuousStar β]
    [ContinuousConstSMul R β] : StarModule R C(α, β)
    where star_smul k f := ext fun x => star_smul _ _

end StarStructure

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (𝕜 : Type _) [CommSemiring 𝕜]

variable (A : Type _) [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [StarRing A]

variable [ContinuousStar A] [Algebra 𝕜 A]

/- warning: continuous_map.comp_star_alg_hom' -> ContinuousMap.compStarAlgHom' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (𝕜 : Type.{u3}) [_inst_4 : CommSemiring.{u3} 𝕜] (A : Type.{u4}) [_inst_5 : TopologicalSpace.{u4} A] [_inst_6 : Semiring.{u4} A] [_inst_7 : TopologicalSemiring.{u4} A _inst_5 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} A (Semiring.toNonAssocSemiring.{u4} A _inst_6))] [_inst_8 : StarRing.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6)] [_inst_9 : ContinuousStar.{u4} A _inst_5 (InvolutiveStar.toHasStar.{u4} A (StarAddMonoid.toHasInvolutiveStar.{u4} A (AddCommMonoid.toAddMonoid.{u4} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6)))) (StarRing.toStarAddMonoid.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6) _inst_8)))] [_inst_10 : Algebra.{u3, u4} 𝕜 A _inst_4 _inst_6], (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) -> (StarAlgHom.{u3, max u2 u4, max u1 u4} 𝕜 (ContinuousMap.{u2, u4} Y A _inst_2 _inst_5) (ContinuousMap.{u1, u4} X A _inst_1 _inst_5) _inst_4 (ContinuousMap.semiring.{u2, u4} Y A _inst_2 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u2, u3, u4} Y _inst_2 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.hasStar.{u2, u4} Y A _inst_2 _inst_5 (InvolutiveStar.toHasStar.{u4} A (StarAddMonoid.toHasInvolutiveStar.{u4} A (AddCommMonoid.toAddMonoid.{u4} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6)))) (StarRing.toStarAddMonoid.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6) _inst_8))) _inst_9) (ContinuousMap.semiring.{u1, u4} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u1, u3, u4} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.hasStar.{u1, u4} X A _inst_1 _inst_5 (InvolutiveStar.toHasStar.{u4} A (StarAddMonoid.toHasInvolutiveStar.{u4} A (AddCommMonoid.toAddMonoid.{u4} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6)))) (StarRing.toStarAddMonoid.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6) _inst_8))) _inst_9))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] (𝕜 : Type.{u3}) [_inst_4 : CommSemiring.{u3} 𝕜] (A : Type.{u4}) [_inst_5 : TopologicalSpace.{u4} A] [_inst_6 : Semiring.{u4} A] [_inst_7 : TopologicalSemiring.{u4} A _inst_5 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} A (Semiring.toNonAssocSemiring.{u4} A _inst_6))] [_inst_8 : StarRing.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6)] [_inst_9 : ContinuousStar.{u4} A _inst_5 (InvolutiveStar.toStar.{u4} A (StarAddMonoid.toInvolutiveStar.{u4} A (AddMonoidWithOne.toAddMonoid.{u4} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} A (NonAssocSemiring.toAddCommMonoidWithOne.{u4} A (Semiring.toNonAssocSemiring.{u4} A _inst_6)))) (StarRing.toStarAddMonoid.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6) _inst_8)))] [_inst_10 : Algebra.{u3, u4} 𝕜 A _inst_4 _inst_6], (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) -> (StarAlgHom.{u3, max u4 u2, max u4 u1} 𝕜 (ContinuousMap.{u2, u4} Y A _inst_2 _inst_5) (ContinuousMap.{u1, u4} X A _inst_1 _inst_5) _inst_4 (ContinuousMap.instSemiringContinuousMap.{u2, u4} Y A _inst_2 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u2, u3, u4} Y _inst_2 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.instStarContinuousMap.{u2, u4} Y A _inst_2 _inst_5 (InvolutiveStar.toStar.{u4} A (StarAddMonoid.toInvolutiveStar.{u4} A (AddMonoidWithOne.toAddMonoid.{u4} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} A (NonAssocSemiring.toAddCommMonoidWithOne.{u4} A (Semiring.toNonAssocSemiring.{u4} A _inst_6)))) (StarRing.toStarAddMonoid.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6) _inst_8))) _inst_9) (ContinuousMap.instSemiringContinuousMap.{u1, u4} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u1, u3, u4} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.instStarContinuousMap.{u1, u4} X A _inst_1 _inst_5 (InvolutiveStar.toStar.{u4} A (StarAddMonoid.toInvolutiveStar.{u4} A (AddMonoidWithOne.toAddMonoid.{u4} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u4} A (NonAssocSemiring.toAddCommMonoidWithOne.{u4} A (Semiring.toNonAssocSemiring.{u4} A _inst_6)))) (StarRing.toStarAddMonoid.{u4} A (Semiring.toNonUnitalSemiring.{u4} A _inst_6) _inst_8))) _inst_9))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_star_alg_hom' ContinuousMap.compStarAlgHom'ₓ'. -/
/-- The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre-composition
with the continuous function `f`. See `continuous_map.comp_monoid_hom'` and
`continuous_map.comp_add_monoid_hom'`, `continuous_map.comp_right_alg_hom` for bundlings of
pre-composition into a `monoid_hom`, an `add_monoid_hom` and an `alg_hom`, respectively, under
suitable assumptions on `A`. -/
@[simps]
def compStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A)
    where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp _
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
#align continuous_map.comp_star_alg_hom' ContinuousMap.compStarAlgHom'

/- warning: continuous_map.comp_star_alg_hom'_id -> ContinuousMap.compStarAlgHom'_id is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (𝕜 : Type.{u2}) [_inst_4 : CommSemiring.{u2} 𝕜] (A : Type.{u3}) [_inst_5 : TopologicalSpace.{u3} A] [_inst_6 : Semiring.{u3} A] [_inst_7 : TopologicalSemiring.{u3} A _inst_5 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A _inst_6))] [_inst_8 : StarRing.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6)] [_inst_9 : ContinuousStar.{u3} A _inst_5 (InvolutiveStar.toHasStar.{u3} A (StarAddMonoid.toHasInvolutiveStar.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6)))) (StarRing.toStarAddMonoid.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6) _inst_8)))] [_inst_10 : Algebra.{u2, u3} 𝕜 A _inst_4 _inst_6], Eq.{succ (max u1 u3)} (StarAlgHom.{u2, max u1 u3, max u1 u3} 𝕜 (ContinuousMap.{u1, u3} X A _inst_1 _inst_5) (ContinuousMap.{u1, u3} X A _inst_1 _inst_5) _inst_4 (ContinuousMap.semiring.{u1, u3} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u1, u2, u3} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.hasStar.{u1, u3} X A _inst_1 _inst_5 (InvolutiveStar.toHasStar.{u3} A (StarAddMonoid.toHasInvolutiveStar.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6)))) (StarRing.toStarAddMonoid.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6) _inst_8))) _inst_9) (ContinuousMap.semiring.{u1, u3} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u1, u2, u3} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.hasStar.{u1, u3} X A _inst_1 _inst_5 (InvolutiveStar.toHasStar.{u3} A (StarAddMonoid.toHasInvolutiveStar.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6)))) (StarRing.toStarAddMonoid.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6) _inst_8))) _inst_9)) (ContinuousMap.compStarAlgHom'.{u1, u1, u2, u3} X X _inst_1 _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 (ContinuousMap.id.{u1} X _inst_1)) (StarAlgHom.id.{u2, max u1 u3} 𝕜 (ContinuousMap.{u1, u3} X A _inst_1 _inst_5) _inst_4 (ContinuousMap.semiring.{u1, u3} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u1, u2, u3} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.hasStar.{u1, u3} X A _inst_1 _inst_5 (InvolutiveStar.toHasStar.{u3} A (StarAddMonoid.toHasInvolutiveStar.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6)))) (StarRing.toStarAddMonoid.{u3} A (Semiring.toNonUnitalSemiring.{u3} A _inst_6) _inst_8))) _inst_9))
but is expected to have type
  forall {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] (𝕜 : Type.{u1}) [_inst_4 : CommSemiring.{u1} 𝕜] (A : Type.{u2}) [_inst_5 : TopologicalSpace.{u2} A] [_inst_6 : Semiring.{u2} A] [_inst_7 : TopologicalSemiring.{u2} A _inst_5 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_6))] [_inst_8 : StarRing.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_6)] [_inst_9 : ContinuousStar.{u2} A _inst_5 (InvolutiveStar.toStar.{u2} A (StarAddMonoid.toInvolutiveStar.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_6)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_6) _inst_8)))] [_inst_10 : Algebra.{u1, u2} 𝕜 A _inst_4 _inst_6], Eq.{max (succ u3) (succ u2)} (StarAlgHom.{u1, max u2 u3, max u2 u3} 𝕜 (ContinuousMap.{u3, u2} X A _inst_1 _inst_5) (ContinuousMap.{u3, u2} X A _inst_1 _inst_5) _inst_4 (ContinuousMap.instSemiringContinuousMap.{u3, u2} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u3, u1, u2} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.instStarContinuousMap.{u3, u2} X A _inst_1 _inst_5 (InvolutiveStar.toStar.{u2} A (StarAddMonoid.toInvolutiveStar.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_6)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_6) _inst_8))) _inst_9) (ContinuousMap.instSemiringContinuousMap.{u3, u2} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u3, u1, u2} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.instStarContinuousMap.{u3, u2} X A _inst_1 _inst_5 (InvolutiveStar.toStar.{u2} A (StarAddMonoid.toInvolutiveStar.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_6)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_6) _inst_8))) _inst_9)) (ContinuousMap.compStarAlgHom'.{u3, u3, u1, u2} X X _inst_1 _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 (ContinuousMap.id.{u3} X _inst_1)) (StarAlgHom.id.{u1, max u2 u3} 𝕜 (ContinuousMap.{u3, u2} X A _inst_1 _inst_5) _inst_4 (ContinuousMap.instSemiringContinuousMap.{u3, u2} X A _inst_1 _inst_5 _inst_6 _inst_7) (ContinuousMap.algebra.{u3, u1, u2} X _inst_1 𝕜 _inst_4 A _inst_5 _inst_6 _inst_10 _inst_7) (ContinuousMap.instStarContinuousMap.{u3, u2} X A _inst_1 _inst_5 (InvolutiveStar.toStar.{u2} A (StarAddMonoid.toInvolutiveStar.{u2} A (AddMonoidWithOne.toAddMonoid.{u2} A (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} A (NonAssocSemiring.toAddCommMonoidWithOne.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_6)))) (StarRing.toStarAddMonoid.{u2} A (Semiring.toNonUnitalSemiring.{u2} A _inst_6) _inst_8))) _inst_9))
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_star_alg_hom'_id ContinuousMap.compStarAlgHom'_idₓ'. -/
/-- `continuous_map.comp_star_alg_hom'` sends the identity continuous map to the identity
`star_alg_hom` -/
theorem compStarAlgHom'_id : compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
#align continuous_map.comp_star_alg_hom'_id ContinuousMap.compStarAlgHom'_id

/- warning: continuous_map.comp_star_alg_hom'_comp -> ContinuousMap.compStarAlgHom'_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_map.comp_star_alg_hom'_comp ContinuousMap.compStarAlgHom'_compₓ'. -/
/-- `continuous_map.comp_star_alg_hom` is functorial. -/
theorem compStarAlgHom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compStarAlgHom' 𝕜 A (g.comp f) = (compStarAlgHom' 𝕜 A f).comp (compStarAlgHom' 𝕜 A g) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
#align continuous_map.comp_star_alg_hom'_comp ContinuousMap.compStarAlgHom'_comp

section Periodicity

/-! ### Summing translates of a function -/


/- warning: continuous_map.periodic_tsum_comp_add_zsmul -> ContinuousMap.periodic_tsum_comp_add_zsmul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} Y] [_inst_11 : LocallyCompactSpace.{u1} X _inst_1] [_inst_12 : AddCommGroup.{u1} X] [_inst_13 : TopologicalAddGroup.{u1} X _inst_1 (AddCommGroup.toAddGroup.{u1} X _inst_12)] [_inst_14 : AddCommMonoid.{u2} Y] [_inst_15 : ContinuousAdd.{u2} Y _inst_2 (AddZeroClass.toHasAdd.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y _inst_14)))] [_inst_16 : T2Space.{u2} Y _inst_2] (f : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (p : X), Function.Periodic.{u1, u2} X Y (AddZeroClass.toHasAdd.{u1} X (AddMonoid.toAddZeroClass.{u1} X (SubNegMonoid.toAddMonoid.{u1} X (AddGroup.toSubNegMonoid.{u1} X (AddCommGroup.toAddGroup.{u1} X _inst_12))))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (fun (_x : ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) => X -> Y) (ContinuousMap.hasCoeToFun.{u1, u2} X Y _inst_1 _inst_2) (tsum.{max u1 u2, 0} (ContinuousMap.{u1, u2} X Y _inst_1 _inst_2) (ContinuousMap.addCommMonoid.{u1, u2} X Y _inst_1 _inst_2 _inst_14 _inst_15) (ContinuousMap.compactOpen.{u1, u2} X Y _inst_1 _inst_2) Int (fun (n : Int) => ContinuousMap.comp.{u1, u1, u2} X X Y _inst_1 _inst_1 _inst_2 f (ContinuousMap.addRight.{u1} X _inst_1 (AddZeroClass.toHasAdd.{u1} X (AddMonoid.toAddZeroClass.{u1} X (SubNegMonoid.toAddMonoid.{u1} X (AddGroup.toSubNegMonoid.{u1} X (AddCommGroup.toAddGroup.{u1} X _inst_12))))) (TopologicalAddGroup.to_continuousAdd.{u1} X _inst_1 (AddCommGroup.toAddGroup.{u1} X _inst_12) _inst_13) (SMul.smul.{0, u1} Int X (SubNegMonoid.SMulInt.{u1} X (AddGroup.toSubNegMonoid.{u1} X (AddCommGroup.toAddGroup.{u1} X _inst_12))) n p))))) p
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} Y] [_inst_11 : LocallyCompactSpace.{u2} X _inst_1] [_inst_12 : AddCommGroup.{u2} X] [_inst_13 : TopologicalAddGroup.{u2} X _inst_1 (AddCommGroup.toAddGroup.{u2} X _inst_12)] [_inst_14 : AddCommMonoid.{u1} Y] [_inst_15 : ContinuousAdd.{u1} Y _inst_2 (AddZeroClass.toAdd.{u1} Y (AddMonoid.toAddZeroClass.{u1} Y (AddCommMonoid.toAddMonoid.{u1} Y _inst_14)))] [_inst_16 : T2Space.{u1} Y _inst_2] (f : ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) (p : X), Function.Periodic.{u2, u1} X Y (AddZeroClass.toAdd.{u2} X (AddMonoid.toAddZeroClass.{u2} X (SubNegMonoid.toAddMonoid.{u2} X (AddGroup.toSubNegMonoid.{u2} X (AddCommGroup.toAddGroup.{u2} X _inst_12))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => Y) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) X Y _inst_1 _inst_2 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} X Y _inst_1 _inst_2)) (tsum.{max u1 u2, 0} (ContinuousMap.{u2, u1} X Y _inst_1 _inst_2) (ContinuousMap.instAddCommMonoidContinuousMap.{u2, u1} X Y _inst_1 _inst_2 _inst_14 _inst_15) (ContinuousMap.compactOpen.{u2, u1} X Y _inst_1 _inst_2) Int (fun (n : Int) => ContinuousMap.comp.{u2, u2, u1} X X Y _inst_1 _inst_1 _inst_2 f (ContinuousMap.addRight.{u2} X _inst_1 (AddZeroClass.toAdd.{u2} X (AddMonoid.toAddZeroClass.{u2} X (SubNegMonoid.toAddMonoid.{u2} X (AddGroup.toSubNegMonoid.{u2} X (AddCommGroup.toAddGroup.{u2} X _inst_12))))) (TopologicalAddGroup.toContinuousAdd.{u2} X _inst_1 (AddCommGroup.toAddGroup.{u2} X _inst_12) _inst_13) (HSMul.hSMul.{0, u2, u2} Int X X (instHSMul.{0, u2} Int X (SubNegMonoid.SMulInt.{u2} X (AddGroup.toSubNegMonoid.{u2} X (AddCommGroup.toAddGroup.{u2} X _inst_12)))) n p))))) p
Case conversion may be inaccurate. Consider using '#align continuous_map.periodic_tsum_comp_add_zsmul ContinuousMap.periodic_tsum_comp_add_zsmulₓ'. -/
/-- Summing the translates of `f` by `ℤ • p` gives a map which is periodic with period `p`.
(This is true without any convergence conditions, since if the sum doesn't converge it is taken to
be the zero map, which is periodic.) -/
theorem periodic_tsum_comp_add_zsmul [LocallyCompactSpace X] [AddCommGroup X]
    [TopologicalAddGroup X] [AddCommMonoid Y] [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) :
    Function.Periodic (⇑(∑' n : ℤ, f.comp (ContinuousMap.addRight (n • p)))) p :=
  by
  intro x
  by_cases h : Summable fun n : ℤ => f.comp (ContinuousMap.addRight (n • p))
  · convert congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : ℤ)).tsum_eq _) using 1
    simp_rw [← tsum_apply h, ← tsum_apply ((Equiv.addRight (1 : ℤ)).summable_iff.mpr h),
      Equiv.coe_addRight, comp_apply, coe_add_right, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]
#align continuous_map.periodic_tsum_comp_add_zsmul ContinuousMap.periodic_tsum_comp_add_zsmul

end Periodicity

end ContinuousMap

namespace Homeomorph

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]

variable (𝕜 : Type _) [CommSemiring 𝕜]

variable (A : Type _) [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [StarRing A]

variable [ContinuousStar A] [Algebra 𝕜 A]

/- warning: homeomorph.comp_star_alg_equiv' -> Homeomorph.compStarAlgEquiv' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_star_alg_equiv' Homeomorph.compStarAlgEquiv'ₓ'. -/
/-- `continuous_map.comp_star_alg_hom'` as a `star_alg_equiv` when the continuous map `f` is
actually a homeomorphism. -/
@[simps]
def compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
  {
    f.toContinuousMap.compStarAlgHom' 𝕜
      A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        to_continuous_map_comp_symm, ContinuousMap.comp_id]
    right_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        symm_comp_to_continuous_map, ContinuousMap.comp_id]
    map_smul' := fun k a => map_smul (f.toContinuousMap.compStarAlgHom' 𝕜 A) k a }
#align homeomorph.comp_star_alg_equiv' Homeomorph.compStarAlgEquiv'

end Homeomorph

