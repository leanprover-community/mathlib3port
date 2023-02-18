/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.algebra.group_with_zero
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Algebra.Group.Pi
import Mathbin.Topology.Homeomorph

/-!
# Topological group with zero

In this file we define `has_continuous_inv₀` to be a mixin typeclass a type with `has_inv` and
`has_zero` (e.g., a `group_with_zero`) such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `has_continuous_inv₀` in
`mathlib` which is not a normed field is the type `nnnreal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv'` and
`*.div` operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`,
and `continuous`. As a special case, we provide `*.div_const` operations that require only
`group_with_zero` and `has_continuous_mul` instances.

All lemmas about `(⁻¹)` use `inv'` in their names because lemmas without `'` are used for
`topological_group`s. We also use `'` in the typeclass name `has_continuous_inv₀` for the sake of
consistency of notation.

On a `group_with_zero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/


open Topology Filter

open Filter Function

/-!
### A group with zero with continuous multiplication

If `G₀` is a group with zero with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and
`continuous`.
-/


variable {α β G₀ : Type _}

section DivConst

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousMul G₀] {f : α → G₀} {s : Set α}
  {l : Filter α}

/- warning: filter.tendsto.div_const -> Filter.Tendsto.div_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {l : Filter.{u1} α} {x : G₀}, (Filter.Tendsto.{u1, u2} α G₀ f l (nhds.{u2} G₀ _inst_2 x)) -> (forall (y : G₀), Filter.Tendsto.{u1, u2} α G₀ (fun (a : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f a) y) l (nhds.{u2} G₀ _inst_2 (HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) x y)))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : ContinuousMul.{u1} G₀ _inst_2 (MulOneClass.toMul.{u1} G₀ (Monoid.toMulOneClass.{u1} G₀ (DivInvMonoid.toMonoid.{u1} G₀ _inst_1)))] {f : α -> G₀} {l : Filter.{u2} α} {x : G₀}, (Filter.Tendsto.{u2, u1} α G₀ f l (nhds.{u1} G₀ _inst_2 x)) -> (forall (y : G₀), Filter.Tendsto.{u2, u1} α G₀ (fun (a : α) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toDiv.{u1} G₀ _inst_1)) (f a) y) l (nhds.{u1} G₀ _inst_2 (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toDiv.{u1} G₀ _inst_1)) x y)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.div_const Filter.Tendsto.div_constₓ'. -/
theorem Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) :
    Tendsto (fun a => f a / y) l (𝓝 (x / y)) := by
  simpa only [div_eq_mul_inv] using hf.mul tendsto_const_nhds
#align filter.tendsto.div_const Filter.Tendsto.div_const

variable [TopologicalSpace α]

/- warning: continuous_at.div_const -> ContinuousAt.div_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} [_inst_4 : TopologicalSpace.{u1} α] {a : α}, (ContinuousAt.{u1, u2} α G₀ _inst_4 _inst_2 f a) -> (forall (y : G₀), ContinuousAt.{u1, u2} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f x) y) a)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : ContinuousMul.{u1} G₀ _inst_2 (MulOneClass.toMul.{u1} G₀ (Monoid.toMulOneClass.{u1} G₀ (DivInvMonoid.toMonoid.{u1} G₀ _inst_1)))] {f : α -> G₀} [_inst_4 : TopologicalSpace.{u2} α] {a : α}, (ContinuousAt.{u2, u1} α G₀ _inst_4 _inst_2 f a) -> (forall (y : G₀), ContinuousAt.{u2, u1} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toDiv.{u1} G₀ _inst_1)) (f x) y) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.div_const ContinuousAt.div_constₓ'. -/
theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
    ContinuousAt (fun x => f x / y) a := by
  simpa only [div_eq_mul_inv] using hf.mul continuousAt_const
#align continuous_at.div_const ContinuousAt.div_const

/- warning: continuous_within_at.div_const -> ContinuousWithinAt.div_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {s : Set.{u1} α} [_inst_4 : TopologicalSpace.{u1} α] {a : α}, (ContinuousWithinAt.{u1, u2} α G₀ _inst_4 _inst_2 f s a) -> (forall (y : G₀), ContinuousWithinAt.{u1, u2} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f x) y) s a)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : ContinuousMul.{u1} G₀ _inst_2 (MulOneClass.toMul.{u1} G₀ (Monoid.toMulOneClass.{u1} G₀ (DivInvMonoid.toMonoid.{u1} G₀ _inst_1)))] {f : α -> G₀} {s : Set.{u2} α} [_inst_4 : TopologicalSpace.{u2} α] {a : α}, (ContinuousWithinAt.{u2, u1} α G₀ _inst_4 _inst_2 f s a) -> (forall (y : G₀), ContinuousWithinAt.{u2, u1} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toDiv.{u1} G₀ _inst_1)) (f x) y) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.div_const ContinuousWithinAt.div_constₓ'. -/
theorem ContinuousWithinAt.div_const {a} (hf : ContinuousWithinAt f s a) (y : G₀) :
    ContinuousWithinAt (fun x => f x / y) s a :=
  hf.div_const _
#align continuous_within_at.div_const ContinuousWithinAt.div_const

/- warning: continuous_on.div_const -> ContinuousOn.div_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {s : Set.{u1} α} [_inst_4 : TopologicalSpace.{u1} α], (ContinuousOn.{u1, u2} α G₀ _inst_4 _inst_2 f s) -> (forall (y : G₀), ContinuousOn.{u1, u2} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f x) y) s)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : ContinuousMul.{u1} G₀ _inst_2 (MulOneClass.toMul.{u1} G₀ (Monoid.toMulOneClass.{u1} G₀ (DivInvMonoid.toMonoid.{u1} G₀ _inst_1)))] {f : α -> G₀} {s : Set.{u2} α} [_inst_4 : TopologicalSpace.{u2} α], (ContinuousOn.{u2, u1} α G₀ _inst_4 _inst_2 f s) -> (forall (y : G₀), ContinuousOn.{u2, u1} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toDiv.{u1} G₀ _inst_1)) (f x) y) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.div_const ContinuousOn.div_constₓ'. -/
theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
    ContinuousOn (fun x => f x / y) s := by
  simpa only [div_eq_mul_inv] using hf.mul continuousOn_const
#align continuous_on.div_const ContinuousOn.div_const

/- warning: continuous.div_const -> Continuous.div_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} [_inst_4 : TopologicalSpace.{u1} α], (Continuous.{u1, u2} α G₀ _inst_4 _inst_2 f) -> (forall (y : G₀), Continuous.{u1, u2} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f x) y))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : ContinuousMul.{u1} G₀ _inst_2 (MulOneClass.toMul.{u1} G₀ (Monoid.toMulOneClass.{u1} G₀ (DivInvMonoid.toMonoid.{u1} G₀ _inst_1)))] {f : α -> G₀} [_inst_4 : TopologicalSpace.{u2} α], (Continuous.{u2, u1} α G₀ _inst_4 _inst_2 f) -> (forall (y : G₀), Continuous.{u2, u1} α G₀ _inst_4 _inst_2 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toDiv.{u1} G₀ _inst_1)) (f x) y))
Case conversion may be inaccurate. Consider using '#align continuous.div_const Continuous.div_constₓ'. -/
@[continuity]
theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x / y := by
  simpa only [div_eq_mul_inv] using hf.mul continuous_const
#align continuous.div_const Continuous.div_const

end DivConst

#print HasContinuousInv₀ /-
/-- A type with `0` and `has_inv` such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. -/
class HasContinuousInv₀ (G₀ : Type _) [Zero G₀] [Inv G₀] [TopologicalSpace G₀] : Prop where
  continuousAt_inv₀ : ∀ ⦃x : G₀⦄, x ≠ 0 → ContinuousAt Inv.inv x
#align has_continuous_inv₀ HasContinuousInv₀
-/

export HasContinuousInv₀ (continuousAt_inv₀)

section Inv₀

variable [Zero G₀] [Inv G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] {l : Filter α} {f : α → G₀}
  {s : Set α} {a : α}

/-!
### Continuity of `λ x, x⁻¹` at a non-zero point

We define `topological_group_with_zero` to be a `group_with_zero` such that the operation `x ↦ x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv'` lemmas for
`filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and `continuous`.
-/


#print tendsto_inv₀ /-
theorem tendsto_inv₀ {x : G₀} (hx : x ≠ 0) : Tendsto Inv.inv (𝓝 x) (𝓝 x⁻¹) :=
  continuousAt_inv₀ hx
#align tendsto_inv₀ tendsto_inv₀
-/

/- warning: continuous_on_inv₀ -> continuousOn_inv₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3], ContinuousOn.{u1, u1} G₀ G₀ _inst_3 _inst_3 (Inv.inv.{u1} G₀ _inst_2) (HasCompl.compl.{u1} (Set.{u1} G₀) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} G₀) (Set.booleanAlgebra.{u1} G₀)) (Singleton.singleton.{u1, u1} G₀ (Set.{u1} G₀) (Set.hasSingleton.{u1} G₀) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ _inst_1)))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3], ContinuousOn.{u1, u1} G₀ G₀ _inst_3 _inst_3 (Inv.inv.{u1} G₀ _inst_2) (HasCompl.compl.{u1} (Set.{u1} G₀) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} G₀) (Set.instBooleanAlgebraSet.{u1} G₀)) (Singleton.singleton.{u1, u1} G₀ (Set.{u1} G₀) (Set.instSingletonSet.{u1} G₀) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align continuous_on_inv₀ continuousOn_inv₀ₓ'. -/
theorem continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ → G₀) ({0}ᶜ) := fun x hx =>
  (continuousAt_inv₀ hx).ContinuousWithinAt
#align continuous_on_inv₀ continuousOn_inv₀

/- warning: filter.tendsto.inv₀ -> Filter.Tendsto.inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : Zero.{u2} G₀] [_inst_2 : Inv.{u2} G₀] [_inst_3 : TopologicalSpace.{u2} G₀] [_inst_4 : HasContinuousInv₀.{u2} G₀ _inst_1 _inst_2 _inst_3] {l : Filter.{u1} α} {f : α -> G₀} {a : G₀}, (Filter.Tendsto.{u1, u2} α G₀ f l (nhds.{u2} G₀ _inst_3 a)) -> (Ne.{succ u2} G₀ a (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ _inst_1)))) -> (Filter.Tendsto.{u1, u2} α G₀ (fun (x : α) => Inv.inv.{u2} G₀ _inst_2 (f x)) l (nhds.{u2} G₀ _inst_3 (Inv.inv.{u2} G₀ _inst_2 a)))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3] {l : Filter.{u2} α} {f : α -> G₀} {a : G₀}, (Filter.Tendsto.{u2, u1} α G₀ f l (nhds.{u1} G₀ _inst_3 a)) -> (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ _inst_1))) -> (Filter.Tendsto.{u2, u1} α G₀ (fun (x : α) => Inv.inv.{u1} G₀ _inst_2 (f x)) l (nhds.{u1} G₀ _inst_3 (Inv.inv.{u1} G₀ _inst_2 a)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.inv₀ Filter.Tendsto.inv₀ₓ'. -/
/-- If a function converges to a nonzero value, its inverse converges to the inverse of this value.
We use the name `tendsto.inv₀` as `tendsto.inv` is already used in multiplicative topological
groups. -/
theorem Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a)) (ha : a ≠ 0) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹) :=
  (tendsto_inv₀ ha).comp hf
#align filter.tendsto.inv₀ Filter.Tendsto.inv₀

variable [TopologicalSpace α]

/- warning: continuous_within_at.inv₀ -> ContinuousWithinAt.inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : Zero.{u2} G₀] [_inst_2 : Inv.{u2} G₀] [_inst_3 : TopologicalSpace.{u2} G₀] [_inst_4 : HasContinuousInv₀.{u2} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} {s : Set.{u1} α} {a : α} [_inst_5 : TopologicalSpace.{u1} α], (ContinuousWithinAt.{u1, u2} α G₀ _inst_5 _inst_3 f s a) -> (Ne.{succ u2} G₀ (f a) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ _inst_1)))) -> (ContinuousWithinAt.{u1, u2} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u2} G₀ _inst_2 (f x)) s a)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} {s : Set.{u2} α} {a : α} [_inst_5 : TopologicalSpace.{u2} α], (ContinuousWithinAt.{u2, u1} α G₀ _inst_5 _inst_3 f s a) -> (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ _inst_1))) -> (ContinuousWithinAt.{u2, u1} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u1} G₀ _inst_2 (f x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.inv₀ ContinuousWithinAt.inv₀ₓ'. -/
theorem ContinuousWithinAt.inv₀ (hf : ContinuousWithinAt f s a) (ha : f a ≠ 0) :
    ContinuousWithinAt (fun x => (f x)⁻¹) s a :=
  hf.inv₀ ha
#align continuous_within_at.inv₀ ContinuousWithinAt.inv₀

/- warning: continuous_at.inv₀ -> ContinuousAt.inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : Zero.{u2} G₀] [_inst_2 : Inv.{u2} G₀] [_inst_3 : TopologicalSpace.{u2} G₀] [_inst_4 : HasContinuousInv₀.{u2} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} {a : α} [_inst_5 : TopologicalSpace.{u1} α], (ContinuousAt.{u1, u2} α G₀ _inst_5 _inst_3 f a) -> (Ne.{succ u2} G₀ (f a) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ _inst_1)))) -> (ContinuousAt.{u1, u2} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u2} G₀ _inst_2 (f x)) a)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} {a : α} [_inst_5 : TopologicalSpace.{u2} α], (ContinuousAt.{u2, u1} α G₀ _inst_5 _inst_3 f a) -> (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ _inst_1))) -> (ContinuousAt.{u2, u1} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u1} G₀ _inst_2 (f x)) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.inv₀ ContinuousAt.inv₀ₓ'. -/
theorem ContinuousAt.inv₀ (hf : ContinuousAt f a) (ha : f a ≠ 0) :
    ContinuousAt (fun x => (f x)⁻¹) a :=
  hf.inv₀ ha
#align continuous_at.inv₀ ContinuousAt.inv₀

/- warning: continuous.inv₀ -> Continuous.inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : Zero.{u2} G₀] [_inst_2 : Inv.{u2} G₀] [_inst_3 : TopologicalSpace.{u2} G₀] [_inst_4 : HasContinuousInv₀.{u2} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} [_inst_5 : TopologicalSpace.{u1} α], (Continuous.{u1, u2} α G₀ _inst_5 _inst_3 f) -> (forall (x : α), Ne.{succ u2} G₀ (f x) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ _inst_1)))) -> (Continuous.{u1, u2} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u2} G₀ _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} [_inst_5 : TopologicalSpace.{u2} α], (Continuous.{u2, u1} α G₀ _inst_5 _inst_3 f) -> (forall (x : α), Ne.{succ u1} G₀ (f x) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ _inst_1))) -> (Continuous.{u2, u1} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u1} G₀ _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.inv₀ Continuous.inv₀ₓ'. -/
@[continuity]
theorem Continuous.inv₀ (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : Continuous fun x => (f x)⁻¹ :=
  continuous_iff_continuousAt.2 fun x => (hf.Tendsto x).inv₀ (h0 x)
#align continuous.inv₀ Continuous.inv₀

/- warning: continuous_on.inv₀ -> ContinuousOn.inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : Zero.{u2} G₀] [_inst_2 : Inv.{u2} G₀] [_inst_3 : TopologicalSpace.{u2} G₀] [_inst_4 : HasContinuousInv₀.{u2} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} {s : Set.{u1} α} [_inst_5 : TopologicalSpace.{u1} α], (ContinuousOn.{u1, u2} α G₀ _inst_5 _inst_3 f s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Ne.{succ u2} G₀ (f x) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ _inst_1))))) -> (ContinuousOn.{u1, u2} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u2} G₀ _inst_2 (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : Zero.{u1} G₀] [_inst_2 : Inv.{u1} G₀] [_inst_3 : TopologicalSpace.{u1} G₀] [_inst_4 : HasContinuousInv₀.{u1} G₀ _inst_1 _inst_2 _inst_3] {f : α -> G₀} {s : Set.{u2} α} [_inst_5 : TopologicalSpace.{u2} α], (ContinuousOn.{u2, u1} α G₀ _inst_5 _inst_3 f s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Ne.{succ u1} G₀ (f x) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ _inst_1)))) -> (ContinuousOn.{u2, u1} α G₀ _inst_5 _inst_3 (fun (x : α) => Inv.inv.{u1} G₀ _inst_2 (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.inv₀ ContinuousOn.inv₀ₓ'. -/
theorem ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => (f x)⁻¹) s := fun x hx => (hf x hx).inv₀ (h0 x hx)
#align continuous_on.inv₀ ContinuousOn.inv₀

end Inv₀

/-!
### Continuity of division

If `G₀` is a `group_with_zero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/


section Div

variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀}

/- warning: filter.tendsto.div -> Filter.Tendsto.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} {l : Filter.{u1} α} {a : G₀} {b : G₀}, (Filter.Tendsto.{u1, u2} α G₀ f l (nhds.{u2} G₀ _inst_2 a)) -> (Filter.Tendsto.{u1, u2} α G₀ g l (nhds.{u2} G₀ _inst_2 b)) -> (Ne.{succ u2} G₀ b (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (Filter.Tendsto.{u1, u2} α G₀ (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u1 u2} (α -> G₀) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G₀) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)))) f g) l (nhds.{u2} G₀ _inst_2 (HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) a b)))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} {l : Filter.{u2} α} {a : G₀} {b : G₀}, (Filter.Tendsto.{u2, u1} α G₀ f l (nhds.{u1} G₀ _inst_2 a)) -> (Filter.Tendsto.{u2, u1} α G₀ g l (nhds.{u1} G₀ _inst_2 b)) -> (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Filter.Tendsto.{u2, u1} α G₀ (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u2 u1} (α -> G₀) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G₀) (fun (i : α) => GroupWithZero.toDiv.{u1} G₀ _inst_1))) f g) l (nhds.{u1} G₀ _inst_2 (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.div Filter.Tendsto.divₓ'. -/
theorem Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hy : b ≠ 0) : Tendsto (f / g) l (𝓝 (a / b)) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ hy)
#align filter.tendsto.div Filter.Tendsto.div

/- warning: filter.tendsto_mul_iff_of_ne_zero -> Filter.tendsto_mul_iff_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] [_inst_5 : T1Space.{u2} G₀ _inst_2] {f : α -> G₀} {g : α -> G₀} {l : Filter.{u1} α} {x : G₀} {y : G₀}, (Filter.Tendsto.{u1, u2} α G₀ g l (nhds.{u2} G₀ _inst_2 y)) -> (Ne.{succ u2} G₀ y (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (Iff (Filter.Tendsto.{u1, u2} α G₀ (fun (n : α) => HMul.hMul.{u2, u2, u2} G₀ G₀ G₀ (instHMul.{u2} G₀ (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) (f n) (g n)) l (nhds.{u2} G₀ _inst_2 (HMul.hMul.{u2, u2, u2} G₀ G₀ G₀ (instHMul.{u2} G₀ (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) x y))) (Filter.Tendsto.{u1, u2} α G₀ f l (nhds.{u2} G₀ _inst_2 x)))
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (GroupWithZero.toInv.{u2} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] [_inst_5 : T1Space.{u2} G₀ _inst_2] {f : α -> G₀} {g : α -> G₀} {l : Filter.{u1} α} {x : G₀} {y : G₀}, (Filter.Tendsto.{u1, u2} α G₀ g l (nhds.{u2} G₀ _inst_2 y)) -> (Ne.{succ u2} G₀ y (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) -> (Iff (Filter.Tendsto.{u1, u2} α G₀ (fun (n : α) => HMul.hMul.{u2, u2, u2} G₀ G₀ G₀ (instHMul.{u2} G₀ (MulZeroClass.toMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) (f n) (g n)) l (nhds.{u2} G₀ _inst_2 (HMul.hMul.{u2, u2, u2} G₀ G₀ G₀ (instHMul.{u2} G₀ (MulZeroClass.toMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) x y))) (Filter.Tendsto.{u1, u2} α G₀ f l (nhds.{u2} G₀ _inst_2 x)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_mul_iff_of_ne_zero Filter.tendsto_mul_iff_of_ne_zeroₓ'. -/
theorem Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α → G₀} {l : Filter α} {x y : G₀}
    (hg : Tendsto g l (𝓝 y)) (hy : y ≠ 0) :
    Tendsto (fun n => f n * g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x) :=
  by
  refine' ⟨fun hfg => _, fun hf => hf.mul hg⟩
  rw [← mul_div_cancel x hy]
  refine' tendsto.congr' _ (hfg.div hg hy)
  refine' eventually.mp (hg.eventually_ne hy) (eventually_of_forall fun n hn => mul_div_cancel _ hn)
#align filter.tendsto_mul_iff_of_ne_zero Filter.tendsto_mul_iff_of_ne_zero

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {a : α}

/- warning: continuous_within_at.div -> ContinuousWithinAt.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, u2} α G₀ _inst_5 _inst_2 f s a) -> (ContinuousWithinAt.{u1, u2} α G₀ _inst_5 _inst_2 g s a) -> (Ne.{succ u2} G₀ (g a) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (ContinuousWithinAt.{u1, u2} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u1 u2} (α -> G₀) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G₀) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)))) f g) s a)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {a : α}, (ContinuousWithinAt.{u2, u1} α G₀ _inst_5 _inst_2 f s a) -> (ContinuousWithinAt.{u2, u1} α G₀ _inst_5 _inst_2 g s a) -> (Ne.{succ u1} G₀ (g a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (ContinuousWithinAt.{u2, u1} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u2 u1} (α -> G₀) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G₀) (fun (i : α) => GroupWithZero.toDiv.{u1} G₀ _inst_1))) f g) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.div ContinuousWithinAt.divₓ'. -/
theorem ContinuousWithinAt.div (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a)
    (h₀ : g a ≠ 0) : ContinuousWithinAt (f / g) s a :=
  hf.div hg h₀
#align continuous_within_at.div ContinuousWithinAt.div

/- warning: continuous_on.div -> ContinuousOn.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u1} α] {s : Set.{u1} α}, (ContinuousOn.{u1, u2} α G₀ _inst_5 _inst_2 f s) -> (ContinuousOn.{u1, u2} α G₀ _inst_5 _inst_2 g s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Ne.{succ u2} G₀ (g x) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))))))) -> (ContinuousOn.{u1, u2} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u1 u2} (α -> G₀) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G₀) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)))) f g) s)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u2} α] {s : Set.{u2} α}, (ContinuousOn.{u2, u1} α G₀ _inst_5 _inst_2 f s) -> (ContinuousOn.{u2, u1} α G₀ _inst_5 _inst_2 g s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Ne.{succ u1} G₀ (g x) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))) -> (ContinuousOn.{u2, u1} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u2 u1} (α -> G₀) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G₀) (fun (i : α) => GroupWithZero.toDiv.{u1} G₀ _inst_1))) f g) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.div ContinuousOn.divₓ'. -/
theorem ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (f / g) s := fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)
#align continuous_on.div ContinuousOn.div

/- warning: continuous_at.div -> ContinuousAt.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u1} α] {a : α}, (ContinuousAt.{u1, u2} α G₀ _inst_5 _inst_2 f a) -> (ContinuousAt.{u1, u2} α G₀ _inst_5 _inst_2 g a) -> (Ne.{succ u2} G₀ (g a) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (ContinuousAt.{u1, u2} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u1 u2} (α -> G₀) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G₀) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)))) f g) a)
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u2} α] {a : α}, (ContinuousAt.{u2, u1} α G₀ _inst_5 _inst_2 f a) -> (ContinuousAt.{u2, u1} α G₀ _inst_5 _inst_2 g a) -> (Ne.{succ u1} G₀ (g a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (ContinuousAt.{u2, u1} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u2 u1} (α -> G₀) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G₀) (fun (i : α) => GroupWithZero.toDiv.{u1} G₀ _inst_1))) f g) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.div ContinuousAt.divₓ'. -/
/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
theorem ContinuousAt.div (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (f / g) a :=
  hf.div hg h₀
#align continuous_at.div ContinuousAt.div

/- warning: continuous.div -> Continuous.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u1} α], (Continuous.{u1, u2} α G₀ _inst_5 _inst_2 f) -> (Continuous.{u1, u2} α G₀ _inst_5 _inst_2 g) -> (forall (x : α), Ne.{succ u2} G₀ (g x) (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (Continuous.{u1, u2} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u1 u2} (α -> G₀) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G₀) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)))) f g))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {f : α -> G₀} {g : α -> G₀} [_inst_5 : TopologicalSpace.{u2} α], (Continuous.{u2, u1} α G₀ _inst_5 _inst_2 f) -> (Continuous.{u2, u1} α G₀ _inst_5 _inst_2 g) -> (forall (x : α), Ne.{succ u1} G₀ (g x) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Continuous.{u2, u1} α G₀ _inst_5 _inst_2 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G₀) (α -> G₀) (α -> G₀) (instHDiv.{max u2 u1} (α -> G₀) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G₀) (fun (i : α) => GroupWithZero.toDiv.{u1} G₀ _inst_1))) f g))
Case conversion may be inaccurate. Consider using '#align continuous.div Continuous.divₓ'. -/
@[continuity]
theorem Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (f / g) := by simpa only [div_eq_mul_inv] using hf.mul (hg.inv₀ h₀)
#align continuous.div Continuous.div

/- warning: continuous_on_div -> continuousOn_div is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))], ContinuousOn.{u1, u1} (Prod.{u1, u1} G₀ G₀) G₀ (Prod.topologicalSpace.{u1, u1} G₀ G₀ _inst_2 _inst_2) _inst_2 (fun (p : Prod.{u1, u1} G₀ G₀) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (Prod.fst.{u1, u1} G₀ G₀ p) (Prod.snd.{u1, u1} G₀ G₀ p)) (setOf.{u1} (Prod.{u1, u1} G₀ G₀) (fun (p : Prod.{u1, u1} G₀ G₀) => Ne.{succ u1} G₀ (Prod.snd.{u1, u1} G₀ G₀ p) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))], ContinuousOn.{u1, u1} (Prod.{u1, u1} G₀ G₀) G₀ (instTopologicalSpaceProd.{u1, u1} G₀ G₀ _inst_2 _inst_2) _inst_2 (fun (p : Prod.{u1, u1} G₀ G₀) => HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (Prod.fst.{u1, u1} G₀ G₀ p) (Prod.snd.{u1, u1} G₀ G₀ p)) (setOf.{u1} (Prod.{u1, u1} G₀ G₀) (fun (p : Prod.{u1, u1} G₀ G₀) => Ne.{succ u1} G₀ (Prod.snd.{u1, u1} G₀ G₀ p) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align continuous_on_div continuousOn_divₓ'. -/
theorem continuousOn_div : ContinuousOn (fun p : G₀ × G₀ => p.1 / p.2) { p | p.2 ≠ 0 } :=
  continuousOn_fst.div continuousOn_snd fun _ => id
#align continuous_on_div continuousOn_div

/- warning: continuous_at.comp_div_cases -> ContinuousAt.comp_div_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : GroupWithZero.{u3} G₀] [_inst_2 : TopologicalSpace.{u3} G₀] [_inst_3 : HasContinuousInv₀.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u3} G₀ (GroupWithZero.toDivInvMonoid.{u3} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u3} G₀ _inst_2 (MulZeroClass.toHasMul.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1))))] [_inst_5 : TopologicalSpace.{u1} α] [_inst_6 : TopologicalSpace.{u2} β] {a : α} {f : α -> G₀} {g : α -> G₀} (h : α -> G₀ -> β), (ContinuousAt.{u1, u3} α G₀ _inst_5 _inst_2 f a) -> (ContinuousAt.{u1, u3} α G₀ _inst_5 _inst_2 g a) -> ((Ne.{succ u3} G₀ (g a) (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1)))))))) -> (ContinuousAt.{max u1 u3, u2} (Prod.{u1, u3} α G₀) β (Prod.topologicalSpace.{u1, u3} α G₀ _inst_5 _inst_2) _inst_6 (Function.HasUncurry.uncurry.{max u1 u3 u2, max u1 u3, u2} (α -> G₀ -> β) (Prod.{u1, u3} α G₀) β (Function.hasUncurryInduction.{u1, max u3 u2, u3, u2} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u3, u2} G₀ β)) h) (Prod.mk.{u1, u3} α G₀ a (HDiv.hDiv.{u3, u3, u3} G₀ G₀ G₀ (instHDiv.{u3} G₀ (DivInvMonoid.toHasDiv.{u3} G₀ (GroupWithZero.toDivInvMonoid.{u3} G₀ _inst_1))) (f a) (g a))))) -> ((Eq.{succ u3} G₀ (g a) (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1)))))))) -> (Filter.Tendsto.{max u1 u3, u2} (Prod.{u1, u3} α G₀) β (Function.HasUncurry.uncurry.{max u1 u3 u2, max u1 u3, u2} (α -> G₀ -> β) (Prod.{u1, u3} α G₀) β (Function.hasUncurryInduction.{u1, max u3 u2, u3, u2} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u3, u2} G₀ β)) h) (Filter.prod.{u1, u3} α G₀ (nhds.{u1} α _inst_5 a) (Top.top.{u3} (Filter.{u3} G₀) (Filter.hasTop.{u3} G₀))) (nhds.{u2} β _inst_6 (h a (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1))))))))))) -> (ContinuousAt.{u1, u2} α β _inst_5 _inst_6 (fun (x : α) => h x (HDiv.hDiv.{u3, u3, u3} G₀ G₀ G₀ (instHDiv.{u3} G₀ (DivInvMonoid.toHasDiv.{u3} G₀ (GroupWithZero.toDivInvMonoid.{u3} G₀ _inst_1))) (f x) (g x))) a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (GroupWithZero.toInv.{u2} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] [_inst_5 : TopologicalSpace.{u3} α] [_inst_6 : TopologicalSpace.{u1} β] {a : α} {f : α -> G₀} {g : α -> G₀} (h : α -> G₀ -> β), (ContinuousAt.{u3, u2} α G₀ _inst_5 _inst_2 f a) -> (ContinuousAt.{u3, u2} α G₀ _inst_5 _inst_2 g a) -> ((Ne.{succ u2} G₀ (g a) (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) -> (ContinuousAt.{max u3 u2, u1} (Prod.{u3, u2} α G₀) β (instTopologicalSpaceProd.{u3, u2} α G₀ _inst_5 _inst_2) _inst_6 (Function.HasUncurry.uncurry.{max (max u3 u1) u2, max u3 u2, u1} (α -> G₀ -> β) (Prod.{u3, u2} α G₀) β (Function.hasUncurryInduction.{u3, max u1 u2, u2, u1} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u2, u1} G₀ β)) h) (Prod.mk.{u3, u2} α G₀ a (HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (GroupWithZero.toDiv.{u2} G₀ _inst_1)) (f a) (g a))))) -> ((Eq.{succ u2} G₀ (g a) (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) -> (Filter.Tendsto.{max u3 u2, u1} (Prod.{u3, u2} α G₀) β (Function.HasUncurry.uncurry.{max (max u3 u1) u2, max u3 u2, u1} (α -> G₀ -> β) (Prod.{u3, u2} α G₀) β (Function.hasUncurryInduction.{u3, max u1 u2, u2, u1} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u2, u1} G₀ β)) h) (Filter.prod.{u3, u2} α G₀ (nhds.{u3} α _inst_5 a) (Top.top.{u2} (Filter.{u2} G₀) (Filter.instTopFilter.{u2} G₀))) (nhds.{u1} β _inst_6 (h a (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (ContinuousAt.{u3, u1} α β _inst_5 _inst_6 (fun (x : α) => h x (HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (GroupWithZero.toDiv.{u2} G₀ _inst_1)) (f x) (g x))) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_div_cases ContinuousAt.comp_div_casesₓ'. -/
/-- The function `f x / g x` is discontinuous when `g x = 0`.
However, under appropriate conditions, `h x (f x / g x)` is still continuous.
The condition is that if `g a = 0` then `h x y` must tend to `h a 0` when `x` tends to `a`,
with no information about `y`. This is represented by the `⊤` filter.
Note: `filter.tendsto_prod_top_iff` characterizes this convergence in uniform spaces.
See also `filter.prod_top` and `filter.mem_prod_top`. -/
theorem ContinuousAt.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (hh : g a ≠ 0 → ContinuousAt (↿h) (a, f a / g a))
    (h2h : g a = 0 → Tendsto (↿h) (𝓝 a ×ᶠ ⊤) (𝓝 (h a 0))) :
    ContinuousAt (fun x => h x (f x / g x)) a :=
  by
  show ContinuousAt (↿h ∘ fun x => (x, f x / g x)) a
  by_cases hga : g a = 0
  · rw [ContinuousAt]
    simp_rw [comp_app, hga, div_zero]
    exact (h2h hga).comp (continuous_at_id.prod_mk tendsto_top)
  · exact ContinuousAt.comp (hh hga) (continuous_at_id.prod (hf.div hg hga))
#align continuous_at.comp_div_cases ContinuousAt.comp_div_cases

/- warning: continuous.comp_div_cases -> Continuous.comp_div_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : GroupWithZero.{u3} G₀] [_inst_2 : TopologicalSpace.{u3} G₀] [_inst_3 : HasContinuousInv₀.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u3} G₀ (GroupWithZero.toDivInvMonoid.{u3} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u3} G₀ _inst_2 (MulZeroClass.toHasMul.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1))))] [_inst_5 : TopologicalSpace.{u1} α] [_inst_6 : TopologicalSpace.{u2} β] {f : α -> G₀} {g : α -> G₀} (h : α -> G₀ -> β), (Continuous.{u1, u3} α G₀ _inst_5 _inst_2 f) -> (Continuous.{u1, u3} α G₀ _inst_5 _inst_2 g) -> (forall (a : α), (Ne.{succ u3} G₀ (g a) (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1)))))))) -> (ContinuousAt.{max u1 u3, u2} (Prod.{u1, u3} α G₀) β (Prod.topologicalSpace.{u1, u3} α G₀ _inst_5 _inst_2) _inst_6 (Function.HasUncurry.uncurry.{max u1 u3 u2, max u1 u3, u2} (α -> G₀ -> β) (Prod.{u1, u3} α G₀) β (Function.hasUncurryInduction.{u1, max u3 u2, u3, u2} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u3, u2} G₀ β)) h) (Prod.mk.{u1, u3} α G₀ a (HDiv.hDiv.{u3, u3, u3} G₀ G₀ G₀ (instHDiv.{u3} G₀ (DivInvMonoid.toHasDiv.{u3} G₀ (GroupWithZero.toDivInvMonoid.{u3} G₀ _inst_1))) (f a) (g a))))) -> (forall (a : α), (Eq.{succ u3} G₀ (g a) (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1)))))))) -> (Filter.Tendsto.{max u1 u3, u2} (Prod.{u1, u3} α G₀) β (Function.HasUncurry.uncurry.{max u1 u3 u2, max u1 u3, u2} (α -> G₀ -> β) (Prod.{u1, u3} α G₀) β (Function.hasUncurryInduction.{u1, max u3 u2, u3, u2} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u3, u2} G₀ β)) h) (Filter.prod.{u1, u3} α G₀ (nhds.{u1} α _inst_5 a) (Top.top.{u3} (Filter.{u3} G₀) (Filter.hasTop.{u3} G₀))) (nhds.{u2} β _inst_6 (h a (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_1))))))))))) -> (Continuous.{u1, u2} α β _inst_5 _inst_6 (fun (x : α) => h x (HDiv.hDiv.{u3, u3, u3} G₀ G₀ G₀ (instHDiv.{u3} G₀ (DivInvMonoid.toHasDiv.{u3} G₀ (GroupWithZero.toDivInvMonoid.{u3} G₀ _inst_1))) (f x) (g x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)) (GroupWithZero.toInv.{u2} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] [_inst_5 : TopologicalSpace.{u3} α] [_inst_6 : TopologicalSpace.{u1} β] {f : α -> G₀} {g : α -> G₀} (h : α -> G₀ -> β), (Continuous.{u3, u2} α G₀ _inst_5 _inst_2 f) -> (Continuous.{u3, u2} α G₀ _inst_5 _inst_2 g) -> (forall (a : α), (Ne.{succ u2} G₀ (g a) (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) -> (ContinuousAt.{max u3 u2, u1} (Prod.{u3, u2} α G₀) β (instTopologicalSpaceProd.{u3, u2} α G₀ _inst_5 _inst_2) _inst_6 (Function.HasUncurry.uncurry.{max (max u3 u1) u2, max u3 u2, u1} (α -> G₀ -> β) (Prod.{u3, u2} α G₀) β (Function.hasUncurryInduction.{u3, max u1 u2, u2, u1} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u2, u1} G₀ β)) h) (Prod.mk.{u3, u2} α G₀ a (HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (GroupWithZero.toDiv.{u2} G₀ _inst_1)) (f a) (g a))))) -> (forall (a : α), (Eq.{succ u2} G₀ (g a) (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))) -> (Filter.Tendsto.{max u3 u2, u1} (Prod.{u3, u2} α G₀) β (Function.HasUncurry.uncurry.{max (max u3 u1) u2, max u3 u2, u1} (α -> G₀ -> β) (Prod.{u3, u2} α G₀) β (Function.hasUncurryInduction.{u3, max u1 u2, u2, u1} α (G₀ -> β) G₀ β (Function.hasUncurryBase.{u2, u1} G₀ β)) h) (Filter.prod.{u3, u2} α G₀ (nhds.{u3} α _inst_5 a) (Top.top.{u2} (Filter.{u2} G₀) (Filter.instTopFilter.{u2} G₀))) (nhds.{u1} β _inst_6 (h a (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) -> (Continuous.{u3, u1} α β _inst_5 _inst_6 (fun (x : α) => h x (HDiv.hDiv.{u2, u2, u2} G₀ G₀ G₀ (instHDiv.{u2} G₀ (GroupWithZero.toDiv.{u2} G₀ _inst_1)) (f x) (g x))))
Case conversion may be inaccurate. Consider using '#align continuous.comp_div_cases Continuous.comp_div_casesₓ'. -/
/-- `h x (f x / g x)` is continuous under certain conditions, even if the denominator is sometimes
  `0`. See docstring of `continuous_at.comp_div_cases`. -/
theorem Continuous.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : Continuous f)
    (hg : Continuous g) (hh : ∀ a, g a ≠ 0 → ContinuousAt (↿h) (a, f a / g a))
    (h2h : ∀ a, g a = 0 → Tendsto (↿h) (𝓝 a ×ᶠ ⊤) (𝓝 (h a 0))) :
    Continuous fun x => h x (f x / g x) :=
  continuous_iff_continuousAt.mpr fun a =>
    hf.ContinuousAt.comp_div_cases _ hg.ContinuousAt (hh a) (h2h a)
#align continuous.comp_div_cases Continuous.comp_div_cases

end Div

/-! ### Left and right multiplication as homeomorphisms -/


namespace Homeomorph

variable [TopologicalSpace α] [GroupWithZero α] [ContinuousMul α]

/- warning: homeomorph.mul_left₀ -> Homeomorph.mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α), (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Homeomorph.{u1, u1} α α _inst_1 _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α), (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) -> (Homeomorph.{u1, u1} α α _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_left₀ Homeomorph.mulLeft₀ₓ'. -/
/-- Left multiplication by a nonzero element in a `group_with_zero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mulLeft₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_mul_left _
    continuous_invFun := continuous_mul_left _ }
#align homeomorph.mul_left₀ Homeomorph.mulLeft₀

/- warning: homeomorph.mul_right₀ -> Homeomorph.mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α), (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Homeomorph.{u1, u1} α α _inst_1 _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α), (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) -> (Homeomorph.{u1, u1} α α _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_right₀ Homeomorph.mulRight₀ₓ'. -/
/-- Right multiplication by a nonzero element in a `group_with_zero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mulRight₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_right _
    continuous_invFun := continuous_mul_right _ }
#align homeomorph.mul_right₀ Homeomorph.mulRight₀

/- warning: homeomorph.coe_mul_left₀ -> Homeomorph.coe_mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))), Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) (fun (_x : Homeomorph.{u1, u1} α α _inst_1 _inst_1) => α -> α) (Homeomorph.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (Homeomorph.mulLeft₀.{u1} α _inst_1 _inst_2 _inst_3 c hc)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))), Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (Homeomorph.instEquivLikeHomeomorph.{u1, u1} α α _inst_1 _inst_1))) (Homeomorph.mulLeft₀.{u1} α _inst_1 _inst_2 _inst_3 c hc)) ((fun (x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2132 : α) (x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2134 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2132 x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2134) c)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_mul_left₀ Homeomorph.coe_mulLeft₀ₓ'. -/
@[simp]
theorem coe_mulLeft₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulLeft₀ c hc) = (· * ·) c :=
  rfl
#align homeomorph.coe_mul_left₀ Homeomorph.coe_mulLeft₀

/- warning: homeomorph.mul_left₀_symm_apply -> Homeomorph.mulLeft₀_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))), Eq.{succ u1} ((fun (_x : Homeomorph.{u1, u1} α α _inst_1 _inst_1) => α -> α) (Homeomorph.symm.{u1, u1} α α _inst_1 _inst_1 (Homeomorph.mulLeft₀.{u1} α _inst_1 _inst_2 _inst_3 c hc))) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) (fun (_x : Homeomorph.{u1, u1} α α _inst_1 _inst_1) => α -> α) (Homeomorph.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (Homeomorph.symm.{u1, u1} α α _inst_1 _inst_1 (Homeomorph.mulLeft₀.{u1} α _inst_1 _inst_2 _inst_3 c hc))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_2)) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))), Eq.{succ u1} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (Homeomorph.instEquivLikeHomeomorph.{u1, u1} α α _inst_1 _inst_1))) (Homeomorph.symm.{u1, u1} α α _inst_1 _inst_1 (Homeomorph.mulLeft₀.{u1} α _inst_1 _inst_2 _inst_3 c hc))) ((fun (x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2185 : α) (x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2187 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2185 x._@.Mathlib.Topology.Algebra.GroupWithZero._hyg.2187) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_2) c))
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_left₀_symm_apply Homeomorph.mulLeft₀_symm_applyₓ'. -/
@[simp]
theorem mulLeft₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulLeft₀ c hc).symm : α → α) = (· * ·) c⁻¹ :=
  rfl
#align homeomorph.mul_left₀_symm_apply Homeomorph.mulLeft₀_symm_apply

/- warning: homeomorph.coe_mul_right₀ -> Homeomorph.coe_mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))), Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) (fun (_x : Homeomorph.{u1, u1} α α _inst_1 _inst_1) => α -> α) (Homeomorph.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (Homeomorph.mulRight₀.{u1} α _inst_1 _inst_2 _inst_3 c hc)) (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) x c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))), Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (Homeomorph.instEquivLikeHomeomorph.{u1, u1} α α _inst_1 _inst_1))) (Homeomorph.mulRight₀.{u1} α _inst_1 _inst_2 _inst_3 c hc)) (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) x c)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_mul_right₀ Homeomorph.coe_mulRight₀ₓ'. -/
@[simp]
theorem coe_mulRight₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulRight₀ c hc) = fun x => x * c :=
  rfl
#align homeomorph.coe_mul_right₀ Homeomorph.coe_mulRight₀

/- warning: homeomorph.mul_right₀_symm_apply -> Homeomorph.mulRight₀_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))), Eq.{succ u1} ((fun (_x : Homeomorph.{u1, u1} α α _inst_1 _inst_1) => α -> α) (Homeomorph.symm.{u1, u1} α α _inst_1 _inst_1 (Homeomorph.mulRight₀.{u1} α _inst_1 _inst_2 _inst_3 c hc))) (coeFn.{succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) (fun (_x : Homeomorph.{u1, u1} α α _inst_1 _inst_1) => α -> α) (Homeomorph.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (Homeomorph.symm.{u1, u1} α α _inst_1 _inst_1 (Homeomorph.mulRight₀.{u1} α _inst_1 _inst_2 _inst_3 c hc))) (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_2)) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : ContinuousMul.{u1} α _inst_1 (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))] (c : α) (hc : Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))), Eq.{succ u1} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) α α (Homeomorph.instEquivLikeHomeomorph.{u1, u1} α α _inst_1 _inst_1))) (Homeomorph.symm.{u1, u1} α α _inst_1 _inst_1 (Homeomorph.mulRight₀.{u1} α _inst_1 _inst_2 _inst_3 c hc))) (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) x (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_2) c))
Case conversion may be inaccurate. Consider using '#align homeomorph.mul_right₀_symm_apply Homeomorph.mulRight₀_symm_applyₓ'. -/
@[simp]
theorem mulRight₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulRight₀ c hc).symm : α → α) = fun x => x * c⁻¹ :=
  rfl
#align homeomorph.mul_right₀_symm_apply Homeomorph.mulRight₀_symm_apply

end Homeomorph

section Zpow

variable [GroupWithZero G₀] [TopologicalSpace G₀] [HasContinuousInv₀ G₀] [ContinuousMul G₀]

/- warning: continuous_at_zpow₀ -> continuousAt_zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] (x : G₀) (m : Int), (Or (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m)) -> (ContinuousAt.{u1, u1} G₀ G₀ _inst_2 _inst_2 (fun (x : G₀) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x m) x)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] (x : G₀) (m : Int), (Or (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m)) -> (ContinuousAt.{u1, u1} G₀ G₀ _inst_2 _inst_2 (fun (x : G₀) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x m) x)
Case conversion may be inaccurate. Consider using '#align continuous_at_zpow₀ continuousAt_zpow₀ₓ'. -/
theorem continuousAt_zpow₀ (x : G₀) (m : ℤ) (h : x ≠ 0 ∨ 0 ≤ m) : ContinuousAt (fun x => x ^ m) x :=
  by
  cases m
  · simpa only [zpow_ofNat] using continuousAt_pow x m
  · simp only [zpow_negSucc]
    have hx : x ≠ 0 := h.resolve_right (Int.negSucc_lt_zero m).not_le
    exact (continuousAt_pow x (m + 1)).inv₀ (pow_ne_zero _ hx)
#align continuous_at_zpow₀ continuousAt_zpow₀

/- warning: continuous_on_zpow₀ -> continuousOn_zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] (m : Int), ContinuousOn.{u1, u1} G₀ G₀ _inst_2 _inst_2 (fun (x : G₀) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x m) (HasCompl.compl.{u1} (Set.{u1} G₀) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} G₀) (Set.booleanAlgebra.{u1} G₀)) (Singleton.singleton.{u1, u1} G₀ (Set.{u1} G₀) (Set.hasSingleton.{u1} G₀) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] (m : Int), ContinuousOn.{u1, u1} G₀ G₀ _inst_2 _inst_2 (fun (x : G₀) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x m) (HasCompl.compl.{u1} (Set.{u1} G₀) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} G₀) (Set.instBooleanAlgebraSet.{u1} G₀)) (Singleton.singleton.{u1, u1} G₀ (Set.{u1} G₀) (Set.instSingletonSet.{u1} G₀) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align continuous_on_zpow₀ continuousOn_zpow₀ₓ'. -/
theorem continuousOn_zpow₀ (m : ℤ) : ContinuousOn (fun x : G₀ => x ^ m) ({0}ᶜ) := fun x hx =>
  (continuousAt_zpow₀ _ _ (Or.inl hx)).ContinuousWithinAt
#align continuous_on_zpow₀ continuousOn_zpow₀

/- warning: filter.tendsto.zpow₀ -> Filter.Tendsto.zpow₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : GroupWithZero.{u2} G₀] [_inst_2 : TopologicalSpace.{u2} G₀] [_inst_3 : HasContinuousInv₀.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u2} G₀ _inst_2 (MulZeroClass.toHasMul.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1))))] {f : α -> G₀} {l : Filter.{u1} α} {a : G₀}, (Filter.Tendsto.{u1, u2} α G₀ f l (nhds.{u2} G₀ _inst_2 a)) -> (forall (m : Int), (Or (Ne.{succ u2} G₀ a (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_1)))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m)) -> (Filter.Tendsto.{u1, u2} α G₀ (fun (x : α) => HPow.hPow.{u2, 0, u2} G₀ Int G₀ (instHPow.{u2, 0} G₀ Int (DivInvMonoid.Pow.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) (f x) m) l (nhds.{u2} G₀ _inst_2 (HPow.hPow.{u2, 0, u2} G₀ Int G₀ (instHPow.{u2, 0} G₀ Int (DivInvMonoid.Pow.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_1))) a m))))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {f : α -> G₀} {l : Filter.{u2} α} {a : G₀}, (Filter.Tendsto.{u2, u1} α G₀ f l (nhds.{u1} G₀ _inst_2 a)) -> (forall (m : Int), (Or (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m)) -> (Filter.Tendsto.{u2, u1} α G₀ (fun (x : α) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) l (nhds.{u1} G₀ _inst_2 (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a m))))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.zpow₀ Filter.Tendsto.zpow₀ₓ'. -/
theorem Filter.Tendsto.zpow₀ {f : α → G₀} {l : Filter α} {a : G₀} (hf : Tendsto f l (𝓝 a)) (m : ℤ)
    (h : a ≠ 0 ∨ 0 ≤ m) : Tendsto (fun x => f x ^ m) l (𝓝 (a ^ m)) :=
  (continuousAt_zpow₀ _ m h).Tendsto.comp hf
#align filter.tendsto.zpow₀ Filter.Tendsto.zpow₀

variable {X : Type _} [TopologicalSpace X] {a : X} {s : Set X} {f : X → G₀}

/- warning: continuous_at.zpow₀ -> ContinuousAt.zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {a : X} {f : X -> G₀}, (ContinuousAt.{u2, u1} X G₀ _inst_5 _inst_2 f a) -> (forall (m : Int), (Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m)) -> (ContinuousAt.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) a))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {a : X} {f : X -> G₀}, (ContinuousAt.{u2, u1} X G₀ _inst_5 _inst_2 f a) -> (forall (m : Int), (Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m)) -> (ContinuousAt.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) a))
Case conversion may be inaccurate. Consider using '#align continuous_at.zpow₀ ContinuousAt.zpow₀ₓ'. -/
theorem ContinuousAt.zpow₀ (hf : ContinuousAt f a) (m : ℤ) (h : f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousAt (fun x => f x ^ m) a :=
  hf.zpow₀ m h
#align continuous_at.zpow₀ ContinuousAt.zpow₀

/- warning: continuous_within_at.zpow₀ -> ContinuousWithinAt.zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {a : X} {s : Set.{u2} X} {f : X -> G₀}, (ContinuousWithinAt.{u2, u1} X G₀ _inst_5 _inst_2 f s a) -> (forall (m : Int), (Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m)) -> (ContinuousWithinAt.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) s a))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {a : X} {s : Set.{u2} X} {f : X -> G₀}, (ContinuousWithinAt.{u2, u1} X G₀ _inst_5 _inst_2 f s a) -> (forall (m : Int), (Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m)) -> (ContinuousWithinAt.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) s a))
Case conversion may be inaccurate. Consider using '#align continuous_within_at.zpow₀ ContinuousWithinAt.zpow₀ₓ'. -/
theorem ContinuousWithinAt.zpow₀ (hf : ContinuousWithinAt f s a) (m : ℤ) (h : f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousWithinAt (fun x => f x ^ m) s a :=
  hf.zpow₀ m h
#align continuous_within_at.zpow₀ ContinuousWithinAt.zpow₀

/- warning: continuous_on.zpow₀ -> ContinuousOn.zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {s : Set.{u2} X} {f : X -> G₀}, (ContinuousOn.{u2, u1} X G₀ _inst_5 _inst_2 f s) -> (forall (m : Int), (forall (a : X), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) a s) -> (Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m))) -> (ContinuousOn.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) s))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {s : Set.{u2} X} {f : X -> G₀}, (ContinuousOn.{u2, u1} X G₀ _inst_5 _inst_2 f s) -> (forall (m : Int), (forall (a : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) a s) -> (Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m))) -> (ContinuousOn.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m) s))
Case conversion may be inaccurate. Consider using '#align continuous_on.zpow₀ ContinuousOn.zpow₀ₓ'. -/
theorem ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : ℤ) (h : ∀ a ∈ s, f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousOn (fun x => f x ^ m) s := fun a ha => (hf a ha).zpow₀ m (h a ha)
#align continuous_on.zpow₀ ContinuousOn.zpow₀

/- warning: continuous.zpow₀ -> Continuous.zpow₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {f : X -> G₀}, (Continuous.{u2, u1} X G₀ _inst_5 _inst_2 f) -> (forall (m : Int), (forall (a : X), Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m)) -> (Continuous.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : TopologicalSpace.{u1} G₀] [_inst_3 : HasContinuousInv₀.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)) (GroupWithZero.toInv.{u1} G₀ _inst_1) _inst_2] [_inst_4 : ContinuousMul.{u1} G₀ _inst_2 (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))] {X : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} X] {f : X -> G₀}, (Continuous.{u2, u1} X G₀ _inst_5 _inst_2 f) -> (forall (m : Int), (forall (a : X), Or (Ne.{succ u1} G₀ (f a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m)) -> (Continuous.{u2, u1} X G₀ _inst_5 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) m)))
Case conversion may be inaccurate. Consider using '#align continuous.zpow₀ Continuous.zpow₀ₓ'. -/
@[continuity]
theorem Continuous.zpow₀ (hf : Continuous f) (m : ℤ) (h0 : ∀ a, f a ≠ 0 ∨ 0 ≤ m) :
    Continuous fun x => f x ^ m :=
  continuous_iff_continuousAt.2 fun x => (hf.Tendsto x).zpow₀ m (h0 x)
#align continuous.zpow₀ Continuous.zpow₀

end Zpow

