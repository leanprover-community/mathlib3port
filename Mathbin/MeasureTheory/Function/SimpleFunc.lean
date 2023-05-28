/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module measure_theory.function.simple_func
! leanprover-community/mathlib commit 4280f5f32e16755ec7985ce11e189b6cd6ff6735
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Algebra.Support

/-!
# Simple functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function `f` from a measurable space to any type is called *simple*, if every preimage `f ⁻¹' {x}`
is measurable, and the range is finite. In this file, we define simple functions and establish their
basic properties; and we construct a sequence of simple functions approximating an arbitrary Borel
measurable function `f : α → ℝ≥0∞`.

The theorem `measurable.ennreal_induction` shows that in order to prove something for an arbitrary
measurable function into `ℝ≥0∞`, it is sufficient to show that the property holds for (multiples of)
characteristic functions and is closed under addition and supremum of increasing sequences of
functions.
-/


noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Classical Topology BigOperators NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type _}

#print MeasureTheory.SimpleFunc /-
/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (to_fun ⁻¹' {x})
  finite_range' : (Set.range to_fun).Finite
#align measure_theory.simple_func MeasureTheory.SimpleFunc
-/

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

#print MeasureTheory.SimpleFunc.instCoeFun /-
instance instCoeFun : CoeFun (α →ₛ β) fun _ => α → β :=
  ⟨toFun⟩
#align measure_theory.simple_func.has_coe_to_fun MeasureTheory.SimpleFunc.instCoeFun
-/

/- warning: measure_theory.simple_func.coe_injective -> MeasureTheory.SimpleFunc.coe_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {{f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}} {{g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}}, (Eq.{max (succ u1) (succ u2)} ((fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) g)) -> (Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {{f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β}} {{g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β}}, (Eq.{max (succ u2) (succ u1)} (α -> β) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β g)) -> (Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_injective MeasureTheory.SimpleFunc.coe_injectiveₓ'. -/
theorem coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g := by
  cases f <;> cases g <;> congr <;> exact H
#align measure_theory.simple_func.coe_injective MeasureTheory.SimpleFunc.coe_injective

/- warning: measure_theory.simple_func.ext -> MeasureTheory.SimpleFunc.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) g a)) -> (Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β} {g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β}, (forall (a : α), Eq.{succ u1} β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f a) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β g a)) -> (Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.ext MeasureTheory.SimpleFunc.extₓ'. -/
@[ext]
theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
  coe_injective <| funext H
#align measure_theory.simple_func.ext MeasureTheory.SimpleFunc.ext

/- warning: measure_theory.simple_func.finite_range -> MeasureTheory.SimpleFunc.finite_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Set.Finite.{u2} β (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Set.Finite.{u1} β (Set.range.{u1, succ u2} β α (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.finite_range MeasureTheory.SimpleFunc.finite_rangeₓ'. -/
theorem finite_range (f : α →ₛ β) : (Set.range f).Finite :=
  f.finite_range'
#align measure_theory.simple_func.finite_range MeasureTheory.SimpleFunc.finite_range

/- warning: measure_theory.simple_func.measurable_set_fiber -> MeasureTheory.SimpleFunc.measurableSet_fiber is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (x : β), MeasurableSet.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (x : β), MeasurableSet.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) x))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.measurable_set_fiber MeasureTheory.SimpleFunc.measurableSet_fiberₓ'. -/
theorem measurableSet_fiber (f : α →ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x
#align measure_theory.simple_func.measurable_set_fiber MeasureTheory.SimpleFunc.measurableSet_fiber

/- warning: measure_theory.simple_func.apply_mk -> MeasureTheory.SimpleFunc.apply_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> β) (h : forall (x : β), MeasurableSet.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) x))) (h' : Set.Finite.{u2} β (Set.range.{u2, succ u1} β α f)) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.mk.{u1, u2} α _inst_1 β f h h') x) (f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : α -> β) (h : forall (x : β), MeasurableSet.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) x))) (h' : Set.Finite.{u1} β (Set.range.{u1, succ u2} β α f)) (x : α), Eq.{succ u1} β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.mk.{u2, u1} α _inst_1 β f h h') x) (f x)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.apply_mk MeasureTheory.SimpleFunc.apply_mkₓ'. -/
@[simp]
theorem apply_mk (f : α → β) (h h') (x : α) : SimpleFunc.mk f h h' x = f x :=
  rfl
#align measure_theory.simple_func.apply_mk MeasureTheory.SimpleFunc.apply_mk

#print MeasureTheory.SimpleFunc.ofIsEmpty /-
/-- Simple function defined on the empty type. -/
def ofIsEmpty [IsEmpty α] : α →ₛ β where
  toFun := isEmptyElim
  measurableSet_fiber' x := Subsingleton.measurableSet
  finite_range' := by simp [range_eq_empty]
#align measure_theory.simple_func.of_is_empty MeasureTheory.SimpleFunc.ofIsEmpty
-/

#print MeasureTheory.SimpleFunc.range /-
/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range (f : α →ₛ β) : Finset β :=
  f.finite_range.toFinset
#align measure_theory.simple_func.range MeasureTheory.SimpleFunc.range
-/

/- warning: measure_theory.simple_func.mem_range -> MeasureTheory.SimpleFunc.mem_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β} {b : β}, Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f)) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b (Set.range.{u1, succ u2} β α (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.mem_range MeasureTheory.SimpleFunc.mem_rangeₓ'. -/
@[simp]
theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
  Finite.mem_toFinset _
#align measure_theory.simple_func.mem_range MeasureTheory.SimpleFunc.mem_range

/- warning: measure_theory.simple_func.mem_range_self -> MeasureTheory.SimpleFunc.mem_range_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (x : α), Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f x) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (x : α), Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f x) (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.mem_range_self MeasureTheory.SimpleFunc.mem_range_selfₓ'. -/
theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩
#align measure_theory.simple_func.mem_range_self MeasureTheory.SimpleFunc.mem_range_self

/- warning: measure_theory.simple_func.coe_range -> MeasureTheory.SimpleFunc.coe_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)) (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{succ u1} (Set.{u1} β) (Finset.toSet.{u1} β (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f)) (Set.range.{u1, succ u2} β α (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_range MeasureTheory.SimpleFunc.coe_rangeₓ'. -/
@[simp]
theorem coe_range (f : α →ₛ β) : (↑f.range : Set β) = Set.range f :=
  f.finite_range.coe_toFinset
#align measure_theory.simple_func.coe_range MeasureTheory.SimpleFunc.coe_range

/- warning: measure_theory.simple_func.mem_range_of_measure_ne_zero -> MeasureTheory.SimpleFunc.mem_range_of_measure_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {x : β} {μ : MeasureTheory.Measure.{u1} α _inst_1}, (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) x))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β} {x : β} {μ : MeasureTheory.Measure.{u2} α _inst_1}, (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) x))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.mem_range_of_measure_ne_zero MeasureTheory.SimpleFunc.mem_range_of_measure_ne_zeroₓ'. -/
theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
    x ∈ f.range :=
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩
#align measure_theory.simple_func.mem_range_of_measure_ne_zero MeasureTheory.SimpleFunc.mem_range_of_measure_ne_zero

/- warning: measure_theory.simple_func.forall_range_iff -> MeasureTheory.SimpleFunc.forall_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {p : β -> Prop}, Iff (forall (y : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)) -> (p y)) (forall (x : α), p (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β} {p : β -> Prop}, Iff (forall (y : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f)) -> (p y)) (forall (x : α), p (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f x))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.forall_range_iff MeasureTheory.SimpleFunc.forall_range_iffₓ'. -/
theorem forall_range_iff {f : α →ₛ β} {p : β → Prop} : (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) := by
  simp only [mem_range, Set.forall_range_iff]
#align measure_theory.simple_func.forall_range_iff MeasureTheory.SimpleFunc.forall_range_iff

/- warning: measure_theory.simple_func.exists_range_iff -> MeasureTheory.SimpleFunc.exists_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {p : β -> Prop}, Iff (Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)) => p y))) (Exists.{succ u1} α (fun (x : α) => p (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β} {p : β -> Prop}, Iff (Exists.{succ u1} β (fun (y : β) => And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f)) (p y))) (Exists.{succ u2} α (fun (x : α) => p (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.exists_range_iff MeasureTheory.SimpleFunc.exists_range_iffₓ'. -/
theorem exists_range_iff {f : α →ₛ β} {p : β → Prop} : (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) := by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff
#align measure_theory.simple_func.exists_range_iff MeasureTheory.SimpleFunc.exists_range_iff

/- warning: measure_theory.simple_func.preimage_eq_empty_iff -> MeasureTheory.SimpleFunc.preimage_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (b : β), Iff (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (b : β), Iff (Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Not (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.preimage_eq_empty_iff MeasureTheory.SimpleFunc.preimage_eq_empty_iffₓ'. -/
theorem preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
  preimage_singleton_eq_empty.trans <| not_congr mem_range.symm
#align measure_theory.simple_func.preimage_eq_empty_iff MeasureTheory.SimpleFunc.preimage_eq_empty_iff

/- warning: measure_theory.simple_func.exists_forall_le -> MeasureTheory.SimpleFunc.exists_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : Preorder.{u2} β] [_inst_4 : IsDirected.{u2} β (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_3))] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Exists.{succ u2} β (fun (C : β) => forall (x : α), LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_3) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f x) C)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : Preorder.{u2} β] [_inst_4 : IsDirected.{u2} β (fun (x._@.Mathlib.MeasureTheory.Function.SimpleFunc._hyg.1377 : β) (x._@.Mathlib.MeasureTheory.Function.SimpleFunc._hyg.1379 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_3) x._@.Mathlib.MeasureTheory.Function.SimpleFunc._hyg.1377 x._@.Mathlib.MeasureTheory.Function.SimpleFunc._hyg.1379)] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Exists.{succ u2} β (fun (C : β) => forall (x : α), LE.le.{u2} β (Preorder.toLE.{u2} β _inst_3) (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 β f x) C)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.exists_forall_le MeasureTheory.SimpleFunc.exists_forall_leₓ'. -/
theorem exists_forall_le [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] (f : α →ₛ β) :
    ∃ C, ∀ x, f x ≤ C :=
  f.range.exists_le.imp fun C => forall_range_iff.1
#align measure_theory.simple_func.exists_forall_le MeasureTheory.SimpleFunc.exists_forall_le

#print MeasureTheory.SimpleFunc.const /-
/-- Constant function as a `simple_func`. -/
def const (α) {β} [MeasurableSpace α] (b : β) : α →ₛ β :=
  ⟨fun a => b, fun x => MeasurableSet.const _, finite_range_const⟩
#align measure_theory.simple_func.const MeasureTheory.SimpleFunc.const
-/

instance [Inhabited β] : Inhabited (α →ₛ β) :=
  ⟨const _ default⟩

#print MeasureTheory.SimpleFunc.const_apply /-
theorem const_apply (a : α) (b : β) : (const α b) a = b :=
  rfl
#align measure_theory.simple_func.const_apply MeasureTheory.SimpleFunc.const_apply
-/

/- warning: measure_theory.simple_func.coe_const -> MeasureTheory.SimpleFunc.coe_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (b : β), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1 b)) (Function.const.{succ u2, succ u1} β α b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (b : β), Eq.{max (succ u2) (succ u1)} (α -> β) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.const.{u2, u1} α β _inst_1 b)) (Function.const.{succ u1, succ u2} β α b)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_const MeasureTheory.SimpleFunc.coe_constₓ'. -/
@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align measure_theory.simple_func.coe_const MeasureTheory.SimpleFunc.coe_const

#print MeasureTheory.SimpleFunc.range_const /-
@[simp]
theorem range_const (α) [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).range = {b} :=
  Finset.coe_injective <| by simp
#align measure_theory.simple_func.range_const MeasureTheory.SimpleFunc.range_const
-/

#print MeasureTheory.SimpleFunc.range_const_subset /-
theorem range_const_subset (α) [MeasurableSpace α] (b : β) : (const α b).range ⊆ {b} :=
  Finset.coe_subset.1 <| by simp
#align measure_theory.simple_func.range_const_subset MeasureTheory.SimpleFunc.range_const_subset
-/

/- warning: measure_theory.simple_func.simple_func_bot -> MeasureTheory.SimpleFunc.simpleFunc_bot is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} (f : MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α))) β) [_inst_2 : Nonempty.{succ u1} β], Exists.{succ u1} β (fun (c : β) => forall (x : α), Eq.{succ u1} β (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α))) β) (fun (_x : MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α))) β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u2, u1} α β (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α)))) f x) c)
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} (f : MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) β) [_inst_2 : Nonempty.{succ u1} β], Exists.{succ u1} β (fun (c : β) => forall (x : α), Eq.{succ u1} β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) β f x) c)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.simple_func_bot MeasureTheory.SimpleFunc.simpleFunc_botₓ'. -/
theorem simpleFunc_bot {α} (f : @SimpleFunc α ⊥ β) [Nonempty β] : ∃ c, ∀ x, f x = c :=
  by
  have hf_meas := @simple_func.measurable_set_fiber α _ ⊥ f
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  cases isEmpty_or_nonempty α
  · simp only [IsEmpty.forall_iff, exists_const]
  · specialize hf_meas (f h.some)
    cases hf_meas
    · exfalso
      refine' Set.not_mem_empty h.some _
      rw [← hf_meas, Set.mem_preimage]
      exact Set.mem_singleton _
    · refine' ⟨f h.some, fun x => _⟩
      have : x ∈ f ⁻¹' {f h.some} := by rw [hf_meas]; exact Set.mem_univ x
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
#align measure_theory.simple_func.simple_func_bot MeasureTheory.SimpleFunc.simpleFunc_bot

/- warning: measure_theory.simple_func.simple_func_bot' -> MeasureTheory.SimpleFunc.simpleFunc_bot' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : Nonempty.{succ u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α))) β), Exists.{succ u1} β (fun (c : β) => Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α))) β) f (MeasureTheory.SimpleFunc.const.{u2, u1} α β (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toHasBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.completeLattice.{u2} α))) c))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : Nonempty.{succ u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) β), Exists.{succ u1} β (fun (c : β) => Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u2, u1} α (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) β) f (MeasureTheory.SimpleFunc.const.{u2, u1} α β (Bot.bot.{u2} (MeasurableSpace.{u2} α) (CompleteLattice.toBot.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u2} α))) c))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.simple_func_bot' MeasureTheory.SimpleFunc.simpleFunc_bot'ₓ'. -/
theorem simpleFunc_bot' {α} [Nonempty β] (f : @SimpleFunc α ⊥ β) :
    ∃ c, f = @SimpleFunc.const α _ ⊥ c :=
  by
  obtain ⟨c, h_eq⟩ := simple_func_bot f
  refine' ⟨c, _⟩
  ext1 x
  rw [h_eq x, simple_func.coe_const]
#align measure_theory.simple_func.simple_func_bot' MeasureTheory.SimpleFunc.simpleFunc_bot'

/- warning: measure_theory.simple_func.measurable_set_cut -> MeasureTheory.SimpleFunc.measurableSet_cut is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (r : α -> β -> Prop) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), (forall (b : β), MeasurableSet.{u1} α _inst_1 (setOf.{u1} α (fun (a : α) => r a b))) -> (MeasurableSet.{u1} α _inst_1 (setOf.{u1} α (fun (a : α) => r a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (r : α -> β -> Prop) (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), (forall (b : β), MeasurableSet.{u2} α _inst_1 (setOf.{u2} α (fun (a : α) => r a b))) -> (MeasurableSet.{u2} α _inst_1 (setOf.{u2} α (fun (a : α) => r a (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.measurable_set_cut MeasureTheory.SimpleFunc.measurableSet_cutₓ'. -/
theorem measurableSet_cut (r : α → β → Prop) (f : α →ₛ β) (h : ∀ b, MeasurableSet { a | r a b }) :
    MeasurableSet { a | r a (f a) } :=
  by
  have : { a | r a (f a) } = ⋃ b ∈ range f, { a | r a b } ∩ f ⁻¹' {b} :=
    by
    ext a
    suffices r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  exact
    MeasurableSet.biUnion f.finite_range.countable fun b _ =>
      MeasurableSet.inter (h b) (f.measurable_set_fiber _)
#align measure_theory.simple_func.measurable_set_cut MeasureTheory.SimpleFunc.measurableSet_cut

/- warning: measure_theory.simple_func.measurable_set_preimage -> MeasureTheory.SimpleFunc.measurableSet_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (s : Set.{u2} β), MeasurableSet.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (s : Set.{u1} β), MeasurableSet.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.measurable_set_preimage MeasureTheory.SimpleFunc.measurableSet_preimageₓ'. -/
@[measurability]
theorem measurableSet_preimage (f : α →ₛ β) (s) : MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ b => b ∈ s) f fun b => MeasurableSet.const (b ∈ s)
#align measure_theory.simple_func.measurable_set_preimage MeasureTheory.SimpleFunc.measurableSet_preimage

#print MeasureTheory.SimpleFunc.measurable /-
/-- A simple function is measurable -/
@[measurability]
protected theorem measurable [MeasurableSpace β] (f : α →ₛ β) : Measurable f := fun s _ =>
  measurableSet_preimage f s
#align measure_theory.simple_func.measurable MeasureTheory.SimpleFunc.measurable
-/

#print MeasureTheory.SimpleFunc.aemeasurable /-
@[measurability]
protected theorem aemeasurable [MeasurableSpace β] {μ : Measure α} (f : α →ₛ β) :
    AEMeasurable f μ :=
  f.Measurable.AEMeasurable
#align measure_theory.simple_func.ae_measurable MeasureTheory.SimpleFunc.aemeasurable
-/

/- warning: measure_theory.simple_func.sum_measure_preimage_singleton -> MeasureTheory.SimpleFunc.sum_measure_preimage_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) {μ : MeasureTheory.Measure.{u1} α _inst_1} (s : Finset.{u2} β), Eq.{1} ENNReal (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (y : β) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y)))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) {μ : MeasureTheory.Measure.{u2} α _inst_1} (s : Finset.{u1} β), Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (y : β) => MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y)))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Finset.toSet.{u1} β s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.sum_measure_preimage_singleton MeasureTheory.SimpleFunc.sum_measure_preimage_singletonₓ'. -/
protected theorem sum_measure_preimage_singleton (f : α →ₛ β) {μ : Measure α} (s : Finset β) :
    (∑ y in s, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _
#align measure_theory.simple_func.sum_measure_preimage_singleton MeasureTheory.SimpleFunc.sum_measure_preimage_singleton

/- warning: measure_theory.simple_func.sum_range_measure_preimage_singleton -> MeasureTheory.SimpleFunc.sum_range_measure_preimage_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (μ : MeasureTheory.Measure.{u1} α _inst_1), Eq.{1} ENNReal (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f) (fun (y : β) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y)))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (μ : MeasureTheory.Measure.{u2} α _inst_1), Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f) (fun (y : β) => MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y)))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 μ) (Set.univ.{u2} α))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.sum_range_measure_preimage_singleton MeasureTheory.SimpleFunc.sum_range_measure_preimage_singletonₓ'. -/
theorem sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : Measure α) :
    (∑ y in f.range, μ (f ⁻¹' {y})) = μ univ := by
  rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]
#align measure_theory.simple_func.sum_range_measure_preimage_singleton MeasureTheory.SimpleFunc.sum_range_measure_preimage_singleton

#print MeasureTheory.SimpleFunc.piecewise /-
/-- If-then-else as a `simple_func`. -/
def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α →ₛ β) : α →ₛ β :=
  ⟨s.piecewise f g, fun x =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).Subset range_ite_subset⟩
#align measure_theory.simple_func.piecewise MeasureTheory.SimpleFunc.piecewise
-/

/- warning: measure_theory.simple_func.coe_piecewise -> MeasureTheory.SimpleFunc.coe_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 s hs f g)) (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) g) (fun (j : α) => Classical.propDecidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {s : Set.{u2} α} (hs : MeasurableSet.{u2} α _inst_1 s) (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (α -> β) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 s hs f g)) (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β g) (fun (j : α) => Classical.propDecidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_piecewise MeasureTheory.SimpleFunc.coe_piecewiseₓ'. -/
@[simp]
theorem coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) :
    ⇑(piecewise s hs f g) = s.piecewise f g :=
  rfl
#align measure_theory.simple_func.coe_piecewise MeasureTheory.SimpleFunc.coe_piecewise

/- warning: measure_theory.simple_func.piecewise_apply -> MeasureTheory.SimpleFunc.piecewise_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 s hs f g) a) (ite.{succ u2} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Classical.propDecidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) g a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {s : Set.{u2} α} (hs : MeasurableSet.{u2} α _inst_1 s) (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (a : α), Eq.{succ u1} β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 s hs f g) a) (ite.{succ u1} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (Classical.propDecidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f a) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β g a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.piecewise_apply MeasureTheory.SimpleFunc.piecewise_applyₓ'. -/
theorem piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) (a) :
    piecewise s hs f g a = if a ∈ s then f a else g a :=
  rfl
#align measure_theory.simple_func.piecewise_apply MeasureTheory.SimpleFunc.piecewise_apply

/- warning: measure_theory.simple_func.piecewise_compl -> MeasureTheory.SimpleFunc.piecewise_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) hs f g) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 s (MeasurableSet.of_compl.{u1} α s _inst_1 hs) g f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {s : Set.{u2} α} (hs : MeasurableSet.{u2} α _inst_1 (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) hs f g) (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 s (MeasurableSet.of_compl.{u2} α s _inst_1 hs) g f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.piecewise_compl MeasureTheory.SimpleFunc.piecewise_complₓ'. -/
@[simp]
theorem piecewise_compl {s : Set α} (hs : MeasurableSet (sᶜ)) (f g : α →ₛ β) :
    piecewise (sᶜ) hs f g = piecewise s hs.ofCompl g f :=
  coe_injective <| by simp [hs]
#align measure_theory.simple_func.piecewise_compl MeasureTheory.SimpleFunc.piecewise_compl

/- warning: measure_theory.simple_func.piecewise_univ -> MeasureTheory.SimpleFunc.piecewise_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 (Set.univ.{u1} α) (MeasurableSet.univ.{u1} α _inst_1) f g) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 (Set.univ.{u2} α) (MeasurableSet.univ.{u2} α _inst_1) f g) f
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.piecewise_univ MeasureTheory.SimpleFunc.piecewise_univₓ'. -/
@[simp]
theorem piecewise_univ (f g : α →ₛ β) : piecewise univ MeasurableSet.univ f g = f :=
  coe_injective <| by simp
#align measure_theory.simple_func.piecewise_univ MeasureTheory.SimpleFunc.piecewise_univ

/- warning: measure_theory.simple_func.piecewise_empty -> MeasureTheory.SimpleFunc.piecewise_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (MeasurableSet.empty.{u1} α _inst_1) f g) g
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)) (MeasurableSet.empty.{u2} α _inst_1) f g) g
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.piecewise_empty MeasureTheory.SimpleFunc.piecewise_emptyₓ'. -/
@[simp]
theorem piecewise_empty (f g : α →ₛ β) : piecewise ∅ MeasurableSet.empty f g = g :=
  coe_injective <| by simp
#align measure_theory.simple_func.piecewise_empty MeasureTheory.SimpleFunc.piecewise_empty

/- warning: measure_theory.simple_func.support_indicator -> MeasureTheory.SimpleFunc.support_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 s hs f (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1 (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Function.support.{u1, u2} α β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α β _inst_2 (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 β (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 s hs f (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1 (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_2)))))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Function.support.{u1, u2} α β _inst_2 (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 β f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.support_indicator MeasureTheory.SimpleFunc.support_indicatorₓ'. -/
theorem support_indicator [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α →ₛ β) :
    Function.support (f.piecewise s hs (SimpleFunc.const α 0)) = s ∩ Function.support f :=
  Set.support_indicator
#align measure_theory.simple_func.support_indicator MeasureTheory.SimpleFunc.support_indicator

/- warning: measure_theory.simple_func.range_indicator -> MeasureTheory.SimpleFunc.range_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s), (Set.Nonempty.{u1} α s) -> (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α)) -> (forall (x : β) (y : β), Eq.{succ u2} (Finset.{u2} β) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α β _inst_1 s hs (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1 x) (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1 y))) (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b))) x (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) y)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {s : Set.{u2} α} (hs : MeasurableSet.{u2} α _inst_1 s), (Set.Nonempty.{u2} α s) -> (Ne.{succ u2} (Set.{u2} α) s (Set.univ.{u2} α)) -> (forall (x : β) (y : β), Eq.{succ u1} (Finset.{u1} β) (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α β _inst_1 s hs (MeasureTheory.SimpleFunc.const.{u2, u1} α β _inst_1 x) (MeasureTheory.SimpleFunc.const.{u2, u1} α β _inst_1 y))) (Insert.insert.{u1, u1} β (Finset.{u1} β) (Finset.instInsertFinset.{u1} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b))) x (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) y)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.range_indicator MeasureTheory.SimpleFunc.range_indicatorₓ'. -/
theorem range_indicator {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
    (hs_ne_univ : s ≠ univ) (x y : β) : (piecewise s hs (const α x) (const α y)).range = {x, y} :=
  by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union]
#align measure_theory.simple_func.range_indicator MeasureTheory.SimpleFunc.range_indicator

/- warning: measure_theory.simple_func.measurable_bind -> MeasureTheory.SimpleFunc.measurable_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u3} γ] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : β -> α -> γ), (forall (b : β), Measurable.{u1, u3} α γ _inst_1 _inst_2 (g b)) -> (Measurable.{u1, u3} α γ _inst_1 _inst_2 (fun (a : α) => g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u3} γ] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (g : β -> α -> γ), (forall (b : β), Measurable.{u2, u3} α γ _inst_1 _inst_2 (g b)) -> (Measurable.{u2, u3} α γ _inst_1 _inst_2 (fun (a : α) => g (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f a) a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.measurable_bind MeasureTheory.SimpleFunc.measurable_bindₓ'. -/
theorem measurable_bind [MeasurableSpace γ] (f : α →ₛ β) (g : β → α → γ)
    (hg : ∀ b, Measurable (g b)) : Measurable fun a => g (f a) a := fun s hs =>
  f.measurableSet_cut (fun a b => g b a ∈ s) fun b => hg b hs
#align measure_theory.simple_func.measurable_bind MeasureTheory.SimpleFunc.measurable_bind

#print MeasureTheory.SimpleFunc.bind /-
/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
  ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
    (f.finite_range.biUnion fun b _ => (g b).finite_range).Subset <| by
      rintro _ ⟨a, rfl⟩ <;> simp <;> exact ⟨a, a, rfl⟩⟩
#align measure_theory.simple_func.bind MeasureTheory.SimpleFunc.bind
-/

/- warning: measure_theory.simple_func.bind_apply -> MeasureTheory.SimpleFunc.bind_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : β -> (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ)) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.bind.{u1, u2, u3} α β γ _inst_1 f g) a) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a)) a)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (g : β -> (MeasureTheory.SimpleFunc.{u3, u1} α _inst_1 γ)) (a : α), Eq.{succ u1} γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (MeasureTheory.SimpleFunc.bind.{u3, u2, u1} α β γ _inst_1 f g) a) (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (g (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f a)) a)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.bind_apply MeasureTheory.SimpleFunc.bind_applyₓ'. -/
@[simp]
theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) : f.bind g a = g (f a) a :=
  rfl
#align measure_theory.simple_func.bind_apply MeasureTheory.SimpleFunc.bind_apply

#print MeasureTheory.SimpleFunc.map /-
/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ :=
  bind f (const α ∘ g)
#align measure_theory.simple_func.map MeasureTheory.SimpleFunc.map
-/

/- warning: measure_theory.simple_func.map_apply -> MeasureTheory.SimpleFunc.map_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (g : β -> γ) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f) a) (g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (g : β -> γ) (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (a : α), Eq.{succ u1} γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (MeasureTheory.SimpleFunc.map.{u3, u2, u1} α β γ _inst_1 g f) a) (g (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_apply MeasureTheory.SimpleFunc.map_applyₓ'. -/
theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) :=
  rfl
#align measure_theory.simple_func.map_apply MeasureTheory.SimpleFunc.map_apply

/- warning: measure_theory.simple_func.map_map -> MeasureTheory.SimpleFunc.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] (g : β -> γ) (h : γ -> δ) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u4)} (MeasureTheory.SimpleFunc.{u1, u4} α _inst_1 δ) (MeasureTheory.SimpleFunc.map.{u1, u3, u4} α γ δ _inst_1 h (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f)) (MeasureTheory.SimpleFunc.map.{u1, u2, u4} α β δ _inst_1 (Function.comp.{succ u2, succ u3, succ u4} β γ δ h g) f)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u1}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u4} α] (g : β -> γ) (h : γ -> δ) (f : MeasureTheory.SimpleFunc.{u4, u3} α _inst_1 β), Eq.{max (succ u4) (succ u2)} (MeasureTheory.SimpleFunc.{u4, u2} α _inst_1 δ) (MeasureTheory.SimpleFunc.map.{u4, u1, u2} α γ δ _inst_1 h (MeasureTheory.SimpleFunc.map.{u4, u3, u1} α β γ _inst_1 g f)) (MeasureTheory.SimpleFunc.map.{u4, u3, u2} α β δ _inst_1 (Function.comp.{succ u3, succ u1, succ u2} β γ δ h g) f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_map MeasureTheory.SimpleFunc.map_mapₓ'. -/
theorem map_map (g : β → γ) (h : γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) :=
  rfl
#align measure_theory.simple_func.map_map MeasureTheory.SimpleFunc.map_map

/- warning: measure_theory.simple_func.coe_map -> MeasureTheory.SimpleFunc.coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (g : β -> γ) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u3)} ((fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f)) (Function.comp.{succ u1, succ u2, succ u3} α β γ g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (g : β -> γ) (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β), Eq.{max (succ u3) (succ u1)} (α -> γ) (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (MeasureTheory.SimpleFunc.map.{u3, u2, u1} α β γ _inst_1 g f)) (Function.comp.{succ u3, succ u2, succ u1} α β γ g (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_map MeasureTheory.SimpleFunc.coe_mapₓ'. -/
@[simp]
theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f :=
  rfl
#align measure_theory.simple_func.coe_map MeasureTheory.SimpleFunc.coe_map

/- warning: measure_theory.simple_func.range_map -> MeasureTheory.SimpleFunc.range_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : DecidableEq.{succ u3} γ] (g : β -> γ) (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{succ u3} (Finset.{u3} γ) (MeasureTheory.SimpleFunc.range.{u1, u3} α γ _inst_1 (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f)) (Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) g (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : DecidableEq.{succ u3} γ] (g : β -> γ) (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{succ u3} (Finset.{u3} γ) (MeasureTheory.SimpleFunc.range.{u2, u3} α γ _inst_1 (MeasureTheory.SimpleFunc.map.{u2, u1, u3} α β γ _inst_1 g f)) (Finset.image.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) g (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.range_map MeasureTheory.SimpleFunc.range_mapₓ'. -/
@[simp]
theorem range_map [DecidableEq γ] (g : β → γ) (f : α →ₛ β) : (f.map g).range = f.range.image g :=
  Finset.coe_injective <| by simp only [coe_range, coe_map, Finset.coe_image, range_comp]
#align measure_theory.simple_func.range_map MeasureTheory.SimpleFunc.range_map

/- warning: measure_theory.simple_func.map_const -> MeasureTheory.SimpleFunc.map_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (g : β -> γ) (b : β), Eq.{max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1 b)) (MeasureTheory.SimpleFunc.const.{u1, u3} α γ _inst_1 (g b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u3} α] (g : β -> γ) (b : β), Eq.{max (succ u3) (succ u2)} (MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.map.{u3, u1, u2} α β γ _inst_1 g (MeasureTheory.SimpleFunc.const.{u3, u1} α β _inst_1 b)) (MeasureTheory.SimpleFunc.const.{u3, u2} α γ _inst_1 (g b))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_const MeasureTheory.SimpleFunc.map_constₓ'. -/
@[simp]
theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) :=
  rfl
#align measure_theory.simple_func.map_const MeasureTheory.SimpleFunc.map_const

/- warning: measure_theory.simple_func.map_preimage -> MeasureTheory.SimpleFunc.map_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : β -> γ) (s : Set.{u3} γ), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u3} α γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f)) s) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.filter.{u2} β (fun (b : β) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (g b) s) (fun (a : β) => Classical.propDecidable ((fun (b : β) => Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (g b) s) a)) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (g : β -> γ) (s : Set.{u1} γ), Eq.{succ u3} (Set.{u3} α) (Set.preimage.{u3, u1} α γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (MeasureTheory.SimpleFunc.map.{u3, u2, u1} α β γ _inst_1 g f)) s) (Set.preimage.{u3, u2} α β (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f) (Finset.toSet.{u2} β (Finset.filter.{u2} β (fun (b : β) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) (g b) s) (fun (a : β) => Classical.propDecidable ((fun (b : β) => Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) (g b) s) a)) (MeasureTheory.SimpleFunc.range.{u3, u2} α β _inst_1 f))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_preimage MeasureTheory.SimpleFunc.map_preimageₓ'. -/
theorem map_preimage (f : α →ₛ β) (g : β → γ) (s : Set γ) :
    f.map g ⁻¹' s = f ⁻¹' ↑(f.range.filterₓ fun b => g b ∈ s) :=
  by
  simp only [coe_range, sep_mem_eq, Set.mem_range, Function.comp_apply, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range]
  apply preimage_comp
#align measure_theory.simple_func.map_preimage MeasureTheory.SimpleFunc.map_preimage

/- warning: measure_theory.simple_func.map_preimage_singleton -> MeasureTheory.SimpleFunc.map_preimage_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : β -> γ) (c : γ), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u3} α γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f)) (Singleton.singleton.{u3, u3} γ (Set.{u3} γ) (Set.hasSingleton.{u3} γ) c)) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.filter.{u2} β (fun (b : β) => Eq.{succ u3} γ (g b) c) (fun (a : β) => Classical.propDecidable ((fun (b : β) => Eq.{succ u3} γ (g b) c) a)) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (g : β -> γ) (c : γ), Eq.{succ u3} (Set.{u3} α) (Set.preimage.{u3, u1} α γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (MeasureTheory.SimpleFunc.map.{u3, u2, u1} α β γ _inst_1 g f)) (Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.instSingletonSet.{u1} γ) c)) (Set.preimage.{u3, u2} α β (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f) (Finset.toSet.{u2} β (Finset.filter.{u2} β (fun (b : β) => Eq.{succ u1} γ (g b) c) (fun (a : β) => Classical.propDecidable ((fun (b : β) => Eq.{succ u1} γ (g b) c) a)) (MeasureTheory.SimpleFunc.range.{u3, u2} α β _inst_1 f))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_preimage_singleton MeasureTheory.SimpleFunc.map_preimage_singletonₓ'. -/
theorem map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑(f.range.filterₓ fun b => g b = c) :=
  map_preimage _ _ _
#align measure_theory.simple_func.map_preimage_singleton MeasureTheory.SimpleFunc.map_preimage_singleton

#print MeasureTheory.SimpleFunc.comp /-
/-- Composition of a `simple_fun` and a measurable function is a `simple_func`. -/
def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ
    where
  toFun := f ∘ g
  finite_range' := f.finite_range.Subset <| Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)
#align measure_theory.simple_func.comp MeasureTheory.SimpleFunc.comp
-/

/- warning: measure_theory.simple_func.coe_comp -> MeasureTheory.SimpleFunc.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) {g : α -> β} (hgm : Measurable.{u1, u2} α β _inst_1 _inst_2 g), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 f g hgm)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) (fun (_x : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) => β -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u2, u3} β γ _inst_2) f) g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u3} β] (f : MeasureTheory.SimpleFunc.{u3, u2} β _inst_2 γ) {g : α -> β} (hgm : Measurable.{u1, u3} α β _inst_1 _inst_2 g), Eq.{max (succ u1) (succ u2)} (α -> γ) (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 γ (MeasureTheory.SimpleFunc.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 f g hgm)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (MeasureTheory.SimpleFunc.toFun.{u3, u2} β _inst_2 γ f) g)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_comp MeasureTheory.SimpleFunc.coe_compₓ'. -/
@[simp]
theorem coe_comp [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    ⇑(f.comp g hgm) = f ∘ g :=
  rfl
#align measure_theory.simple_func.coe_comp MeasureTheory.SimpleFunc.coe_comp

/- warning: measure_theory.simple_func.range_comp_subset_range -> MeasureTheory.SimpleFunc.range_comp_subset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) {g : α -> β} (hgm : Measurable.{u1, u2} α β _inst_1 _inst_2 g), HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (MeasureTheory.SimpleFunc.range.{u1, u3} α γ _inst_1 (MeasureTheory.SimpleFunc.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 f g hgm)) (MeasureTheory.SimpleFunc.range.{u2, u3} β γ _inst_2 f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u3} β] (f : MeasureTheory.SimpleFunc.{u3, u2} β _inst_2 γ) {g : α -> β} (hgm : Measurable.{u1, u3} α β _inst_1 _inst_2 g), HasSubset.Subset.{u2} (Finset.{u2} γ) (Finset.instHasSubsetFinset.{u2} γ) (MeasureTheory.SimpleFunc.range.{u1, u2} α γ _inst_1 (MeasureTheory.SimpleFunc.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 f g hgm)) (MeasureTheory.SimpleFunc.range.{u3, u2} β γ _inst_2 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.range_comp_subset_range MeasureTheory.SimpleFunc.range_comp_subset_rangeₓ'. -/
theorem range_comp_subset_range [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    (f.comp g hgm).range ⊆ f.range :=
  Finset.coe_subset.1 <| by simp only [coe_range, coe_comp, Set.range_comp_subset_range]
#align measure_theory.simple_func.range_comp_subset_range MeasureTheory.SimpleFunc.range_comp_subset_range

#print MeasureTheory.SimpleFunc.extend /-
/-- Extend a `simple_func` along a measurable embedding: `f₁.extend g hg f₂` is the function
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`. -/
def extend [MeasurableSpace β] (f₁ : α →ₛ γ) (g : α → β) (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : β →ₛ γ where
  toFun := Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.Subset (image_subset_range _ _)).Subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    letI : MeasurableSpace γ := ⊤; haveI : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurable_set_singleton _)
#align measure_theory.simple_func.extend MeasureTheory.SimpleFunc.extend
-/

/- warning: measure_theory.simple_func.extend_apply -> MeasureTheory.SimpleFunc.extend_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f₁ : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) (x : α), Eq.{succ u3} γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) (fun (_x : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) => β -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u2, u3} β γ _inst_2) (MeasureTheory.SimpleFunc.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 f₁ g hg f₂) (g x)) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) f₁ x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u3} β] (f₁ : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u2, u3} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u3, u1} β _inst_2 γ) (x : α), Eq.{succ u1} γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} β _inst_2 γ (MeasureTheory.SimpleFunc.extend.{u2, u3, u1} α β γ _inst_1 _inst_2 f₁ g hg f₂) (g x)) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 γ f₁ x)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.extend_apply MeasureTheory.SimpleFunc.extend_applyₓ'. -/
@[simp]
theorem extend_apply [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
  hg.Injective.extend_apply _ _ _
#align measure_theory.simple_func.extend_apply MeasureTheory.SimpleFunc.extend_apply

/- warning: measure_theory.simple_func.extend_apply' -> MeasureTheory.SimpleFunc.extend_apply' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f₁ : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) {y : β}, (Not (Exists.{succ u1} α (fun (x : α) => Eq.{succ u2} β (g x) y))) -> (Eq.{succ u3} γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) (fun (_x : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) => β -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u2, u3} β γ _inst_2) (MeasureTheory.SimpleFunc.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 f₁ g hg f₂) y) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) (fun (_x : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) => β -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u2, u3} β γ _inst_2) f₂ y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u3} β] (f₁ : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u2, u3} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u3, u1} β _inst_2 γ) {y : β}, (Not (Exists.{succ u2} α (fun (x : α) => Eq.{succ u3} β (g x) y))) -> (Eq.{succ u1} γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} β _inst_2 γ (MeasureTheory.SimpleFunc.extend.{u2, u3, u1} α β γ _inst_1 _inst_2 f₁ g hg f₂) y) (MeasureTheory.SimpleFunc.toFun.{u3, u1} β _inst_2 γ f₂ y))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.extend_apply' MeasureTheory.SimpleFunc.extend_apply'ₓ'. -/
@[simp]
theorem extend_apply' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) {y : β} (h : ¬∃ x, g x = y) : (f₁.extend g hg f₂) y = f₂ y :=
  Function.extend_apply' _ _ _ h
#align measure_theory.simple_func.extend_apply' MeasureTheory.SimpleFunc.extend_apply'

/- warning: measure_theory.simple_func.extend_comp_eq' -> MeasureTheory.SimpleFunc.extend_comp_eq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f₁ : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ), Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) (fun (_x : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ) => β -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u2, u3} β γ _inst_2) (MeasureTheory.SimpleFunc.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 f₁ g hg f₂)) g) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) f₁)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u3} β] (f₁ : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u2, u3} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u3, u1} β _inst_2 γ), Eq.{max (succ u2) (succ u1)} (α -> γ) (Function.comp.{succ u2, succ u3, succ u1} α β γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} β _inst_2 γ (MeasureTheory.SimpleFunc.extend.{u2, u3, u1} α β γ _inst_1 _inst_2 f₁ g hg f₂)) g) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 γ f₁)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.extend_comp_eq' MeasureTheory.SimpleFunc.extend_comp_eq'ₓ'. -/
@[simp]
theorem extend_comp_eq' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : f₁.extend g hg f₂ ∘ g = f₁ :=
  funext fun x => extend_apply _ _ _ _
#align measure_theory.simple_func.extend_comp_eq' MeasureTheory.SimpleFunc.extend_comp_eq'

/- warning: measure_theory.simple_func.extend_comp_eq -> MeasureTheory.SimpleFunc.extend_comp_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f₁ : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u1, u2} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u2, u3} β _inst_2 γ), Eq.{max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (MeasureTheory.SimpleFunc.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 (MeasureTheory.SimpleFunc.extend.{u1, u2, u3} α β γ _inst_1 _inst_2 f₁ g hg f₂) g (MeasurableEmbedding.measurable.{u1, u2} α β _inst_1 _inst_2 g hg)) f₁
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u3} β] (f₁ : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) {g : α -> β} (hg : MeasurableEmbedding.{u2, u3} α β _inst_1 _inst_2 g) (f₂ : MeasureTheory.SimpleFunc.{u3, u1} β _inst_2 γ), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) (MeasureTheory.SimpleFunc.comp.{u2, u3, u1} α β γ _inst_1 _inst_2 (MeasureTheory.SimpleFunc.extend.{u2, u3, u1} α β γ _inst_1 _inst_2 f₁ g hg f₂) g (MeasurableEmbedding.measurable.{u2, u3} α β _inst_1 _inst_2 g hg)) f₁
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.extend_comp_eq MeasureTheory.SimpleFunc.extend_comp_eqₓ'. -/
@[simp]
theorem extend_comp_eq [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : (f₁.extend g hg f₂).comp g hg.Measurable = f₁ :=
  coe_injective <| extend_comp_eq' _ _ _
#align measure_theory.simple_func.extend_comp_eq MeasureTheory.SimpleFunc.extend_comp_eq

#print MeasureTheory.SimpleFunc.seq /-
/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ β → γ) (g : α →ₛ β) : α →ₛ γ :=
  f.bind fun f => g.map f
#align measure_theory.simple_func.seq MeasureTheory.SimpleFunc.seq
-/

/- warning: measure_theory.simple_func.seq_apply -> MeasureTheory.SimpleFunc.seq_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (β -> γ)) (g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) (MeasureTheory.SimpleFunc.seq.{u1, u2, u3} α β γ _inst_1 f g) a) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (β -> γ)) (fun (_x : MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (β -> γ)) => α -> β -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, max u2 u3} α (β -> γ) _inst_1) f a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) g a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, max u2 u1} α _inst_1 (β -> γ)) (g : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (a : α), Eq.{succ u1} γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ (MeasureTheory.SimpleFunc.seq.{u3, u2, u1} α β γ _inst_1 f g) a) (MeasureTheory.SimpleFunc.toFun.{u3, max u2 u1} α _inst_1 (β -> γ) f a (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β g a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.seq_apply MeasureTheory.SimpleFunc.seq_applyₓ'. -/
@[simp]
theorem seq_apply (f : α →ₛ β → γ) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) :=
  rfl
#align measure_theory.simple_func.seq_apply MeasureTheory.SimpleFunc.seq_apply

#print MeasureTheory.SimpleFunc.pair /-
/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ β × γ :=
  (f.map Prod.mk).seq g
#align measure_theory.simple_func.pair MeasureTheory.SimpleFunc.pair
-/

/- warning: measure_theory.simple_func.pair_apply -> MeasureTheory.SimpleFunc.pair_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (a : α), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} β γ) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (Prod.{u2, u3} β γ)) (fun (_x : MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (Prod.{u2, u3} β γ)) => α -> (Prod.{u2, u3} β γ)) (MeasureTheory.SimpleFunc.instCoeFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1) (MeasureTheory.SimpleFunc.pair.{u1, u2, u3} α β γ _inst_1 f g) a) (Prod.mk.{u2, u3} β γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f a) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) g a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u3, u1} α _inst_1 γ) (a : α), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} β γ) (MeasureTheory.SimpleFunc.toFun.{u3, max u2 u1} α _inst_1 (Prod.{u2, u1} β γ) (MeasureTheory.SimpleFunc.pair.{u3, u2, u1} α β γ _inst_1 f g) a) (Prod.mk.{u2, u1} β γ (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f a) (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ g a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.pair_apply MeasureTheory.SimpleFunc.pair_applyₓ'. -/
@[simp]
theorem pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) :=
  rfl
#align measure_theory.simple_func.pair_apply MeasureTheory.SimpleFunc.pair_apply

/- warning: measure_theory.simple_func.pair_preimage -> MeasureTheory.SimpleFunc.pair_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (s : Set.{u2} β) (t : Set.{u3} γ), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (Prod.{u2, u3} β γ)) (fun (_x : MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (Prod.{u2, u3} β γ)) => α -> (Prod.{u2, u3} β γ)) (MeasureTheory.SimpleFunc.instCoeFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1) (MeasureTheory.SimpleFunc.pair.{u1, u2, u3} α β γ _inst_1 f g)) (Set.prod.{u2, u3} β γ s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) s) (Set.preimage.{u1, u3} α γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) g) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u3, u1} α _inst_1 γ) (s : Set.{u2} β) (t : Set.{u1} γ), Eq.{succ u3} (Set.{u3} α) (Set.preimage.{u3, max u2 u1} α (Prod.{u2, u1} β γ) (MeasureTheory.SimpleFunc.toFun.{u3, max u2 u1} α _inst_1 (Prod.{u2, u1} β γ) (MeasureTheory.SimpleFunc.pair.{u3, u2, u1} α β γ _inst_1 f g)) (Set.prod.{u2, u1} β γ s t)) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (Set.preimage.{u3, u2} α β (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f) s) (Set.preimage.{u3, u1} α γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ g) t))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.pair_preimage MeasureTheory.SimpleFunc.pair_preimageₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : Set β) (t : Set γ) :
    pair f g ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl
#align measure_theory.simple_func.pair_preimage MeasureTheory.SimpleFunc.pair_preimage

/- warning: measure_theory.simple_func.pair_preimage_singleton -> MeasureTheory.SimpleFunc.pair_preimage_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (b : β) (c : γ), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (coeFn.{max (succ u1) (succ (max u2 u3)), max (succ u1) (succ (max u2 u3))} (MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (Prod.{u2, u3} β γ)) (fun (_x : MeasureTheory.SimpleFunc.{u1, max u2 u3} α _inst_1 (Prod.{u2, u3} β γ)) => α -> (Prod.{u2, u3} β γ)) (MeasureTheory.SimpleFunc.instCoeFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1) (MeasureTheory.SimpleFunc.pair.{u1, u2, u3} α β γ _inst_1 f g)) (Singleton.singleton.{max u2 u3, max u2 u3} (Prod.{u2, u3} β γ) (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasSingleton.{max u2 u3} (Prod.{u2, u3} β γ)) (Prod.mk.{u2, u3} β γ b c))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (Set.preimage.{u1, u3} α γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u3} α γ _inst_1) g) (Singleton.singleton.{u3, u3} γ (Set.{u3} γ) (Set.hasSingleton.{u3} γ) c)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] (f : MeasureTheory.SimpleFunc.{u3, u2} α _inst_1 β) (g : MeasureTheory.SimpleFunc.{u3, u1} α _inst_1 γ) (b : β) (c : γ), Eq.{succ u3} (Set.{u3} α) (Set.preimage.{u3, max u2 u1} α (Prod.{u2, u1} β γ) (MeasureTheory.SimpleFunc.toFun.{u3, max u2 u1} α _inst_1 (Prod.{u2, u1} β γ) (MeasureTheory.SimpleFunc.pair.{u3, u2, u1} α β γ _inst_1 f g)) (Singleton.singleton.{max u1 u2, max u2 u1} (Prod.{u2, u1} β γ) (Set.{max u2 u1} (Prod.{u2, u1} β γ)) (Set.instSingletonSet.{max u2 u1} (Prod.{u2, u1} β γ)) (Prod.mk.{u2, u1} β γ b c))) (Inter.inter.{u3} (Set.{u3} α) (Set.instInterSet.{u3} α) (Set.preimage.{u3, u2} α β (MeasureTheory.SimpleFunc.toFun.{u3, u2} α _inst_1 β f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.instSingletonSet.{u2} β) b)) (Set.preimage.{u3, u1} α γ (MeasureTheory.SimpleFunc.toFun.{u3, u1} α _inst_1 γ g) (Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.instSingletonSet.{u1} γ) c)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.pair_preimage_singleton MeasureTheory.SimpleFunc.pair_preimage_singletonₓ'. -/
-- A special form of `pair_preimage`
theorem pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
    pair f g ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} := by rw [← singleton_prod_singleton];
  exact pair_preimage _ _ _ _
#align measure_theory.simple_func.pair_preimage_singleton MeasureTheory.SimpleFunc.pair_preimage_singleton

/- warning: measure_theory.simple_func.bind_const -> MeasureTheory.SimpleFunc.bind_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.bind.{u1, u2, u2} α β β _inst_1 f (MeasureTheory.SimpleFunc.const.{u1, u2} α β _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.bind.{u2, u1, u1} α β β _inst_1 f (MeasureTheory.SimpleFunc.const.{u2, u1} α β _inst_1)) f
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.bind_const MeasureTheory.SimpleFunc.bind_constₓ'. -/
theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext <;> simp
#align measure_theory.simple_func.bind_const MeasureTheory.SimpleFunc.bind_const

@[to_additive]
instance [One β] : One (α →ₛ β) :=
  ⟨const α 1⟩

@[to_additive]
instance [Mul β] : Mul (α →ₛ β) :=
  ⟨fun f g => (f.map (· * ·)).seq g⟩

@[to_additive]
instance [Div β] : Div (α →ₛ β) :=
  ⟨fun f g => (f.map (· / ·)).seq g⟩

@[to_additive]
instance [Inv β] : Inv (α →ₛ β) :=
  ⟨fun f => f.map Inv.inv⟩

instance [Sup β] : Sup (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩

instance [Inf β] : Inf (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩

instance [LE β] : LE (α →ₛ β) :=
  ⟨fun f g => ∀ a, f a ≤ g a⟩

#print MeasureTheory.SimpleFunc.const_one /-
@[simp, to_additive]
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl
#align measure_theory.simple_func.const_one MeasureTheory.SimpleFunc.const_one
#align measure_theory.simple_func.const_zero MeasureTheory.SimpleFunc.const_zero
-/

#print MeasureTheory.SimpleFunc.coe_one /-
@[simp, norm_cast, to_additive]
theorem coe_one [One β] : ⇑(1 : α →ₛ β) = 1 :=
  rfl
#align measure_theory.simple_func.coe_one MeasureTheory.SimpleFunc.coe_one
#align measure_theory.simple_func.coe_zero MeasureTheory.SimpleFunc.coe_zero
-/

#print MeasureTheory.SimpleFunc.coe_mul /-
@[simp, norm_cast, to_additive]
theorem coe_mul [Mul β] (f g : α →ₛ β) : ⇑(f * g) = f * g :=
  rfl
#align measure_theory.simple_func.coe_mul MeasureTheory.SimpleFunc.coe_mul
#align measure_theory.simple_func.coe_add MeasureTheory.SimpleFunc.coe_add
-/

#print MeasureTheory.SimpleFunc.coe_inv /-
@[simp, norm_cast, to_additive]
theorem coe_inv [Inv β] (f : α →ₛ β) : ⇑f⁻¹ = f⁻¹ :=
  rfl
#align measure_theory.simple_func.coe_inv MeasureTheory.SimpleFunc.coe_inv
#align measure_theory.simple_func.coe_neg MeasureTheory.SimpleFunc.coe_neg
-/

#print MeasureTheory.SimpleFunc.coe_div /-
@[simp, norm_cast, to_additive]
theorem coe_div [Div β] (f g : α →ₛ β) : ⇑(f / g) = f / g :=
  rfl
#align measure_theory.simple_func.coe_div MeasureTheory.SimpleFunc.coe_div
#align measure_theory.simple_func.coe_sub MeasureTheory.SimpleFunc.coe_sub
-/

/- warning: measure_theory.simple_func.coe_le -> MeasureTheory.SimpleFunc.coe_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, Iff (LE.le.{max u1 u2} ((fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) f) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Preorder.toHasLe.{u2} β _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) g)) (LE.le.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instLE.{u1, u2} α β _inst_1 (Preorder.toHasLe.{u2} β _inst_2)) f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Preorder.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, Iff (LE.le.{max u1 u2} (α -> β) (Pi.hasLe.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Preorder.toLE.{u2} β _inst_2)) (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 β f) (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 β g)) (LE.le.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instLE.{u1, u2} α β _inst_1 (Preorder.toLE.{u2} β _inst_2)) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_le MeasureTheory.SimpleFunc.coe_leₓ'. -/
@[simp, norm_cast]
theorem coe_le [Preorder β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl
#align measure_theory.simple_func.coe_le MeasureTheory.SimpleFunc.coe_le

#print MeasureTheory.SimpleFunc.coe_sup /-
@[simp, norm_cast]
theorem coe_sup [Sup β] (f g : α →ₛ β) : ⇑(f ⊔ g) = f ⊔ g :=
  rfl
#align measure_theory.simple_func.coe_sup MeasureTheory.SimpleFunc.coe_sup
-/

#print MeasureTheory.SimpleFunc.coe_inf /-
@[simp, norm_cast]
theorem coe_inf [Inf β] (f g : α →ₛ β) : ⇑(f ⊓ g) = f ⊓ g :=
  rfl
#align measure_theory.simple_func.coe_inf MeasureTheory.SimpleFunc.coe_inf
-/

#print MeasureTheory.SimpleFunc.mul_apply /-
@[to_additive]
theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a :=
  rfl
#align measure_theory.simple_func.mul_apply MeasureTheory.SimpleFunc.mul_apply
#align measure_theory.simple_func.add_apply MeasureTheory.SimpleFunc.add_apply
-/

#print MeasureTheory.SimpleFunc.div_apply /-
@[to_additive]
theorem div_apply [Div β] (f g : α →ₛ β) (x : α) : (f / g) x = f x / g x :=
  rfl
#align measure_theory.simple_func.div_apply MeasureTheory.SimpleFunc.div_apply
#align measure_theory.simple_func.sub_apply MeasureTheory.SimpleFunc.sub_apply
-/

#print MeasureTheory.SimpleFunc.inv_apply /-
@[to_additive]
theorem inv_apply [Inv β] (f : α →ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align measure_theory.simple_func.inv_apply MeasureTheory.SimpleFunc.inv_apply
#align measure_theory.simple_func.neg_apply MeasureTheory.SimpleFunc.neg_apply
-/

#print MeasureTheory.SimpleFunc.sup_apply /-
theorem sup_apply [Sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
#align measure_theory.simple_func.sup_apply MeasureTheory.SimpleFunc.sup_apply
-/

#print MeasureTheory.SimpleFunc.inf_apply /-
theorem inf_apply [Inf β] (f g : α →ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl
#align measure_theory.simple_func.inf_apply MeasureTheory.SimpleFunc.inf_apply
-/

/- warning: measure_theory.simple_func.range_one -> MeasureTheory.SimpleFunc.range_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Nonempty.{succ u1} α] [_inst_3 : One.{u2} β], Eq.{succ u2} (Finset.{u2} β) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 (OfNat.ofNat.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) 1 (OfNat.mk.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) 1 (One.one.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instOne.{u1, u2} α β _inst_1 _inst_3))))) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_3))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Nonempty.{succ u2} α] [_inst_3 : One.{u1} β], Eq.{succ u1} (Finset.{u1} β) (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 (OfNat.ofNat.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) 1 (One.toOfNat1.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.instOne.{u2, u1} α β _inst_1 _inst_3)))) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β _inst_3)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.range_one MeasureTheory.SimpleFunc.range_oneₓ'. -/
@[simp, to_additive]
theorem range_one [Nonempty α] [One β] : (1 : α →ₛ β).range = {1} :=
  Finset.ext fun x => by simp [eq_comm]
#align measure_theory.simple_func.range_one MeasureTheory.SimpleFunc.range_one
#align measure_theory.simple_func.range_zero MeasureTheory.SimpleFunc.range_zero

#print MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty /-
@[simp]
theorem range_eq_empty_of_isEmpty {β} [hα : IsEmpty α] (f : α →ₛ β) : f.range = ∅ :=
  by
  rw [← Finset.not_nonempty_iff_eq_empty]
  by_contra
  obtain ⟨y, hy_mem⟩ := h
  rw [simple_func.mem_range, Set.mem_range] at hy_mem
  obtain ⟨x, hxy⟩ := hy_mem
  rw [isEmpty_iff] at hα
  exact hα x
#align measure_theory.simple_func.range_eq_empty_of_is_empty MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty
-/

#print MeasureTheory.SimpleFunc.eq_zero_of_mem_range_zero /-
theorem eq_zero_of_mem_range_zero [Zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
  forall_range_iff.2 fun x => rfl
#align measure_theory.simple_func.eq_zero_of_mem_range_zero MeasureTheory.SimpleFunc.eq_zero_of_mem_range_zero
-/

#print MeasureTheory.SimpleFunc.mul_eq_map₂ /-
@[to_additive]
theorem mul_eq_map₂ [Mul β] (f g : α →ₛ β) : f * g = (pair f g).map fun p : β × β => p.1 * p.2 :=
  rfl
#align measure_theory.simple_func.mul_eq_map₂ MeasureTheory.SimpleFunc.mul_eq_map₂
#align measure_theory.simple_func.add_eq_map₂ MeasureTheory.SimpleFunc.add_eq_map₂
-/

#print MeasureTheory.SimpleFunc.sup_eq_map₂ /-
theorem sup_eq_map₂ [Sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2 :=
  rfl
#align measure_theory.simple_func.sup_eq_map₂ MeasureTheory.SimpleFunc.sup_eq_map₂
-/

#print MeasureTheory.SimpleFunc.const_mul_eq_map /-
@[to_additive]
theorem const_mul_eq_map [Mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map fun a => b * a :=
  rfl
#align measure_theory.simple_func.const_mul_eq_map MeasureTheory.SimpleFunc.const_mul_eq_map
#align measure_theory.simple_func.const_add_eq_map MeasureTheory.SimpleFunc.const_add_eq_map
-/

/- warning: measure_theory.simple_func.map_mul -> MeasureTheory.SimpleFunc.map_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Mul.{u2} β] [_inst_3 : Mul.{u3} γ] {g : β -> γ}, (forall (x : β) (y : β), Eq.{succ u3} γ (g (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_2) x y)) (HMul.hMul.{u3, u3, u3} γ γ γ (instHMul.{u3} γ _inst_3) (g x) (g y))) -> (forall (f₁ : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (f₂ : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u3)} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (instHMul.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instMul.{u1, u2} α β _inst_1 _inst_2)) f₁ f₂)) (HMul.hMul.{max u1 u3, max u1 u3, max u1 u3} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (instHMul.{max u1 u3} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 γ) (MeasureTheory.SimpleFunc.instMul.{u1, u3} α γ _inst_1 _inst_3)) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f₁) (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ _inst_1 g f₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Mul.{u3} β] [_inst_3 : Mul.{u2} γ] {g : β -> γ}, (forall (x : β) (y : β), Eq.{succ u2} γ (g (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β _inst_2) x y)) (HMul.hMul.{u2, u2, u2} γ γ γ (instHMul.{u2} γ _inst_3) (g x) (g y))) -> (forall (f₁ : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 β) (f₂ : MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.map.{u1, u3, u2} α β γ _inst_1 g (HMul.hMul.{max u1 u3, max u1 u3, max u1 u3} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 β) (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 β) (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 β) (instHMul.{max u1 u3} (MeasureTheory.SimpleFunc.{u1, u3} α _inst_1 β) (MeasureTheory.SimpleFunc.instMul.{u1, u3} α β _inst_1 _inst_2)) f₁ f₂)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (instHMul.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.instMul.{u1, u2} α γ _inst_1 _inst_3)) (MeasureTheory.SimpleFunc.map.{u1, u3, u2} α β γ _inst_1 g f₁) (MeasureTheory.SimpleFunc.map.{u1, u3, u2} α β γ _inst_1 g f₂)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_mul MeasureTheory.SimpleFunc.map_mulₓ'. -/
@[to_additive]
theorem map_mul [Mul β] [Mul γ] {g : β → γ} (hg : ∀ x y, g (x * y) = g x * g y) (f₁ f₂ : α →ₛ β) :
    (f₁ * f₂).map g = f₁.map g * f₂.map g :=
  ext fun x => hg _ _
#align measure_theory.simple_func.map_mul MeasureTheory.SimpleFunc.map_mul
#align measure_theory.simple_func.map_add MeasureTheory.SimpleFunc.map_add

variable {K : Type _}

instance [SMul K β] : SMul K (α →ₛ β) :=
  ⟨fun k f => f.map ((· • ·) k)⟩

#print MeasureTheory.SimpleFunc.coe_smul /-
@[simp]
theorem coe_smul [SMul K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • f :=
  rfl
#align measure_theory.simple_func.coe_smul MeasureTheory.SimpleFunc.coe_smul
-/

#print MeasureTheory.SimpleFunc.smul_apply /-
theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
  rfl
#align measure_theory.simple_func.smul_apply MeasureTheory.SimpleFunc.smul_apply
-/

#print MeasureTheory.SimpleFunc.hasNatPow /-
instance hasNatPow [Monoid β] : Pow (α →ₛ β) ℕ :=
  ⟨fun f n => f.map (· ^ n)⟩
#align measure_theory.simple_func.has_nat_pow MeasureTheory.SimpleFunc.hasNatPow
-/

#print MeasureTheory.SimpleFunc.coe_pow /-
@[simp]
theorem coe_pow [Monoid β] (f : α →ₛ β) (n : ℕ) : ⇑(f ^ n) = f ^ n :=
  rfl
#align measure_theory.simple_func.coe_pow MeasureTheory.SimpleFunc.coe_pow
-/

#print MeasureTheory.SimpleFunc.pow_apply /-
theorem pow_apply [Monoid β] (n : ℕ) (f : α →ₛ β) (a : α) : (f ^ n) a = f a ^ n :=
  rfl
#align measure_theory.simple_func.pow_apply MeasureTheory.SimpleFunc.pow_apply
-/

#print MeasureTheory.SimpleFunc.hasIntPow /-
instance hasIntPow [DivInvMonoid β] : Pow (α →ₛ β) ℤ :=
  ⟨fun f n => f.map (· ^ n)⟩
#align measure_theory.simple_func.has_int_pow MeasureTheory.SimpleFunc.hasIntPow
-/

#print MeasureTheory.SimpleFunc.coe_zpow /-
@[simp]
theorem coe_zpow [DivInvMonoid β] (f : α →ₛ β) (z : ℤ) : ⇑(f ^ z) = f ^ z :=
  rfl
#align measure_theory.simple_func.coe_zpow MeasureTheory.SimpleFunc.coe_zpow
-/

#print MeasureTheory.SimpleFunc.zpow_apply /-
theorem zpow_apply [DivInvMonoid β] (z : ℤ) (f : α →ₛ β) (a : α) : (f ^ z) a = f a ^ z :=
  rfl
#align measure_theory.simple_func.zpow_apply MeasureTheory.SimpleFunc.zpow_apply
-/

-- TODO: work out how to generate these instances with `to_additive`, which gets confused by the
-- argument order swap between `coe_smul` and `coe_pow`.
section Additive

instance [AddMonoid β] : AddMonoid (α →ₛ β) :=
  Function.Injective.addMonoid (fun f => show α → β from f) coe_injective coe_zero coe_add
    fun _ _ => coe_smul _ _

instance [AddCommMonoid β] : AddCommMonoid (α →ₛ β) :=
  Function.Injective.addCommMonoid (fun f => show α → β from f) coe_injective coe_zero coe_add
    fun _ _ => coe_smul _ _

instance [AddGroup β] : AddGroup (α →ₛ β) :=
  Function.Injective.addGroup (fun f => show α → β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

instance [AddCommGroup β] : AddCommGroup (α →ₛ β) :=
  Function.Injective.addCommGroup (fun f => show α → β from f) coe_injective coe_zero coe_add
    coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

end Additive

@[to_additive]
instance [Monoid β] : Monoid (α →ₛ β) :=
  Function.Injective.monoid (fun f => show α → β from f) coe_injective coe_one coe_mul coe_pow

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ₛ β) :=
  Function.Injective.commMonoid (fun f => show α → β from f) coe_injective coe_one coe_mul coe_pow

@[to_additive]
instance [Group β] : Group (α →ₛ β) :=
  Function.Injective.group (fun f => show α → β from f) coe_injective coe_one coe_mul coe_inv
    coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup β] : CommGroup (α →ₛ β) :=
  Function.Injective.commGroup (fun f => show α → β from f) coe_injective coe_one coe_mul coe_inv
    coe_div coe_pow coe_zpow

instance [Semiring K] [AddCommMonoid β] [Module K β] : Module K (α →ₛ β) :=
  Function.Injective.module K ⟨fun f => show α → β from f, coe_zero, coe_add⟩ coe_injective coe_smul

#print MeasureTheory.SimpleFunc.smul_eq_map /-
theorem smul_eq_map [SMul K β] (k : K) (f : α →ₛ β) : k • f = f.map ((· • ·) k) :=
  rfl
#align measure_theory.simple_func.smul_eq_map MeasureTheory.SimpleFunc.smul_eq_map
-/

instance [Preorder β] : Preorder (α →ₛ β) :=
  { SimpleFunc.instLE with
    le_refl := fun f a => le_rfl
    le_trans := fun f g h hfg hgh a => le_trans (hfg _) (hgh a) }

instance [PartialOrder β] : PartialOrder (α →ₛ β) :=
  { SimpleFunc.instPreorder with
    le_antisymm := fun f g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }

instance [LE β] [OrderBot β] : OrderBot (α →ₛ β)
    where
  bot := const α ⊥
  bot_le f a := bot_le

instance [LE β] [OrderTop β] : OrderTop (α →ₛ β)
    where
  top := const α ⊤
  le_top f a := le_top

instance [SemilatticeInf β] : SemilatticeInf (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun f g a => inf_le_left
    inf_le_right := fun f g a => inf_le_right
    le_inf := fun f g h hfh hgh a => le_inf (hfh a) (hgh a) }

instance [SemilatticeSup β] : SemilatticeSup (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun f g a => le_sup_left
    le_sup_right := fun f g a => le_sup_right
    sup_le := fun f g h hfh hgh a => sup_le (hfh a) (hgh a) }

instance [Lattice β] : Lattice (α →ₛ β) :=
  { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }

instance [LE β] [BoundedOrder β] : BoundedOrder (α →ₛ β) :=
  { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }

/- warning: measure_theory.simple_func.finset_sup_apply -> MeasureTheory.SimpleFunc.finset_sup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] {f : γ -> (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β)} (s : Finset.{u3} γ) (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (Finset.sup.{max u1 u2, u3} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) γ (MeasureTheory.SimpleFunc.instSemilatticeSup.{u1, u2} α β _inst_1 _inst_2) (MeasureTheory.SimpleFunc.instOrderBot.{u1, u2} α β _inst_1 (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) _inst_3) s f) a) (Finset.sup.{u2, u3} β γ _inst_2 _inst_3 s (fun (c : γ) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (f c) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : SemilatticeSup.{u3} β] [_inst_3 : OrderBot.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_2)))] {f : γ -> (MeasureTheory.SimpleFunc.{u2, u3} α _inst_1 β)} (s : Finset.{u1} γ) (a : α), Eq.{succ u3} β (MeasureTheory.SimpleFunc.toFun.{u2, u3} α _inst_1 β (Finset.sup.{max u2 u3, u1} (MeasureTheory.SimpleFunc.{u2, u3} α _inst_1 β) γ (MeasureTheory.SimpleFunc.instSemilatticeSup.{u2, u3} α β _inst_1 _inst_2) (MeasureTheory.SimpleFunc.instOrderBot.{u2, u3} α β _inst_1 (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_2))) _inst_3) s f) a) (Finset.sup.{u3, u1} β γ _inst_2 _inst_3 s (fun (c : γ) => MeasureTheory.SimpleFunc.toFun.{u2, u3} α _inst_1 β (f c) a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.finset_sup_apply MeasureTheory.SimpleFunc.finset_sup_applyₓ'. -/
theorem finset_sup_apply [SemilatticeSup β] [OrderBot β] {f : γ → α →ₛ β} (s : Finset γ) (a : α) :
    s.sup f a = s.sup fun c => f c a :=
  by
  refine' Finset.induction_on s rfl _
  intro a s hs ih
  rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]
#align measure_theory.simple_func.finset_sup_apply MeasureTheory.SimpleFunc.finset_sup_apply

section Restrict

variable [Zero β]

#print MeasureTheory.SimpleFunc.restrict /-
/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0
#align measure_theory.simple_func.restrict MeasureTheory.SimpleFunc.restrict
-/

/- warning: measure_theory.simple_func.restrict_of_not_measurable -> MeasureTheory.SimpleFunc.restrict_of_not_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {s : Set.{u1} α}, (Not (MeasurableSet.{u1} α _inst_1 s)) -> (Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s) (OfNat.ofNat.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) 0 (OfNat.mk.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) 0 (Zero.zero.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instZero.{u1, u2} α β _inst_1 _inst_2)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β} {s : Set.{u2} α}, (Not (MeasurableSet.{u2} α _inst_1 s)) -> (Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s) (OfNat.ofNat.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) 0 (Zero.toOfNat0.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.instZero.{u2, u1} α β _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_of_not_measurable MeasureTheory.SimpleFunc.restrict_of_not_measurableₓ'. -/
theorem restrict_of_not_measurable {f : α →ₛ β} {s : Set α} (hs : ¬MeasurableSet s) :
    restrict f s = 0 :=
  dif_neg hs
#align measure_theory.simple_func.restrict_of_not_measurable MeasureTheory.SimpleFunc.restrict_of_not_measurable

/- warning: measure_theory.simple_func.coe_restrict -> MeasureTheory.SimpleFunc.coe_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s)) (Set.indicator.{u1, u2} α β _inst_2 s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_1 s) -> (Eq.{max (succ u2) (succ u1)} (α -> β) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s)) (Set.indicator.{u2, u1} α β _inst_2 s (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.coe_restrict MeasureTheory.SimpleFunc.coe_restrictₓ'. -/
@[simp]
theorem coe_restrict (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) :
    ⇑(restrict f s) = indicator s f := by rw [restrict, dif_pos hs]; rfl
#align measure_theory.simple_func.coe_restrict MeasureTheory.SimpleFunc.coe_restrict

/- warning: measure_theory.simple_func.restrict_univ -> MeasureTheory.SimpleFunc.restrict_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f (Set.univ.{u1} α)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f (Set.univ.{u2} α)) f
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_univ MeasureTheory.SimpleFunc.restrict_univₓ'. -/
@[simp]
theorem restrict_univ (f : α →ₛ β) : restrict f univ = f := by simp [restrict]
#align measure_theory.simple_func.restrict_univ MeasureTheory.SimpleFunc.restrict_univ

/- warning: measure_theory.simple_func.restrict_empty -> MeasureTheory.SimpleFunc.restrict_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) 0 (OfNat.mk.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) 0 (Zero.zero.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instZero.{u1, u2} α β _inst_1 _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{max (succ u2) (succ u1)} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (OfNat.ofNat.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) 0 (Zero.toOfNat0.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) (MeasureTheory.SimpleFunc.instZero.{u2, u1} α β _inst_1 _inst_2)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_empty MeasureTheory.SimpleFunc.restrict_emptyₓ'. -/
@[simp]
theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 := by simp [restrict]
#align measure_theory.simple_func.restrict_empty MeasureTheory.SimpleFunc.restrict_empty

#print MeasureTheory.SimpleFunc.map_restrict_of_zero /-
theorem map_restrict_of_zero [Zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : Set α) :
    (f.restrict s).map g = (f.map g).restrict s :=
  ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
    else by simp [restrict_of_not_measurable hs, hg]
#align measure_theory.simple_func.map_restrict_of_zero MeasureTheory.SimpleFunc.map_restrict_of_zero
-/

/- warning: measure_theory.simple_func.map_coe_ennreal_restrict -> MeasureTheory.SimpleFunc.map_coe_ennreal_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) (s : Set.{u1} α), Eq.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe)))) (MeasureTheory.SimpleFunc.restrict.{u1, 0} α NNReal _inst_1 (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) f s)) (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal _inst_1 ENNReal.hasZero (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe)))) f) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) (s : Set.{u1} α), Eq.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal _inst_1 ENNReal.some (MeasureTheory.SimpleFunc.restrict.{u1, 0} α NNReal _inst_1 instNNRealZero f s)) (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal _inst_1 instENNRealZero (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal ENNReal _inst_1 ENNReal.some f) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_coe_ennreal_restrict MeasureTheory.SimpleFunc.map_coe_ennreal_restrictₓ'. -/
theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map (coe : ℝ≥0 → ℝ≥0∞) = (f.map coe).restrict s :=
  map_restrict_of_zero ENNReal.coe_zero _ _
#align measure_theory.simple_func.map_coe_ennreal_restrict MeasureTheory.SimpleFunc.map_coe_ennreal_restrict

/- warning: measure_theory.simple_func.map_coe_nnreal_restrict -> MeasureTheory.SimpleFunc.map_coe_nnreal_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) (s : Set.{u1} α), Eq.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 Real) (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal Real _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) (MeasureTheory.SimpleFunc.restrict.{u1, 0} α NNReal _inst_1 (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) f s)) (MeasureTheory.SimpleFunc.restrict.{u1, 0} α Real _inst_1 Real.hasZero (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal Real _inst_1 ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) f) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) (s : Set.{u1} α), Eq.{succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 Real) (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal Real _inst_1 NNReal.toReal (MeasureTheory.SimpleFunc.restrict.{u1, 0} α NNReal _inst_1 instNNRealZero f s)) (MeasureTheory.SimpleFunc.restrict.{u1, 0} α Real _inst_1 Real.instZeroReal (MeasureTheory.SimpleFunc.map.{u1, 0, 0} α NNReal Real _inst_1 NNReal.toReal f) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_coe_nnreal_restrict MeasureTheory.SimpleFunc.map_coe_nnreal_restrictₓ'. -/
theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map (coe : ℝ≥0 → ℝ) = (f.map coe).restrict s :=
  map_restrict_of_zero NNReal.coe_zero _ _
#align measure_theory.simple_func.map_coe_nnreal_restrict MeasureTheory.SimpleFunc.map_coe_nnreal_restrict

/- warning: measure_theory.simple_func.restrict_apply -> MeasureTheory.SimpleFunc.restrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s) a) (Set.indicator.{u1, u2} α β _inst_2 s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_1 s) -> (forall (a : α), Eq.{succ u1} β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s) a) (Set.indicator.{u2, u1} α β _inst_2 s (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_apply MeasureTheory.SimpleFunc.restrict_applyₓ'. -/
theorem restrict_apply (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) (a) :
    restrict f s a = indicator s f a := by simp only [f.coe_restrict hs]
#align measure_theory.simple_func.restrict_apply MeasureTheory.SimpleFunc.restrict_apply

/- warning: measure_theory.simple_func.restrict_preimage -> MeasureTheory.SimpleFunc.restrict_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (forall {t : Set.{u2} β}, (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))) t)) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s)) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) t))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_1 s) -> (forall {t : Set.{u1} β}, (Not (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2)) t)) -> (Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s)) t) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) t))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_preimage MeasureTheory.SimpleFunc.restrict_preimageₓ'. -/
theorem restrict_preimage (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
    (ht : (0 : β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t := by
  simp [hs, indicator_preimage_of_not_mem _ _ ht, inter_comm]
#align measure_theory.simple_func.restrict_preimage MeasureTheory.SimpleFunc.restrict_preimage

/- warning: measure_theory.simple_func.restrict_preimage_singleton -> MeasureTheory.SimpleFunc.restrict_preimage_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (forall {r : β}, (Ne.{succ u2} β r (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) -> (Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s)) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) r)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) r)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β) {s : Set.{u2} α}, (MeasurableSet.{u2} α _inst_1 s) -> (forall {r : β}, (Ne.{succ u1} β r (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) -> (Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) r)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) r)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_preimage_singleton MeasureTheory.SimpleFunc.restrict_preimage_singletonₓ'. -/
theorem restrict_preimage_singleton (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
    (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
  f.restrictPreimage hs hr.symm
#align measure_theory.simple_func.restrict_preimage_singleton MeasureTheory.SimpleFunc.restrict_preimage_singleton

/- warning: measure_theory.simple_func.mem_restrict_range -> MeasureTheory.SimpleFunc.mem_restrict_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] {r : β} {s : Set.{u1} α} {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, (MeasurableSet.{u1} α _inst_1 s) -> (Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) r (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s))) (Or (And (Eq.{succ u2} β r (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) r (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] {r : β} {s : Set.{u2} α} {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β}, (MeasurableSet.{u2} α _inst_1 s) -> (Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) r (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s))) (Or (And (Eq.{succ u1} β r (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) (Ne.{succ u2} (Set.{u2} α) s (Set.univ.{u2} α))) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) r (Set.image.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) s))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.mem_restrict_range MeasureTheory.SimpleFunc.mem_restrict_rangeₓ'. -/
theorem mem_restrict_range {r : β} {s : Set α} {f : α →ₛ β} (hs : MeasurableSet s) :
    r ∈ (restrict f s).range ↔ r = 0 ∧ s ≠ univ ∨ r ∈ f '' s := by
  rw [← Finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]
#align measure_theory.simple_func.mem_restrict_range MeasureTheory.SimpleFunc.mem_restrict_range

/- warning: measure_theory.simple_func.mem_image_of_mem_range_restrict -> MeasureTheory.SimpleFunc.mem_image_of_mem_range_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] {r : β} {s : Set.{u1} α} {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) r (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s))) -> (Ne.{succ u2} β r (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) r (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] {r : β} {s : Set.{u2} α} {f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β}, (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) r (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 (MeasureTheory.SimpleFunc.restrict.{u2, u1} α β _inst_1 _inst_2 f s))) -> (Ne.{succ u1} β r (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) r (Set.image.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.mem_image_of_mem_range_restrict MeasureTheory.SimpleFunc.mem_image_of_mem_range_restrictₓ'. -/
theorem mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α →ₛ β}
    (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) : r ∈ f '' s :=
  if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0] using hr
  else by
    rw [restrict_of_not_measurable hs] at hr
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim
#align measure_theory.simple_func.mem_image_of_mem_range_restrict MeasureTheory.SimpleFunc.mem_image_of_mem_range_restrict

/- warning: measure_theory.simple_func.restrict_mono -> MeasureTheory.SimpleFunc.restrict_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : Preorder.{u2} β] (s : Set.{u1} α) {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, (LE.le.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instLE.{u1, u2} α β _inst_1 (Preorder.toHasLe.{u2} β _inst_3)) f g) -> (LE.le.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instLE.{u1, u2} α β _inst_1 (Preorder.toHasLe.{u2} β _inst_3)) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 g s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : Preorder.{u2} β] (s : Set.{u1} α) {f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β} {g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β}, (LE.le.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instLE.{u1, u2} α β _inst_1 (Preorder.toLE.{u2} β _inst_3)) f g) -> (LE.le.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (MeasureTheory.SimpleFunc.instLE.{u1, u2} α β _inst_1 (Preorder.toLE.{u2} β _inst_3)) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 f s) (MeasureTheory.SimpleFunc.restrict.{u1, u2} α β _inst_1 _inst_2 g s))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_mono MeasureTheory.SimpleFunc.restrict_monoₓ'. -/
@[mono]
theorem restrict_mono [Preorder β] (s : Set α) {f g : α →ₛ β} (H : f ≤ g) :
    f.restrict s ≤ g.restrict s :=
  if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else by simp only [restrict_of_not_measurable hs, le_refl]
#align measure_theory.simple_func.restrict_mono MeasureTheory.SimpleFunc.restrict_mono

end Restrict

section Approx

section

variable [SemilatticeSup β] [OrderBot β] [Zero β]

/- warning: measure_theory.simple_func.approx -> MeasureTheory.SimpleFunc.approx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] [_inst_4 : Zero.{u2} β], (Nat -> β) -> (α -> β) -> Nat -> (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] [_inst_4 : Zero.{u2} β], (Nat -> β) -> (α -> β) -> Nat -> (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.approx MeasureTheory.SimpleFunc.approxₓ'. -/
/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `supr_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k ≤ f a }
#align measure_theory.simple_func.approx MeasureTheory.SimpleFunc.approx

/- warning: measure_theory.simple_func.approx_apply -> MeasureTheory.SimpleFunc.approx_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] [_inst_4 : Zero.{u2} β] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : OrderClosedTopology.{u2} β _inst_5 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))] [_inst_7 : MeasurableSpace.{u2} β] [_inst_8 : OpensMeasurableSpace.{u2} β _inst_5 _inst_7] {i : Nat -> β} {f : α -> β} {n : Nat} (a : α), (Measurable.{u1, u2} α β _inst_1 _inst_7 f) -> (Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) (MeasureTheory.SimpleFunc.approx.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 i f n) a) (Finset.sup.{u2, 0} β Nat _inst_2 _inst_3 (Finset.range n) (fun (k : Nat) => ite.{succ u2} β (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (i k) (f a)) (Classical.propDecidable (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (i k) (f a))) (i k) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_4))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] [_inst_4 : Zero.{u2} β] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : OrderClosedTopology.{u2} β _inst_5 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))] [_inst_7 : MeasurableSpace.{u2} β] [_inst_8 : OpensMeasurableSpace.{u2} β _inst_5 _inst_7] {i : Nat -> β} {f : α -> β} {n : Nat} (a : α), (Measurable.{u1, u2} α β _inst_1 _inst_7 f) -> (Eq.{succ u2} β (MeasureTheory.SimpleFunc.toFun.{u1, u2} α _inst_1 β (MeasureTheory.SimpleFunc.approx.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 i f n) a) (Finset.sup.{u2, 0} β Nat _inst_2 _inst_3 (Finset.range n) (fun (k : Nat) => ite.{succ u2} β (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (i k) (f a)) (Classical.propDecidable (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (i k) (f a))) (i k) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_4)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.approx_apply MeasureTheory.SimpleFunc.approx_applyₓ'. -/
theorem approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : Measurable f) :
    (approx i f n : α →ₛ β) a = (Finset.range n).sup fun k => if i k ≤ f a then i k else 0 :=
  by
  dsimp only [approx]
  rw [finset_sup_apply]
  congr
  funext k
  rw [restrict_apply]
  rfl
  exact hf measurableSet_Ici
#align measure_theory.simple_func.approx_apply MeasureTheory.SimpleFunc.approx_apply

/- warning: measure_theory.simple_func.monotone_approx -> MeasureTheory.SimpleFunc.monotone_approx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] [_inst_4 : Zero.{u2} β] (i : Nat -> β) (f : α -> β), Monotone.{0, max u1 u2} Nat (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (MeasureTheory.SimpleFunc.instPreorder.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (MeasureTheory.SimpleFunc.approx.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 i f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : SemilatticeSup.{u2} β] [_inst_3 : OrderBot.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2)))] [_inst_4 : Zero.{u2} β] (i : Nat -> β) (f : α -> β), Monotone.{0, max u2 u1} Nat (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (MeasureTheory.SimpleFunc.instPreorder.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_2))) (MeasureTheory.SimpleFunc.approx.{u1, u2} α β _inst_1 _inst_2 _inst_3 _inst_4 i f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.monotone_approx MeasureTheory.SimpleFunc.monotone_approxₓ'. -/
theorem monotone_approx (i : ℕ → β) (f : α → β) : Monotone (approx i f) := fun n m h =>
  Finset.sup_mono <| Finset.range_subset.2 h
#align measure_theory.simple_func.monotone_approx MeasureTheory.SimpleFunc.monotone_approx

/- warning: measure_theory.simple_func.approx_comp -> MeasureTheory.SimpleFunc.approx_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.approx_comp MeasureTheory.SimpleFunc.approx_compₓ'. -/
theorem approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] [MeasurableSpace γ] {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
    (hf : Measurable f) (hg : Measurable g) :
    (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) := by
  rw [approx_apply _ hf, approx_apply _ (hf.comp hg)]
#align measure_theory.simple_func.approx_comp MeasureTheory.SimpleFunc.approx_comp

end

/- warning: measure_theory.simple_func.supr_approx_apply -> MeasureTheory.SimpleFunc.iSup_approx_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.supr_approx_apply MeasureTheory.SimpleFunc.iSup_approx_applyₓ'. -/
theorem iSup_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : (⨆ n, (approx i f n : α →ₛ β) a) = ⨆ (k) (h : i k ≤ f a), i k :=
  by
  refine' le_antisymm (iSup_le fun n => _) (iSup_le fun k => iSup_le fun hk => _)
  · rw [approx_apply a hf, h_zero]
    refine' Finset.sup_le fun k hk => _
    split_ifs
    exact le_iSup_of_le k (le_iSup _ h)
    exact bot_le
  · refine' le_iSup_of_le (k + 1) _
    rw [approx_apply a hf]
    have : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
    refine' le_trans (le_of_eq _) (Finset.le_sup this)
    rw [if_pos hk]
#align measure_theory.simple_func.supr_approx_apply MeasureTheory.SimpleFunc.iSup_approx_apply

end Approx

section Eapprox

#print MeasureTheory.SimpleFunc.ennrealRatEmbed /-
/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode ℚ n).getD (0 : ℚ))
#align measure_theory.simple_func.ennreal_rat_embed MeasureTheory.SimpleFunc.ennrealRatEmbed
-/

/- warning: measure_theory.simple_func.ennreal_rat_embed_encode -> MeasureTheory.SimpleFunc.ennrealRatEmbed_encode is a dubious translation:
lean 3 declaration is
  forall (q : Rat), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.ennrealRatEmbed (Encodable.encode.{0} Rat Rat.encodable q)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (Real.toNNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q)))
but is expected to have type
  forall (q : Rat), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.ennrealRatEmbed (Encodable.encode.{0} Rat Rat.instEncodableRat q)) (ENNReal.some (Real.toNNReal (Rat.cast.{0} Real Real.ratCast q)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.ennreal_rat_embed_encode MeasureTheory.SimpleFunc.ennrealRatEmbed_encodeₓ'. -/
theorem ennrealRatEmbed_encode (q : ℚ) : ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q :=
  by rw [ennreal_rat_embed, Encodable.encodek] <;> rfl
#align measure_theory.simple_func.ennreal_rat_embed_encode MeasureTheory.SimpleFunc.ennrealRatEmbed_encode

#print MeasureTheory.SimpleFunc.eapprox /-
/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
  approx ennrealRatEmbed
#align measure_theory.simple_func.eapprox MeasureTheory.SimpleFunc.eapprox
-/

/- warning: measure_theory.simple_func.eapprox_lt_top -> MeasureTheory.SimpleFunc.eapprox_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal) (n : Nat) (a : α), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal _inst_1) (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f n) a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal) (n : Nat) (a : α), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α _inst_1 ENNReal (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f n) a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.eapprox_lt_top MeasureTheory.SimpleFunc.eapprox_lt_topₓ'. -/
theorem eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ :=
  by
  simp only [eapprox, approx, finset_sup_apply, Finset.sup_lt_iff, WithTop.zero_lt_top,
    Finset.mem_range, ENNReal.bot_eq_zero, restrict]
  intro b hb
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { a : α | ennreal_rat_embed b ≤ f a }.indicator (fun x => ennreal_rat_embed b) a ≤
          ennreal_rat_embed b :=
        indicator_le_self _ _ a
      _ < ⊤ := ENNReal.coe_lt_top
      
  · exact WithTop.zero_lt_top
#align measure_theory.simple_func.eapprox_lt_top MeasureTheory.SimpleFunc.eapprox_lt_top

/- warning: measure_theory.simple_func.monotone_eapprox -> MeasureTheory.SimpleFunc.monotone_eapprox is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal), Monotone.{0, u1} Nat (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (MeasureTheory.SimpleFunc.instPreorder.{u1, 0} α ENNReal _inst_1 (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal), Monotone.{0, u1} Nat (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (MeasureTheory.SimpleFunc.instPreorder.{u1, 0} α ENNReal _inst_1 (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.monotone_eapprox MeasureTheory.SimpleFunc.monotone_eapproxₓ'. -/
@[mono]
theorem monotone_eapprox (f : α → ℝ≥0∞) : Monotone (eapprox f) :=
  monotone_approx _ f
#align measure_theory.simple_func.monotone_eapprox MeasureTheory.SimpleFunc.monotone_eapprox

/- warning: measure_theory.simple_func.supr_eapprox_apply -> MeasureTheory.SimpleFunc.iSup_eapprox_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal), (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (forall (a : α), Eq.{1} ENNReal (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal _inst_1) (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f n) a)) (f a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal), (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (forall (a : α), Eq.{1} ENNReal (iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => MeasureTheory.SimpleFunc.toFun.{u1, 0} α _inst_1 ENNReal (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f n) a)) (f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.supr_eapprox_apply MeasureTheory.SimpleFunc.iSup_eapprox_applyₓ'. -/
theorem iSup_eapprox_apply (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) :
    (⨆ n, (eapprox f n : α →ₛ ℝ≥0∞) a) = f a :=
  by
  rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl]
  refine' le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt _)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : ℝ≥0∞) ≤ ⨆ (k : ℕ) (h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k :=
    by
    refine' le_iSup_of_le (Encodable.encode q) _
    rw [ennreal_rat_embed_encode q]
    refine' le_iSup_of_le (le_of_lt q_lt) _
    exact le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
#align measure_theory.simple_func.supr_eapprox_apply MeasureTheory.SimpleFunc.iSup_eapprox_apply

#print MeasureTheory.SimpleFunc.eapprox_comp /-
theorem eapprox_comp [MeasurableSpace γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ} (hf : Measurable f)
    (hg : Measurable g) : (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
  funext fun a => approx_comp a hf hg
#align measure_theory.simple_func.eapprox_comp MeasureTheory.SimpleFunc.eapprox_comp
-/

#print MeasureTheory.SimpleFunc.eapproxDiff /-
/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapproxDiff (f : α → ℝ≥0∞) : ∀ n : ℕ, α →ₛ ℝ≥0
  | 0 => (eapprox f 0).map ENNReal.toNNReal
  | n + 1 => (eapprox f (n + 1) - eapprox f n).map ENNReal.toNNReal
#align measure_theory.simple_func.eapprox_diff MeasureTheory.SimpleFunc.eapproxDiff
-/

/- warning: measure_theory.simple_func.sum_eapprox_diff -> MeasureTheory.SimpleFunc.sum_eapproxDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal) (n : Nat) (a : α), Eq.{1} ENNReal (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal _inst_1) (MeasureTheory.SimpleFunc.eapproxDiff.{u1} α _inst_1 f k) a))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal _inst_1) (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f n) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal) (n : Nat) (a : α), Eq.{1} ENNReal (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α _inst_1 NNReal (MeasureTheory.SimpleFunc.eapproxDiff.{u1} α _inst_1 f k) a))) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α _inst_1 ENNReal (MeasureTheory.SimpleFunc.eapprox.{u1} α _inst_1 f n) a)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.sum_eapprox_diff MeasureTheory.SimpleFunc.sum_eapproxDiffₓ'. -/
theorem sum_eapproxDiff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
    (∑ k in Finset.range (n + 1), (eapproxDiff f k a : ℝ≥0∞)) = eapprox f n a :=
  by
  induction' n with n IH
  · simp only [Nat.zero_eq, Finset.sum_singleton, Finset.range_one]; rfl
  · rw [Finset.sum_range_succ, Nat.succ_eq_add_one, IH, eapprox_diff, coe_map, Function.comp_apply,
      coe_sub, Pi.sub_apply, ENNReal.coe_toNNReal,
      add_tsub_cancel_of_le (monotone_eapprox f (Nat.le_succ _) _)]
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n + 1) a)).Ne
    rw [tsub_le_iff_right]
    exact le_self_add
#align measure_theory.simple_func.sum_eapprox_diff MeasureTheory.SimpleFunc.sum_eapproxDiff

/- warning: measure_theory.simple_func.tsum_eapprox_diff -> MeasureTheory.SimpleFunc.tsum_eapproxDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal), (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (forall (a : α), Eq.{1} ENNReal (tsum.{0, 0} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace Nat (fun (n : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 NNReal) => α -> NNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α NNReal _inst_1) (MeasureTheory.SimpleFunc.eapproxDiff.{u1} α _inst_1 f n) a))) (f a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : α -> ENNReal), (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (forall (a : α), Eq.{1} ENNReal (tsum.{0, 0} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal Nat (fun (n : Nat) => ENNReal.some (MeasureTheory.SimpleFunc.toFun.{u1, 0} α _inst_1 NNReal (MeasureTheory.SimpleFunc.eapproxDiff.{u1} α _inst_1 f n) a))) (f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.tsum_eapprox_diff MeasureTheory.SimpleFunc.tsum_eapproxDiffₓ'. -/
theorem tsum_eapproxDiff (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) :
    (∑' n, (eapproxDiff f n a : ℝ≥0∞)) = f a := by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_at_top_nat 1), sum_eapprox_diff,
    supr_eapprox_apply f hf a]
#align measure_theory.simple_func.tsum_eapprox_diff MeasureTheory.SimpleFunc.tsum_eapproxDiff

end Eapprox

end Measurable

section Measure

variable {m : MeasurableSpace α} {μ ν : Measure α}

#print MeasureTheory.SimpleFunc.lintegral /-
/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  ∑ x in f.range, x * μ (f ⁻¹' {x})
#align measure_theory.simple_func.lintegral MeasureTheory.SimpleFunc.lintegral
-/

/- warning: measure_theory.simple_func.lintegral_eq_of_subset -> MeasureTheory.SimpleFunc.lintegral_eq_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Finset.{0} ENNReal}, (forall (x : α), (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, 0} α ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasSingleton.{0} ENNReal) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f x)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Membership.Mem.{0, 0} ENNReal (Finset.{0} ENNReal) (Finset.hasMem.{0} ENNReal) (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f x) s)) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Finset.sum.{0, 0} ENNReal ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, 0} α ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasSingleton.{0} ENNReal) x))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Finset.{0} ENNReal}, (forall (x : α), (Ne.{1} ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.preimage.{u1, 0} α ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instSingletonSet.{0} ENNReal) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f x)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Membership.mem.{0, 0} ENNReal (Finset.{0} ENNReal) (Finset.instMembershipFinset.{0} ENNReal) (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f x) s)) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Finset.sum.{0, 0} ENNReal ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.preimage.{u1, 0} α ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instSingletonSet.{0} ENNReal) x))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_eq_of_subset MeasureTheory.SimpleFunc.lintegral_eq_of_subsetₓ'. -/
theorem lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞}
    (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
    f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
  by
  refine' Finset.sum_bij_ne_zero (fun r _ _ => r) _ _ _ _
  · simpa only [forall_range_iff, mul_ne_zero_iff, and_imp]
  · intros ; assumption
  · intro b _ hb
    refine' ⟨b, _, hb, rfl⟩
    rw [mem_range, ← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
  · intros ; rfl
#align measure_theory.simple_func.lintegral_eq_of_subset MeasureTheory.SimpleFunc.lintegral_eq_of_subset

/- warning: measure_theory.simple_func.lintegral_eq_of_subset' -> MeasureTheory.SimpleFunc.lintegral_eq_of_subset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Finset.{0} ENNReal}, (HasSubset.Subset.{0} (Finset.{0} ENNReal) (Finset.hasSubset.{0} ENNReal) (SDiff.sdiff.{0} (Finset.{0} ENNReal) (Finset.hasSdiff.{0} ENNReal (fun (a : ENNReal) (b : ENNReal) => Option.decidableEq.{0} NNReal (fun (a : NNReal) (b : NNReal) => Subtype.decidableEq.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (a : Real) (b : Real) => Real.decidableEq a b) a b) a b)) (MeasureTheory.SimpleFunc.range.{u1, 0} α ENNReal m f) (Singleton.singleton.{0, 0} ENNReal (Finset.{0} ENNReal) (Finset.hasSingleton.{0} ENNReal) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Finset.sum.{0, 0} ENNReal ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, 0} α ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasSingleton.{0} ENNReal) x))))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Finset.{0} ENNReal}, (HasSubset.Subset.{0} (Finset.{0} ENNReal) (Finset.instHasSubsetFinset.{0} ENNReal) (SDiff.sdiff.{0} (Finset.{0} ENNReal) (Finset.instSDiffFinset.{0} ENNReal (fun (a : ENNReal) (b : ENNReal) => instDecidableEq.{0} ENNReal (instLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))) a b)) (MeasureTheory.SimpleFunc.range.{u1, 0} α ENNReal m f) (Singleton.singleton.{0, 0} ENNReal (Finset.{0} ENNReal) (Finset.instSingletonFinset.{0} ENNReal) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Finset.sum.{0, 0} ENNReal ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (x : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.preimage.{u1, 0} α ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instSingletonSet.{0} ENNReal) x))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_eq_of_subset' MeasureTheory.SimpleFunc.lintegral_eq_of_subset'ₓ'. -/
theorem lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞} (hs : f.range \ {0} ⊆ s) :
    f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hfx _ =>
    hs <| Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩
#align measure_theory.simple_func.lintegral_eq_of_subset' MeasureTheory.SimpleFunc.lintegral_eq_of_subset'

/- warning: measure_theory.simple_func.map_lintegral -> MeasureTheory.SimpleFunc.map_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (g : β -> ENNReal) (f : MeasureTheory.SimpleFunc.{u1, u2} α m β), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.map.{u1, u2, 0} α β ENNReal m g f) μ) (Finset.sum.{0, u2} ENNReal β (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (MeasureTheory.SimpleFunc.range.{u1, u2} α β m f) (fun (x : β) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (g x) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} (g : β -> ENNReal) (f : MeasureTheory.SimpleFunc.{u2, u1} α m β), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u2} α m (MeasureTheory.SimpleFunc.map.{u2, u1, 0} α β ENNReal m g f) μ) (Finset.sum.{0, u1} ENNReal β (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (MeasureTheory.SimpleFunc.range.{u2, u1} α β m f) (fun (x : β) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (g x) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) x)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.map_lintegral MeasureTheory.SimpleFunc.map_lintegralₓ'. -/
/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.  -/
theorem map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
    (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) :=
  by
  simp only [lintegral, range_map]
  refine' Finset.sum_image' _ fun b hb => _
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, Finset.mul_sum]
  refine' Finset.sum_congr _ _
  · congr
  · intro x; simp only [Finset.mem_filter]; rintro ⟨_, h⟩; rw [h]
#align measure_theory.simple_func.map_lintegral MeasureTheory.SimpleFunc.map_lintegral

/- warning: measure_theory.simple_func.add_lintegral -> MeasureTheory.SimpleFunc.add_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (g : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (instHAdd.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instAdd.{u1, 0} α ENNReal m (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g) μ) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m g μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (g : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (instHAdd.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instAdd.{u1, 0} α ENNReal m (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) f g) μ) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m g μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.add_lintegral MeasureTheory.SimpleFunc.add_lintegralₓ'. -/
theorem add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
  calc
    (f + g).lintegral μ =
        ∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x}) :=
      by rw [add_eq_map₂, map_lintegral] <;> exact Finset.sum_congr rfl fun a ha => add_mul _ _ _
    _ =
        (∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) :=
      by rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).lintegral μ + ((pair f g).map Prod.snd).lintegral μ := by
      rw [map_lintegral, map_lintegral]
    _ = lintegral f μ + lintegral g μ := rfl
    
#align measure_theory.simple_func.add_lintegral MeasureTheory.SimpleFunc.add_lintegral

/- warning: measure_theory.simple_func.const_mul_lintegral -> MeasureTheory.SimpleFunc.const_mul_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (x : ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (HMul.hMul.{u1, u1, u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (instHMul.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instMul.{u1, 0} α ENNReal m (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m x) f) μ) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (x : ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (HMul.hMul.{u1, u1, u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (instHMul.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instMul.{u1, 0} α ENNReal m (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m x) f) μ) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.const_mul_lintegral MeasureTheory.SimpleFunc.const_mul_lintegralₓ'. -/
theorem const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
    (const α x * f).lintegral μ = x * f.lintegral μ :=
  calc
    (f.map fun a => x * a).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = ∑ r in f.range, x * (r * μ (f ⁻¹' {r})) :=
      (Finset.sum_congr rfl fun a ha => mul_assoc _ _ _)
    _ = x * f.lintegral μ := Finset.mul_sum.symm
    
#align measure_theory.simple_func.const_mul_lintegral MeasureTheory.SimpleFunc.const_mul_lintegral

/- warning: measure_theory.simple_func.lintegralₗ -> MeasureTheory.SimpleFunc.lintegralₗ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegralₗ MeasureTheory.SimpleFunc.lintegralₗₓ'. -/
/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ {m : MeasurableSpace α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] Measure α →ₗ[ℝ≥0∞] ℝ≥0∞
    where
  toFun f :=
    { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by simp [lintegral, mul_left_comm _ c, Finset.mul_sum] }
  map_add' f g := LinearMap.ext fun μ => add_lintegral f g
  map_smul' c f := LinearMap.ext fun μ => const_mul_lintegral f c
#align measure_theory.simple_func.lintegralₗ MeasureTheory.SimpleFunc.lintegralₗ

/- warning: measure_theory.simple_func.zero_lintegral -> MeasureTheory.SimpleFunc.zero_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (OfNat.ofNat.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) 0 (OfNat.mk.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) 0 (Zero.zero.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instZero.{u1, 0} α ENNReal m ENNReal.hasZero)))) μ) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (OfNat.ofNat.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) 0 (Zero.toOfNat0.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instZero.{u1, 0} α ENNReal m instENNRealZero))) μ) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.zero_lintegral MeasureTheory.SimpleFunc.zero_lintegralₓ'. -/
@[simp]
theorem zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
  LinearMap.ext_iff.1 lintegralₗ.map_zero μ
#align measure_theory.simple_func.zero_lintegral MeasureTheory.SimpleFunc.zero_lintegral

/- warning: measure_theory.simple_func.lintegral_add -> MeasureTheory.SimpleFunc.lintegral_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ν : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHAdd.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instAdd.{u1} α m)) μ ν)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f ν))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ν : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHAdd.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instAdd.{u1} α m)) μ ν)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f ν))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_add MeasureTheory.SimpleFunc.lintegral_addₓ'. -/
theorem lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
  (lintegralₗ f).map_add μ ν
#align measure_theory.simple_func.lintegral_add MeasureTheory.SimpleFunc.lintegral_add

/- warning: measure_theory.simple_func.lintegral_smul -> MeasureTheory.SimpleFunc.lintegral_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) m) c μ)) (SMul.smul.{0, 0} ENNReal ENNReal (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) m)) c μ)) (HSMul.hSMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHSMul.{0, 0} ENNReal ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) c (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_smul MeasureTheory.SimpleFunc.lintegral_smulₓ'. -/
theorem lintegral_smul (f : α →ₛ ℝ≥0∞) (c : ℝ≥0∞) : f.lintegral (c • μ) = c • f.lintegral μ :=
  (lintegralₗ f).map_smul c μ
#align measure_theory.simple_func.lintegral_smul MeasureTheory.SimpleFunc.lintegral_smul

/- warning: measure_theory.simple_func.lintegral_zero -> MeasureTheory.SimpleFunc.lintegral_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α _inst_1 f (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α _inst_1) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α _inst_1) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instZero.{u1} α _inst_1))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, 0} α _inst_1 ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α _inst_1 f (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α _inst_1) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instZero.{u1} α _inst_1)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_zero MeasureTheory.SimpleFunc.lintegral_zeroₓ'. -/
@[simp]
theorem lintegral_zero [MeasurableSpace α] (f : α →ₛ ℝ≥0∞) : f.lintegral 0 = 0 :=
  (lintegralₗ f).map_zero
#align measure_theory.simple_func.lintegral_zero MeasureTheory.SimpleFunc.lintegral_zero

/- warning: measure_theory.simple_func.lintegral_sum -> MeasureTheory.SimpleFunc.lintegral_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {ι : Type.{u2}} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (μ : ι -> (MeasureTheory.Measure.{u1} α m)), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (MeasureTheory.Measure.sum.{u1, u2} α ι m μ)) (tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => MeasureTheory.SimpleFunc.lintegral.{u1} α m f (μ i)))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {ι : Type.{u1}} (f : MeasureTheory.SimpleFunc.{u2, 0} α m ENNReal) (μ : ι -> (MeasureTheory.Measure.{u2} α m)), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u2} α m f (MeasureTheory.Measure.sum.{u2, u1} α ι m μ)) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => MeasureTheory.SimpleFunc.lintegral.{u2} α m f (μ i)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_sum MeasureTheory.SimpleFunc.lintegral_sumₓ'. -/
theorem lintegral_sum {m : MeasurableSpace α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measure α) :
    f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i) :=
  by
  simp only [lintegral, measure.sum_apply, f.measurable_set_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm
#align measure_theory.simple_func.lintegral_sum MeasureTheory.SimpleFunc.lintegral_sum

/- warning: measure_theory.simple_func.restrict_lintegral -> MeasureTheory.SimpleFunc.restrict_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal m ENNReal.hasZero f s) μ) (Finset.sum.{0, 0} ENNReal ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (MeasureTheory.SimpleFunc.range.{u1, 0} α ENNReal m f) (fun (r : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, 0} α ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasSingleton.{0} ENNReal) r)) s)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal m instENNRealZero f s) μ) (Finset.sum.{0, 0} ENNReal ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (MeasureTheory.SimpleFunc.range.{u1, 0} α ENNReal m f) (fun (r : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.preimage.{u1, 0} α ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instSingletonSet.{0} ENNReal) r)) s)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_lintegral MeasureTheory.SimpleFunc.restrict_lintegralₓ'. -/
theorem restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
  calc
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x ∈ s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
        else False.elim <| hx <| by simp [*]
    _ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
      Finset.sum_congr rfl <|
        forall_range_iff.2 fun b =>
          if hb : f b = 0 then by simp only [hb, MulZeroClass.zero_mul]
          else by rw [restrict_preimage_singleton _ hs hb, inter_comm]
    
#align measure_theory.simple_func.restrict_lintegral MeasureTheory.SimpleFunc.restrict_lintegral

/- warning: measure_theory.simple_func.lintegral_restrict -> MeasureTheory.SimpleFunc.lintegral_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (s : Set.{u1} α) (μ : MeasureTheory.Measure.{u1} α m), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (MeasureTheory.Measure.restrict.{u1} α m μ s)) (Finset.sum.{0, 0} ENNReal ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (MeasureTheory.SimpleFunc.range.{u1, 0} α ENNReal m f) (fun (y : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) y (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.preimage.{u1, 0} α ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasSingleton.{0} ENNReal) y)) s))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (s : Set.{u1} α) (μ : MeasureTheory.Measure.{u1} α m), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (MeasureTheory.Measure.restrict.{u1} α m μ s)) (Finset.sum.{0, 0} ENNReal ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (MeasureTheory.SimpleFunc.range.{u1, 0} α ENNReal m f) (fun (y : ENNReal) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) y (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.preimage.{u1, 0} α ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f) (Singleton.singleton.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instSingletonSet.{0} ENNReal) y)) s))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_restrict MeasureTheory.SimpleFunc.lintegral_restrictₓ'. -/
theorem lintegral_restrict {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (s : Set α) (μ : Measure α) :
    f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y} ∩ s) := by
  simp only [lintegral, measure.restrict_apply, f.measurable_set_preimage]
#align measure_theory.simple_func.lintegral_restrict MeasureTheory.SimpleFunc.lintegral_restrict

/- warning: measure_theory.simple_func.restrict_lintegral_eq_lintegral_restrict -> MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal m ENNReal.hasZero f s) μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (MeasureTheory.Measure.restrict.{u1} α m μ s)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal m instENNRealZero f s) μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f (MeasureTheory.Measure.restrict.{u1} α m μ s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_lintegral_eq_lintegral_restrict MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrictₓ'. -/
theorem restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : Set α}
    (hs : MeasurableSet s) : (restrict f s).lintegral μ = f.lintegral (μ.restrict s) := by
  rw [f.restrict_lintegral hs, lintegral_restrict]
#align measure_theory.simple_func.restrict_lintegral_eq_lintegral_restrict MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict

/- warning: measure_theory.simple_func.const_lintegral -> MeasureTheory.SimpleFunc.const_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m c) μ) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m c) μ) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.const_lintegral MeasureTheory.SimpleFunc.const_lintegralₓ'. -/
theorem const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ :=
  by
  rw [lintegral]
  cases isEmpty_or_nonempty α
  · simp [μ.eq_zero_of_is_empty]
  · simp [preimage_const_of_mem]
#align measure_theory.simple_func.const_lintegral MeasureTheory.SimpleFunc.const_lintegral

/- warning: measure_theory.simple_func.const_lintegral_restrict -> MeasureTheory.SimpleFunc.const_lintegral_restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m c) (MeasureTheory.Measure.restrict.{u1} α m μ s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m c) (MeasureTheory.Measure.restrict.{u1} α m μ s)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.const_lintegral_restrict MeasureTheory.SimpleFunc.const_lintegral_restrictₓ'. -/
theorem const_lintegral_restrict (c : ℝ≥0∞) (s : Set α) :
    (const α c).lintegral (μ.restrict s) = c * μ s := by
  rw [const_lintegral, measure.restrict_apply MeasurableSet.univ, univ_inter]
#align measure_theory.simple_func.const_lintegral_restrict MeasureTheory.SimpleFunc.const_lintegral_restrict

/- warning: measure_theory.simple_func.restrict_const_lintegral -> MeasureTheory.SimpleFunc.restrict_const_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal m ENNReal.hasZero (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m c) s) μ) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) c (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ s)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (c : ENNReal) {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (Eq.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m (MeasureTheory.SimpleFunc.restrict.{u1, 0} α ENNReal m instENNRealZero (MeasureTheory.SimpleFunc.const.{u1, 0} α ENNReal m c) s) μ) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) c (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.restrict_const_lintegral MeasureTheory.SimpleFunc.restrict_const_lintegralₓ'. -/
theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ((const α c).restrict s).lintegral μ = c * μ s := by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]
#align measure_theory.simple_func.restrict_const_lintegral MeasureTheory.SimpleFunc.restrict_const_lintegral

/- warning: measure_theory.simple_func.le_sup_lintegral -> MeasureTheory.SimpleFunc.le_sup_lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (g : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal), LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (Sup.sup.{0} ENNReal (SemilatticeSup.toHasSup.{0} ENNReal ENNReal.semilatticeSup) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m g μ)) (MeasureTheory.SimpleFunc.lintegral.{u1} α m (Sup.sup.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instSup.{u1, 0} α ENNReal m (SemilatticeSup.toHasSup.{0} ENNReal ENNReal.semilatticeSup)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (g : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (Sup.sup.{0} ENNReal (SemilatticeSup.toSup.{0} ENNReal instENNRealSemilatticeSup) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m g μ)) (MeasureTheory.SimpleFunc.lintegral.{u1} α m (Sup.sup.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instSup.{u1, 0} α ENNReal m (SemilatticeSup.toSup.{0} ENNReal instENNRealSemilatticeSup)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.le_sup_lintegral MeasureTheory.SimpleFunc.le_sup_lintegralₓ'. -/
theorem le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
  calc
    f.lintegral μ ⊔ g.lintegral μ =
        ((pair f g).map Prod.fst).lintegral μ ⊔ ((pair f g).map Prod.snd).lintegral μ :=
      rfl
    _ ≤ ∑ x in (pair f g).range, (x.1 ⊔ x.2) * μ (pair f g ⁻¹' {x}) :=
      by
      rw [map_lintegral, map_lintegral]
      refine' sup_le _ _ <;> refine' Finset.sum_le_sum fun a _ => mul_le_mul_right' _ _
      exact le_sup_left
      exact le_sup_right
    _ = (f ⊔ g).lintegral μ := by rw [sup_eq_map₂, map_lintegral]
    
#align measure_theory.simple_func.le_sup_lintegral MeasureTheory.SimpleFunc.le_sup_lintegral

/- warning: measure_theory.simple_func.lintegral_mono -> MeasureTheory.SimpleFunc.lintegral_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ν : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal} {g : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (LE.le.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instLE.{u1, 0} α ENNReal m (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) f g) -> (LE.le.{u1} (MeasureTheory.Measure.{u1} α m) (Preorder.toHasLe.{u1} (MeasureTheory.Measure.{u1} α m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instPartialOrder.{u1} α m))) μ ν) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m g ν))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {ν : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal} {g : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (LE.le.{u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (MeasureTheory.SimpleFunc.instLE.{u1, 0} α ENNReal m (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) f g) -> (LE.le.{u1} (MeasureTheory.Measure.{u1} α m) (Preorder.toLE.{u1} (MeasureTheory.Measure.{u1} α m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instPartialOrder.{u1} α m))) μ ν) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (MeasureTheory.SimpleFunc.lintegral.{u1} α m g ν))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.lintegral_mono MeasureTheory.SimpleFunc.lintegral_monoₓ'. -/
/-- `simple_func.lintegral` is monotone both in function and in measure. -/
@[mono]
theorem lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) :
    f.lintegral μ ≤ g.lintegral ν :=
  calc
    f.lintegral μ ≤ f.lintegral μ ⊔ g.lintegral μ := le_sup_left
    _ ≤ (f ⊔ g).lintegral μ := (le_sup_lintegral _ _)
    _ = g.lintegral μ := by rw [sup_of_le_right hfg]
    _ ≤ g.lintegral ν :=
      Finset.sum_le_sum fun y hy => ENNReal.mul_left_mono <| hμν _ (g.measurableSet_preimage _)
    
#align measure_theory.simple_func.lintegral_mono MeasureTheory.SimpleFunc.lintegral_mono

#print MeasureTheory.SimpleFunc.lintegral_eq_of_measure_preimage /-
/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
theorem lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
    {ν : Measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν :=
  by
  simp only [lintegral, ← H]
  apply lintegral_eq_of_subset
  simp only [H]
  intros
  exact mem_range_of_measure_ne_zero ‹_›
#align measure_theory.simple_func.lintegral_eq_of_measure_preimage MeasureTheory.SimpleFunc.lintegral_eq_of_measure_preimage
-/

#print MeasureTheory.SimpleFunc.lintegral_congr /-
/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
theorem lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage fun y =>
    measure_congr <| Eventually.set_eq <| h.mono fun x hx => by simp [hx]
#align measure_theory.simple_func.lintegral_congr MeasureTheory.SimpleFunc.lintegral_congr
-/

#print MeasureTheory.SimpleFunc.lintegral_map' /-
theorem lintegral_map' {β} [MeasurableSpace β] {μ' : Measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
    (m' : α → β) (eq : ∀ a, f a = g (m' a)) (h : ∀ s, MeasurableSet s → μ' s = μ (m' ⁻¹' s)) :
    f.lintegral μ = g.lintegral μ' :=
  lintegral_eq_of_measure_preimage fun y => by simp only [preimage, Eq];
    exact (h (g ⁻¹' {y}) (g.measurable_set_preimage _)).symm
#align measure_theory.simple_func.lintegral_map' MeasureTheory.SimpleFunc.lintegral_map'
-/

#print MeasureTheory.SimpleFunc.lintegral_map /-
theorem lintegral_map {β} [MeasurableSpace β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : Measurable f) :
    g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ :=
  Eq.symm <| lintegral_map' _ _ f (fun a => rfl) fun s hs => Measure.map_apply hf hs
#align measure_theory.simple_func.lintegral_map MeasureTheory.SimpleFunc.lintegral_map
-/

end Measure

section FinMeasSupp

open Finset Function

/- warning: measure_theory.simple_func.support_eq -> MeasureTheory.SimpleFunc.support_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : Zero.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β), Eq.{succ u1} (Set.{u1} α) (Function.support.{u1, u2} α β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f)) (Set.iUnion.{u1, succ u2} α β (fun (y : β) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (Finset.filter.{u2} β (fun (y : β) => Ne.{succ u2} β y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (fun (a : β) => Ne.decidable.{succ u2} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b)) a (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (Finset.filter.{u2} β (fun (y : β) => Ne.{succ u2} β y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (fun (a : β) => Ne.decidable.{succ u2} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u2} β a b)) a (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2)))) (MeasureTheory.SimpleFunc.range.{u1, u2} α β _inst_1 f))) => Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_1) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : Zero.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 β), Eq.{succ u2} (Set.{u2} α) (Function.support.{u2, u1} α β _inst_2 (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f)) (Set.iUnion.{u2, succ u1} α β (fun (y : β) => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (Finset.filter.{u1} β (fun (y : β) => Ne.{succ u1} β y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) (fun (a : β) => instDecidableNot (Eq.{succ u1} β a (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) (Classical.propDecidable (Eq.{succ u1} β a (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))))) (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f))) (fun (H : Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (Finset.filter.{u1} β (fun (y : β) => Ne.{succ u1} β y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) (fun (a : β) => instDecidableNot (Eq.{succ u1} β a (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))) (Classical.propDecidable (Eq.{succ u1} β a (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2))))) (MeasureTheory.SimpleFunc.range.{u2, u1} α β _inst_1 f))) => Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.support_eq MeasureTheory.SimpleFunc.support_eqₓ'. -/
theorem support_eq [MeasurableSpace α] [Zero β] (f : α →ₛ β) :
    support f = ⋃ y ∈ f.range.filterₓ fun y => y ≠ 0, f ⁻¹' {y} :=
  Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and_iff, exists_prop,
      mem_Union, Set.mem_range, mem_singleton_iff, exists_eq_right']
#align measure_theory.simple_func.support_eq MeasureTheory.SimpleFunc.support_eq

variable {m : MeasurableSpace α} [Zero β] [Zero γ] {μ : Measure α} {f : α →ₛ β}

/- warning: measure_theory.simple_func.measurable_set_support -> MeasureTheory.SimpleFunc.measurableSet_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u2} β] [_inst_3 : MeasurableSpace.{u1} α] (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_3 β), MeasurableSet.{u1} α _inst_3 (Function.support.{u1, u2} α β _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_3 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_3 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β _inst_3) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u1} β] [_inst_3 : MeasurableSpace.{u2} α] (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_3 β), MeasurableSet.{u2} α _inst_3 (Function.support.{u2, u1} α β _inst_1 (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_3 β f))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.measurable_set_support MeasureTheory.SimpleFunc.measurableSet_supportₓ'. -/
theorem measurableSet_support [MeasurableSpace α] (f : α →ₛ β) : MeasurableSet (support f) := by
  rw [f.support_eq]; exact Finset.measurableSet_biUnion _ fun y hy => measurable_set_fiber _ _
#align measure_theory.simple_func.measurable_set_support MeasureTheory.SimpleFunc.measurableSet_support

#print MeasureTheory.SimpleFunc.FinMeasSupp /-
/-- A `simple_func` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def FinMeasSupp {m : MeasurableSpace α} (f : α →ₛ β) (μ : Measure α) : Prop :=
  f =ᶠ[μ.cofinite] 0
#align measure_theory.simple_func.fin_meas_supp MeasureTheory.SimpleFunc.FinMeasSupp
-/

/- warning: measure_theory.simple_func.fin_meas_supp_iff_support -> MeasureTheory.SimpleFunc.finMeasSupp_iff_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β}, Iff (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Function.support.{u1, u2} α β _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) f))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : Zero.{u1} β] {μ : MeasureTheory.Measure.{u2} α m} {f : MeasureTheory.SimpleFunc.{u2, u1} α m β}, Iff (MeasureTheory.SimpleFunc.FinMeasSupp.{u2, u1} α β _inst_1 m f μ) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m μ) (Function.support.{u2, u1} α β _inst_1 (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β f))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp_iff_support MeasureTheory.SimpleFunc.finMeasSupp_iff_supportₓ'. -/
theorem finMeasSupp_iff_support : f.FinMeasSupp μ ↔ μ (support f) < ∞ :=
  Iff.rfl
#align measure_theory.simple_func.fin_meas_supp_iff_support MeasureTheory.SimpleFunc.finMeasSupp_iff_support

/- warning: measure_theory.simple_func.fin_meas_supp_iff -> MeasureTheory.SimpleFunc.finMeasSupp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β}, Iff (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ) (forall (y : β), (Ne.{succ u2} β y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_1)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : Zero.{u1} β] {μ : MeasureTheory.Measure.{u2} α m} {f : MeasureTheory.SimpleFunc.{u2, u1} α m β}, Iff (MeasureTheory.SimpleFunc.FinMeasSupp.{u2, u1} α β _inst_1 m f μ) (forall (y : β), (Ne.{succ u1} β y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_1))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp_iff MeasureTheory.SimpleFunc.finMeasSupp_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem finMeasSupp_iff : f.FinMeasSupp μ ↔ ∀ (y) (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞ :=
  by
  constructor
  · refine' fun h y hy => lt_of_le_of_lt (measure_mono _) h
    exact fun x hx (H : f x = 0) => hy <| H ▸ Eq.symm hx
  · intro H
    rw [fin_meas_supp_iff_support, support_eq]
    refine' lt_of_le_of_lt (measure_bUnion_finset_le _ _) (sum_lt_top _)
    exact fun y hy => (H y (Finset.mem_filter.1 hy).2).Ne
#align measure_theory.simple_func.fin_meas_supp_iff MeasureTheory.SimpleFunc.finMeasSupp_iff

namespace FinMeasSupp

/- warning: measure_theory.simple_func.fin_meas_supp.meas_preimage_singleton_ne_zero -> MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ) -> (forall {y : β}, (Ne.{succ u2} β y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_1)))) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) y))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_1 : Zero.{u1} β] {μ : MeasureTheory.Measure.{u2} α m} {f : MeasureTheory.SimpleFunc.{u2, u1} α m β}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u2, u1} α β _inst_1 m f μ) -> (forall {y : β}, (Ne.{succ u1} β y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_1))) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m μ) (Set.preimage.{u2, u1} α β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.meas_preimage_singleton_ne_zero MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zeroₓ'. -/
theorem meas_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y ≠ 0) :
    μ (f ⁻¹' {y}) < ∞ :=
  finMeasSupp_iff.1 h y hy
#align measure_theory.simple_func.fin_meas_supp.meas_preimage_singleton_ne_zero MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zero

/- warning: measure_theory.simple_func.fin_meas_supp.map -> MeasureTheory.SimpleFunc.FinMeasSupp.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] [_inst_2 : Zero.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : β -> γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ) -> (Eq.{succ u3} γ (g (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_1)))) (OfNat.ofNat.{u3} γ 0 (OfNat.mk.{u3} γ 0 (Zero.zero.{u3} γ _inst_2)))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u3} α γ _inst_2 m (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ m g f) μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : MeasurableSpace.{u3} α} [_inst_1 : Zero.{u2} β] [_inst_2 : Zero.{u1} γ] {μ : MeasureTheory.Measure.{u3} α m} {f : MeasureTheory.SimpleFunc.{u3, u2} α m β} {g : β -> γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u2} α β _inst_1 m f μ) -> (Eq.{succ u1} γ (g (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_1))) (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_2))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u1} α γ _inst_2 m (MeasureTheory.SimpleFunc.map.{u3, u2, u1} α β γ m g f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.map MeasureTheory.SimpleFunc.FinMeasSupp.mapₓ'. -/
protected theorem map {g : β → γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0) : (f.map g).FinMeasSupp μ :=
  flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)
#align measure_theory.simple_func.fin_meas_supp.map MeasureTheory.SimpleFunc.FinMeasSupp.map

/- warning: measure_theory.simple_func.fin_meas_supp.of_map -> MeasureTheory.SimpleFunc.FinMeasSupp.of_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] [_inst_2 : Zero.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : β -> γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u3} α γ _inst_2 m (MeasureTheory.SimpleFunc.map.{u1, u2, u3} α β γ m g f) μ) -> (forall (b : β), (Eq.{succ u3} γ (g b) (OfNat.ofNat.{u3} γ 0 (OfNat.mk.{u3} γ 0 (Zero.zero.{u3} γ _inst_2)))) -> (Eq.{succ u2} β b (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_1))))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {m : MeasurableSpace.{u3} α} [_inst_1 : Zero.{u1} β] [_inst_2 : Zero.{u2} γ] {μ : MeasureTheory.Measure.{u3} α m} {f : MeasureTheory.SimpleFunc.{u3, u1} α m β} {g : β -> γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u2} α γ _inst_2 m (MeasureTheory.SimpleFunc.map.{u3, u1, u2} α β γ m g f) μ) -> (forall (b : β), (Eq.{succ u2} γ (g b) (OfNat.ofNat.{u2} γ 0 (Zero.toOfNat0.{u2} γ _inst_2))) -> (Eq.{succ u1} β b (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_1)))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u1} α β _inst_1 m f μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.of_map MeasureTheory.SimpleFunc.FinMeasSupp.of_mapₓ'. -/
theorem of_map {g : β → γ} (h : (f.map g).FinMeasSupp μ) (hg : ∀ b, g b = 0 → b = 0) :
    f.FinMeasSupp μ :=
  flip lt_of_le_of_lt h <| measure_mono <| support_subset_comp hg _
#align measure_theory.simple_func.fin_meas_supp.of_map MeasureTheory.SimpleFunc.FinMeasSupp.of_map

#print MeasureTheory.SimpleFunc.FinMeasSupp.map_iff /-
theorem map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
    (f.map g).FinMeasSupp μ ↔ f.FinMeasSupp μ :=
  ⟨fun h => h.of_map fun b => hg.1, fun h => h.map <| hg.2 rfl⟩
#align measure_theory.simple_func.fin_meas_supp.map_iff MeasureTheory.SimpleFunc.FinMeasSupp.map_iff
-/

/- warning: measure_theory.simple_func.fin_meas_supp.pair -> MeasureTheory.SimpleFunc.FinMeasSupp.pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] [_inst_2 : Zero.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : MeasureTheory.SimpleFunc.{u1, u3} α m γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u3} α γ _inst_2 m g μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (Prod.hasZero.{u2, u3} β γ _inst_1 _inst_2) m (MeasureTheory.SimpleFunc.pair.{u1, u2, u3} α β γ m f g) μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {m : MeasurableSpace.{u3} α} [_inst_1 : Zero.{u1} β] [_inst_2 : Zero.{u2} γ] {μ : MeasureTheory.Measure.{u3} α m} {f : MeasureTheory.SimpleFunc.{u3, u1} α m β} {g : MeasureTheory.SimpleFunc.{u3, u2} α m γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u1} α β _inst_1 m f μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u2} α γ _inst_2 m g μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, max u1 u2} α (Prod.{u1, u2} β γ) (Prod.instZeroSum.{u1, u2} β γ _inst_1 _inst_2) m (MeasureTheory.SimpleFunc.pair.{u3, u1, u2} α β γ m f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.pair MeasureTheory.SimpleFunc.FinMeasSupp.pairₓ'. -/
protected theorem pair {g : α →ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    (pair f g).FinMeasSupp μ :=
  calc
    μ (support <| pair f g) = μ (support f ∪ support g) := congr_arg μ <| support_prod_mk f g
    _ ≤ μ (support f) + μ (support g) := (measure_union_le _ _)
    _ < _ := add_lt_top.2 ⟨hf, hg⟩
    
#align measure_theory.simple_func.fin_meas_supp.pair MeasureTheory.SimpleFunc.FinMeasSupp.pair

/- warning: measure_theory.simple_func.fin_meas_supp.map₂ -> MeasureTheory.SimpleFunc.FinMeasSupp.map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {m : MeasurableSpace.{u1} α} [_inst_1 : Zero.{u2} β] [_inst_2 : Zero.{u3} γ] {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} [_inst_3 : Zero.{u4} δ], (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β _inst_1 m f μ) -> (forall {g : MeasureTheory.SimpleFunc.{u1, u3} α m γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u3} α γ _inst_2 m g μ) -> (forall {op : β -> γ -> δ}, (Eq.{succ u4} δ (op (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_1))) (OfNat.ofNat.{u3} γ 0 (OfNat.mk.{u3} γ 0 (Zero.zero.{u3} γ _inst_2)))) (OfNat.ofNat.{u4} δ 0 (OfNat.mk.{u4} δ 0 (Zero.zero.{u4} δ _inst_3)))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u4} α δ _inst_3 m (MeasureTheory.SimpleFunc.map.{u1, max u2 u3, u4} α (Prod.{u2, u3} β γ) δ m (Function.uncurry.{u2, u3, u4} β γ δ op) (MeasureTheory.SimpleFunc.pair.{u1, u2, u3} α β γ m f g)) μ)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u4}} {m : MeasurableSpace.{u3} α} [_inst_1 : Zero.{u2} β] [_inst_2 : Zero.{u1} γ] {μ : MeasureTheory.Measure.{u3} α m} {f : MeasureTheory.SimpleFunc.{u3, u2} α m β} [_inst_3 : Zero.{u4} δ], (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u2} α β _inst_1 m f μ) -> (forall {g : MeasureTheory.SimpleFunc.{u3, u1} α m γ}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u1} α γ _inst_2 m g μ) -> (forall {op : β -> γ -> δ}, (Eq.{succ u4} δ (op (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_1)) (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_2))) (OfNat.ofNat.{u4} δ 0 (Zero.toOfNat0.{u4} δ _inst_3))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u3, u4} α δ _inst_3 m (MeasureTheory.SimpleFunc.map.{u3, max u1 u2, u4} α (Prod.{u2, u1} β γ) δ m (Function.uncurry.{u2, u1, u4} β γ δ op) (MeasureTheory.SimpleFunc.pair.{u3, u2, u1} α β γ m f g)) μ)))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.map₂ MeasureTheory.SimpleFunc.FinMeasSupp.map₂ₓ'. -/
protected theorem map₂ [Zero δ] (hf : f.FinMeasSupp μ) {g : α →ₛ γ} (hg : g.FinMeasSupp μ)
    {op : β → γ → δ} (H : op 0 0 = 0) : ((pair f g).map (Function.uncurry op)).FinMeasSupp μ :=
  (hf.pair hg).map H
#align measure_theory.simple_func.fin_meas_supp.map₂ MeasureTheory.SimpleFunc.FinMeasSupp.map₂

/- warning: measure_theory.simple_func.fin_meas_supp.add -> MeasureTheory.SimpleFunc.FinMeasSupp.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_3 : AddMonoid.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : MeasureTheory.SimpleFunc.{u1, u2} α m β}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m f μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m g μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (instHAdd.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.instAdd.{u1, u2} α β m (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_3 : AddMonoid.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : MeasureTheory.SimpleFunc.{u1, u2} α m β}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_3) m f μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_3) m g μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (AddMonoid.toZero.{u2} β _inst_3) m (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (instHAdd.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.instAdd.{u1, u2} α β m (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.add MeasureTheory.SimpleFunc.FinMeasSupp.addₓ'. -/
protected theorem add {β} [AddMonoid β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f + g).FinMeasSupp μ := by rw [add_eq_map₂];
  exact hf.map₂ hg (zero_add 0)
#align measure_theory.simple_func.fin_meas_supp.add MeasureTheory.SimpleFunc.FinMeasSupp.add

/- warning: measure_theory.simple_func.fin_meas_supp.mul -> MeasureTheory.SimpleFunc.FinMeasSupp.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_3 : MonoidWithZero.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : MeasureTheory.SimpleFunc.{u1, u2} α m β}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m f μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m g μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (instHMul.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.instMul.{u1, u2} α β m (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_3 : MonoidWithZero.{u2} β] {f : MeasureTheory.SimpleFunc.{u1, u2} α m β} {g : MeasureTheory.SimpleFunc.{u1, u2} α m β}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β _inst_3) m f μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β _inst_3) m g μ) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β _inst_3) m (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.{u1, u2} α m β) (instHMul.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (MeasureTheory.SimpleFunc.instMul.{u1, u2} α β m (MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.mul MeasureTheory.SimpleFunc.FinMeasSupp.mulₓ'. -/
protected theorem mul {β} [MonoidWithZero β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f * g).FinMeasSupp μ := by rw [mul_eq_map₂];
  exact hf.map₂ hg (MulZeroClass.zero_mul 0)
#align measure_theory.simple_func.fin_meas_supp.mul MeasureTheory.SimpleFunc.FinMeasSupp.mul

/- warning: measure_theory.simple_func.fin_meas_supp.lintegral_lt_top -> MeasureTheory.SimpleFunc.FinMeasSupp.lintegral_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, 0} α ENNReal ENNReal.hasZero m f μ) -> (Filter.Eventually.{u1} α (fun (a : α) => Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, 0} α ENNReal instENNRealZero m f μ) -> (Filter.Eventually.{u1} α (fun (a : α) => Ne.{1} ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.lintegral_lt_top MeasureTheory.SimpleFunc.FinMeasSupp.lintegral_lt_topₓ'. -/
theorem lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.FinMeasSupp μ) (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.lintegral μ < ∞ := by
  refine' sum_lt_top fun a ha => _
  rcases eq_or_ne a ∞ with (rfl | ha)
  · simp only [ae_iff, Ne.def, Classical.not_not] at hf
    simp [Set.preimage, hf]
  · by_cases ha0 : a = 0
    · subst a; rwa [MulZeroClass.zero_mul]
    · exact mul_ne_top ha (fin_meas_supp_iff.1 hm _ ha0).Ne
#align measure_theory.simple_func.fin_meas_supp.lintegral_lt_top MeasureTheory.SimpleFunc.FinMeasSupp.lintegral_lt_top

/- warning: measure_theory.simple_func.fin_meas_supp.of_lintegral_ne_top -> MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (Ne.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, 0} α ENNReal ENNReal.hasZero m f μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (Ne.{1} ENNReal (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, 0} α ENNReal instENNRealZero m f μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.of_lintegral_ne_top MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_topₓ'. -/
theorem of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.FinMeasSupp μ :=
  by
  refine' fin_meas_supp_iff.2 fun b hb => _
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  refine' ENNReal.lt_top_of_mul_ne_top_right _ hb
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).Ne
#align measure_theory.simple_func.fin_meas_supp.of_lintegral_ne_top MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top

/- warning: measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top -> MeasureTheory.SimpleFunc.FinMeasSupp.iff_lintegral_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (Filter.Eventually.{u1} α (fun (a : α) => Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) (fun (_x : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal) => α -> ENNReal) (MeasureTheory.SimpleFunc.instCoeFun.{u1, 0} α ENNReal m) f a) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Iff (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, 0} α ENNReal ENNReal.hasZero m f μ) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : MeasureTheory.SimpleFunc.{u1, 0} α m ENNReal}, (Filter.Eventually.{u1} α (fun (a : α) => Ne.{1} ENNReal (MeasureTheory.SimpleFunc.toFun.{u1, 0} α m ENNReal f a) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (MeasureTheory.Measure.ae.{u1} α m μ)) -> (Iff (MeasureTheory.SimpleFunc.FinMeasSupp.{u1, 0} α ENNReal instENNRealZero m f μ) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.SimpleFunc.lintegral.{u1} α m f μ) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top MeasureTheory.SimpleFunc.FinMeasSupp.iff_lintegral_lt_topₓ'. -/
theorem iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.FinMeasSupp μ ↔ f.lintegral μ < ∞ :=
  ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.Ne⟩
#align measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top MeasureTheory.SimpleFunc.FinMeasSupp.iff_lintegral_lt_top

end FinMeasSupp

end FinMeasSupp

/- warning: measure_theory.simple_func.induction -> MeasureTheory.SimpleFunc.induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : AddMonoid.{u2} γ] {P : (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) -> Prop}, (forall (c : γ) {s : Set.{u1} α} (hs : MeasurableSet.{u1} α _inst_1 s), P (MeasureTheory.SimpleFunc.piecewise.{u1, u2} α γ _inst_1 s hs (MeasureTheory.SimpleFunc.const.{u1, u2} α γ _inst_1 c) (MeasureTheory.SimpleFunc.const.{u1, u2} α γ _inst_1 (OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ _inst_2)))))))) -> (forall {{f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ}} {{g : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ}}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.support.{u1, u2} α γ (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α γ _inst_1) f)) (Function.support.{u1, u2} α γ (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) => α -> γ) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α γ _inst_1) g))) -> (P f) -> (P g) -> (P (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (instHAdd.{max u1 u2} (MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ) (MeasureTheory.SimpleFunc.instAdd.{u1, u2} α γ _inst_1 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ _inst_2)))) f g))) -> (forall (f : MeasureTheory.SimpleFunc.{u1, u2} α _inst_1 γ), P f)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : AddMonoid.{u1} γ] {P : (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) -> Prop}, (forall (c : γ) {s : Set.{u2} α} (hs : MeasurableSet.{u2} α _inst_1 s), P (MeasureTheory.SimpleFunc.piecewise.{u2, u1} α γ _inst_1 s hs (MeasureTheory.SimpleFunc.const.{u2, u1} α γ _inst_1 c) (MeasureTheory.SimpleFunc.const.{u2, u1} α γ _inst_1 (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ (AddMonoid.toZero.{u1} γ _inst_2)))))) -> (forall {{f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ}} {{g : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ}}, (Disjoint.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (Function.support.{u2, u1} α γ (AddMonoid.toZero.{u1} γ _inst_2) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 γ f)) (Function.support.{u2, u1} α γ (AddMonoid.toZero.{u1} γ _inst_2) (MeasureTheory.SimpleFunc.toFun.{u2, u1} α _inst_1 γ g))) -> (P f) -> (P g) -> (P (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) (instHAdd.{max u2 u1} (MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ) (MeasureTheory.SimpleFunc.instAdd.{u2, u1} α γ _inst_1 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ _inst_2)))) f g))) -> (forall (f : MeasureTheory.SimpleFunc.{u2, u1} α _inst_1 γ), P f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.induction MeasureTheory.SimpleFunc.inductionₓ'. -/
/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
@[elab_as_elim]
protected theorem induction {α γ} [MeasurableSpace α] [AddMonoid γ] {P : SimpleFunc α γ → Prop}
    (h_ind :
      ∀ (c) {s} (hs : MeasurableSet s),
        P (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)))
    (h_add : ∀ ⦃f g : SimpleFunc α γ⦄, Disjoint (support f) (support g) → P f → P g → P (f + g))
    (f : SimpleFunc α γ) : P f :=
  by
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, simple_func.coe_range] at h
  revert s f h; refine' Finset.induction _ _
  · intro f hf; rw [Finset.coe_empty, diff_eq_empty, range_subset_singleton] at hf
    convert h_ind 0 MeasurableSet.univ; ext x; simp [hf]
  · intro x s hxs ih f hf
    have mx := f.measurable_set_preimage {x}
    let g := simple_func.piecewise (f ⁻¹' {x}) mx 0 f
    have Pg : P g := by
      apply ih; simp only [g, simple_func.coe_piecewise, range_piecewise]
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, hf, Finset.coe_insert,
        insert_diff_self_of_not_mem, diff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]; convert Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert h_add _ Pg (h_ind x mx)
    · ext1 y; by_cases hy : y ∈ f ⁻¹' {x} <;> [simpa [hy] ;simp [hy]]
    rw [disjoint_iff_inf_le]
    rintro y; by_cases hy : y ∈ f ⁻¹' {x} <;> simp [hy]
#align measure_theory.simple_func.induction MeasureTheory.SimpleFunc.induction

end SimpleFunc

end MeasureTheory

open MeasureTheory MeasureTheory.SimpleFunc

/- warning: measurable.ennreal_induction -> Measurable.ennreal_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {P : (α -> ENNReal) -> Prop}, (forall (c : ENNReal) {{s : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 s) -> (P (Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (fun (_x : α) => c)))) -> (forall {{f : α -> ENNReal}} {{g : α -> ENNReal}}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Function.support.{u1, 0} α ENNReal ENNReal.hasZero f) (Function.support.{u1, 0} α ENNReal ENNReal.hasZero g)) -> (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace g) -> (P f) -> (P g) -> (P (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) f g))) -> (forall {{f : Nat -> α -> ENNReal}}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace (f n)) -> (Monotone.{0, u1} Nat (α -> ENNReal) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) f) -> (forall (n : Nat), P (f n)) -> (P (fun (x : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) Nat (fun (n : Nat) => f n x)))) -> (forall {{f : α -> ENNReal}}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (P f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {P : (α -> ENNReal) -> Prop}, (forall (c : ENNReal) {{s : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 s) -> (P (Set.indicator.{u1, 0} α ENNReal instENNRealZero s (fun (_x : α) => c)))) -> (forall {{f : α -> ENNReal}} {{g : α -> ENNReal}}, (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Function.support.{u1, 0} α ENNReal instENNRealZero f) (Function.support.{u1, 0} α ENNReal instENNRealZero g)) -> (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace g) -> (P f) -> (P g) -> (P (HAdd.hAdd.{u1, u1, u1} (α -> ENNReal) (α -> ENNReal) (α -> ENNReal) (instHAdd.{u1} (α -> ENNReal) (Pi.instAdd.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))))) f g))) -> (forall {{f : Nat -> α -> ENNReal}}, (forall (n : Nat), Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace (f n)) -> (Monotone.{0, u1} Nat (α -> ENNReal) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Pi.preorder.{u1, 0} α (fun (ᾰ : α) => ENNReal) (fun (i : α) => PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) f) -> (forall (n : Nat), P (f n)) -> (P (fun (x : α) => iSup.{0, 1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) Nat (fun (n : Nat) => f n x)))) -> (forall {{f : α -> ENNReal}}, (Measurable.{u1, 0} α ENNReal _inst_1 ENNReal.measurableSpace f) -> (P f))
Case conversion may be inaccurate. Consider using '#align measurable.ennreal_induction Measurable.ennreal_inductionₓ'. -/
/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
theorem Measurable.ennreal_induction {α} [MeasurableSpace α] {P : (α → ℝ≥0∞) → Prop}
    (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → P (indicator s fun _ => c))
    (h_add :
      ∀ ⦃f g : α → ℝ≥0∞⦄,
        Disjoint (support f) (support g) → Measurable f → Measurable g → P f → P g → P (f + g))
    (h_supr :
      ∀ ⦃f : ℕ → α → ℝ≥0∞⦄ (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) (hP : ∀ n, P (f n)),
        P fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : P f :=
  by
  convert h_supr (fun n => (eapprox f n).Measurable) (monotone_eapprox f) _
  · ext1 x; rw [supr_eapprox_apply f hf]
  ·
    exact fun n =>
      simple_func.induction (fun c s hs => h_ind c hs)
        (fun f g hfg hf hg => h_add hfg f.Measurable g.Measurable hf hg) (eapprox f n)
#align measurable.ennreal_induction Measurable.ennreal_induction

