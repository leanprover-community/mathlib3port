/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.ring
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.NatAntidiagonal
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Ring.Basic

/-!
# Infinite sum in a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
-/


open Filter Finset Function

open BigOperators Classical

variable {ι κ R α : Type _}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] {f g : ι → α}
  {a a₁ a₂ : α}

/- warning: has_sum.mul_left -> HasSum.mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} {a₁ : α} (a₂ : α), (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a₂ (f i)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a₂ a₁))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} {a₁ : α} (a₂ : α), (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a₂ (f i)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a₂ a₁))
Case conversion may be inaccurate. Consider using '#align has_sum.mul_left HasSum.mul_leftₓ'. -/
theorem HasSum.mul_left (a₂) (h : HasSum f a₁) : HasSum (fun i => a₂ * f i) (a₂ * a₁) := by
  simpa only using h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)
#align has_sum.mul_left HasSum.mul_left

/- warning: has_sum.mul_right -> HasSum.mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} {a₁ : α} (a₂ : α), (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) (f i) a₂) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a₁ a₂))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} {a₁ : α} (a₂ : α), (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f a₁) -> (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (f i) a₂) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a₁ a₂))
Case conversion may be inaccurate. Consider using '#align has_sum.mul_right HasSum.mul_rightₓ'. -/
theorem HasSum.mul_right (a₂) (hf : HasSum f a₁) : HasSum (fun i => f i * a₂) (a₁ * a₂) := by
  simpa only using hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)
#align has_sum.mul_right HasSum.mul_right

/- warning: summable.mul_left -> Summable.mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a (f i)))
Case conversion may be inaccurate. Consider using '#align summable.mul_left Summable.mul_leftₓ'. -/
theorem Summable.mul_left (a) (hf : Summable f) : Summable fun i => a * f i :=
  (hf.HasSum.mulLeft _).Summable
#align summable.mul_left Summable.mul_left

/- warning: summable.mul_right -> Summable.mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) (f i) a))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (f i) a))
Case conversion may be inaccurate. Consider using '#align summable.mul_right Summable.mul_rightₓ'. -/
theorem Summable.mul_right (a) (hf : Summable f) : Summable fun i => f i * a :=
  (hf.HasSum.mulRight _).Summable
#align summable.mul_right Summable.mul_right

section tsum

variable [T2Space α]

/- warning: summable.tsum_mul_left -> Summable.tsum_mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a (f i))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a (f i))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i))))
Case conversion may be inaccurate. Consider using '#align summable.tsum_mul_left Summable.tsum_mul_leftₓ'. -/
theorem Summable.tsum_mul_left (a) (hf : Summable f) : (∑' i, a * f i) = a * ∑' i, f i :=
  (hf.HasSum.mulLeft _).tsum_eq
#align summable.tsum_mul_left Summable.tsum_mul_left

/- warning: summable.tsum_mul_right -> Summable.tsum_mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) (f i) a)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 f) -> (Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (f i) a)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a))
Case conversion may be inaccurate. Consider using '#align summable.tsum_mul_right Summable.tsum_mul_rightₓ'. -/
theorem Summable.tsum_mul_right (a) (hf : Summable f) : (∑' i, f i * a) = (∑' i, f i) * a :=
  (hf.HasSum.mulRight _).tsum_eq
#align summable.tsum_mul_right Summable.tsum_mul_right

/- warning: commute.tsum_right -> Commute.tsum_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (forall (i : ι), Commute.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1)) a (f i)) -> (Commute.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1)) a (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (forall (i : ι), Commute.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) a (f i)) -> (Commute.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) a (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align commute.tsum_right Commute.tsum_rightₓ'. -/
theorem Commute.tsum_right (a) (h : ∀ i, Commute a (f i)) : Commute a (∑' i, f i) :=
  if hf : Summable f then
    (hf.tsum_mul_left a).symm.trans ((congr_arg _ <| funext h).trans (hf.tsum_mul_right a))
  else (tsum_eq_zero_of_not_summable hf).symm ▸ Commute.zero_right _
#align commute.tsum_right Commute.tsum_right

/- warning: commute.tsum_left -> Commute.tsum_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (forall (i : ι), Commute.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1)) (f i) a) -> (Commute.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1)) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 _inst_1] {f : ι -> α} [_inst_4 : T2Space.{u2} α _inst_2] (a : α), (forall (i : ι), Commute.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) (f i) a) -> (Commute.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) _inst_2 ι (fun (i : ι) => f i)) a)
Case conversion may be inaccurate. Consider using '#align commute.tsum_left Commute.tsum_leftₓ'. -/
theorem Commute.tsum_left (a) (h : ∀ i, Commute (f i) a) : Commute (∑' i, f i) a :=
  (Commute.tsum_right _ fun i => (h i).symm).symm
#align commute.tsum_left Commute.tsum_left

end tsum

end NonUnitalNonAssocSemiring

section DivisionSemiring

variable [DivisionSemiring α] [TopologicalSpace α] [TopologicalSemiring α] {f g : ι → α}
  {a a₁ a₂ : α}

/- warning: has_sum.div_const -> HasSum.div_const is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a) -> (forall (b : α), HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) (f i) b) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) a b))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a) -> (forall (b : α), HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) (f i) b) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align has_sum.div_const HasSum.div_constₓ'. -/
theorem HasSum.div_const (h : HasSum f a) (b : α) : HasSum (fun i => f i / b) (a / b) := by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]
#align has_sum.div_const HasSum.div_const

/- warning: summable.div_const -> Summable.div_const is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f) -> (forall (b : α), Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) (f i) b))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α}, (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f) -> (forall (b : α), Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) (f i) b))
Case conversion may be inaccurate. Consider using '#align summable.div_const Summable.div_constₓ'. -/
theorem Summable.div_const (h : Summable f) (b : α) : Summable fun i => f i / b :=
  (h.HasSum.div_const _).Summable
#align summable.div_const Summable.div_const

/- warning: has_sum_mul_left_iff -> hasSum_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a₁ : α} {a₂ : α}, (Ne.{succ u2} α a₂ (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))))))) -> (Iff (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) a₂ (f i)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) a₂ a₁)) (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a₁))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a₁ : α} {a₂ : α}, (Ne.{succ u2} α a₂ (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) -> (Iff (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) a₂ (f i)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) a₂ a₁)) (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a₁))
Case conversion may be inaccurate. Consider using '#align has_sum_mul_left_iff hasSum_mul_left_iffₓ'. -/
theorem hasSum_mul_left_iff (h : a₂ ≠ 0) : HasSum (fun i => a₂ * f i) (a₂ * a₁) ↔ HasSum f a₁ :=
  ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSum.mul_left _⟩
#align has_sum_mul_left_iff hasSum_mul_left_iff

/- warning: has_sum_mul_right_iff -> hasSum_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a₁ : α} {a₂ : α}, (Ne.{succ u2} α a₂ (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))))))) -> (Iff (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) (f i) a₂) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) a₁ a₂)) (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a₁))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a₁ : α} {a₂ : α}, (Ne.{succ u2} α a₂ (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) -> (Iff (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) (f i) a₂) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) a₁ a₂)) (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a₁))
Case conversion may be inaccurate. Consider using '#align has_sum_mul_right_iff hasSum_mul_right_iffₓ'. -/
theorem hasSum_mul_right_iff (h : a₂ ≠ 0) : HasSum (fun i => f i * a₂) (a₁ * a₂) ↔ HasSum f a₁ :=
  ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSum.mul_right _⟩
#align has_sum_mul_right_iff hasSum_mul_right_iff

/- warning: has_sum_div_const_iff -> hasSum_div_const_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a₁ : α} {a₂ : α}, (Ne.{succ u2} α a₂ (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))))))) -> (Iff (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) (f i) a₂) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) a₁ a₂)) (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a₁))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a₁ : α} {a₂ : α}, (Ne.{succ u2} α a₂ (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) -> (Iff (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) (f i) a₂) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) a₁ a₂)) (HasSum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f a₁))
Case conversion may be inaccurate. Consider using '#align has_sum_div_const_iff hasSum_div_const_iffₓ'. -/
theorem hasSum_div_const_iff (h : a₂ ≠ 0) : HasSum (fun i => f i / a₂) (a₁ / a₂) ↔ HasSum f a₁ := by
  simpa only [div_eq_mul_inv] using hasSum_mul_right_iff (inv_ne_zero h)
#align has_sum_div_const_iff hasSum_div_const_iff

/- warning: summable_mul_left_iff -> summable_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))))))) -> (Iff (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) a (f i))) (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) -> (Iff (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) a (f i))) (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f))
Case conversion may be inaccurate. Consider using '#align summable_mul_left_iff summable_mul_left_iffₓ'. -/
theorem summable_mul_left_iff (h : a ≠ 0) : (Summable fun i => a * f i) ↔ Summable f :=
  ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H => H.mulLeft _⟩
#align summable_mul_left_iff summable_mul_left_iff

/- warning: summable_mul_right_iff -> summable_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))))))) -> (Iff (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) (f i) a)) (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) -> (Iff (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) (f i) a)) (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f))
Case conversion may be inaccurate. Consider using '#align summable_mul_right_iff summable_mul_right_iffₓ'. -/
theorem summable_mul_right_iff (h : a ≠ 0) : (Summable fun i => f i * a) ↔ Summable f :=
  ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H => H.mulRight _⟩
#align summable_mul_right_iff summable_mul_right_iff

/- warning: summable_div_const_iff -> summable_div_const_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (OfNat.mk.{u2} α 0 (Zero.zero.{u2} α (MulZeroClass.toHasZero.{u2} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))))))) -> (Iff (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) (f i) a)) (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) -> (Iff (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) (f i) a)) (Summable.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 f))
Case conversion may be inaccurate. Consider using '#align summable_div_const_iff summable_div_const_iffₓ'. -/
theorem summable_div_const_iff (h : a ≠ 0) : (Summable fun i => f i / a) ↔ Summable f := by
  simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)
#align summable_div_const_iff summable_div_const_iff

/- warning: tsum_mul_left -> tsum_mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) a (f x))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) a (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => f x)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) a (f x))) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) a (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align tsum_mul_left tsum_mul_leftₓ'. -/
theorem tsum_mul_left [T2Space α] : (∑' x, a * f x) = a * ∑' x, f x :=
  if hf : Summable f then hf.tsum_mul_left a
  else
    if ha : a = 0 then by simp [ha]
    else by
      rw [tsum_eq_zero_of_not_summable hf,
        tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).mp hf), MulZeroClass.mul_zero]
#align tsum_mul_left tsum_mul_left

/- warning: tsum_mul_right -> tsum_mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) (f x) a)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))))) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => f x)) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) (f x) a)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1))))) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => f x)) a)
Case conversion may be inaccurate. Consider using '#align tsum_mul_right tsum_mul_rightₓ'. -/
theorem tsum_mul_right [T2Space α] : (∑' x, f x * a) = (∑' x, f x) * a :=
  if hf : Summable f then hf.tsum_mul_right a
  else
    if ha : a = 0 then by simp [ha]
    else by
      rw [tsum_eq_zero_of_not_summable hf,
        tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).mp hf), MulZeroClass.zero_mul]
#align tsum_mul_right tsum_mul_right

/- warning: tsum_div_const -> tsum_div_const is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) (f x) a)) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (GroupWithZero.toDivInvMonoid.{u2} α (DivisionSemiring.toGroupWithZero.{u2} α _inst_1)))) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => f x)) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionSemiring.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : TopologicalSemiring.{u2} α _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))] {f : ι -> α} {a : α} [_inst_4 : T2Space.{u2} α _inst_2], Eq.{succ u2} α (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) (f x) a)) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivisionSemiring.toDiv.{u2} α _inst_1)) (tsum.{u2, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (DivisionSemiring.toSemiring.{u2} α _inst_1)))) _inst_2 ι (fun (x : ι) => f x)) a)
Case conversion may be inaccurate. Consider using '#align tsum_div_const tsum_div_constₓ'. -/
theorem tsum_div_const [T2Space α] : (∑' x, f x / a) = (∑' x, f x) / a := by
  simpa only [div_eq_mul_inv] using tsum_mul_right
#align tsum_div_const tsum_div_const

end DivisionSemiring

/-!
### Multipliying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `λ x : ι × κ, f x.1 * g x.2` is summable, since there is no way to
deduce this from the summmabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `analysis/normed_space/basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/


section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiring α] [TopologicalSemiring α]
  {f : ι → α} {g : κ → α} {s t u : α}

/- warning: has_sum.mul_eq -> HasSum.mul_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : T3Space.{u3} α _inst_1] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] [_inst_4 : TopologicalSemiring.{u3} α _inst_1 _inst_3] {f : ι -> α} {g : κ -> α} {s : α} {t : α} {u : α}, (HasSum.{u3, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 f s) -> (HasSum.{u3, u2} α κ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 g t) -> (HasSum.{u3, max u1 u2} α (Prod.{u1, u2} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u1, u2} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (f (Prod.fst.{u1, u2} ι κ x)) (g (Prod.snd.{u1, u2} ι κ x))) u) -> (Eq.{succ u3} α (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) s t) u)
but is expected to have type
  forall {ι : Type.{u2}} {κ : Type.{u1}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : T3Space.{u3} α _inst_1] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] [_inst_4 : TopologicalSemiring.{u3} α _inst_1 _inst_3] {f : ι -> α} {g : κ -> α} {s : α} {t : α} {u : α}, (HasSum.{u3, u2} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 f s) -> (HasSum.{u3, u1} α κ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 g t) -> (HasSum.{u3, max u2 u1} α (Prod.{u2, u1} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u2, u1} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) (f (Prod.fst.{u2, u1} ι κ x)) (g (Prod.snd.{u2, u1} ι κ x))) u) -> (Eq.{succ u3} α (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) s t) u)
Case conversion may be inaccurate. Consider using '#align has_sum.mul_eq HasSum.mul_eqₓ'. -/
theorem HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ => f x.1 * g x.2) u) : s * t = u :=
  have key₁ : HasSum (fun i => f i * t) (s * t) := hf.mulRight t
  have this : ∀ i : ι, HasSum (fun c : κ => f i * g c) (f i * t) := fun i => hg.mulLeft (f i)
  have key₂ : HasSum (fun i => f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂
#align has_sum.mul_eq HasSum.mul_eq

/- warning: has_sum.mul -> HasSum.mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : T3Space.{u3} α _inst_1] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] [_inst_4 : TopologicalSemiring.{u3} α _inst_1 _inst_3] {f : ι -> α} {g : κ -> α} {s : α} {t : α}, (HasSum.{u3, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 f s) -> (HasSum.{u3, u2} α κ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 g t) -> (Summable.{u3, max u1 u2} α (Prod.{u1, u2} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u1, u2} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (f (Prod.fst.{u1, u2} ι κ x)) (g (Prod.snd.{u1, u2} ι κ x)))) -> (HasSum.{u3, max u1 u2} α (Prod.{u1, u2} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u1, u2} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (f (Prod.fst.{u1, u2} ι κ x)) (g (Prod.snd.{u1, u2} ι κ x))) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) s t))
but is expected to have type
  forall {ι : Type.{u2}} {κ : Type.{u1}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : T3Space.{u3} α _inst_1] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] [_inst_4 : TopologicalSemiring.{u3} α _inst_1 _inst_3] {f : ι -> α} {g : κ -> α} {s : α} {t : α}, (HasSum.{u3, u2} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 f s) -> (HasSum.{u3, u1} α κ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 g t) -> (Summable.{u3, max u2 u1} α (Prod.{u2, u1} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u2, u1} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) (f (Prod.fst.{u2, u1} ι κ x)) (g (Prod.snd.{u2, u1} ι κ x)))) -> (HasSum.{u3, max u2 u1} α (Prod.{u2, u1} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u2, u1} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) (f (Prod.fst.{u2, u1} ι κ x)) (g (Prod.snd.{u2, u1} ι κ x))) (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) s t))
Case conversion may be inaccurate. Consider using '#align has_sum.mul HasSum.mulₓ'. -/
theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ => f x.1 * g x.2) :
    HasSum (fun x : ι × κ => f x.1 * g x.2) (s * t) :=
  let ⟨u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu
#align has_sum.mul HasSum.mul

/- warning: tsum_mul_tsum -> tsum_mul_tsum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {κ : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : T3Space.{u3} α _inst_1] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] [_inst_4 : TopologicalSemiring.{u3} α _inst_1 _inst_3] {f : ι -> α} {g : κ -> α}, (Summable.{u3, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 f) -> (Summable.{u3, u2} α κ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 g) -> (Summable.{u3, max u1 u2} α (Prod.{u1, u2} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u1, u2} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (f (Prod.fst.{u1, u2} ι κ x)) (g (Prod.snd.{u1, u2} ι κ x)))) -> (Eq.{succ u3} α (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (tsum.{u3, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 ι (fun (x : ι) => f x)) (tsum.{u3, u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 κ (fun (y : κ) => g y))) (tsum.{u3, max u1 u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (Prod.{u1, u2} ι κ) (fun (z : Prod.{u1, u2} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (Distrib.toHasMul.{u3} α (NonUnitalNonAssocSemiring.toDistrib.{u3} α _inst_3))) (f (Prod.fst.{u1, u2} ι κ z)) (g (Prod.snd.{u1, u2} ι κ z)))))
but is expected to have type
  forall {ι : Type.{u2}} {κ : Type.{u1}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : T3Space.{u3} α _inst_1] [_inst_3 : NonUnitalNonAssocSemiring.{u3} α] [_inst_4 : TopologicalSemiring.{u3} α _inst_1 _inst_3] {f : ι -> α} {g : κ -> α}, (Summable.{u3, u2} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 f) -> (Summable.{u3, u1} α κ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 g) -> (Summable.{u3, max u2 u1} α (Prod.{u2, u1} ι κ) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (fun (x : Prod.{u2, u1} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) (f (Prod.fst.{u2, u1} ι κ x)) (g (Prod.snd.{u2, u1} ι κ x)))) -> (Eq.{succ u3} α (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) (tsum.{u3, u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 ι (fun (x : ι) => f x)) (tsum.{u3, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 κ (fun (y : κ) => g y))) (tsum.{u3, max u2 u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α _inst_3) _inst_1 (Prod.{u2, u1} ι κ) (fun (z : Prod.{u2, u1} ι κ) => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocSemiring.toMul.{u3} α _inst_3)) (f (Prod.fst.{u2, u1} ι κ z)) (g (Prod.snd.{u2, u1} ι κ z)))))
Case conversion may be inaccurate. Consider using '#align tsum_mul_tsum tsum_mul_tsumₓ'. -/
/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are abolutely summable. -/
theorem tsum_mul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ => f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2 :=
  hf.HasSum.mul_eq hg.HasSum hfg.HasSum
#align tsum_mul_tsum tsum_mul_tsum

end tsum_mul_tsum

/-!
#### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `finset.range (n+1)`
involving `nat` subtraction.
In order to avoid `nat` subtraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`
-/


section CauchyProduct

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : ℕ → α}

/- warning: summable_mul_prod_iff_summable_mul_sigma_antidiagonal -> summable_mul_prod_iff_summable_mul_sigma_antidiagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α}, Iff (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) (Summable.{u1, 0} α (Sigma.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Sigma.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n))) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (coeBase.{1, 1} (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (coeSubtype.{1} (Prod.{0, 0} Nat Nat) (fun (x_1 : Prod.{0, 0} Nat Nat) => Membership.Mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.hasMem.{0} (Prod.{0, 0} Nat Nat)) x_1 (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))))))) (Sigma.snd.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x)))) (g (Prod.snd.{0, 0} Nat Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (coeBase.{1, 1} (coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))) (Prod.{0, 0} Nat Nat) (coeSubtype.{1} (Prod.{0, 0} Nat Nat) (fun (x_1 : Prod.{0, 0} Nat Nat) => Membership.Mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.hasMem.{0} (Prod.{0, 0} Nat Nat)) x_1 (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))))))) (Sigma.snd.{0, 0} Nat (fun (n : Nat) => coeSort.{1, 2} (Finset.{0} (Prod.{0, 0} Nat Nat)) Type (Finset.hasCoeToSort.{0} (Prod.{0, 0} Nat Nat)) (Finset.Nat.antidiagonal n)) x))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α}, Iff (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) (Summable.{u1, 0} α (Sigma.{0, 0} Nat (fun (n : Nat) => Subtype.{1} (Prod.{0, 0} Nat Nat) (fun (x : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x (Finset.Nat.antidiagonal n)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Sigma.{0, 0} Nat (fun (n : Nat) => Subtype.{1} (Prod.{0, 0} Nat Nat) (fun (x : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x (Finset.Nat.antidiagonal n)))) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat (Subtype.val.{1} (Prod.{0, 0} Nat Nat) (fun (x_1 : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x_1 (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => Subtype.{1} (Prod.{0, 0} Nat Nat) (fun (x : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x (Finset.Nat.antidiagonal n))) x))) (Sigma.snd.{0, 0} Nat (fun (n : Nat) => Subtype.{1} (Prod.{0, 0} Nat Nat) (fun (x : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x (Finset.Nat.antidiagonal n))) x)))) (g (Prod.snd.{0, 0} Nat Nat (Subtype.val.{1} (Prod.{0, 0} Nat Nat) (fun (x_1 : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x_1 (Finset.Nat.antidiagonal (Sigma.fst.{0, 0} Nat (fun (n : Nat) => Subtype.{1} (Prod.{0, 0} Nat Nat) (fun (x : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x (Finset.Nat.antidiagonal n))) x))) (Sigma.snd.{0, 0} Nat (fun (n : Nat) => Subtype.{1} (Prod.{0, 0} Nat Nat) (fun (x : Prod.{0, 0} Nat Nat) => Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.instMembershipFinset.{0} (Prod.{0, 0} Nat Nat)) x (Finset.Nat.antidiagonal n))) x))))))
Case conversion may be inaccurate. Consider using '#align summable_mul_prod_iff_summable_mul_sigma_antidiagonal summable_mul_prod_iff_summable_mul_sigma_antidiagonalₓ'. -/
/- The family `(k, l) : ℕ × ℕ ↦ f k * g l` is summable if and only if the family
`(n, k, l) : Σ (n : ℕ), nat.antidiagonal n ↦ f k * g l` is summable. -/
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal :
    (Summable fun x : ℕ × ℕ => f x.1 * g x.2) ↔
      Summable fun x : Σn : ℕ, Nat.antidiagonal n => f (x.2 : ℕ × ℕ).1 * g (x.2 : ℕ × ℕ).2 :=
  Nat.sigmaAntidiagonalEquivProd.summable_iff.symm
#align summable_mul_prod_iff_summable_mul_sigma_antidiagonal summable_mul_prod_iff_summable_mul_sigma_antidiagonal

variable [T3Space α] [TopologicalSemiring α]

/- warning: summable_sum_mul_antidiagonal_of_summable_mul -> summable_sum_mul_antidiagonal_of_summable_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (n : Nat) => Finset.sum.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.Nat.antidiagonal n) (fun (kl : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat kl)) (g (Prod.snd.{0, 0} Nat Nat kl)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (n : Nat) => Finset.sum.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.Nat.antidiagonal n) (fun (kl : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat kl)) (g (Prod.snd.{0, 0} Nat Nat kl)))))
Case conversion may be inaccurate. Consider using '#align summable_sum_mul_antidiagonal_of_summable_mul summable_sum_mul_antidiagonal_of_summable_mulₓ'. -/
theorem summable_sum_mul_antidiagonal_of_summable_mul
    (h : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    Summable fun n => ∑ kl in Nat.antidiagonal n, f kl.1 * g kl.2 :=
  by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv =>
    congr
    ext
    rw [← Finset.sum_finset_coe, ← tsum_fintype]
  exact h.sigma' fun n => (hasSum_fintype _).Summable
#align summable_sum_mul_antidiagonal_of_summable_mul summable_sum_mul_antidiagonal_of_summable_mul

/- warning: tsum_mul_tsum_eq_tsum_sum_antidiagonal -> tsum_mul_tsum_eq_tsum_sum_antidiagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 f) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 g) -> (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => Finset.sum.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.Nat.antidiagonal n) (fun (kl : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat kl)) (g (Prod.snd.{0, 0} Nat Nat kl))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 f) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 g) -> (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => Finset.sum.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.Nat.antidiagonal n) (fun (kl : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat kl)) (g (Prod.snd.{0, 0} Nat Nat kl))))))
Case conversion may be inaccurate. Consider using '#align tsum_mul_tsum_eq_tsum_sum_antidiagonal tsum_mul_tsum_eq_tsum_sum_antidiagonalₓ'. -/
/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `finset.nat.antidiagonal`.

See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` if `f` and `g` are absolutely
summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in Nat.antidiagonal n, f kl.1 * g kl.2 :=
  by
  conv_rhs =>
    congr
    ext
    rw [← Finset.sum_finset_coe, ← tsum_fintype]
  rw [tsum_mul_tsum hf hg hfg, ← nat.sigma_antidiagonal_equiv_prod.tsum_eq (_ : ℕ × ℕ → α)]
  exact
    tsum_sigma' (fun n => (hasSum_fintype _).Summable)
      (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg)
#align tsum_mul_tsum_eq_tsum_sum_antidiagonal tsum_mul_tsum_eq_tsum_sum_antidiagonal

/- warning: summable_sum_mul_range_of_summable_mul -> summable_sum_mul_range_of_summable_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k)))))
Case conversion may be inaccurate. Consider using '#align summable_sum_mul_range_of_summable_mul summable_sum_mul_range_of_summable_mulₓ'. -/
theorem summable_sum_mul_range_of_summable_mul (h : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    Summable fun n => ∑ k in range (n + 1), f k * g (n - k) :=
  by
  simp_rw [← nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h
#align summable_sum_mul_range_of_summable_mul summable_sum_mul_range_of_summable_mul

/- warning: tsum_mul_tsum_eq_tsum_sum_range -> tsum_mul_tsum_eq_tsum_sum_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 f) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 g) -> (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_2))) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u1} α] {f : Nat -> α} {g : Nat -> α} [_inst_3 : T3Space.{u1} α _inst_1] [_inst_4 : TopologicalSemiring.{u1} α _inst_1 _inst_2], (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 f) -> (Summable.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 g) -> (Summable.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 (fun (x : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f (Prod.fst.{0, 0} Nat Nat x)) (g (Prod.snd.{0, 0} Nat Nat x)))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) _inst_1 Nat (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_2)) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k))))))
Case conversion may be inaccurate. Consider using '#align tsum_mul_tsum_eq_tsum_sum_range tsum_mul_tsum_eq_tsum_sum_rangeₓ'. -/
/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `finset.range`.

See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` if `f` and `g` are absolutely summable.
-/
theorem tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ => f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) :=
  by
  simp_rw [← nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg
#align tsum_mul_tsum_eq_tsum_sum_range tsum_mul_tsum_eq_tsum_sum_range

end CauchyProduct

