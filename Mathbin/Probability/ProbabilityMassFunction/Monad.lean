/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma

! This file was ported from Lean 3 source module probability.probability_mass_function.monad
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.ProbabilityMassFunction.Basic

/-!
# Monad Operations for Probability Mass Functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file constructs two operations on `pmf` that give it a monad structure.
`pure a` is the distribution where a single value `a` has probability `1`.
`bind pa pb : pmf β` is the distribution given by sampling `a : α` from `pa : pmf α`,
and then sampling from `pb a : pmf β` to get a final result `b : β`.

`bind_on_support` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

-/


noncomputable section

variable {α β γ : Type _}

open Classical BigOperators NNReal ENNReal

open MeasureTheory

namespace Pmf

section Pure

#print Pmf.pure /-
/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : Pmf α :=
  ⟨fun a' => if a' = a then 1 else 0, hasSum_ite_eq _ _⟩
#align pmf.pure Pmf.pure
-/

variable (a a' : α)

/- warning: pmf.pure_apply -> Pmf.pure_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (a' : α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.pure.{u1} α a) a') (ite.{1} ENNReal (Eq.{succ u1} α a' a) (Classical.propDecidable (Eq.{succ u1} α a' a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (a' : α), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.pure.{u1} α a) a') (ite.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') (Eq.{succ u1} α a' a) (Classical.propDecidable (Eq.{succ u1} α a' a)) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') (CanonicallyOrderedCommSemiring.toOne.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.pure_apply Pmf.pure_applyₓ'. -/
@[simp]
theorem pure_apply : pure a a' = if a' = a then 1 else 0 :=
  rfl
#align pmf.pure_apply Pmf.pure_apply

#print Pmf.support_pure /-
@[simp]
theorem support_pure : (pure a).support = {a} :=
  Set.ext fun a' => by simp [mem_support_iff]
#align pmf.support_pure Pmf.support_pure
-/

#print Pmf.mem_support_pure_iff /-
theorem mem_support_pure_iff : a' ∈ (pure a).support ↔ a' = a := by simp
#align pmf.mem_support_pure_iff Pmf.mem_support_pure_iff
-/

#print Pmf.pure_apply_self /-
@[simp]
theorem pure_apply_self : pure a a = 1 :=
  if_pos rfl
#align pmf.pure_apply_self Pmf.pure_apply_self
-/

/- warning: pmf.pure_apply_of_ne -> Pmf.pure_apply_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (a' : α), (Ne.{succ u1} α a' a) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.pure.{u1} α a) a') (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (a' : α), (Ne.{succ u1} α a' a) -> (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.pure.{u1} α a) a') (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a') instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.pure_apply_of_ne Pmf.pure_apply_of_neₓ'. -/
theorem pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 :=
  if_neg h
#align pmf.pure_apply_of_ne Pmf.pure_apply_of_ne

instance [Inhabited α] : Inhabited (Pmf α) :=
  ⟨pure default⟩

section Measure

variable (s : Set α)

/- warning: pmf.to_outer_measure_pure_apply -> Pmf.toOuterMeasure_pure_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α (Pmf.pure.{u1} α a)) s) (ite.{1} ENNReal (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Classical.propDecidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α (Pmf.pure.{u1} α a)) s) (ite.{1} ENNReal (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Classical.propDecidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_pure_apply Pmf.toOuterMeasure_pure_applyₓ'. -/
@[simp]
theorem toOuterMeasure_pure_apply : (pure a).toOuterMeasure s = if a ∈ s then 1 else 0 :=
  by
  refine' (to_outer_measure_apply (pure a) s).trans _
  split_ifs with ha ha
  · refine' (tsum_congr fun b => _).trans (tsum_ite_eq a 1)
    exact ite_eq_left_iff.2 fun hb => symm (ite_eq_right_iff.2 fun h => (hb <| h.symm ▸ ha).elim)
  · refine' (tsum_congr fun b => _).trans tsum_zero
    exact ite_eq_right_iff.2 fun hb => ite_eq_right_iff.2 fun h => (ha <| h ▸ hb).elim
#align pmf.to_outer_measure_pure_apply Pmf.toOuterMeasure_pure_apply

variable [MeasurableSpace α]

/- warning: pmf.to_measure_pure_apply -> Pmf.toMeasure_pure_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α) [_inst_1 : MeasurableSpace.{u1} α], (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 (Pmf.pure.{u1} α a)) s) (ite.{1} ENNReal (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Classical.propDecidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α) [_inst_1 : MeasurableSpace.{u1} α], (MeasurableSet.{u1} α _inst_1 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 (Pmf.pure.{u1} α a))) s) (ite.{1} ENNReal (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Classical.propDecidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_pure_apply Pmf.toMeasure_pure_applyₓ'. -/
/-- The measure of a set under `pure a` is `1` for sets containing `a` and `0` otherwise -/
@[simp]
theorem toMeasure_pure_apply (hs : MeasurableSet s) :
    (pure a).toMeasure s = if a ∈ s then 1 else 0 :=
  (toMeasure_apply_eq_toOuterMeasure_apply (pure a) s hs).trans (toOuterMeasure_pure_apply a s)
#align pmf.to_measure_pure_apply Pmf.toMeasure_pure_apply

#print Pmf.toMeasure_pure /-
theorem toMeasure_pure : (pure a).toMeasure = Measure.dirac a :=
  Measure.ext fun s hs => by simpa only [to_measure_pure_apply a s hs, measure.dirac_apply' a hs]
#align pmf.to_measure_pure Pmf.toMeasure_pure
-/

#print Pmf.toPmf_dirac /-
@[simp]
theorem toPmf_dirac [Countable α] [h : MeasurableSingletonClass α] :
    (Measure.dirac a).toPmf = pure a := by rw [to_pmf_eq_iff_to_measure_eq, to_measure_pure]
#align pmf.to_pmf_dirac Pmf.toPmf_dirac
-/

end Measure

end Pure

section Bind

#print Pmf.bind /-
/-- The monadic bind operation for `pmf`. -/
def bind (p : Pmf α) (f : α → Pmf β) : Pmf β :=
  ⟨fun b => ∑' a, p a * f a b,
    ENNReal.summable.hasSum_iff.2
      (ENNReal.tsum_comm.trans <| by simp only [ENNReal.tsum_mul_left, tsum_coe, mul_one])⟩
#align pmf.bind Pmf.bind
-/

variable (p : Pmf α) (f : α → Pmf β) (g : β → Pmf γ)

/- warning: pmf.bind_apply -> Pmf.bind_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (b : β), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (Pmf.bind.{u1, u2} α β p f) b) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (f a) b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (b : β), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (Pmf.bind.{u1, u2} α β p f) b) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (f a) b)))
Case conversion may be inaccurate. Consider using '#align pmf.bind_apply Pmf.bind_applyₓ'. -/
@[simp]
theorem bind_apply (b : β) : p.bind f b = ∑' a, p a * f a b :=
  rfl
#align pmf.bind_apply Pmf.bind_apply

#print Pmf.support_bind /-
@[simp]
theorem support_bind : (p.bind f).support = ⋃ a ∈ p.support, (f a).support :=
  Set.ext fun b => by simp [mem_support_iff, ENNReal.tsum_eq_zero, not_or]
#align pmf.support_bind Pmf.support_bind
-/

/- warning: pmf.mem_support_bind_iff -> Pmf.mem_support_bind_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (b : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (Pmf.bind.{u1, u2} α β p f))) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (f a)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (b : β), Iff (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (Pmf.bind.{u1, u2} α β p f))) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (f a)))))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_bind_iff Pmf.mem_support_bind_iffₓ'. -/
theorem mem_support_bind_iff (b : β) :
    b ∈ (p.bind f).support ↔ ∃ a ∈ p.support, b ∈ (f a).support := by
  simp only [support_bind, Set.mem_unionᵢ, Set.mem_setOf_eq]
#align pmf.mem_support_bind_iff Pmf.mem_support_bind_iff

#print Pmf.pure_bind /-
@[simp]
theorem pure_bind (a : α) (f : α → Pmf β) : (pure a).bind f = f a :=
  by
  have : ∀ b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0 := fun b a' => by
    split_ifs <;> simp <;> subst h <;> simp
  ext b <;> simp [this]
#align pmf.pure_bind Pmf.pure_bind
-/

#print Pmf.bind_pure /-
@[simp]
theorem bind_pure : p.bind pure = p :=
  Pmf.ext fun x =>
    (bind_apply _ _ _).trans
      (trans
          (tsum_eq_single x fun y hy => by
            rw [pure_apply_of_ne _ _ hy.symm, MulZeroClass.mul_zero]) <|
        by rw [pure_apply_self, mul_one])
#align pmf.bind_pure Pmf.bind_pure
-/

/- warning: pmf.bind_const -> Pmf.bind_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (q : Pmf.{u2} β), Eq.{succ u2} (Pmf.{u2} β) (Pmf.bind.{u1, u2} α β p (fun (_x : α) => q)) q
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : Pmf.{u2} α) (q : Pmf.{u1} β), Eq.{succ u1} (Pmf.{u1} β) (Pmf.bind.{u2, u1} α β p (fun (_x : α) => q)) q
Case conversion may be inaccurate. Consider using '#align pmf.bind_const Pmf.bind_constₓ'. -/
@[simp]
theorem bind_const (p : Pmf α) (q : Pmf β) : (p.bind fun _ => q) = q :=
  Pmf.ext fun x => by rw [bind_apply, ENNReal.tsum_mul_right, tsum_coe, one_mul]
#align pmf.bind_const Pmf.bind_const

#print Pmf.bind_bind /-
@[simp]
theorem bind_bind : (p.bind f).bind g = p.bind fun a => (f a).bind g :=
  Pmf.ext fun b => by
    simpa only [ennreal.coe_eq_coe.symm, bind_apply, ennreal.tsum_mul_left.symm,
      ennreal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm
#align pmf.bind_bind Pmf.bind_bind
-/

/- warning: pmf.bind_comm -> Pmf.bind_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (p : Pmf.{u1} α) (q : Pmf.{u2} β) (f : α -> β -> (Pmf.{u3} γ)), Eq.{succ u3} (Pmf.{u3} γ) (Pmf.bind.{u1, u3} α γ p (fun (a : α) => Pmf.bind.{u2, u3} β γ q (f a))) (Pmf.bind.{u2, u3} β γ q (fun (b : β) => Pmf.bind.{u1, u3} α γ p (fun (a : α) => f a b)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (p : Pmf.{u3} α) (q : Pmf.{u2} β) (f : α -> β -> (Pmf.{u1} γ)), Eq.{succ u1} (Pmf.{u1} γ) (Pmf.bind.{u3, u1} α γ p (fun (a : α) => Pmf.bind.{u2, u1} β γ q (f a))) (Pmf.bind.{u2, u1} β γ q (fun (b : β) => Pmf.bind.{u3, u1} α γ p (fun (a : α) => f a b)))
Case conversion may be inaccurate. Consider using '#align pmf.bind_comm Pmf.bind_commₓ'. -/
theorem bind_comm (p : Pmf α) (q : Pmf β) (f : α → β → Pmf γ) :
    (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  Pmf.ext fun b => by
    simpa only [ennreal.coe_eq_coe.symm, bind_apply, ennreal.tsum_mul_left.symm,
      ennreal.tsum_mul_right.symm, mul_assoc, mul_left_comm, mul_comm] using ENNReal.tsum_comm
#align pmf.bind_comm Pmf.bind_comm

section Measure

variable (s : Set β)

/- warning: pmf.to_outer_measure_bind_apply -> Pmf.toOuterMeasure_bind_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (s : Set.{u2} β), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.OuterMeasure.{u2} β) (fun (_x : MeasureTheory.OuterMeasure.{u2} β) => (Set.{u2} β) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u2} β) (Pmf.toOuterMeasure.{u2} β (Pmf.bind.{u1, u2} α β p f)) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (coeFn.{succ u2, succ u2} (MeasureTheory.OuterMeasure.{u2} β) (fun (_x : MeasureTheory.OuterMeasure.{u2} β) => (Set.{u2} β) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u2} β) (Pmf.toOuterMeasure.{u2} β (f a)) s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (s : Set.{u2} β), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} β (Pmf.toOuterMeasure.{u2} β (Pmf.bind.{u1, u2} α β p f)) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (MeasureTheory.OuterMeasure.measureOf.{u2} β (Pmf.toOuterMeasure.{u2} β (f a)) s)))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_bind_apply Pmf.toOuterMeasure_bind_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b a) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
@[simp]
theorem toOuterMeasure_bind_apply :
    (p.bind f).toOuterMeasure s = ∑' a, p a * (f a).toOuterMeasure s :=
  calc
    (p.bind f).toOuterMeasure s = ∑' b, if b ∈ s then ∑' a, p a * f a b else 0 := by
      simp [to_outer_measure_apply, Set.indicator_apply]
    _ = ∑' (b) (a), p a * if b ∈ s then f a b else 0 := (tsum_congr fun b => by split_ifs <;> simp)
    _ = ∑' (a) (b), p a * if b ∈ s then f a b else 0 :=
      (tsum_comm' ENNReal.summable (fun _ => ENNReal.summable) fun _ => ENNReal.summable)
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 := (tsum_congr fun a => ENNReal.tsum_mul_left)
    _ = ∑' a, p a * ∑' b, if b ∈ s then f a b else 0 :=
      (tsum_congr fun a => (congr_arg fun x => p a * x) <| tsum_congr fun b => by split_ifs <;> rfl)
    _ = ∑' a, p a * (f a).toOuterMeasure s :=
      tsum_congr fun a => by simp only [to_outer_measure_apply, Set.indicator_apply]
    
#align pmf.to_outer_measure_bind_apply Pmf.toOuterMeasure_bind_apply

/- warning: pmf.to_measure_bind_apply -> Pmf.toMeasure_bind_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (s : Set.{u2} β) [_inst_1 : MeasurableSpace.{u2} β], (MeasurableSet.{u2} β _inst_1 s) -> (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_1) (fun (_x : MeasureTheory.Measure.{u2} β _inst_1) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_1) (Pmf.toMeasure.{u2} β _inst_1 (Pmf.bind.{u1, u2} α β p f)) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_1) (fun (_x : MeasureTheory.Measure.{u2} β _inst_1) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_1) (Pmf.toMeasure.{u2} β _inst_1 (f a)) s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)) (s : Set.{u2} β) [_inst_1 : MeasurableSpace.{u2} β], (MeasurableSet.{u2} β _inst_1 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} β (MeasureTheory.Measure.toOuterMeasure.{u2} β _inst_1 (Pmf.toMeasure.{u2} β _inst_1 (Pmf.bind.{u1, u2} α β p f))) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (MeasureTheory.OuterMeasure.measureOf.{u2} β (MeasureTheory.Measure.toOuterMeasure.{u2} β _inst_1 (Pmf.toMeasure.{u2} β _inst_1 (f a))) s))))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_bind_apply Pmf.toMeasure_bind_applyₓ'. -/
/-- The measure of a set under `p.bind f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a` -/
@[simp]
theorem toMeasure_bind_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bind f).toMeasure s = ∑' a, p a * (f a).toMeasure s :=
  (toMeasure_apply_eq_toOuterMeasure_apply (p.bind f) s hs).trans
    ((toOuterMeasure_bind_apply p f s).trans
      (tsum_congr fun a =>
        congr_arg (fun x => p a * x) (toMeasure_apply_eq_toOuterMeasure_apply (f a) s hs).symm))
#align pmf.to_measure_bind_apply Pmf.toMeasure_bind_apply

end Measure

end Bind

instance : Monad Pmf where
  pure A a := pure a
  bind A B pa pb := pa.bind pb

section BindOnSupport

#print Pmf.bindOnSupport /-
/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bind_on_support (λ a _, f a)`, see `bind_on_support_eq_bind` -/
def bindOnSupport (p : Pmf α) (f : ∀ a ∈ p.support, Pmf β) : Pmf β :=
  ⟨fun b => ∑' a, p a * if h : p a = 0 then 0 else f a h b,
    ENNReal.summable.hasSum_iff.2
      (by
        refine' ennreal.tsum_comm.trans (trans (tsum_congr fun a => _) p.tsum_coe)
        simp_rw [ENNReal.tsum_mul_left]
        split_ifs with h
        · simp only [h, MulZeroClass.zero_mul]
        · rw [(f a h).tsum_coe, mul_one])⟩
#align pmf.bind_on_support Pmf.bindOnSupport
-/

variable {p : Pmf α} (f : ∀ a ∈ p.support, Pmf β)

/- warning: pmf.bind_on_support_apply -> Pmf.bindOnSupport_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (b : β), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (Pmf.bindOnSupport.{u1, u2} α β p f) b) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (dite.{1} ENNReal (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Option.decidableEq.{0} NNReal (fun (a : NNReal) (b : NNReal) => Subtype.decidableEq.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (a : Real) (b : Real) => Real.decidableEq a b) a b) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (h : Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (fun (h : Not (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) => coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (f a h) b))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (b : β), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (Pmf.bindOnSupport.{u1, u2} α β p f) b) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (dite.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (instDecidableEq.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instLinearOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCompleteLinearOrderENNReal))) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (fun (h : Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) => OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) instENNRealZero)) (fun (h : Not (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)))) => FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (f a h) b))))
Case conversion may be inaccurate. Consider using '#align pmf.bind_on_support_apply Pmf.bindOnSupport_applyₓ'. -/
@[simp]
theorem bindOnSupport_apply (b : β) :
    p.bindOnSupport f b = ∑' a, p a * if h : p a = 0 then 0 else f a h b :=
  rfl
#align pmf.bind_on_support_apply Pmf.bindOnSupport_apply

#print Pmf.support_bindOnSupport /-
@[simp]
theorem support_bindOnSupport :
    (p.bindOnSupport f).support = ⋃ (a : α) (h : a ∈ p.support), (f a h).support :=
  by
  refine' Set.ext fun b => _
  simp only [ENNReal.tsum_eq_zero, not_or, mem_support_iff, bind_on_support_apply, Ne.def,
    not_forall, mul_eq_zero, Set.mem_unionᵢ]
  exact
    ⟨fun hb =>
      let ⟨a, ⟨ha, ha'⟩⟩ := hb
      ⟨a, ha, by simpa [ha] using ha'⟩,
      fun hb =>
      let ⟨a, ha, ha'⟩ := hb
      ⟨a, ⟨ha, by simpa [(mem_support_iff _ a).1 ha] using ha'⟩⟩⟩
#align pmf.support_bind_on_support Pmf.support_bindOnSupport
-/

#print Pmf.mem_support_bindOnSupport_iff /-
theorem mem_support_bindOnSupport_iff (b : β) :
    b ∈ (p.bindOnSupport f).support ↔ ∃ (a : α)(h : a ∈ p.support), b ∈ (f a h).support := by
  simp only [support_bind_on_support, Set.mem_setOf_eq, Set.mem_unionᵢ]
#align pmf.mem_support_bind_on_support_iff Pmf.mem_support_bindOnSupport_iff
-/

/- warning: pmf.bind_on_support_eq_bind -> Pmf.bindOnSupport_eq_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (p : Pmf.{u1} α) (f : α -> (Pmf.{u2} β)), Eq.{succ u2} (Pmf.{u2} β) (Pmf.bindOnSupport.{u1, u2} α β p (fun (a : α) (_x : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => f a)) (Pmf.bind.{u1, u2} α β p f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (p : Pmf.{u2} α) (f : α -> (Pmf.{u1} β)), Eq.{succ u1} (Pmf.{u1} β) (Pmf.bindOnSupport.{u2, u1} α β p (fun (a : α) (_x : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Pmf.support.{u2} α p)) => f a)) (Pmf.bind.{u2, u1} α β p f)
Case conversion may be inaccurate. Consider using '#align pmf.bind_on_support_eq_bind Pmf.bindOnSupport_eq_bindₓ'. -/
/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp]
theorem bindOnSupport_eq_bind (p : Pmf α) (f : α → Pmf β) :
    (p.bindOnSupport fun a _ => f a) = p.bind f :=
  by
  ext (b x)
  have : ∀ a, ite (p a = 0) 0 (p a * f a b) = p a * f a b := fun a =>
    ite_eq_right_iff.2 fun h => h.symm ▸ symm (MulZeroClass.zero_mul <| f a b)
  simp only [bind_on_support_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, mul_ite,
    MulZeroClass.mul_zero, this]
#align pmf.bind_on_support_eq_bind Pmf.bindOnSupport_eq_bind

/- warning: pmf.bind_on_support_eq_zero_iff -> Pmf.bindOnSupport_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (b : β), Iff (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (Pmf.bindOnSupport.{u1, u2} α β p f) b) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (forall (a : α) (ha : Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (f a ha) b) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (b : β), Iff (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (Pmf.bindOnSupport.{u1, u2} α β p f) b) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) instENNRealZero))) (forall (a : α) (ha : Ne.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (f a ha) b) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.bind_on_support_eq_zero_iff Pmf.bindOnSupport_eq_zero_iffₓ'. -/
theorem bindOnSupport_eq_zero_iff (b : β) :
    p.bindOnSupport f b = 0 ↔ ∀ (a) (ha : p a ≠ 0), f a ha b = 0 :=
  by
  simp only [bind_on_support_apply, ENNReal.tsum_eq_zero, mul_eq_zero, or_iff_not_imp_left]
  exact ⟨fun h a ha => trans (dif_neg ha).symm (h a ha), fun h a ha => trans (dif_neg ha) (h a ha)⟩
#align pmf.bind_on_support_eq_zero_iff Pmf.bindOnSupport_eq_zero_iff

/- warning: pmf.pure_bind_on_support -> Pmf.pure_bindOnSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (f : forall (a' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a' (Pmf.support.{u1} α (Pmf.pure.{u1} α a))) -> (Pmf.{u2} β)), Eq.{succ u2} (Pmf.{u2} β) (Pmf.bindOnSupport.{u1, u2} α β (Pmf.pure.{u1} α a) f) (f a (Iff.mpr (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α (Pmf.pure.{u1} α a))) (Eq.{succ u1} α a a) (Pmf.mem_support_pure_iff.{u1} α a a) (rfl.{succ u1} α a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (f : forall (a' : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a' (Pmf.support.{u2} α (Pmf.pure.{u2} α a))) -> (Pmf.{u1} β)), Eq.{succ u1} (Pmf.{u1} β) (Pmf.bindOnSupport.{u2, u1} α β (Pmf.pure.{u2} α a) f) (f a (Iff.mpr (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Pmf.support.{u2} α (Pmf.pure.{u2} α a))) (Eq.{succ u2} α a a) (Pmf.mem_support_pure_iff.{u2} α a a) (rfl.{succ u2} α a)))
Case conversion may be inaccurate. Consider using '#align pmf.pure_bind_on_support Pmf.pure_bindOnSupportₓ'. -/
@[simp]
theorem pure_bindOnSupport (a : α) (f : ∀ (a' : α) (ha : a' ∈ (pure a).support), Pmf β) :
    (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) :=
  by
  refine' Pmf.ext fun b => _
  simp only [bind_on_support_apply, pure_apply]
  refine' trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
  by_cases h : a' = a <;> simp [h]
#align pmf.pure_bind_on_support Pmf.pure_bindOnSupport

#print Pmf.bindOnSupport_pure /-
theorem bindOnSupport_pure (p : Pmf α) : (p.bindOnSupport fun a _ => pure a) = p := by
  simp only [Pmf.bind_pure, Pmf.bindOnSupport_eq_bind]
#align pmf.bind_on_support_pure Pmf.bindOnSupport_pure
-/

/- warning: pmf.bind_on_support_bind_on_support -> Pmf.bindOnSupport_bindOnSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (p : Pmf.{u1} α) (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (g : forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (Pmf.bindOnSupport.{u1, u2} α β p f))) -> (Pmf.{u3} γ)), Eq.{succ u3} (Pmf.{u3} γ) (Pmf.bindOnSupport.{u2, u3} β γ (Pmf.bindOnSupport.{u1, u2} α β p f) g) (Pmf.bindOnSupport.{u1, u3} α γ p (fun (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Pmf.bindOnSupport.{u2, u3} β γ (f a ha) (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (f a ha))) => g b (Iff.mpr (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (Pmf.bindOnSupport.{u1, u2} α β p f))) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (f a h))))) (Pmf.mem_support_bindOnSupport_iff.{u1, u2} α β p f b) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (f a h)))) a (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) (fun (h : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (f a h))) ha hb))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (p : Pmf.{u3} α) (f : forall (a : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) -> (Pmf.{u2} β)) (g : forall (b : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (Pmf.bindOnSupport.{u3, u2} α β p f))) -> (Pmf.{u1} γ)), Eq.{succ u1} (Pmf.{u1} γ) (Pmf.bindOnSupport.{u2, u1} β γ (Pmf.bindOnSupport.{u3, u2} α β p f) g) (Pmf.bindOnSupport.{u3, u1} α γ p (fun (a : α) (ha : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) => Pmf.bindOnSupport.{u2, u1} β γ (f a ha) (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (f a ha))) => g b (Iff.mpr (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (Pmf.bindOnSupport.{u3, u2} α β p f))) (Exists.{succ u3} α (fun (a : α) => Exists.{0} (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) (fun (h : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (f a h))))) (Pmf.mem_support_bindOnSupport_iff.{u3, u2} α β p f b) (Exists.intro.{succ u3} α (fun (a : α) => Exists.{0} (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) (fun (h : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (f a h)))) a (Exists.intro.{0} (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) (fun (h : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (f a h))) ha hb))))))
Case conversion may be inaccurate. Consider using '#align pmf.bind_on_support_bind_on_support Pmf.bindOnSupport_bindOnSupportₓ'. -/
@[simp]
theorem bindOnSupport_bindOnSupport (p : Pmf α) (f : ∀ a ∈ p.support, Pmf β)
    (g : ∀ b ∈ (p.bindOnSupport f).support, Pmf γ) :
    (p.bindOnSupport f).bindOnSupport g =
      p.bindOnSupport fun a ha =>
        (f a ha).bindOnSupport fun b hb =>
          g b ((mem_support_bindOnSupport_iff f b).mpr ⟨a, ha, hb⟩) :=
  by
  refine' Pmf.ext fun a => _
  simp only [ennreal.coe_eq_coe.symm, bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm]
  simp only [ENNReal.tsum_eq_zero, ENNReal.coe_eq_coe, ENNReal.coe_eq_zero, ENNReal.coe_zero,
    dite_eq_left_iff, mul_eq_zero]
  refine' ennreal.tsum_comm.trans (tsum_congr fun a' => tsum_congr fun b => _)
  split_ifs
  any_goals ring1
  · have := h_1 a'
    simp [h] at this
    contradiction
  · simp [h_2]
#align pmf.bind_on_support_bind_on_support Pmf.bindOnSupport_bindOnSupport

/- warning: pmf.bind_on_support_comm -> Pmf.bindOnSupport_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (p : Pmf.{u1} α) (q : Pmf.{u2} β) (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β q)) -> (Pmf.{u3} γ))), Eq.{succ u3} (Pmf.{u3} γ) (Pmf.bindOnSupport.{u1, u3} α γ p (fun (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Pmf.bindOnSupport.{u2, u3} β γ q (f a ha))) (Pmf.bindOnSupport.{u2, u3} β γ q (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β q)) => Pmf.bindOnSupport.{u1, u3} α γ p (fun (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => f a ha b hb)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (p : Pmf.{u3} α) (q : Pmf.{u2} β) (f : forall (a : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) -> (forall (b : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β q)) -> (Pmf.{u1} γ))), Eq.{succ u1} (Pmf.{u1} γ) (Pmf.bindOnSupport.{u3, u1} α γ p (fun (a : α) (ha : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) => Pmf.bindOnSupport.{u2, u1} β γ q (f a ha))) (Pmf.bindOnSupport.{u2, u1} β γ q (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β q)) => Pmf.bindOnSupport.{u3, u1} α γ p (fun (a : α) (ha : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Pmf.support.{u3} α p)) => f a ha b hb)))
Case conversion may be inaccurate. Consider using '#align pmf.bind_on_support_comm Pmf.bindOnSupport_commₓ'. -/
theorem bindOnSupport_comm (p : Pmf α) (q : Pmf β) (f : ∀ a ∈ p.support, ∀ b ∈ q.support, Pmf γ) :
    (p.bindOnSupport fun a ha => q.bindOnSupport (f a ha)) =
      q.bindOnSupport fun b hb => p.bindOnSupport fun a ha => f a ha b hb :=
  by
  apply Pmf.ext; rintro c
  simp only [ennreal.coe_eq_coe.symm, bind_on_support_apply, ← tsum_dite_right,
    ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm]
  refine' trans ENNReal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
  split_ifs with h1 h2 h2 <;> ring
#align pmf.bind_on_support_comm Pmf.bindOnSupport_comm

section Measure

variable (s : Set β)

/- warning: pmf.to_outer_measure_bind_on_support_apply -> Pmf.toOuterMeasure_bindOnSupport_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (s : Set.{u2} β), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.OuterMeasure.{u2} β) (fun (_x : MeasureTheory.OuterMeasure.{u2} β) => (Set.{u2} β) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u2} β) (Pmf.toOuterMeasure.{u2} β (Pmf.bindOnSupport.{u1, u2} α β p f)) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (dite.{1} ENNReal (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Option.decidableEq.{0} NNReal (fun (a : NNReal) (b : NNReal) => Subtype.decidableEq.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (a : Real) (b : Real) => Real.decidableEq a b) a b) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (h : Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (fun (h : Not (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) => coeFn.{succ u2, succ u2} (MeasureTheory.OuterMeasure.{u2} β) (fun (_x : MeasureTheory.OuterMeasure.{u2} β) => (Set.{u2} β) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u2} β) (Pmf.toOuterMeasure.{u2} β (f a h)) s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (s : Set.{u2} β), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} β (Pmf.toOuterMeasure.{u2} β (Pmf.bindOnSupport.{u1, u2} α β p f)) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (dite.{1} ENNReal (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (instDecidableEq.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instLinearOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCompleteLinearOrderENNReal))) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (fun (h : Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) => OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (fun (h : Not (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)))) => MeasureTheory.OuterMeasure.measureOf.{u2} β (Pmf.toOuterMeasure.{u2} β (f a h)) s))))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_bind_on_support_apply Pmf.toOuterMeasure_bindOnSupport_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (b a) -/
@[simp]
theorem toOuterMeasure_bindOnSupport_apply :
    (p.bindOnSupport f).toOuterMeasure s =
      ∑' a, p a * if h : p a = 0 then 0 else (f a h).toOuterMeasure s :=
  by
  simp only [to_outer_measure_apply, Set.indicator_apply, bind_on_support_apply]
  calc
    (∑' b, ite (b ∈ s) (∑' a, p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0) =
        ∑' (b) (a), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      tsum_congr fun b => by split_ifs with hbs <;> simp only [eq_self_iff_true, tsum_zero]
    _ = ∑' (a) (b), ite (b ∈ s) (p a * dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, ite (b ∈ s) (dite (p a = 0) (fun h => 0) fun h => f a h b) 0 :=
      (tsum_congr fun a => by simp only [← ENNReal.tsum_mul_left, mul_ite, MulZeroClass.mul_zero])
    _ = ∑' a, p a * dite (p a = 0) (fun h => 0) fun h => ∑' b, ite (b ∈ s) (f a h b) 0 :=
      tsum_congr fun a => by split_ifs with ha <;> simp only [if_t_t, tsum_zero, eq_self_iff_true]
    
#align pmf.to_outer_measure_bind_on_support_apply Pmf.toOuterMeasure_bindOnSupport_apply

/- warning: pmf.to_measure_bind_on_support_apply -> Pmf.toMeasure_bindOnSupport_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (s : Set.{u2} β) [_inst_1 : MeasurableSpace.{u2} β], (MeasurableSet.{u2} β _inst_1 s) -> (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_1) (fun (_x : MeasureTheory.Measure.{u2} β _inst_1) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_1) (Pmf.toMeasure.{u2} β _inst_1 (Pmf.bindOnSupport.{u1, u2} α β p f)) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (dite.{1} ENNReal (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Option.decidableEq.{0} NNReal (fun (a : NNReal) (b : NNReal) => Subtype.decidableEq.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (a : Real) (b : Real) => Real.decidableEq a b) a b) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (h : Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (fun (h : Not (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) => coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_1) (fun (_x : MeasureTheory.Measure.{u2} β _inst_1) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_1) (Pmf.toMeasure.{u2} β _inst_1 (f a h)) s)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : Pmf.{u1} α} (f : forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) -> (Pmf.{u2} β)) (s : Set.{u2} β) [_inst_1 : MeasurableSpace.{u2} β], (MeasurableSet.{u2} β _inst_1 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} β (MeasureTheory.Measure.toOuterMeasure.{u2} β _inst_1 (Pmf.toMeasure.{u2} β _inst_1 (Pmf.bindOnSupport.{u1, u2} α β p f))) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (dite.{1} ENNReal (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (instDecidableEq.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (instLinearOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ENNReal.instCompleteLinearOrderENNReal))) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (fun (h : Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) => OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (fun (h : Not (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)))) => MeasureTheory.OuterMeasure.measureOf.{u2} β (MeasureTheory.Measure.toOuterMeasure.{u2} β _inst_1 (Pmf.toMeasure.{u2} β _inst_1 (f a h))) s)))))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_bind_on_support_apply Pmf.toMeasure_bindOnSupport_applyₓ'. -/
/-- The measure of a set under `p.bind_on_support f` is the sum over `a : α`
  of the probability of `a` under `p` times the measure of the set under `f a _`.
  The additional if statement is needed since `f` is only a partial function -/
@[simp]
theorem toMeasure_bindOnSupport_apply [MeasurableSpace β] (hs : MeasurableSet s) :
    (p.bindOnSupport f).toMeasure s = ∑' a, p a * if h : p a = 0 then 0 else (f a h).toMeasure s :=
  by
  simp only [to_measure_apply_eq_to_outer_measure_apply _ _ hs,
    to_outer_measure_bind_on_support_apply]
#align pmf.to_measure_bind_on_support_apply Pmf.toMeasure_bindOnSupport_apply

end Measure

end BindOnSupport

end Pmf

