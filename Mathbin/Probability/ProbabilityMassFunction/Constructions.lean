/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma

! This file was ported from Lean 3 source module probability.probability_mass_function.constructions
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.ProbabilityMassFunction.Monad

/-!
# Specific Constructions of Probability Mass Functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives a number of different `pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `pmf α` along a function `f : α → β` (or distribution of
functions `f : pmf (α → β)`) to get a `pmf β`

`of_finset` and `of_fintype` simplify the construction of a `pmf α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `finset.sum` instead of `tsum`.

`normalize` constructs a `pmf α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `pmf` and re-normalize the new distribution.

`bernoulli` represents the bernoulli distribution on `bool`

-/


namespace Pmf

noncomputable section

variable {α β γ : Type _}

open Classical BigOperators NNReal ENNReal

section Map

#print Pmf.map /-
/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : Pmf α) : Pmf β :=
  bind p (pure ∘ f)
#align pmf.map Pmf.map
-/

variable (f : α → β) (p : Pmf α) (b : β)

/- warning: pmf.monad_map_eq_map -> Pmf.monad_map_eq_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (p : Pmf.{u1} α), Eq.{succ u1} (Pmf.{u1} β) (Functor.map.{u1, u1} (fun {α : Type.{u1}} => Pmf.{u1} α) (Applicative.toFunctor.{u1, u1} (fun {α : Type.{u1}} => Pmf.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => Pmf.{u1} α) Pmf.monad.{u1})) α β f p) (Pmf.map.{u1, u1} α β f p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (p : Pmf.{u1} α), Eq.{succ u1} (Pmf.{u1} β) (Functor.map.{u1, u1} Pmf.{u1} (Applicative.toFunctor.{u1, u1} Pmf.{u1} (Monad.toApplicative.{u1, u1} Pmf.{u1} Pmf.instMonadPmf.{u1})) α β f p) (Pmf.map.{u1, u1} α β f p)
Case conversion may be inaccurate. Consider using '#align pmf.monad_map_eq_map Pmf.monad_map_eq_mapₓ'. -/
theorem monad_map_eq_map {α β : Type _} (f : α → β) (p : Pmf α) : f <$> p = p.map f :=
  rfl
#align pmf.monad_map_eq_map Pmf.monad_map_eq_map

/- warning: pmf.map_apply -> Pmf.map_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : Pmf.{u1} α) (b : β), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (Pmf.map.{u1, u2} α β f p) b) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => ite.{1} ENNReal (Eq.{succ u2} β b (f a)) (Classical.propDecidable (Eq.{succ u2} β b (f a))) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : Pmf.{u1} α) (b : β), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (Pmf.map.{u1, u2} α β f p) b) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => ite.{1} ENNReal (Eq.{succ u2} β b (f a)) (Classical.propDecidable (Eq.{succ u2} β b (f a))) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align pmf.map_apply Pmf.map_applyₓ'. -/
@[simp]
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]
#align pmf.map_apply Pmf.map_apply

#print Pmf.support_map /-
@[simp]
theorem support_map : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]
#align pmf.support_map Pmf.support_map
-/

/- warning: pmf.mem_support_map_iff -> Pmf.mem_support_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : Pmf.{u1} α) (b : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (Pmf.map.{u1, u2} α β f p))) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)) => Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : Pmf.{u1} α) (b : β), Iff (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (Pmf.map.{u1, u2} α β f p))) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)) (Eq.{succ u2} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_map_iff Pmf.mem_support_map_iffₓ'. -/
theorem mem_support_map_iff : b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp
#align pmf.mem_support_map_iff Pmf.mem_support_map_iff

#print Pmf.bind_pure_comp /-
theorem bind_pure_comp : bind p (pure ∘ f) = map f p :=
  rfl
#align pmf.bind_pure_comp Pmf.bind_pure_comp
-/

#print Pmf.map_id /-
theorem map_id : map id p = p :=
  bind_pure _
#align pmf.map_id Pmf.map_id
-/

#print Pmf.map_comp /-
theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map]
#align pmf.map_comp Pmf.map_comp
-/

#print Pmf.pure_map /-
theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _
#align pmf.pure_map Pmf.pure_map
-/

/- warning: pmf.map_bind -> Pmf.map_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (p : Pmf.{u1} α) (q : α -> (Pmf.{u2} β)) (f : β -> γ), Eq.{succ u3} (Pmf.{u3} γ) (Pmf.map.{u2, u3} β γ f (Pmf.bind.{u1, u2} α β p q)) (Pmf.bind.{u1, u3} α γ p (fun (a : α) => Pmf.map.{u2, u3} β γ f (q a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} (p : Pmf.{u1} α) (q : α -> (Pmf.{u3} β)) (f : β -> γ), Eq.{succ u2} (Pmf.{u2} γ) (Pmf.map.{u3, u2} β γ f (Pmf.bind.{u1, u3} α β p q)) (Pmf.bind.{u1, u2} α γ p (fun (a : α) => Pmf.map.{u3, u2} β γ f (q a)))
Case conversion may be inaccurate. Consider using '#align pmf.map_bind Pmf.map_bindₓ'. -/
theorem map_bind (q : α → Pmf β) (f : β → γ) : (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _
#align pmf.map_bind Pmf.map_bind

/- warning: pmf.bind_map -> Pmf.bind_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (p : Pmf.{u1} α) (f : α -> β) (q : β -> (Pmf.{u3} γ)), Eq.{succ u3} (Pmf.{u3} γ) (Pmf.bind.{u2, u3} β γ (Pmf.map.{u1, u2} α β f p) q) (Pmf.bind.{u1, u3} α γ p (Function.comp.{succ u1, succ u2, succ u3} α β (Pmf.{u3} γ) q f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (p : Pmf.{u3} α) (f : α -> β) (q : β -> (Pmf.{u2} γ)), Eq.{succ u2} (Pmf.{u2} γ) (Pmf.bind.{u1, u2} β γ (Pmf.map.{u3, u1} α β f p) q) (Pmf.bind.{u3, u2} α γ p (Function.comp.{succ u3, succ u1, succ u2} α β (Pmf.{u2} γ) q f))
Case conversion may be inaccurate. Consider using '#align pmf.bind_map Pmf.bind_mapₓ'. -/
@[simp]
theorem bind_map (p : Pmf α) (f : α → β) (q : β → Pmf γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun a => pure_bind _ _))
#align pmf.bind_map Pmf.bind_map

#print Pmf.map_const /-
@[simp]
theorem map_const : p.map (Function.const α b) = pure b := by
  simp only [map, bind_const, Function.comp_const]
#align pmf.map_const Pmf.map_const
-/

section Measure

variable (s : Set β)

#print Pmf.toOuterMeasure_map_apply /-
@[simp]
theorem toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, to_outer_measure_apply p (f ⁻¹' s)]
#align pmf.to_outer_measure_map_apply Pmf.toOuterMeasure_map_apply
-/

/- warning: pmf.to_measure_map_apply -> Pmf.toMeasure_map_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (p : Pmf.{u1} α) (s : Set.{u2} β) [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β], (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (MeasurableSet.{u2} β _inst_2 s) -> (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (fun (_x : MeasureTheory.Measure.{u2} β _inst_2) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_2) (Pmf.toMeasure.{u2} β _inst_2 (Pmf.map.{u1, u2} α β f p)) s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 p) (Set.preimage.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) (p : Pmf.{u2} α) (s : Set.{u1} β) [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β], (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (MeasurableSet.{u1} β _inst_2 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} β (MeasureTheory.Measure.toOuterMeasure.{u1} β _inst_2 (Pmf.toMeasure.{u1} β _inst_2 (Pmf.map.{u2, u1} α β f p))) s) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 (Pmf.toMeasure.{u2} α _inst_1 p)) (Set.preimage.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_map_apply Pmf.toMeasure_map_applyₓ'. -/
@[simp]
theorem toMeasure_map_apply [MeasurableSpace α] [MeasurableSpace β] (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) :=
  by
  rw [to_measure_apply_eq_to_outer_measure_apply _ s hs,
    to_measure_apply_eq_to_outer_measure_apply _ (f ⁻¹' s) (measurableSet_preimage hf hs)]
  exact to_outer_measure_map_apply f p s
#align pmf.to_measure_map_apply Pmf.toMeasure_map_apply

end Measure

end Map

section Seq

#print Pmf.seq /-
/-- The monadic sequencing operation for `pmf`. -/
def seq (q : Pmf (α → β)) (p : Pmf α) : Pmf β :=
  q.bind fun m => p.bind fun a => pure (m a)
#align pmf.seq Pmf.seq
-/

variable (q : Pmf (α → β)) (p : Pmf α) (b : β)

/- warning: pmf.monad_seq_eq_seq -> Pmf.monad_seq_eq_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (q : Pmf.{u1} (α -> β)) (p : Pmf.{u1} α), Eq.{succ u1} (Pmf.{u1} β) (Seq.seq.{u1, u1} Pmf.{u1} (Applicative.toHasSeq.{u1, u1} Pmf.{u1} (Monad.toApplicative.{u1, u1} Pmf.{u1} Pmf.monad.{u1})) α β q p) (Pmf.seq.{u1, u1} α β q p)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (q : Pmf.{u1} (α -> β)) (p : Pmf.{u1} α), Eq.{succ u1} (Pmf.{u1} β) (Seq.seq.{u1, u1} Pmf.{u1} (Applicative.toSeq.{u1, u1} Pmf.{u1} (Monad.toApplicative.{u1, u1} Pmf.{u1} Pmf.instMonadPmf.{u1})) α β q (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Constructions._hyg.722 : Unit) => p)) (Pmf.seq.{u1, u1} α β q p)
Case conversion may be inaccurate. Consider using '#align pmf.monad_seq_eq_seq Pmf.monad_seq_eq_seqₓ'. -/
theorem monad_seq_eq_seq {α β : Type _} (q : Pmf (α → β)) (p : Pmf α) : q <*> p = q.seq p :=
  rfl
#align pmf.monad_seq_eq_seq Pmf.monad_seq_eq_seq

/- warning: pmf.seq_apply -> Pmf.seq_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (q : Pmf.{max u1 u2} (α -> β)) (p : Pmf.{u1} α) (b : β), Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (Pmf.{u2} β) (fun (_x : Pmf.{u2} β) => β -> ENNReal) (FunLike.hasCoeToFun.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (p : β) => ENNReal) (Pmf.funLike.{u2} β)) (Pmf.seq.{u1, u2} α β q p) b) (tsum.{0, max u1 u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace (α -> β) (fun (f : α -> β) => tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a : α) => ite.{1} ENNReal (Eq.{succ u2} β b (f a)) (Classical.propDecidable (Eq.{succ u2} β b (f a))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Pmf.{max u1 u2} (α -> β)) (fun (_x : Pmf.{max u1 u2} (α -> β)) => (α -> β) -> ENNReal) (FunLike.hasCoeToFun.{succ (max u1 u2), succ (max u1 u2), 1} (Pmf.{max u1 u2} (α -> β)) (α -> β) (fun (p : α -> β) => ENNReal) (Pmf.funLike.{max u1 u2} (α -> β))) q f) (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p a)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (q : Pmf.{max u1 u2} (α -> β)) (p : Pmf.{u1} α) (b : β), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) b) (FunLike.coe.{succ u2, succ u2, 1} (Pmf.{u2} β) β (fun (_x : β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : β) => ENNReal) _x) (Pmf.funLike.{u2} β) (Pmf.seq.{u1, u2} α β q p) b) (tsum.{0, max u1 u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal (α -> β) (fun (f : α -> β) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a : α) => ite.{1} ENNReal (Eq.{succ u2} β b (f a)) (Classical.propDecidable (Eq.{succ u2} β b (f a))) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α -> β) => ENNReal) f) ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α -> β) => ENNReal) f) (instHMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α -> β) => ENNReal) f) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α -> β) => ENNReal) f) ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), 1} (Pmf.{max u1 u2} (α -> β)) (α -> β) (fun (_x : α -> β) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α -> β) => ENNReal) _x) (Pmf.funLike.{max u1 u2} (α -> β)) q f) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p a)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))
Case conversion may be inaccurate. Consider using '#align pmf.seq_apply Pmf.seq_applyₓ'. -/
@[simp]
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 :=
  by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine' tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => _)
  simpa only [MulZeroClass.mul_zero] using mul_ite (b = f a) (q f) (p a) 0
#align pmf.seq_apply Pmf.seq_apply

#print Pmf.support_seq /-
@[simp]
theorem support_seq : (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]
#align pmf.support_seq Pmf.support_seq
-/

/- warning: pmf.mem_support_seq_iff -> Pmf.mem_support_seq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (q : Pmf.{max u1 u2} (α -> β)) (p : Pmf.{u1} α) (b : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Pmf.support.{u2} β (Pmf.seq.{u1, u2} α β q p))) (Exists.{succ (max u1 u2)} (α -> β) (fun (f : α -> β) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f (Pmf.support.{max u1 u2} (α -> β) q)) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.hasMem.{max u1 u2} (α -> β)) f (Pmf.support.{max u1 u2} (α -> β) q)) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b (Set.image.{u1, u2} α β f (Pmf.support.{u1} α p)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (q : Pmf.{max u1 u2} (α -> β)) (p : Pmf.{u1} α) (b : β), Iff (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Pmf.support.{u2} β (Pmf.seq.{u1, u2} α β q p))) (Exists.{succ (max u1 u2)} (α -> β) (fun (f : α -> β) => And (Membership.mem.{max u1 u2, max u1 u2} (α -> β) (Set.{max u1 u2} (α -> β)) (Set.instMembershipSet.{max u1 u2} (α -> β)) f (Pmf.support.{max u1 u2} (α -> β) q)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Set.image.{u1, u2} α β f (Pmf.support.{u1} α p)))))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_seq_iff Pmf.mem_support_seq_iffₓ'. -/
theorem mem_support_seq_iff : b ∈ (seq q p).support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by simp
#align pmf.mem_support_seq_iff Pmf.mem_support_seq_iff

end Seq

instance : LawfulFunctor Pmf where
  mapConst_eq α β := rfl
  id_map α := bind_pure
  comp_map α β γ g h x := (map_comp _ _ _).symm

instance : LawfulMonad Pmf where
  bind_pure_comp_eq_map α β f x := rfl
  bind_map_eq_seq α β f x := rfl
  pure_bind α β := pure_bind
  bind_assoc α β γ := bind_bind

section OfFinset

/- warning: pmf.of_finset -> Pmf.ofFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> ENNReal) (s : Finset.{u1} α), (Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) -> (Pmf.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (f : α -> ENNReal) (s : Finset.{u1} α), (Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) -> (Pmf.{u1} α)
Case conversion may be inaccurate. Consider using '#align pmf.of_finset Pmf.ofFinsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∉ » s) -/
/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `pmf` -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : (∑ a in s, f a) = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : Pmf α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩
#align pmf.of_finset Pmf.ofFinset

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∉ » s) -/
variable {f : α → ℝ≥0∞} {s : Finset α} (h : (∑ a in s, f a) = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

/- warning: pmf.of_finset_apply -> Pmf.ofFinset_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (h' : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) (a : α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.ofFinset.{u1} α f s h h') a) (f a)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (h' : forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) (a : α), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.ofFinset.{u1} α f s h h') a) (f a)
Case conversion may be inaccurate. Consider using '#align pmf.of_finset_apply Pmf.ofFinset_applyₓ'. -/
@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a :=
  rfl
#align pmf.of_finset_apply Pmf.ofFinset_apply

/- warning: pmf.support_of_finset -> Pmf.support_ofFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (h' : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.ofFinset.{u1} α f s h h')) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Function.support.{u1, 0} α ENNReal ENNReal.hasZero f))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (h' : forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.ofFinset.{u1} α f s h h')) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Finset.toSet.{u1} α s) (Function.support.{u1, 0} α ENNReal instENNRealZero f))
Case conversion may be inaccurate. Consider using '#align pmf.support_of_finset Pmf.support_ofFinsetₓ'. -/
@[simp]
theorem support_ofFinset : (ofFinset f s h h').support = s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)
#align pmf.support_of_finset Pmf.support_ofFinset

/- warning: pmf.mem_support_of_finset_iff -> Pmf.mem_support_ofFinset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (h' : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) (a : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α (Pmf.ofFinset.{u1} α f s h h'))) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Ne.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (h' : forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) (a : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α (Pmf.ofFinset.{u1} α f s h h'))) (And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Ne.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_of_finset_iff Pmf.mem_support_ofFinset_iffₓ'. -/
theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp
#align pmf.mem_support_of_finset_iff Pmf.mem_support_ofFinset_iff

/- warning: pmf.of_finset_apply_of_not_mem -> Pmf.ofFinset_apply_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (h' : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) {a : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.ofFinset.{u1} α f s h h') a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (h' : forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) {a : α}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.ofFinset.{u1} α f s h h') a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.of_finset_apply_of_not_mem Pmf.ofFinset_apply_of_not_memₓ'. -/
theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha
#align pmf.of_finset_apply_of_not_mem Pmf.ofFinset_apply_of_not_mem

section Measure

variable (t : Set α)

/- warning: pmf.to_outer_measure_of_finset_apply -> Pmf.toOuterMeasure_ofFinset_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (h' : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) (t : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α (Pmf.ofFinset.{u1} α f s h h')) t) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero t f x))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (h' : forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) (t : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α (Pmf.ofFinset.{u1} α f s h h')) t) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero t f x))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_of_finset_apply Pmf.toOuterMeasure_ofFinset_applyₓ'. -/
@[simp]
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t
#align pmf.to_outer_measure_of_finset_apply Pmf.toOuterMeasure_ofFinset_apply

/- warning: pmf.to_measure_of_finset_apply -> Pmf.toMeasure_ofFinset_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (h' : forall (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))) (t : Set.{u1} α) [_inst_1 : MeasurableSpace.{u1} α], (MeasurableSet.{u1} α _inst_1 t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (Pmf.toMeasure.{u1} α _inst_1 (Pmf.ofFinset.{u1} α f s h h')) t) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero t f x)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} {s : Finset.{u1} α} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) s (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (h' : forall (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))) (t : Set.{u1} α) [_inst_1 : MeasurableSpace.{u1} α], (MeasurableSet.{u1} α _inst_1 t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 (Pmf.toMeasure.{u1} α _inst_1 (Pmf.ofFinset.{u1} α f s h h'))) t) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero t f x)))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_of_finset_apply Pmf.toMeasure_ofFinset_applyₓ'. -/
@[simp]
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofFinset_apply h h' t)
#align pmf.to_measure_of_finset_apply Pmf.toMeasure_ofFinset_apply

end Measure

end OfFinset

section OfFintype

/- warning: pmf.of_fintype -> Pmf.ofFintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (f : α -> ENNReal), (Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (Pmf.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (f : α -> ENNReal), (Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (Pmf.{u1} α)
Case conversion may be inaccurate. Consider using '#align pmf.of_fintype Pmf.ofFintypeₓ'. -/
/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `pmf`. -/
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : (∑ a, f a) = 1) : Pmf α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha
#align pmf.of_fintype Pmf.ofFintype

variable [Fintype α] {f : α → ℝ≥0∞} (h : (∑ a, f a) = 1)

/- warning: pmf.of_fintype_apply -> Pmf.ofFintype_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (a : α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.ofFintype.{u1} α _inst_1 f h) a) (f a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (a : α), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.ofFintype.{u1} α _inst_1 f h) a) (f a)
Case conversion may be inaccurate. Consider using '#align pmf.of_fintype_apply Pmf.ofFintype_applyₓ'. -/
@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a :=
  rfl
#align pmf.of_fintype_apply Pmf.ofFintype_apply

/- warning: pmf.support_of_fintype -> Pmf.support_ofFintype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.ofFintype.{u1} α _inst_1 f h)) (Function.support.{u1, 0} α ENNReal ENNReal.hasZero f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.ofFintype.{u1} α _inst_1 f h)) (Function.support.{u1, 0} α ENNReal instENNRealZero f)
Case conversion may be inaccurate. Consider using '#align pmf.support_of_fintype Pmf.support_ofFintypeₓ'. -/
@[simp]
theorem support_ofFintype : (ofFintype f h).support = Function.support f :=
  rfl
#align pmf.support_of_fintype Pmf.support_ofFintype

/- warning: pmf.mem_support_of_fintype_iff -> Pmf.mem_support_ofFintype_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (a : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α (Pmf.ofFintype.{u1} α _inst_1 f h))) (Ne.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (a : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α (Pmf.ofFintype.{u1} α _inst_1 f h))) (Ne.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_of_fintype_iff Pmf.mem_support_ofFintype_iffₓ'. -/
theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 :=
  Iff.rfl
#align pmf.mem_support_of_fintype_iff Pmf.mem_support_ofFintype_iff

section Measure

variable (s : Set α)

/- warning: pmf.to_outer_measure_of_fintype_apply -> Pmf.toOuterMeasure_ofFintype_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (s : Set.{u1} α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.OuterMeasure.{u1} α) (fun (_x : MeasureTheory.OuterMeasure.{u1} α) => (Set.{u1} α) -> ENNReal) (MeasureTheory.OuterMeasure.instCoeFun.{u1} α) (Pmf.toOuterMeasure.{u1} α (Pmf.ofFintype.{u1} α _inst_1 f h)) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s f x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (s : Set.{u1} α), Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (Pmf.toOuterMeasure.{u1} α (Pmf.ofFintype.{u1} α _inst_1 f h)) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s f x))
Case conversion may be inaccurate. Consider using '#align pmf.to_outer_measure_of_fintype_apply Pmf.toOuterMeasure_ofFintype_applyₓ'. -/
@[simp]
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s
#align pmf.to_outer_measure_of_fintype_apply Pmf.toOuterMeasure_ofFintype_apply

/- warning: pmf.to_measure_of_fintype_apply -> Pmf.toMeasure_ofFintype_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (s : Set.{u1} α) [_inst_2 : MeasurableSpace.{u1} α], (MeasurableSet.{u1} α _inst_2 s) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) (Pmf.toMeasure.{u1} α _inst_2 (Pmf.ofFintype.{u1} α _inst_1 f h)) s) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s f x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] {f : α -> ENNReal} (h : Eq.{1} ENNReal (Finset.sum.{0, u1} ENNReal α (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (s : Set.{u1} α) [_inst_2 : MeasurableSpace.{u1} α], (MeasurableSet.{u1} α _inst_2 s) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 (Pmf.toMeasure.{u1} α _inst_2 (Pmf.ofFintype.{u1} α _inst_1 f h))) s) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s f x)))
Case conversion may be inaccurate. Consider using '#align pmf.to_measure_of_fintype_apply Pmf.toMeasure_ofFintype_applyₓ'. -/
@[simp]
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ s hs).trans (toOuterMeasure_ofFintype_apply h s)
#align pmf.to_measure_of_fintype_apply Pmf.toMeasure_ofFintype_apply

end Measure

end OfFintype

section normalize

/- warning: pmf.normalize -> Pmf.normalize is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : α -> ENNReal), (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Pmf.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (f : α -> ENNReal), (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Pmf.{u1} α)
Case conversion may be inaccurate. Consider using '#align pmf.normalize Pmf.normalizeₓ'. -/
/-- Given a `f` with non-zero and non-infinite sum, get a `pmf` by normalizing `f` by its `tsum` -/
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : Pmf α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩
#align pmf.normalize Pmf.normalize

variable {f : α → ℝ≥0∞} (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)

/- warning: pmf.normalize_apply -> Pmf.normalize_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} (hf0 : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (hf : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (a : α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.normalize.{u1} α f hf0 hf) a) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (f a) (Inv.inv.{0} ENNReal ENNReal.hasInv (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (x : α) => f x))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} (hf0 : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (hf : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (a : α), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.normalize.{u1} α f hf0 hf) a) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (f a) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align pmf.normalize_apply Pmf.normalize_applyₓ'. -/
@[simp]
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ :=
  rfl
#align pmf.normalize_apply Pmf.normalize_apply

/- warning: pmf.support_normalize -> Pmf.support_normalize is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} (hf0 : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (hf : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.normalize.{u1} α f hf0 hf)) (Function.support.{u1, 0} α ENNReal ENNReal.hasZero f)
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} (hf0 : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (hf : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.normalize.{u1} α f hf0 hf)) (Function.support.{u1, 0} α ENNReal instENNRealZero f)
Case conversion may be inaccurate. Consider using '#align pmf.support_normalize Pmf.support_normalizeₓ'. -/
@[simp]
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff]
#align pmf.support_normalize Pmf.support_normalize

/- warning: pmf.mem_support_normalize_iff -> Pmf.mem_support_normalize_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> ENNReal} (hf0 : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (hf : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α f) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (a : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α (Pmf.normalize.{u1} α f hf0 hf))) (Ne.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> ENNReal} (hf0 : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (hf : Ne.{1} ENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α f) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (a : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α (Pmf.normalize.{u1} α f hf0 hf))) (Ne.{1} ENNReal (f a) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_normalize_iff Pmf.mem_support_normalize_iffₓ'. -/
theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0 hf).support ↔ f a ≠ 0 := by simp
#align pmf.mem_support_normalize_iff Pmf.mem_support_normalize_iff

end normalize

section Filter

/- warning: pmf.filter -> Pmf.filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))) -> (Pmf.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (p : Pmf.{u1} α) (s : Set.{u1} α), (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))) -> (Pmf.{u1} α)
Case conversion may be inaccurate. Consider using '#align pmf.filter Pmf.filterₓ'. -/
/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def filter (p : Pmf α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : Pmf α :=
  Pmf.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)
#align pmf.filter Pmf.filter

variable {p : Pmf α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support)

/- warning: pmf.filter_apply -> Pmf.filter_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))) (a : α), Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.filter.{u1} α p s h) a) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) a) (Inv.inv.{0} ENNReal ENNReal.hasInv (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace α (fun (a' : α) => Set.indicator.{u1, 0} α ENNReal ENNReal.hasZero s (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) p) a'))))
but is expected to have type
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))) (a : α), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.filter.{u1} α p s h) a) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) a) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal α (fun (a' : α) => Set.indicator.{u1, 0} α ENNReal instENNRealZero s (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) p) a'))))
Case conversion may be inaccurate. Consider using '#align pmf.filter_apply Pmf.filter_applyₓ'. -/
@[simp]
theorem filter_apply (a : α) :
    (p.filterₓ s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [Filter, normalize_apply]
#align pmf.filter_apply Pmf.filter_apply

/- warning: pmf.filter_apply_eq_zero_of_not_mem -> Pmf.filter_apply_eq_zero_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))) {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.filter.{u1} α p s h) a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))) {a : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.filter.{u1} α p s h) a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align pmf.filter_apply_eq_zero_of_not_mem Pmf.filter_apply_eq_zero_of_not_memₓ'. -/
theorem filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (p.filterₓ s h) a = 0 := by
  rw [filter_apply, set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, MulZeroClass.zero_mul]
#align pmf.filter_apply_eq_zero_of_not_mem Pmf.filter_apply_eq_zero_of_not_mem

/- warning: pmf.mem_support_filter_iff -> Pmf.mem_support_filter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))) {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α (Pmf.filter.{u1} α p s h))) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))
but is expected to have type
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))) {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α (Pmf.filter.{u1} α p s h))) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_filter_iff Pmf.mem_support_filter_iffₓ'. -/
theorem mem_support_filter_iff {a : α} : a ∈ (p.filterₓ s h).support ↔ a ∈ s ∧ a ∈ p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero
#align pmf.mem_support_filter_iff Pmf.mem_support_filter_iff

/- warning: pmf.support_filter -> Pmf.support_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.filter.{u1} α p s h)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Pmf.support.{u1} α p))
but is expected to have type
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))), Eq.{succ u1} (Set.{u1} α) (Pmf.support.{u1} α (Pmf.filter.{u1} α p s h)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Pmf.support.{u1} α p))
Case conversion may be inaccurate. Consider using '#align pmf.support_filter Pmf.support_filterₓ'. -/
@[simp]
theorem support_filter : (p.filterₓ s h).support = s ∩ p.support :=
  Set.ext fun x => mem_support_filter_iff _
#align pmf.support_filter Pmf.support_filter

/- warning: pmf.filter_apply_eq_zero_iff -> Pmf.filter_apply_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))) (a : α), Iff (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.filter.{u1} α p s h) a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Or (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p))))
but is expected to have type
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))) (a : α), Iff (Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.filter.{u1} α p s h) a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (Or (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p))))
Case conversion may be inaccurate. Consider using '#align pmf.filter_apply_eq_zero_iff Pmf.filter_apply_eq_zero_iffₓ'. -/
theorem filter_apply_eq_zero_iff (a : α) : (p.filterₓ s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  erw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_or]
#align pmf.filter_apply_eq_zero_iff Pmf.filter_apply_eq_zero_iff

/- warning: pmf.filter_apply_ne_zero_iff -> Pmf.filter_apply_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))) (a : α), Iff (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (Pmf.{u1} α) (fun (_x : Pmf.{u1} α) => α -> ENNReal) (FunLike.hasCoeToFun.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (p : α) => ENNReal) (Pmf.funLike.{u1} α)) (Pmf.filter.{u1} α p s h) a) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Pmf.support.{u1} α p)))
but is expected to have type
  forall {α : Type.{u1}} {p : Pmf.{u1} α} {s : Set.{u1} α} (h : Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))) (a : α), Iff (Ne.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) (FunLike.coe.{succ u1, succ u1, 1} (Pmf.{u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) _x) (Pmf.funLike.{u1} α) (Pmf.filter.{u1} α p s h) a) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : α) => ENNReal) a) instENNRealZero))) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Pmf.support.{u1} α p)))
Case conversion may be inaccurate. Consider using '#align pmf.filter_apply_ne_zero_iff Pmf.filter_apply_ne_zero_iffₓ'. -/
theorem filter_apply_ne_zero_iff (a : α) : (p.filterₓ s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne.def, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]
#align pmf.filter_apply_ne_zero_iff Pmf.filter_apply_ne_zero_iff

end Filter

section bernoulli

/- warning: pmf.bernoulli -> Pmf.bernoulli is a dubious translation:
lean 3 declaration is
  forall (p : ENNReal), (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) p (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) -> (Pmf.{0} Bool)
but is expected to have type
  forall (p : ENNReal), (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) p (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) -> (Pmf.{0} Bool)
Case conversion may be inaccurate. Consider using '#align pmf.bernoulli Pmf.bernoulliₓ'. -/
/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : Pmf Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])
#align pmf.bernoulli Pmf.bernoulli

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

/- warning: pmf.bernoulli_apply -> Pmf.bernoulli_apply is a dubious translation:
lean 3 declaration is
  forall {p : ENNReal} (h : LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) p (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (b : Bool), Eq.{1} ENNReal (coeFn.{1, 1} (Pmf.{0} Bool) (fun (_x : Pmf.{0} Bool) => Bool -> ENNReal) (FunLike.hasCoeToFun.{1, 1, 1} (Pmf.{0} Bool) Bool (fun (p : Bool) => ENNReal) (Pmf.funLike.{0} Bool)) (Pmf.bernoulli p h) b) (cond.{0} ENNReal b p (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) p))
but is expected to have type
  forall {p : ENNReal} (h : LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) p (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (b : Bool), Eq.{1} ((fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : Bool) => ENNReal) b) (FunLike.coe.{1, 1, 1} (Pmf.{0} Bool) Bool (fun (_x : Bool) => (fun (x._@.Mathlib.Probability.ProbabilityMassFunction.Basic._hyg.47 : Bool) => ENNReal) _x) (Pmf.funLike.{0} Bool) (Pmf.bernoulli p h) b) (cond.{0} ENNReal b p (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) p))
Case conversion may be inaccurate. Consider using '#align pmf.bernoulli_apply Pmf.bernoulli_applyₓ'. -/
@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) :=
  rfl
#align pmf.bernoulli_apply Pmf.bernoulli_apply

/- warning: pmf.support_bernoulli -> Pmf.support_bernoulli is a dubious translation:
lean 3 declaration is
  forall {p : ENNReal} (h : LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) p (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))), Eq.{1} (Set.{0} Bool) (Pmf.support.{0} Bool (Pmf.bernoulli p h)) (setOf.{0} Bool (fun (b : Bool) => cond.{0} Prop b (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))))
but is expected to have type
  forall {p : ENNReal} (h : LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) p (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))), Eq.{1} (Set.{0} Bool) (Pmf.support.{0} Bool (Pmf.bernoulli p h)) (setOf.{0} Bool (fun (b : Bool) => cond.{0} Prop b (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))
Case conversion may be inaccurate. Consider using '#align pmf.support_bernoulli Pmf.support_bernoulliₓ'. -/
@[simp]
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p ≠ 0) (p ≠ 1) } :=
  by
  refine' Set.ext fun b => _
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne.def, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]
#align pmf.support_bernoulli Pmf.support_bernoulli

/- warning: pmf.mem_support_bernoulli_iff -> Pmf.mem_support_bernoulli_iff is a dubious translation:
lean 3 declaration is
  forall {p : ENNReal} (h : LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) p (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (b : Bool), Iff (Membership.Mem.{0, 0} Bool (Set.{0} Bool) (Set.hasMem.{0} Bool) b (Pmf.support.{0} Bool (Pmf.bernoulli p h))) (cond.{0} Prop b (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))))
but is expected to have type
  forall {p : ENNReal} (h : LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) p (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (b : Bool), Iff (Membership.mem.{0, 0} Bool (Set.{0} Bool) (Set.instMembershipSet.{0} Bool) b (Pmf.support.{0} Bool (Pmf.bernoulli p h))) (cond.{0} Prop b (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Ne.{1} ENNReal p (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))
Case conversion may be inaccurate. Consider using '#align pmf.mem_support_bernoulli_iff Pmf.mem_support_bernoulli_iffₓ'. -/
theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by simp
#align pmf.mem_support_bernoulli_iff Pmf.mem_support_bernoulli_iff

end bernoulli

end Pmf

