/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris Van Doorn, Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.regular
! leanprover-community/mathlib commit bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Regular measures

A measure is `outer_regular` if the measure of any measurable set `A` is the infimum of `μ U` over
all open sets `U` containing `A`.

A measure is `regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular;
* it is inner regular for open sets with respect to compacts sets: the measure of any open set `U`
  is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `weakly_regular` if it satisfies the following properties:
* it is outer regular;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all closed sets `F` contained in `U`.

In a Hausdorff topological space, regularity implies weak regularity. These three conditions are
registered as typeclasses for a measure `μ`, and this implication is recorded as an instance.

In order to avoid code duplication, we also define a measure `μ` to be `inner_regular` for sets
satisfying a predicate `q` with respect to sets satisfying a predicate `p` if for any set
`U ∈ {U | q U}` and a number `r < μ U` there exists `F ⊆ U` such that `p F` and `r < μ F`.

We prove that inner regularity for open sets with respect to compact sets or closed sets implies
inner regularity for all measurable sets of finite measure (with respect to
compact sets or closed sets respectively), and register some corollaries for (weakly) regular
measures.

Note that a similar statement for measurable sets of infinite mass can fail. For a counterexample,
consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second one the
usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal to
Lebesgue measure on each vertical fiber. The set `ℝ × {0}` has infinite measure (by outer
regularity), but any compact set it contains has zero measure (as it is finite).

Several authors require as a definition of regularity that all measurable sets are inner regular.
We have opted for the slightly weaker definition above as it holds for all Haar measures, it is
enough for essentially all applications, and it is equivalent to the other definition when the
measure is finite.

The interest of the notion of weak regularity is that it is enough for many applications, and it
is automatically satisfied by any finite measure on a metric space.

## Main definitions

* `measure_theory.measure.outer_regular μ`: a typeclass registering that a measure `μ` on a
  topological space is outer regular.
* `measure_theory.measure.regular μ`: a typeclass registering that a measure `μ` on a topological
  space is regular.
* `measure_theory.measure.weakly_regular μ`: a typeclass registering that a measure `μ` on a
  topological space is weakly regular.
* `measure_theory.measure.inner_regular μ p q`: a non-typeclass predicate saying that a measure `μ`
  is inner regular for sets satisfying `q` with respect to sets satisfying `p`.

## Main results

### Outer regular measures

* `set.measure_eq_infi_is_open` asserts that, when `μ` is outer regular, the measure of a
  set is the infimum of the measure of open sets containing it.
* `set.exists_is_open_lt_of_lt` asserts that, when `μ` is outer regular, for every set `s`
  and `r > μ s` there exists an open superset `U ⊇ s` of measure less than `r`.
* push forward of an outer regular measure is outer regular, and scalar multiplication of a regular
  measure by a finite number is outer regular.

### Weakly regular measures

* `is_open.measure_eq_supr_is_closed` asserts that the measure of an open set is the supremum of
  the measure of closed sets it contains.
* `is_open.exists_lt_is_closed`: for an open set `U` and `r < μ U`, there exists a closed `F ⊆ U`
  of measure greater than `r`;
* `measurable_set.measure_eq_supr_is_closed_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of closed sets it contains.
*  `measurable_set.exists_lt_is_closed_of_ne_top` and `measurable_set.exists_is_closed_lt_add`:
  a measurable set of finite measure can be approximated by a closed subset (stated as
  `r < μ F` and `μ s < μ F + ε`, respectively).
* `measure_theory.measure.weakly_regular.of_pseudo_emetric_space_of_is_finite_measure` is an
  instance registering that a finite measure on a metric space is weakly regular (in fact, a pseudo
  emetric space is enough);
* `measure_theory.measure.weakly_regular.of_pseudo_emetric_second_countable_of_locally_finite`
  is an instance registering that a locally finite measure on a second countable metric space (or
  even a pseudo emetric space) is weakly regular.

### Regular measures

* `is_open.measure_eq_supr_is_compact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains.
* `is_open.exists_lt_is_compact`: for an open set `U` and `r < μ U`, there exists a compact `K ⊆ U`
  of measure greater than `r`;
* `measurable_set.measure_eq_supr_is_compact_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains.
*  `measurable_set.exists_lt_is_compact_of_ne_top` and `measurable_set.exists_is_compact_lt_add`:
  a measurable set of finite measure can be approximated by a compact subset (stated as
  `r < μ K` and `μ s < μ K + ε`, respectively).
* `measure_theory.measure.regular.of_sigma_compact_space_of_is_locally_finite_measure` is an
  instance registering that a locally finite measure on a `σ`-compact metric space is regular (in
  fact, an emetric space is enough).

## Implementation notes

The main nontrivial statement is `measure_theory.measure.inner_regular.weakly_regular_of_finite`,
expressing that in a finite measure space, if every open set can be approximated from inside by
closed sets, then the measure is in fact weakly regular. To prove that we show that any measurable
set can be approximated from inside by closed sets and from outside by open sets. This statement is
proved by measurable induction, starting from open sets and checking that it is stable by taking
complements (this is the point of this condition, being symmetrical between inside and outside) and
countable disjoint unions.

Once this statement is proved, one deduces results for `σ`-finite measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular, using
again the same statement).

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]
-/


open Set Filter

open ENNReal Topology NNReal BigOperators

namespace MeasureTheory

namespace Measure

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » U) -/
#print MeasureTheory.Measure.InnerRegular /-
/-- We say that a measure `μ` is *inner regular* with respect to predicates `p q : set α → Prop`,
if for every `U` such that `q U` and `r < μ U`, there exists a subset `K ⊆ U` satisfying `p K`
of measure greater than `r`.

This definition is used to prove some facts about regular and weakly regular measures without
repeating the proofs. -/
def InnerRegular {α} {m : MeasurableSpace α} (μ : Measure α) (p q : Set α → Prop) :=
  ∀ ⦃U⦄, q U → ∀ r < μ U, ∃ (K : _)(_ : K ⊆ U), p K ∧ r < μ K
#align measure_theory.measure.inner_regular MeasureTheory.Measure.InnerRegular
-/

namespace InnerRegular

variable {α : Type _} {m : MeasurableSpace α} {μ : Measure α} {p q : Set α → Prop} {U : Set α}
  {ε : ℝ≥0∞}

/- warning: measure_theory.measure.inner_regular.measure_eq_supr -> MeasureTheory.Measure.InnerRegular.measure_eq_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : (Set.{u1} α) -> Prop} {q : (Set.{u1} α) -> Prop} {U : Set.{u1} α}, (MeasureTheory.Measure.InnerRegular.{u1} α m μ p q) -> (q U) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ U) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (p K) (fun (hK : p K) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ K)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : (Set.{u1} α) -> Prop} {q : (Set.{u1} α) -> Prop} {U : Set.{u1} α}, (MeasureTheory.Measure.InnerRegular.{u1} α m μ p q) -> (q U) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) U) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (p K) (fun (hK : p K) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) K)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.inner_regular.measure_eq_supr MeasureTheory.Measure.InnerRegular.measure_eq_iSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » U) -/
theorem measure_eq_iSup (H : InnerRegular μ p q) (hU : q U) :
    μ U = ⨆ (K) (_ : K ⊆ U) (hK : p K), μ K :=
  by
  refine'
    le_antisymm (le_of_forall_lt fun r hr => _) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr
#align measure_theory.measure.inner_regular.measure_eq_supr MeasureTheory.Measure.InnerRegular.measure_eq_iSup

/- warning: measure_theory.measure.inner_regular.exists_subset_lt_add -> MeasureTheory.Measure.InnerRegular.exists_subset_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : (Set.{u1} α) -> Prop} {q : (Set.{u1} α) -> Prop} {U : Set.{u1} α} {ε : ENNReal}, (MeasureTheory.Measure.InnerRegular.{u1} α m μ p q) -> (p (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (q U) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ U) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) => And (p K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ U) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m) (fun (_x : MeasureTheory.Measure.{u1} α m) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m) μ K) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : (Set.{u1} α) -> Prop} {q : (Set.{u1} α) -> Prop} {U : Set.{u1} α} {ε : ENNReal}, (MeasureTheory.Measure.InnerRegular.{u1} α m μ p q) -> (p (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (q U) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) U) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) (And (p K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) U) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m μ) K) ε)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.inner_regular.exists_subset_lt_add MeasureTheory.Measure.InnerRegular.exists_subset_lt_addₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » U) -/
theorem exists_subset_lt_add (H : InnerRegular μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞)
    (hε : ε ≠ 0) : ∃ (K : _)(_ : K ⊆ U), p K ∧ μ U < μ K + ε :=
  by
  cases' eq_or_ne (μ U) 0 with h₀ h₀
  · refine' ⟨∅, empty_subset _, h0, _⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩
#align measure_theory.measure.inner_regular.exists_subset_lt_add MeasureTheory.Measure.InnerRegular.exists_subset_lt_add

/- warning: measure_theory.measure.inner_regular.map -> MeasureTheory.Measure.InnerRegular.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α _inst_1} {pa : (Set.{u1} α) -> Prop} {qa : (Set.{u1} α) -> Prop}, (MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ pa qa) -> (forall (f : Equiv.{succ u1, succ u2} α β), (AEMeasurable.{u1, u2} α β _inst_2 _inst_1 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f) μ) -> (forall {pb : (Set.{u2} β) -> Prop} {qb : (Set.{u2} β) -> Prop}, (forall (U : Set.{u2} β), (qb U) -> (qa (Set.preimage.{u1, u2} α β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f) U))) -> (forall (K : Set.{u1} α), (pa K) -> (pb (Set.image.{u1, u2} α β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f) K))) -> (forall (K : Set.{u2} β), (pb K) -> (MeasurableSet.{u2} β _inst_2 K)) -> (forall (U : Set.{u2} β), (qb U) -> (MeasurableSet.{u2} β _inst_2 U)) -> (MeasureTheory.Measure.InnerRegular.{u2} β _inst_2 (MeasureTheory.Measure.map.{u1, u2} α β _inst_2 _inst_1 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f) μ) pb qb)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μ : MeasureTheory.Measure.{u2} α _inst_1} {pa : (Set.{u2} α) -> Prop} {qa : (Set.{u2} α) -> Prop}, (MeasureTheory.Measure.InnerRegular.{u2} α _inst_1 μ pa qa) -> (forall (f : Equiv.{succ u2, succ u1} α β), (AEMeasurable.{u2, u1} α β _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f) μ) -> (forall {pb : (Set.{u1} β) -> Prop} {qb : (Set.{u1} β) -> Prop}, (forall (U : Set.{u1} β), (qb U) -> (qa (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f) U))) -> (forall (K : Set.{u2} α), (pa K) -> (pb (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f) K))) -> (forall (K : Set.{u1} β), (pb K) -> (MeasurableSet.{u1} β _inst_2 K)) -> (forall (U : Set.{u1} β), (qb U) -> (MeasurableSet.{u1} β _inst_2 U)) -> (MeasureTheory.Measure.InnerRegular.{u1} β _inst_2 (MeasureTheory.Measure.map.{u2, u1} α β _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f) μ) pb qb)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.inner_regular.map MeasureTheory.Measure.InnerRegular.mapₓ'. -/
theorem map {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α → Prop}
    (H : InnerRegular μ pa qa) (f : α ≃ β) (hf : AEMeasurable f μ) {pb qb : Set β → Prop}
    (hAB : ∀ U, qb U → qa (f ⁻¹' U)) (hAB' : ∀ K, pa K → pb (f '' K))
    (hB₁ : ∀ K, pb K → MeasurableSet K) (hB₂ : ∀ U, qb U → MeasurableSet U) :
    InnerRegular (map f μ) pb qb := by
  intro U hU r hr
  rw [map_apply_of_ae_measurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine' ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, _⟩
  rwa [map_apply_of_ae_measurable hf (hB₁ _ <| hAB' _ hKc), f.preimage_image]
#align measure_theory.measure.inner_regular.map MeasureTheory.Measure.InnerRegular.map

/- warning: measure_theory.measure.inner_regular.smul -> MeasureTheory.Measure.InnerRegular.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : (Set.{u1} α) -> Prop} {q : (Set.{u1} α) -> Prop}, (MeasureTheory.Measure.InnerRegular.{u1} α m μ p q) -> (forall (c : ENNReal), MeasureTheory.Measure.InnerRegular.{u1} α m (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) m) c μ) p q)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {p : (Set.{u1} α) -> Prop} {q : (Set.{u1} α) -> Prop}, (MeasureTheory.Measure.InnerRegular.{u1} α m μ p q) -> (forall (c : ENNReal), MeasureTheory.Measure.InnerRegular.{u1} α m (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.{u1} α m) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) m)) c μ) p q)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.inner_regular.smul MeasureTheory.Measure.InnerRegular.smulₓ'. -/
theorem smul (H : InnerRegular μ p q) (c : ℝ≥0∞) : InnerRegular (c • μ) p q :=
  by
  intro U hU r hr
  rw [smul_apply, H.measure_eq_supr hU, smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using hr
#align measure_theory.measure.inner_regular.smul MeasureTheory.Measure.InnerRegular.smul

#print MeasureTheory.Measure.InnerRegular.trans /-
theorem trans {q' : Set α → Prop} (H : InnerRegular μ p q) (H' : InnerRegular μ q q') :
    InnerRegular μ p q' := by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩
#align measure_theory.measure.inner_regular.trans MeasureTheory.Measure.InnerRegular.trans
-/

end InnerRegular

variable {α β : Type _} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

#print MeasureTheory.Measure.OuterRegular /-
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » A) -/
/-- A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measurable set `A`.

This definition implies the same equality for any (not necessarily measurable) set, see
`set.measure_eq_infi_is_open`. -/
@[protect_proj]
class OuterRegular (μ : Measure α) : Prop where
  OuterRegular :
    ∀ ⦃A : Set α⦄, MeasurableSet A → ∀ r > μ A, ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < r
#align measure_theory.measure.outer_regular MeasureTheory.Measure.OuterRegular
-/

#print MeasureTheory.Measure.Regular /-
/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open. -/
@[protect_proj]
class Regular (μ : Measure α) extends FiniteMeasureOnCompacts μ, OuterRegular μ : Prop where
  InnerRegular : InnerRegular μ IsCompact IsOpen
#align measure_theory.measure.regular MeasureTheory.Measure.Regular
-/

#print MeasureTheory.Measure.WeaklyRegular /-
/-- A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U compact}` for `U` open. -/
@[protect_proj]
class WeaklyRegular (μ : Measure α) extends OuterRegular μ : Prop where
  InnerRegular : InnerRegular μ IsClosed IsOpen
#align measure_theory.measure.weakly_regular MeasureTheory.Measure.WeaklyRegular
-/

#print MeasureTheory.Measure.Regular.weaklyRegular /-
-- see Note [lower instance priority]
/-- A regular measure is weakly regular. -/
instance (priority := 100) Regular.weaklyRegular [T2Space α] [Regular μ] : WeaklyRegular μ
    where InnerRegular U hU r hr :=
    let ⟨K, hKU, hcK, hK⟩ := Regular.innerRegular hU r hr
    ⟨K, hKU, hcK.IsClosed, hK⟩
#align measure_theory.measure.regular.weakly_regular MeasureTheory.Measure.Regular.weaklyRegular
-/

namespace OuterRegular

#print MeasureTheory.Measure.OuterRegular.zero /-
instance zero : OuterRegular (0 : Measure α) :=
  ⟨fun A hA r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩
#align measure_theory.measure.outer_regular.zero MeasureTheory.Measure.OuterRegular.zero
-/

/- warning: set.exists_is_open_lt_of_lt -> Set.exists_isOpen_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] (A : Set.{u1} α) (r : ENNReal), (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) r) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{0} (Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) (fun (H : Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) => And (IsOpen.{u1} α _inst_2 U) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U) r))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] (A : Set.{u1} α) (r : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) r) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (Superset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) U A) (And (IsOpen.{u1} α _inst_2 U) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U) r))))
Case conversion may be inaccurate. Consider using '#align set.exists_is_open_lt_of_lt Set.exists_isOpen_lt_of_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » A) -/
/-- Given `r` larger than the measure of a set `A`, there exists an open superset of `A` with
measure less than `r`. -/
theorem Set.exists_isOpen_lt_of_lt [OuterRegular μ] (A : Set α) (r : ℝ≥0∞) (hr : μ A < r) :
    ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < r :=
  by
  rcases outer_regular.outer_regular (measurable_set_to_measurable μ A) r
      (by rwa [measure_to_measurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_to_measurable _ _).trans hAU, hUo, hU⟩
#align set.exists_is_open_lt_of_lt Set.exists_isOpen_lt_of_lt

/- warning: set.measure_eq_infi_is_open -> Set.measure_eq_iInf_isOpen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (A : Set.{u1} α) (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ], Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (U : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) A U) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) A U) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasInf.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (IsOpen.{u1} α _inst_2 U) (fun (h2 : IsOpen.{u1} α _inst_2 U) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (A : Set.{u1} α) (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (iInf.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (U : Set.{u1} α) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) A U) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) A U) => iInf.{0, 0} ENNReal (ConditionallyCompleteLattice.toInfSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (IsOpen.{u1} α _inst_2 U) (fun (h2 : IsOpen.{u1} α _inst_2 U) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U))))
Case conversion may be inaccurate. Consider using '#align set.measure_eq_infi_is_open Set.measure_eq_iInf_isOpenₓ'. -/
/-- For an outer regular measure, the measure of a set is the infimum of the measures of open sets
containing it. -/
theorem Set.measure_eq_iInf_isOpen (A : Set α) (μ : Measure α) [OuterRegular μ] :
    μ A = ⨅ (U : Set α) (h : A ⊆ U) (h2 : IsOpen U), μ U :=
  by
  refine' le_antisymm (le_iInf₂ fun s hs => le_iInf fun h2s => μ.mono hs) _
  refine' le_of_forall_lt' fun r hr => _
  simpa only [iInf_lt_iff, exists_prop] using A.exists_is_open_lt_of_lt r hr
#align set.measure_eq_infi_is_open Set.measure_eq_iInf_isOpen

/- warning: set.exists_is_open_lt_add -> Set.exists_isOpen_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] (A : Set.{u1} α), (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{0} (Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) (fun (H : Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) => And (IsOpen.{u1} α _inst_2 U) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) ε))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] (A : Set.{u1} α), (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (Superset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) U A) (And (IsOpen.{u1} α _inst_2 U) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) ε))))))
Case conversion may be inaccurate. Consider using '#align set.exists_is_open_lt_add Set.exists_isOpen_lt_addₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » A) -/
theorem Set.exists_isOpen_lt_add [OuterRegular μ] (A : Set α) (hA : μ A ≠ ∞) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < μ A + ε :=
  A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)
#align set.exists_is_open_lt_add Set.exists_isOpen_lt_add

/- warning: set.exists_is_open_le_add -> Set.exists_isOpen_le_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (A : Set.{u1} α) (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{0} (Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) (fun (H : Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) => And (IsOpen.{u1} α _inst_2 U) (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (A : Set.{u1} α) (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (Superset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) U A) (And (IsOpen.{u1} α _inst_2 U) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) ε)))))
Case conversion may be inaccurate. Consider using '#align set.exists_is_open_le_add Set.exists_isOpen_le_addₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » A) -/
theorem Set.exists_isOpen_le_add (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U ≤ μ A + ε :=
  by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_is_open_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩
#align set.exists_is_open_le_add Set.exists_isOpen_le_add

/- warning: measurable_set.exists_is_open_diff_lt -> MeasurableSet.exists_isOpen_diff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] {A : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => Exists.{0} (Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) (fun (H : Superset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) U A) => And (IsOpen.{u1} α _inst_2 U) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) U A)) ε))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] {A : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (U : Set.{u1} α) => And (Superset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) U A) (And (IsOpen.{u1} α _inst_2 U) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) U A)) ε))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_is_open_diff_lt MeasurableSet.exists_isOpen_diff_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » A) -/
theorem MeasurableSet.exists_isOpen_diff_lt [OuterRegular μ] {A : Set α} (hA : MeasurableSet A)
    (hA' : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < ∞ ∧ μ (U \ A) < ε :=
  by
  rcases A.exists_is_open_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_diff_lt_of_lt_add hA hAU hA' hU
#align measurable_set.exists_is_open_diff_lt MeasurableSet.exists_isOpen_diff_lt

/- warning: measure_theory.measure.outer_regular.map -> MeasureTheory.Measure.OuterRegular.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : OpensMeasurableSpace.{u1} α _inst_2 _inst_1] [_inst_4 : MeasurableSpace.{u2} β] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : BorelSpace.{u2} β _inst_5 _inst_4] (f : Homeomorph.{u1, u2} α β _inst_2 _inst_5) (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_7 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ], MeasureTheory.Measure.OuterRegular.{u2} β _inst_4 _inst_5 (MeasureTheory.Measure.map.{u1, u2} α β _inst_4 _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_2 _inst_5) (fun (_x : Homeomorph.{u1, u2} α β _inst_2 _inst_5) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_2 _inst_5) f) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : OpensMeasurableSpace.{u2} α _inst_2 _inst_1] [_inst_4 : MeasurableSpace.{u1} β] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : BorelSpace.{u1} β _inst_5 _inst_4] (f : Homeomorph.{u2, u1} α β _inst_2 _inst_5) (μ : MeasureTheory.Measure.{u2} α _inst_1) [_inst_7 : MeasureTheory.Measure.OuterRegular.{u2} α _inst_1 _inst_2 μ], MeasureTheory.Measure.OuterRegular.{u1} β _inst_4 _inst_5 (MeasureTheory.Measure.map.{u2, u1} α β _inst_4 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_2 _inst_5) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_2 _inst_5) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_2 _inst_5) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_2 _inst_5))) f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.outer_regular.map MeasureTheory.Measure.OuterRegular.mapₓ'. -/
protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) (μ : Measure α) [OuterRegular μ] : (Measure.map f μ).OuterRegular :=
  by
  refine' ⟨fun A hA r hr => _⟩
  rw [map_apply f.measurable hA, ← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine' ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, _⟩
  rwa [map_apply f.measurable this.measurable_set, f.preimage_symm, f.preimage_image]
#align measure_theory.measure.outer_regular.map MeasureTheory.Measure.OuterRegular.map

/- warning: measure_theory.measure.outer_regular.smul -> MeasureTheory.Measure.OuterRegular.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) _inst_1) x μ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ] {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.{u1} α _inst_1) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) _inst_1)) x μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.outer_regular.smul MeasureTheory.Measure.OuterRegular.smulₓ'. -/
protected theorem smul (μ : Measure α) [OuterRegular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) :
    (x • μ).OuterRegular := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact outer_regular.zero
  · refine' ⟨fun A hA r hr => _⟩
    rw [smul_apply, A.measure_eq_infi_is_open, smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using hr
#align measure_theory.measure.outer_regular.smul MeasureTheory.Measure.OuterRegular.smul

end OuterRegular

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » A n) -/
#print MeasureTheory.Measure.FiniteSpanningSetsIn.outerRegular /-
/-- If a measure `μ` admits finite spanning open sets such that the restriction of `μ` to each set
is outer regular, then the original measure is outer regular as well. -/
protected theorem FiniteSpanningSetsIn.outerRegular [OpensMeasurableSpace α] {μ : Measure α}
    (s : μ.FiniteSpanningSetsIn { U | IsOpen U ∧ OuterRegular (μ.restrict U) }) : OuterRegular μ :=
  by
  refine' ⟨fun A hA r hr => _⟩
  have hm : ∀ n, MeasurableSet (s.set n) := fun n => (s.set_mem n).1.MeasurableSet
  haveI : ∀ n, outer_regular (μ.restrict (s.set n)) := fun n => (s.set_mem n).2
  -- Note that `A = ⋃ n, A ∩ disjointed s n`. We replace `A` with this sequence.
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    ∃ A' : ℕ → Set α,
      (∀ n, MeasurableSet (A' n)) ∧
        (∀ n, A' n ⊆ s.set n) ∧ Pairwise (Disjoint on A') ∧ A = ⋃ n, A' n :=
    by
    refine'
      ⟨fun n => A ∩ disjointed s.set n, fun n => hA.inter (MeasurableSet.disjointed hm _), fun n =>
        (inter_subset_right _ _).trans (disjointed_subset _ _),
        (disjoint_disjointed s.set).mono fun k l hkl => hkl.mono inf_le_right inf_le_right, _⟩
    rw [← inter_Union, iUnion_disjointed, s.spanning, inter_univ]
  rcases ENNReal.exists_pos_sum_of_countable' (tsub_pos_iff_lt.2 hr).ne' ℕ with ⟨δ, δ0, hδε⟩
  rw [lt_tsub_iff_right, add_comm] at hδε
  have : ∀ n, ∃ (U : _)(_ : U ⊇ A n), IsOpen U ∧ μ U < μ (A n) + δ n :=
    by
    intro n
    have H₁ : ∀ t, μ.restrict (s.set n) t = μ (t ∩ s.set n) := fun t => restrict_apply' (hm n)
    have Ht : μ.restrict (s.set n) (A n) ≠ ⊤ := by
      rw [H₁]
      exact ((measure_mono <| inter_subset_right _ _).trans_lt (s.finite n)).Ne
    rcases(A n).exists_isOpen_lt_add Ht (δ0 n).ne' with ⟨U, hAU, hUo, hU⟩
    rw [H₁, H₁, inter_eq_self_of_subset_left (hAs _)] at hU
    exact ⟨U ∩ s.set n, subset_inter hAU (hAs _), hUo.inter (s.set_mem n).1, hU⟩
  choose U hAU hUo hU
  refine' ⟨⋃ n, U n, Union_mono hAU, isOpen_iUnion hUo, _⟩
  calc
    μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_Union_le _
    _ ≤ ∑' n, μ (A n) + δ n := (ENNReal.tsum_le_tsum fun n => (hU n).le)
    _ = (∑' n, μ (A n)) + ∑' n, δ n := ENNReal.tsum_add
    _ = μ (⋃ n, A n) + ∑' n, δ n := (congr_arg₂ (· + ·) (measure_Union hAd hAm).symm rfl)
    _ < r := hδε
    
#align measure_theory.measure.finite_spanning_sets_in.outer_regular MeasureTheory.Measure.FiniteSpanningSetsIn.outerRegular
-/

namespace InnerRegular

variable {p q : Set α → Prop} {U s : Set α} {ε r : ℝ≥0∞}

/- warning: measure_theory.measure.inner_regular.measurable_set_of_open -> MeasureTheory.Measure.InnerRegular.measurableSet_of_open is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : (Set.{u1} α) -> Prop} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ], (MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ p (IsOpen.{u1} α _inst_2)) -> (p (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (forall {{s : Set.{u1} α}} {{U : Set.{u1} α}}, (p s) -> (IsOpen.{u1} α _inst_2 U) -> (p (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s U))) -> (MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ p (fun (s : Set.{u1} α) => And (MeasurableSet.{u1} α _inst_1 s) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {p : (Set.{u1} α) -> Prop} [_inst_3 : MeasureTheory.Measure.OuterRegular.{u1} α _inst_1 _inst_2 μ], (MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ p (IsOpen.{u1} α _inst_2)) -> (p (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (forall {{s : Set.{u1} α}} {{U : Set.{u1} α}}, (p s) -> (IsOpen.{u1} α _inst_2 U) -> (p (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s U))) -> (MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ p (fun (s : Set.{u1} α) => And (MeasurableSet.{u1} α _inst_1 s) (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.inner_regular.measurable_set_of_open MeasureTheory.Measure.InnerRegular.measurableSet_of_openₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (ε «expr ≠ » 0) -/
/-- If a measure is inner regular (using closed or compact sets), then every measurable set of
finite measure can by approximated by a (closed or compact) subset. -/
theorem measurableSet_of_open [OuterRegular μ] (H : InnerRegular μ p IsOpen) (h0 : p ∅)
    (hd : ∀ ⦃s U⦄, p s → IsOpen U → p (s \ U)) :
    InnerRegular μ p fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  by
  rintro s ⟨hs, hμs⟩ r hr
  obtain ⟨ε, hε, hεs, rfl⟩ : ∃ (ε : _)(_ : ε ≠ 0), ε + ε ≤ μ s ∧ r = μ s - (ε + ε) :=
    by
    use (μ s - r) / 2
    simp [*, hr.le, ENNReal.add_halves, ENNReal.sub_sub_cancel, le_add_right]
  rcases hs.exists_is_open_diff_lt hμs hε with ⟨U, hsU, hUo, hUt, hμU⟩
  rcases(U \ s).exists_isOpen_lt_of_lt _ hμU with ⟨U', hsU', hU'o, hμU'⟩
  replace hsU' := diff_subset_comm.1 hsU'
  rcases H.exists_subset_lt_add h0 hUo hUt.ne hε with ⟨K, hKU, hKc, hKr⟩
  refine' ⟨K \ U', fun x hx => hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, ENNReal.sub_lt_of_lt_add hεs _⟩
  calc
    μ s ≤ μ U := μ.mono hsU
    _ < μ K + ε := hKr
    _ ≤ μ (K \ U') + μ U' + ε := (add_le_add_right (tsub_le_iff_right.1 le_measure_diff) _)
    _ ≤ μ (K \ U') + ε + ε := by
      mono*
      exacts[hμU'.le, le_rfl]
    _ = μ (K \ U') + (ε + ε) := add_assoc _ _ _
    
#align measure_theory.measure.inner_regular.measurable_set_of_open MeasureTheory.Measure.InnerRegular.measurableSet_of_open

open Finset

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (ε «expr ≠ » 0) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (F «expr ⊆ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » s) -/
#print MeasureTheory.Measure.InnerRegular.weaklyRegular_of_finite /-
/-- In a finite measure space, assume that any open set can be approximated from inside by closed
sets. Then the measure is weakly regular. -/
theorem weaklyRegular_of_finite [BorelSpace α] (μ : Measure α) [FiniteMeasure μ]
    (H : InnerRegular μ IsClosed IsOpen) : WeaklyRegular μ :=
  by
  have hfin : ∀ {s}, μ s ≠ ⊤ := measure_ne_top μ
  suffices
    ∀ s,
      MeasurableSet s →
        ∀ (ε) (_ : ε ≠ 0),
          ∃ (F : _)(_ : F ⊆ s)(U : _)(_ : U ⊇ s),
            IsClosed F ∧ IsOpen U ∧ μ s ≤ μ F + ε ∧ μ U ≤ μ s + ε
    by
    refine'
      { OuterRegular := fun s hs r hr => _
        InnerRegular := H }
    rcases exists_between hr with ⟨r', hsr', hr'r⟩
    rcases this s hs _ (tsub_pos_iff_lt.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩
    refine' ⟨U, hsU, hUo, _⟩
    rw [add_tsub_cancel_of_le hsr'.le] at H
    exact H.trans_lt hr'r
  refine' MeasurableSet.induction_on_open _ _ _
  /- The proof is by measurable induction: we should check that the property is true for the empty
    set, for open sets, and is stable by taking the complement and by taking countable disjoint
    unions. The point of the property we are proving is that it is stable by taking complements
    (exchanging the roles of closed and open sets and thanks to the finiteness of the measure). -/
  -- check for open set
  · intro U hU ε hε
    rcases H.exists_subset_lt_add isClosed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩
    exact ⟨F, hsF, U, subset.rfl, hFc, hU, hF.le, le_self_add⟩
  -- check for complements
  · rintro s hs H ε hε
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩
    refine'
      ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs, hUo.is_closed_compl,
        hFc.is_open_compl, _⟩
    simp only [measure_compl_le_add_iff, *, hUo.measurable_set, hFc.measurable_set, true_and_iff]
  -- check for disjoint unions
  · intro s hsd hsm H ε ε0
    have ε0' : ε / 2 ≠ 0 := (ENNReal.half_pos ε0).ne'
    rcases ENNReal.exists_pos_sum_of_countable' ε0' ℕ with ⟨δ, δ0, hδε⟩
    choose F hFs U hsU hFc hUo hF hU using fun n => H n (δ n) (δ0 n).ne'
    -- the approximating closed set is constructed by considering finitely many sets `s i`, which
    -- cover all the measure up to `ε/2`, approximating each of these by a closed set `F i`, and
    -- taking the union of these (finitely many) `F i`.
    have : tendsto (fun t => (∑ k in t, μ (s k)) + ε / 2) at_top (𝓝 <| μ (⋃ n, s n) + ε / 2) :=
      by
      rw [measure_Union hsd hsm]
      exact tendsto.add ennreal.summable.has_sum tendsto_const_nhds
    rcases(this.eventually <| lt_mem_nhds <| ENNReal.lt_add_right hfin ε0').exists with ⟨t, ht⟩
    -- the approximating open set is constructed by taking for each `s n` an approximating open set
    -- `U n` with measure at most `μ (s n) + δ n` for a summable `δ`, and taking the union of these.
    refine'
      ⟨⋃ k ∈ t, F k, Union_mono fun k => Union_subset fun _ => hFs _, ⋃ n, U n, Union_mono hsU,
        isClosed_biUnion t.finite_to_set fun k _ => hFc k, isOpen_iUnion hUo, ht.le.trans _, _⟩
    · calc
        (∑ k in t, μ (s k)) + ε / 2 ≤ ((∑ k in t, μ (F k)) + ∑ k in t, δ k) + ε / 2 :=
          by
          rw [← sum_add_distrib]
          exact add_le_add_right (sum_le_sum fun k hk => hF k) _
        _ ≤ (∑ k in t, μ (F k)) + ε / 2 + ε / 2 :=
          (add_le_add_right (add_le_add_left ((ENNReal.sum_le_tsum _).trans hδε.le) _) _)
        _ = μ (⋃ k ∈ t, F k) + ε := _
        
      rw [measure_bUnion_finset, add_assoc, ENNReal.add_halves]
      exacts[fun k _ n _ hkn => (hsd hkn).mono (hFs k) (hFs n), fun k hk => (hFc k).MeasurableSet]
    ·
      calc
        μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_Union_le _
        _ ≤ ∑' n, μ (s n) + δ n := (ENNReal.tsum_le_tsum hU)
        _ = μ (⋃ n, s n) + ∑' n, δ n := by rw [measure_Union hsd hsm, ENNReal.tsum_add]
        _ ≤ μ (⋃ n, s n) + ε := add_le_add_left (hδε.le.trans ENNReal.half_le_self) _
        
#align measure_theory.measure.inner_regular.weakly_regular_of_finite MeasureTheory.Measure.InnerRegular.weaklyRegular_of_finite
-/

#print MeasureTheory.Measure.InnerRegular.of_pseudoEMetricSpace /-
/-- In a metric space (or even a pseudo emetric space), an open set can be approximated from inside
by closed sets. -/
theorem of_pseudoEMetricSpace {X : Type _} [PseudoEMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) : InnerRegular μ IsClosed IsOpen :=
  by
  intro U hU r hr
  rcases hU.exists_Union_is_closed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [measure_Union_eq_supr F_mono.directed_le] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_Union _ _, F_closed n, hn⟩
#align measure_theory.measure.inner_regular.of_pseudo_emetric_space MeasureTheory.Measure.InnerRegular.of_pseudoEMetricSpace
-/

#print MeasureTheory.Measure.InnerRegular.isCompact_isClosed /-
/-- In a `σ`-compact space, any closed set can be approximated by a compact subset. -/
theorem isCompact_isClosed {X : Type _} [TopologicalSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegular μ IsCompact IsClosed :=
  by
  intro F hF r hr
  set B : ℕ → Set X := compactCovering X
  have hBc : ∀ n, IsCompact (F ∩ B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : (⋃ n, F ∩ B n) = F := by rw [← inter_Union, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F ∩ B n) :=
    by
    rw [← measure_Union_eq_supr, hBU]
    exact Monotone.directed_le fun m n h => inter_subset_inter_right _ (compactCovering_subset _ h)
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨_, inter_subset_left _ _, hBc n, hn⟩
#align measure_theory.measure.inner_regular.is_compact_is_closed MeasureTheory.Measure.InnerRegular.isCompact_isClosed
-/

end InnerRegular

namespace Regular

#print MeasureTheory.Measure.Regular.zero /-
instance zero : Regular (0 : Measure α) :=
  ⟨fun U hU r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩
#align measure_theory.measure.regular.zero MeasureTheory.Measure.Regular.zero
-/

/- warning: is_open.exists_lt_is_compact -> IsOpen.exists_lt_isCompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U)) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) => And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U)) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) (And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K))))))
Case conversion may be inaccurate. Consider using '#align is_open.exists_lt_is_compact IsOpen.exists_lt_isCompactₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » U) -/
/-- If `μ` is a regular measure, then any open set can be approximated by a compact subset. -/
theorem IsOpen.exists_lt_isCompact [Regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ (K : _)(_ : K ⊆ U), IsCompact K ∧ r < μ K :=
  Regular.innerRegular hU r hr
#align is_open.exists_lt_is_compact IsOpen.exists_lt_isCompact

/- warning: is_open.measure_eq_supr_is_compact -> IsOpen.measure_eq_iSup_isCompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ], Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K U) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (IsCompact.{u1} α _inst_2 K) (fun (h2 : IsCompact.{u1} α _inst_2 K) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) (fun (h : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K U) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (IsCompact.{u1} α _inst_2 K) (fun (h2 : IsCompact.{u1} α _inst_2 K) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K)))))
Case conversion may be inaccurate. Consider using '#align is_open.measure_eq_supr_is_compact IsOpen.measure_eq_iSup_isCompactₓ'. -/
/-- The measure of an open set is the supremum of the measures of compact sets it contains. -/
theorem IsOpen.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α) [Regular μ] :
    μ U = ⨆ (K : Set α) (h : K ⊆ U) (h2 : IsCompact K), μ K :=
  Regular.innerRegular.measure_eq_iSup hU
#align is_open.measure_eq_supr_is_compact IsOpen.measure_eq_iSup_isCompact

/- warning: measure_theory.measure.regular.exists_compact_not_null -> MeasureTheory.Measure.Regular.exists_compact_not_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ], Iff (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (IsCompact.{u1} α _inst_2 K) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))))) (Ne.{succ u1} (MeasureTheory.Measure.{u1} α _inst_1) μ (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α _inst_1) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α _inst_1) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instZero.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ], Iff (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (IsCompact.{u1} α _inst_2 K) (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))))) (Ne.{succ u1} (MeasureTheory.Measure.{u1} α _inst_1) μ (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α _inst_1) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.regular.exists_compact_not_null MeasureTheory.Measure.Regular.exists_compact_not_nullₓ'. -/
theorem exists_compact_not_null [Regular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne.def, ← measure_univ_eq_zero, is_open_univ.measure_eq_supr_is_compact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and_iff]
#align measure_theory.measure.regular.exists_compact_not_null MeasureTheory.Measure.Regular.exists_compact_not_null

/- warning: measure_theory.measure.regular.inner_regular_measurable -> MeasureTheory.Measure.Regular.innerRegular_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ], MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ (IsCompact.{u1} α _inst_2) (fun (s : Set.{u1} α) => And (MeasurableSet.{u1} α _inst_1 s) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ], MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ (IsCompact.{u1} α _inst_2) (fun (s : Set.{u1} α) => And (MeasurableSet.{u1} α _inst_1 s) (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.regular.inner_regular_measurable MeasureTheory.Measure.Regular.innerRegular_measurableₓ'. -/
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_is_compact_lt_add` and
`measurable_set.exists_lt_is_compact_of_ne_top`. -/
theorem innerRegular_measurable [Regular μ] :
    InnerRegular μ IsCompact fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  Regular.innerRegular.measurableSet_of_open isCompact_empty fun _ _ => IsCompact.diff
#align measure_theory.measure.regular.inner_regular_measurable MeasureTheory.Measure.Regular.innerRegular_measurable

/- warning: measurable_set.exists_is_compact_lt_add -> MeasurableSet.exists_isCompact_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) => And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K) ε))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) (And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K) ε))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_is_compact_lt_add MeasurableSet.exists_isCompact_lt_addₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » A) -/
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_lt_is_compact_of_ne_top`. -/
theorem MeasurableSet.exists_isCompact_lt_add [Regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ (K : _)(_ : K ⊆ A), IsCompact K ∧ μ A < μ K + ε :=
  Regular.innerRegular_measurable.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε
#align measurable_set.exists_is_compact_lt_add MeasurableSet.exists_isCompact_lt_add

/- warning: measurable_set.exists_is_compact_diff_lt -> MeasurableSet.exists_isCompact_diff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : OpensMeasurableSpace.{u1} α _inst_2 _inst_1] [_inst_4 : T2Space.{u1} α _inst_2] [_inst_5 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) => And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) A K)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : OpensMeasurableSpace.{u1} α _inst_2 _inst_1] [_inst_4 : T2Space.{u1} α _inst_2] [_inst_5 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) (And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) A K)) ε)))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_is_compact_diff_lt MeasurableSet.exists_isCompact_diff_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » A) -/
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_is_compact_lt_add` and
`measurable_set.exists_lt_is_compact_of_ne_top`. -/
theorem MeasurableSet.exists_isCompact_diff_lt [OpensMeasurableSpace α] [T2Space α] [Regular μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (K : _)(_ : K ⊆ A), IsCompact K ∧ μ (A \ K) < ε :=
  by
  rcases hA.exists_is_compact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact
    ⟨K, hKA, hKc,
      measure_diff_lt_of_lt_add hKc.measurable_set hKA (ne_top_of_le_ne_top h'A <| measure_mono hKA)
        hK⟩
#align measurable_set.exists_is_compact_diff_lt MeasurableSet.exists_isCompact_diff_lt

/- warning: measurable_set.exists_lt_is_compact_of_ne_top -> MeasurableSet.exists_lt_isCompact_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A)) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) => And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A)) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) (And (IsCompact.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_lt_is_compact_of_ne_top MeasurableSet.exists_lt_isCompact_of_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » A) -/
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_is_compact_lt_add`. -/
theorem MeasurableSet.exists_lt_isCompact_of_ne_top [Regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) : ∃ (K : _)(_ : K ⊆ A), IsCompact K ∧ r < μ K :=
  Regular.innerRegular_measurable ⟨hA, h'A⟩ _ hr
#align measurable_set.exists_lt_is_compact_of_ne_top MeasurableSet.exists_lt_isCompact_of_ne_top

/- warning: measurable_set.measure_eq_supr_is_compact_of_ne_top -> MeasurableSet.measure_eq_iSup_isCompact_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (IsCompact.{u1} α _inst_2 K) (fun (h : IsCompact.{u1} α _inst_2 K) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (IsCompact.{u1} α _inst_2 K) (fun (h : IsCompact.{u1} α _inst_2 K) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K)))))
Case conversion may be inaccurate. Consider using '#align measurable_set.measure_eq_supr_is_compact_of_ne_top MeasurableSet.measure_eq_iSup_isCompact_of_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » A) -/
/-- Given a regular measure, any measurable set of finite mass can be approximated from
inside by compact sets. -/
theorem MeasurableSet.measure_eq_iSup_isCompact_of_ne_top [Regular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (h : IsCompact K), μ K :=
  Regular.innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩
#align measurable_set.measure_eq_supr_is_compact_of_ne_top MeasurableSet.measure_eq_iSup_isCompact_of_ne_top

/- warning: measure_theory.measure.regular.map -> MeasureTheory.Measure.Regular.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : OpensMeasurableSpace.{u1} α _inst_2 _inst_1] [_inst_4 : MeasurableSpace.{u2} β] [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : T2Space.{u2} β _inst_5] [_inst_7 : BorelSpace.{u2} β _inst_5 _inst_4] [_inst_8 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] (f : Homeomorph.{u1, u2} α β _inst_2 _inst_5), MeasureTheory.Measure.Regular.{u2} β _inst_4 _inst_5 (MeasureTheory.Measure.map.{u1, u2} α β _inst_4 _inst_1 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_2 _inst_5) (fun (_x : Homeomorph.{u1, u2} α β _inst_2 _inst_5) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_2 _inst_5) f) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : TopologicalSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : OpensMeasurableSpace.{u2} α _inst_2 _inst_1] [_inst_4 : MeasurableSpace.{u1} β] [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : T2Space.{u1} β _inst_5] [_inst_7 : BorelSpace.{u1} β _inst_5 _inst_4] [_inst_8 : MeasureTheory.Measure.Regular.{u2} α _inst_1 _inst_2 μ] (f : Homeomorph.{u2, u1} α β _inst_2 _inst_5), MeasureTheory.Measure.Regular.{u1} β _inst_4 _inst_5 (MeasureTheory.Measure.map.{u2, u1} α β _inst_4 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_2 _inst_5) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_2 _inst_5) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_2 _inst_5) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_2 _inst_5))) f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.regular.map MeasureTheory.Measure.Regular.mapₓ'. -/
protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [T2Space β]
    [BorelSpace β] [Regular μ] (f : α ≃ₜ β) : (Measure.map f μ).regular :=
  by
  haveI := outer_regular.map f μ
  haveI := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨regular.inner_regular.map f.to_equiv f.measurable.ae_measurable
        (fun U hU => hU.Preimage f.continuous) (fun K hK => hK.image f.continuous)
        (fun K hK => hK.MeasurableSet) fun U hU => hU.MeasurableSet⟩
#align measure_theory.measure.regular.map MeasureTheory.Measure.Regular.map

/- warning: measure_theory.measure.regular.smul -> MeasureTheory.Measure.Regular.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 (SMul.smul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (SMulZeroClass.toHasSmul.{0, 0} ENNReal ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (SMulWithZero.toSmulZeroClass.{0, 0} ENNReal ENNReal (MulZeroClass.toHasZero.{0} ENNReal (MulZeroOneClass.toMulZeroClass.{0} ENNReal (MonoidWithZero.toMulZeroOneClass.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (MulActionWithZero.toSMulWithZero.{0, 0} ENNReal ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddCommMonoid.toAddMonoid.{0} ENNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))))) (Module.toMulActionWithZero.{0, 0} ENNReal ENNReal (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))) (Algebra.toModule.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))) _inst_1) x μ))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 μ] {x : ENNReal}, (Ne.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (MeasureTheory.Measure.Regular.{u1} α _inst_1 _inst_2 (HSMul.hSMul.{0, u1, u1} ENNReal (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.{u1} α _inst_1) (instHSMul.{0, u1} ENNReal (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instSMul.{u1, 0} α ENNReal (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (IsScalarTower.right.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (CommSemiring.toSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) _inst_1)) x μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.regular.smul MeasureTheory.Measure.Regular.smulₓ'. -/
protected theorem smul [Regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).regular :=
  by
  haveI := outer_regular.smul μ hx
  haveI := is_finite_measure_on_compacts.smul μ hx
  exact ⟨regular.inner_regular.smul x⟩
#align measure_theory.measure.regular.smul MeasureTheory.Measure.Regular.smul

#print MeasureTheory.Measure.Regular.sigmaFinite /-
-- see Note [lower instance priority]
/-- A regular measure in a σ-compact space is σ-finite. -/
instance (priority := 100) sigmaFinite [SigmaCompactSpace α] [Regular μ] : SigmaFinite μ :=
  ⟨⟨{   Set := compactCovering α
        set_mem := fun n => trivial
        Finite := fun n => (isCompact_compactCovering α n).measure_lt_top
        spanning := iUnion_compactCovering α }⟩⟩
#align measure_theory.measure.regular.sigma_finite MeasureTheory.Measure.Regular.sigmaFinite
-/

end Regular

namespace WeaklyRegular

/- warning: is_open.exists_lt_is_closed -> IsOpen.exists_lt_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U)) -> (Exists.{succ u1} (Set.{u1} α) (fun (F : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) F U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) F U) => And (IsClosed.{u1} α _inst_2 F) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ F))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U)) -> (Exists.{succ u1} (Set.{u1} α) (fun (F : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) F U) (And (IsClosed.{u1} α _inst_2 F) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) F))))))
Case conversion may be inaccurate. Consider using '#align is_open.exists_lt_is_closed IsOpen.exists_lt_isClosedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (F «expr ⊆ » U) -/
/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
theorem IsOpen.exists_lt_isClosed [WeaklyRegular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞}
    (hr : r < μ U) : ∃ (F : _)(_ : F ⊆ U), IsClosed F ∧ r < μ F :=
  WeaklyRegular.innerRegular hU r hr
#align is_open.exists_lt_is_closed IsOpen.exists_lt_isClosed

/- warning: is_open.measure_eq_supr_is_closed -> IsOpen.measure_eq_iSup_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ], Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ U) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (F : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) F U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) F U) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (IsClosed.{u1} α _inst_2 F) (fun (h : IsClosed.{u1} α _inst_2 F) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ F)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {{U : Set.{u1} α}}, (IsOpen.{u1} α _inst_2 U) -> (forall (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ], Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) U) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (F : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) F U) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) F U) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (IsClosed.{u1} α _inst_2 F) (fun (h : IsClosed.{u1} α _inst_2 F) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) F)))))
Case conversion may be inaccurate. Consider using '#align is_open.measure_eq_supr_is_closed IsOpen.measure_eq_iSup_isClosedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (F «expr ⊆ » U) -/
/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
theorem IsOpen.measure_eq_iSup_isClosed ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [WeaklyRegular μ] : μ U = ⨆ (F) (_ : F ⊆ U) (h : IsClosed F), μ F :=
  WeaklyRegular.innerRegular.measure_eq_iSup hU
#align is_open.measure_eq_supr_is_closed IsOpen.measure_eq_iSup_isClosed

/- warning: measure_theory.measure.weakly_regular.inner_regular_measurable -> MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ], MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ (IsClosed.{u1} α _inst_2) (fun (s : Set.{u1} α) => And (MeasurableSet.{u1} α _inst_1 s) (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ], MeasureTheory.Measure.InnerRegular.{u1} α _inst_1 μ (IsClosed.{u1} α _inst_2) (fun (s : Set.{u1} α) => And (MeasurableSet.{u1} α _inst_1 s) (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.weakly_regular.inner_regular_measurable MeasureTheory.Measure.WeaklyRegular.innerRegular_measurableₓ'. -/
theorem innerRegular_measurable [WeaklyRegular μ] :
    InnerRegular μ IsClosed fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  WeaklyRegular.innerRegular.measurableSet_of_open isClosed_empty fun _ _ h₁ h₂ =>
    h₁.inter h₂.isClosed_compl
#align measure_theory.measure.weakly_regular.inner_regular_measurable MeasureTheory.Measure.WeaklyRegular.innerRegular_measurable

/- warning: measurable_set.exists_is_closed_lt_add -> MeasurableSet.exists_isClosed_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K s) => And (IsClosed.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K) ε))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {s : Set.{u1} α}, (MeasurableSet.{u1} α _inst_1 s) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K s) (And (IsClosed.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) s) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K) ε))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_is_closed_lt_add MeasurableSet.exists_isClosed_lt_addₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » s) -/
/-- If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `ε` is a positive
number, then there exist a closed set `K ⊆ s` such that `μ s < μ K + ε`. -/
theorem MeasurableSet.exists_isClosed_lt_add [WeaklyRegular μ] {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ (K : _)(_ : K ⊆ s), IsClosed K ∧ μ s < μ K + ε :=
  innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε
#align measurable_set.exists_is_closed_lt_add MeasurableSet.exists_isClosed_lt_add

/- warning: measurable_set.exists_is_closed_diff_lt -> MeasurableSet.exists_isClosed_diff_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : OpensMeasurableSpace.{u1} α _inst_2 _inst_1] [_inst_4 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (F : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) F A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) F A) => And (IsClosed.{u1} α _inst_2 F) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) A F)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : OpensMeasurableSpace.{u1} α _inst_2 _inst_1] [_inst_4 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {ε : ENNReal}, (Ne.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (F : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) F A) (And (IsClosed.{u1} α _inst_2 F) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) A F)) ε)))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_is_closed_diff_lt MeasurableSet.exists_isClosed_diff_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (F «expr ⊆ » A) -/
theorem MeasurableSet.exists_isClosed_diff_lt [OpensMeasurableSpace α] [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (F : _)(_ : F ⊆ A), IsClosed F ∧ μ (A \ F) < ε :=
  by
  rcases hA.exists_is_closed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact
    ⟨F, hFA, hFc,
      measure_diff_lt_of_lt_add hFc.measurable_set hFA (ne_top_of_le_ne_top h'A <| measure_mono hFA)
        hF⟩
#align measurable_set.exists_is_closed_diff_lt MeasurableSet.exists_isClosed_diff_lt

/- warning: measurable_set.exists_lt_is_closed_of_ne_top -> MeasurableSet.exists_lt_isClosed_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A)) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) => And (IsClosed.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) r (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall {r : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A)) -> (Exists.{succ u1} (Set.{u1} α) (fun (K : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) (And (IsClosed.{u1} α _inst_2 K) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) r (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K))))))
Case conversion may be inaccurate. Consider using '#align measurable_set.exists_lt_is_closed_of_ne_top MeasurableSet.exists_lt_isClosed_of_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » A) -/
/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
theorem MeasurableSet.exists_lt_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) :
    ∃ (K : _)(_ : K ⊆ A), IsClosed K ∧ r < μ K :=
  innerRegular_measurable ⟨hA, h'A⟩ _ hr
#align measurable_set.exists_lt_is_closed_of_ne_top MeasurableSet.exists_lt_isClosed_of_ne_top

/- warning: measurable_set.measure_eq_supr_is_closed_of_ne_top -> MeasurableSet.measure_eq_iSup_isClosed_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) K A) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (IsClosed.{u1} α _inst_2 K) (fun (h : IsClosed.{u1} α _inst_2 K) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ K)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] {{A : Set.{u1} α}}, (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (iSup.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.{u1} α) (fun (K : Set.{u1} α) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K A) => iSup.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (IsClosed.{u1} α _inst_2 K) (fun (h : IsClosed.{u1} α _inst_2 K) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) K)))))
Case conversion may be inaccurate. Consider using '#align measurable_set.measure_eq_supr_is_closed_of_ne_top MeasurableSet.measure_eq_iSup_isClosed_of_ne_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (K «expr ⊆ » A) -/
/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
theorem MeasurableSet.measure_eq_iSup_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (h : IsClosed K), μ K :=
  innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩
#align measurable_set.measure_eq_supr_is_closed_of_ne_top MeasurableSet.measure_eq_iSup_isClosed_of_ne_top

/- warning: measure_theory.measure.weakly_regular.restrict_of_measurable_set -> MeasureTheory.Measure.WeaklyRegular.restrict_of_measurableSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] [_inst_4 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] (A : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) μ A) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 (MeasureTheory.Measure.restrict.{u1} α _inst_1 μ A))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : TopologicalSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] [_inst_4 : MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 μ] (A : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 A) -> (Ne.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_1 μ) A) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (MeasureTheory.Measure.WeaklyRegular.{u1} α _inst_1 _inst_2 (MeasureTheory.Measure.restrict.{u1} α _inst_1 μ A))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.weakly_regular.restrict_of_measurable_set MeasureTheory.Measure.WeaklyRegular.restrict_of_measurableSetₓ'. -/
/-- The restriction of a weakly regular measure to a measurable set of finite measure is
weakly regular. -/
theorem restrict_of_measurableSet [BorelSpace α] [WeaklyRegular μ] (A : Set α)
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) : WeaklyRegular (μ.restrict A) :=
  by
  haveI : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine' inner_regular.weakly_regular_of_finite _ fun V V_open => _
  simp only [restrict_apply' hA]
  intro r hr
  have : μ (V ∩ A) ≠ ∞ := ne_top_of_le_ne_top h'A (measure_mono <| inter_subset_right _ _)
  rcases(V_open.measurable_set.inter hA).exists_lt_isClosed_of_ne_top this hr with
    ⟨F, hFVA, hFc, hF⟩
  refine' ⟨F, hFVA.trans (inter_subset_left _ _), hFc, _⟩
  rwa [inter_eq_self_of_subset_left (hFVA.trans <| inter_subset_right _ _)]
#align measure_theory.measure.weakly_regular.restrict_of_measurable_set MeasureTheory.Measure.WeaklyRegular.restrict_of_measurableSet

#print MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetricSpace_of_finiteMeasure /-
-- see Note [lower instance priority]
/-- Any finite measure on a metric space (or even a pseudo emetric space) is weakly regular. -/
instance (priority := 100) of_pseudoEMetricSpace_of_finiteMeasure {X : Type _}
    [PseudoEMetricSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [FiniteMeasure μ] :
    WeaklyRegular μ :=
  (InnerRegular.of_pseudoEMetricSpace μ).weaklyRegular_of_finite μ
#align measure_theory.measure.weakly_regular.of_pseudo_emetric_space_of_is_finite_measure MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetricSpace_of_finiteMeasure
-/

#print MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetric_secondCountable_of_locallyFinite /-
-- see Note [lower instance priority]
/-- Any locally finite measure on a second countable metric space (or even a pseudo emetric space)
is weakly regular. -/
instance (priority := 100) of_pseudoEMetric_secondCountable_of_locallyFinite {X : Type _}
    [PseudoEMetricSpace X] [TopologicalSpace.SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [LocallyFiniteMeasure μ] : WeaklyRegular μ :=
  haveI : outer_regular μ :=
    by
    refine' (μ.finite_spanning_sets_in_open'.mono' fun U hU => _).OuterRegular
    have : Fact (μ U < ∞) := ⟨hU.2⟩
    exact ⟨hU.1, inferInstance⟩
  ⟨inner_regular.of_pseudo_emetric_space μ⟩
#align measure_theory.measure.weakly_regular.of_pseudo_emetric_second_countable_of_locally_finite MeasureTheory.Measure.WeaklyRegular.of_pseudoEMetric_secondCountable_of_locallyFinite
-/

end WeaklyRegular

attribute [local instance] EMetric.secondCountable_of_sigmaCompact

#print MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_locallyFiniteMeasure /-
-- see Note [lower instance priority]
/-- Any locally finite measure on a `σ`-compact (e)metric space is regular. -/
instance (priority := 100) Regular.of_sigmaCompactSpace_of_locallyFiniteMeasure {X : Type _}
    [EMetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [LocallyFiniteMeasure μ] : Regular μ
    where
  lt_top_of_isCompact K hK := hK.measure_lt_top
  InnerRegular := (InnerRegular.isCompact_isClosed μ).trans (InnerRegular.of_pseudoEMetricSpace μ)
#align measure_theory.measure.regular.of_sigma_compact_space_of_is_locally_finite_measure MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_locallyFiniteMeasure
-/

end Measure

end MeasureTheory

