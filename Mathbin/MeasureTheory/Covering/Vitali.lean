/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.covering.vitali
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.MeasureTheory.Constructions.BorelSpace.Basic
import Mathbin.MeasureTheory.Covering.VitaliFamily

/-!
# Vitali covering theorems

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological Vitali covering theorem, in its most classical version, states the following.
Consider a family of balls `(B (x_i, r_i))_{i ∈ I}` in a metric space, with uniformly bounded
radii. Then one can extract a disjoint subfamily indexed by `J ⊆ I`, such that any `B (x_i, r_i)`
is included in a ball `B (x_j, 5 r_j)`.

We prove this theorem in `vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball`.
It is deduced from a more general version, called
`vitali.exists_disjoint_subfamily_covering_enlargment`, which applies to any family of sets
together with a size function `δ` (think "radius" or "diameter").

We deduce the measurable Vitali covering theorem. Assume one is given a family `t` of closed sets
with nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a
definite proportion of the ball `B (x, 6 r)` for a given measure `μ` (think of the situation
where `μ` is a doubling measure and `t` is a family of balls). Consider a set `s` at which the
family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`. Then one
can extract from `t` a disjoint subfamily that covers almost all `s`. It is proved in
`vitali.exists_disjoint_covering_ae`.

A way to restate this theorem is to say that the set of closed sets `a` with nonempty interior
covering a fixed proportion `1/C` of the ball `closed_ball x (3 * diam a)` forms a Vitali family.
This version is given in `vitali.vitali_family`.
-/


variable {α ι : Type _}

open Set Metric MeasureTheory TopologicalSpace Filter

open NNReal Classical ENNReal Topology

namespace Vitali

/- warning: vitali.exists_disjoint_subfamily_covering_enlargment -> Vitali.exists_disjoint_subfamily_covering_enlargment is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (B : ι -> (Set.{u1} α)) (t : Set.{u2} ι) (δ : ι -> Real) (τ : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) τ) -> (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (δ a))) -> (forall (R : Real), (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (LE.le.{0} Real Real.hasLe (δ a) R)) -> (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (Set.Nonempty.{u1} α (B a))) -> (Exists.{succ u2} (Set.{u2} ι) (fun (u : Set.{u2} ι) => Exists.{0} (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) u t) (fun (H : HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) u t) => And (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) u B) (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) b u) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) b u) => And (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (B a) (B b))) (LE.le.{0} Real Real.hasLe (δ a) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) τ (δ b)))))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (B : ι -> (Set.{u2} α)) (t : Set.{u1} ι) (δ : ι -> Real) (τ : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) τ) -> (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (δ a))) -> (forall (R : Real), (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (LE.le.{0} Real Real.instLEReal (δ a) R)) -> (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (Set.Nonempty.{u2} α (B a))) -> (Exists.{succ u1} (Set.{u1} ι) (fun (u : Set.{u1} ι) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) u t) (fun (H : HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) u t) => And (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) u B) (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) b u) (And (Set.Nonempty.{u2} α (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (B a) (B b))) (LE.le.{0} Real Real.instLEReal (δ a) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) τ (δ b)))))))))))
Case conversion may be inaccurate. Consider using '#align vitali.exists_disjoint_subfamily_covering_enlargment Vitali.exists_disjoint_subfamily_covering_enlargmentₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊆ » t) -/
/-- Vitali covering theorem: given a set `t` of subsets of a type, one may extract a disjoint
subfamily `u` such that the `τ`-enlargment of this family covers all elements of `t`, where `τ > 1`
is any fixed number.

When `t` is a family of balls, the `τ`-enlargment of `ball x r` is `ball x ((1+2τ) r)`. In general,
it is expressed in terms of a function `δ` (think "radius" or "diameter"), positive and bounded on
all elements of `t`. The condition is that every element `a` of `t` should intersect an
element `b` of `u` of size larger than that of `a` up to `τ`, i.e., `δ b ≥ δ a / τ`.

We state the lemma slightly more generally, with an indexed family of sets `B a` for `a ∈ t`, for
wider applicability.
-/
theorem exists_disjoint_subfamily_covering_enlargment (B : ι → Set α) (t : Set ι) (δ : ι → ℝ)
    (τ : ℝ) (hτ : 1 < τ) (δnonneg : ∀ a ∈ t, 0 ≤ δ a) (R : ℝ) (δle : ∀ a ∈ t, δ a ≤ R)
    (hne : ∀ a ∈ t, (B a).Nonempty) :
    ∃ (u : _)(_ : u ⊆ t),
      u.PairwiseDisjoint B ∧ ∀ a ∈ t, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ δ a ≤ τ * δ b :=
  by
  /- The proof could be formulated as a transfinite induction. First pick an element of `t` with `δ`
    as large as possible (up to a factor of `τ`). Then among the remaining elements not intersecting
    the already chosen one, pick another element with large `δ`. Go on forever (transfinitely) until
    there is nothing left.
  
    Instead, we give a direct Zorn-based argument. Consider a maximal family `u` of disjoint sets
    with the following property: if an element `a` of `t` intersects some element `b` of `u`, then it
    intersects some `b' ∈ u` with `δ b' ≥ δ a / τ`. Such a maximal family exists by Zorn. If this
    family did not intersect some element `a ∈ t`, then take an element `a' ∈ t` which does not
    intersect any element of `u`, with `δ a'` almost as large as possible. One checks easily
    that `u ∪ {a'}` still has this property, contradicting the maximality. Therefore, `u`
    intersects all elements of `t`, and by definition it satisfies all the desired properties.
    -/
  let T : Set (Set ι) :=
    { u |
      u ⊆ t ∧
        u.PairwiseDisjoint B ∧
          ∀ a ∈ t, ∀ b ∈ u, (B a ∩ B b).Nonempty → ∃ c ∈ u, (B a ∩ B c).Nonempty ∧ δ a ≤ τ * δ c }
  -- By Zorn, choose a maximal family in the good set `T` of disjoint families.
  obtain ⟨u, uT, hu⟩ : ∃ u ∈ T, ∀ v ∈ T, u ⊆ v → v = u :=
    by
    refine' zorn_subset _ fun U UT hU => _
    refine' ⟨⋃₀ U, _, fun s hs => subset_sUnion_of_mem hs⟩
    simp only [Set.sUnion_subset_iff, and_imp, exists_prop, forall_exists_index, mem_sUnion,
      Set.mem_setOf_eq]
    refine'
      ⟨fun u hu => (UT hu).1, (pairwise_disjoint_sUnion hU.directed_on).2 fun u hu => (UT hu).2.1,
        fun a hat b u uU hbu hab => _⟩
    obtain ⟨c, cu, ac, hc⟩ : ∃ (c : ι)(H : c ∈ u), (B a ∩ B c).Nonempty ∧ δ a ≤ τ * δ c :=
      (UT uU).2.2 a hat b hbu hab
    exact ⟨c, ⟨u, uU, cu⟩, ac, hc⟩
  -- the only nontrivial bit is to check that every `a ∈ t` intersects an element `b ∈ u` with
  -- comparatively large `δ b`. Assume this is not the case, then we will contradict the maximality.
  refine' ⟨u, uT.1, uT.2.1, fun a hat => _⟩
  contrapose! hu
  have a_disj : ∀ c ∈ u, Disjoint (B a) (B c) :=
    by
    intro c hc
    by_contra
    rw [not_disjoint_iff_nonempty_inter] at h
    obtain ⟨d, du, ad, hd⟩ : ∃ (d : ι)(H : d ∈ u), (B a ∩ B d).Nonempty ∧ δ a ≤ τ * δ d :=
      uT.2.2 a hat c hc h
    exact lt_irrefl _ ((hu d du ad).trans_le hd)
  -- Let `A` be all the elements of `t` which do not intersect the family `u`. It is nonempty as it
  -- contains `a`. We will pick an element `a'` of `A` with `δ a'` almost as large as possible.
  let A := { a' | a' ∈ t ∧ ∀ c ∈ u, Disjoint (B a') (B c) }
  have Anonempty : A.nonempty := ⟨a, hat, a_disj⟩
  let m := Sup (δ '' A)
  have bddA : BddAbove (δ '' A) := by
    refine' ⟨R, fun x xA => _⟩
    rcases(mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩
    exact δle a' ha'.1
  obtain ⟨a', a'A, ha'⟩ : ∃ a' ∈ A, m / τ ≤ δ a' :=
    by
    have : 0 ≤ m := (δnonneg a hat).trans (le_csSup bddA (mem_image_of_mem _ ⟨hat, a_disj⟩))
    rcases eq_or_lt_of_le this with (mzero | mpos)
    · refine' ⟨a, ⟨hat, a_disj⟩, _⟩
      simpa only [← mzero, zero_div] using δnonneg a hat
    · have I : m / τ < m := by
        rw [div_lt_iff (zero_lt_one.trans hτ)]
        conv_lhs => rw [← mul_one m]
        exact (mul_lt_mul_left mpos).2 hτ
      rcases exists_lt_of_lt_csSup (nonempty_image_iff.2 Anonempty) I with ⟨x, xA, hx⟩
      rcases(mem_image _ _ _).1 xA with ⟨a', ha', rfl⟩
      exact ⟨a', ha', hx.le⟩
  clear hat hu a_disj a
  have a'_ne_u : a' ∉ u := fun H => (hne _ a'A.1).ne_empty (disjoint_self.1 (a'A.2 _ H))
  -- we claim that `u ∪ {a'}` still belongs to `T`, contradicting the maximality of `u`.
  refine' ⟨insert a' u, ⟨_, _, _⟩, subset_insert _ _, (ne_insert_of_not_mem _ a'_ne_u).symm⟩
  -- check that `u ∪ {a'}` is made of elements of `t`.
  · rw [insert_subset]
    exact ⟨a'A.1, uT.1⟩
  -- check that `u ∪ {a'}` is a disjoint family. This follows from the fact that `a'` does not
  -- intersect `u`.
  · exact uT.2.1.insert fun b bu ba' => a'A.2 b bu
  -- check that every element `c` of `t` intersecting `u ∪ {a'}` intersects an element of this
  -- family with large `δ`.
  · intro c ct b ba'u hcb
    -- if `c` already intersects an element of `u`, then it intersects an element of `u` with
    -- large `δ` by the assumption on `u`, and there is nothing left to do.
    by_cases H : ∃ d ∈ u, (B c ∩ B d).Nonempty
    · rcases H with ⟨d, du, hd⟩
      rcases uT.2.2 c ct d du hd with ⟨d', d'u, hd'⟩
      exact ⟨d', mem_insert_of_mem _ d'u, hd'⟩
    -- otherwise, `c` belongs to `A`. The element of `u ∪ {a'}` that it intersects has to be `a'`.
    -- moreover, `δ c` is smaller than the maximum `m` of `δ` over `A`, which is `≤ δ a' / τ`
    -- thanks to the good choice of `a'`. This is the desired inequality.
    · push_neg  at H
      simp only [← not_disjoint_iff_nonempty_inter, Classical.not_not] at H
      rcases mem_insert_iff.1 ba'u with (rfl | H')
      · refine' ⟨b, mem_insert _ _, hcb, _⟩
        calc
          δ c ≤ m := le_csSup bddA (mem_image_of_mem _ ⟨ct, H⟩)
          _ = τ * (m / τ) := by
            field_simp [(zero_lt_one.trans hτ).ne']
            ring
          _ ≤ τ * δ b := mul_le_mul_of_nonneg_left ha' (zero_le_one.trans hτ.le)
          
      · rw [← not_disjoint_iff_nonempty_inter] at hcb
        exact (hcb (H _ H')).elim
#align vitali.exists_disjoint_subfamily_covering_enlargment Vitali.exists_disjoint_subfamily_covering_enlargment

/- warning: vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball -> Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : MetricSpace.{u1} α] (t : Set.{u2} ι) (x : ι -> α) (r : ι -> Real) (R : Real), (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (LE.le.{0} Real Real.hasLe (r a) R)) -> (Exists.{succ u2} (Set.{u2} ι) (fun (u : Set.{u2} ι) => Exists.{0} (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) u t) (fun (H : HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) u t) => And (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) u (fun (a : ι) => Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) (x a) (r a))) (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (Exists.{succ u2} ι (fun (b : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) b u) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) b u) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) (x a) (r a)) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) (x b) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 5 (OfNat.mk.{0} Real 5 (bit1.{0} Real Real.hasOne Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (r b))))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : MetricSpace.{u2} α] (t : Set.{u1} ι) (x : ι -> α) (r : ι -> Real) (R : Real), (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (LE.le.{0} Real Real.instLEReal (r a) R)) -> (Exists.{succ u1} (Set.{u1} ι) (fun (u : Set.{u1} ι) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) u t) (fun (H : HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) u t) => And (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) u (fun (a : ι) => Metric.closedBall.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1) (x a) (r a))) (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (Exists.{succ u1} ι (fun (b : ι) => And (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) b u) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Metric.closedBall.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1) (x a) (r a)) (Metric.closedBall.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1) (x b) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 5 (instOfNat.{0} Real 5 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))) (r b))))))))))
Case conversion may be inaccurate. Consider using '#align vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball Vitali.exists_disjoint_subfamily_covering_enlargment_closedBallₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊆ » t) -/
/-- Vitali covering theorem, closed balls version: given a family `t` of closed balls, one can
extract a disjoint subfamily `u ⊆ t` so that all balls in `t` are covered by the 5-times
dilations of balls in `u`. -/
theorem exists_disjoint_subfamily_covering_enlargment_closedBall [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) :
    ∃ (u : _)(_ : u ⊆ t),
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (5 * r b) :=
  by
  rcases eq_empty_or_nonempty t with (rfl | tnonempty)
  · exact ⟨∅, subset.refl _, pairwise_disjoint_empty, by simp⟩
  by_cases ht : ∀ a ∈ t, r a < 0
  ·
    exact
      ⟨t, subset.rfl, fun a ha b hb hab => by
        simp only [Function.onFun, closed_ball_eq_empty.2 (ht a ha), empty_disjoint], fun a ha =>
        ⟨a, ha, by simp only [closed_ball_eq_empty.2 (ht a ha), empty_subset]⟩⟩
  push_neg  at ht
  let t' := { a ∈ t | 0 ≤ r a }
  rcases exists_disjoint_subfamily_covering_enlargment (fun a => closed_ball (x a) (r a)) t' r 2
      one_lt_two (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closed_ball_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, closed_ball (x a) (r a) ⊆ closed_ball (x b) (5 * r b) :=
    by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine' ⟨b, bu, _⟩
    have : dist (x a) (x b) ≤ r a + r b := dist_le_add_of_nonempty_closed_ball_inter_closed_ball hb
    apply closed_ball_subset_closed_ball'
    linarith
  refine' ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => _⟩
  rcases le_or_lt 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, hc⟩
    refine' ⟨c, cu, by simp only [closed_ball_eq_empty.2 h'a, empty_subset]⟩
#align vitali.exists_disjoint_subfamily_covering_enlargment_closed_ball Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall

/- warning: vitali.exists_disjoint_covering_ae -> Vitali.exists_disjoint_covering_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : OpensMeasurableSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) _inst_2] [_inst_4 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_5 : MeasureTheory.LocallyFiniteMeasure.{u1} α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) μ] (s : Set.{u1} α) (t : Set.{u2} ι) (C : NNReal) (r : ι -> Real) (c : ι -> α) (B : ι -> (Set.{u1} α)), (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (B a) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) (c a) (r a)))) -> (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) (c a) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 3 (OfNat.mk.{0} Real 3 (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne)))) (r a)))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (B a))))) -> (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (Set.Nonempty.{u1} α (interior.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) (B a)))) -> (forall (a : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) (B a))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} ι (fun (a : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a t) => And (LE.le.{0} Real Real.hasLe (r a) ε) (Eq.{succ u1} α (c a) x)))))) -> (Exists.{succ u2} (Set.{u2} ι) (fun (u : Set.{u2} ι) => Exists.{0} (HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) u t) (fun (H : HasSubset.Subset.{u2} (Set.{u2} ι) (Set.hasSubset.{u2} ι) u t) => And (Set.Countable.{u2} ι u) (And (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) u B) (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.iUnion.{u1, succ u2} α ι (fun (a : ι) => Set.iUnion.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a u) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) a u) => B a))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : MetricSpace.{u2} α] [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : OpensMeasurableSpace.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1))) _inst_2] [_inst_4 : TopologicalSpace.SecondCountableTopology.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1)))] (μ : MeasureTheory.Measure.{u2} α _inst_2) [_inst_5 : MeasureTheory.LocallyFiniteMeasure.{u2} α _inst_2 (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1))) μ] (s : Set.{u2} α) (t : Set.{u1} ι) (C : NNReal) (r : ι -> Real) (c : ι -> α) (B : ι -> (Set.{u2} α)), (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (B a) (Metric.closedBall.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1) (c a) (r a)))) -> (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_2 μ) (Metric.closedBall.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1) (c a) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 3 (instOfNat.{0} Real 3 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (r a)))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_2 μ) (B a))))) -> (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (Set.Nonempty.{u2} α (interior.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1))) (B a)))) -> (forall (a : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) -> (IsClosed.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_1))) (B a))) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} ι (fun (a : ι) => And (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a t) (And (LE.le.{0} Real Real.instLEReal (r a) ε) (Eq.{succ u2} α (c a) x)))))) -> (Exists.{succ u1} (Set.{u1} ι) (fun (u : Set.{u1} ι) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) u t) (fun (H : HasSubset.Subset.{u1} (Set.{u1} ι) (Set.instHasSubsetSet.{u1} ι) u t) => And (Set.Countable.{u1} ι u) (And (Set.PairwiseDisjoint.{u2, u1} (Set.{u2} α) ι (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) u B) (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_2 μ) (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s (Set.iUnion.{u2, succ u1} α ι (fun (a : ι) => Set.iUnion.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a u) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) a u) => B a))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))))))
Case conversion may be inaccurate. Consider using '#align vitali.exists_disjoint_covering_ae Vitali.exists_disjoint_covering_aeₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊆ » t') -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊆ » t) -/
/-- The measurable Vitali covering theorem. Assume one is given a family `t` of closed sets with
nonempty interior, such that each `a ∈ t` is included in a ball `B (x, r)` and covers a definite
proportion of the ball `B (x, 3 r)` for a given measure `μ` (think of the situation where `μ` is
a doubling measure and `t` is a family of balls). Consider a (possibly non-measurable) set `s`
at which the family is fine, i.e., every point of `s` belongs to arbitrarily small elements of `t`.
Then one can extract from `t` a disjoint subfamily that covers almost all `s`.

For more flexibility, we give a statement with a parameterized family of sets.
-/
theorem exists_disjoint_covering_ae [MetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (μ : Measure α) [LocallyFiniteMeasure μ] (s : Set α) (t : Set ι)
    (C : ℝ≥0) (r : ι → ℝ) (c : ι → α) (B : ι → Set α) (hB : ∀ a ∈ t, B a ⊆ closedBall (c a) (r a))
    (μB : ∀ a ∈ t, μ (closedBall (c a) (3 * r a)) ≤ C * μ (B a))
    (ht : ∀ a ∈ t, (interior (B a)).Nonempty) (h't : ∀ a ∈ t, IsClosed (B a))
    (hf : ∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ a ∈ t, r a ≤ ε ∧ c a = x) :
    ∃ (u : _)(_ : u ⊆ t), u.Countable ∧ u.PairwiseDisjoint B ∧ μ (s \ ⋃ a ∈ u, B a) = 0 :=
  by
  /- The idea of the proof is the following. Assume for simplicity that `μ` is finite. Applying the
    abstract Vitali covering theorem with `δ = r` given by `hf`, one obtains a disjoint subfamily `u`,
    such that any element of `t` intersects an element of `u` with comparable radius. Fix `ε > 0`.
    Since the elements of `u` have summable measure, one can remove finitely elements `w_1, ..., w_n`.
    so that the measure of the remaining elements is `< ε`. Consider now a point `z` not
    in the `w_i`. There is a small ball around `z` not intersecting the `w_i` (as they are closed),
    an element `a ∈ t` contained in this small ball (as the family `t` is fine at `z`) and an element
    `b ∈ u` intersecting `a`, with comparable radius (by definition of `u`). Then `z` belongs to the
    enlargement of `b`. This shows that `s \ (w_1 ∪ ... ∪ w_n)` is contained in
    `⋃ (b ∈ u \ {w_1, ... w_n}) (enlargement of b)`. The measure of the latter set is bounded by
    `∑ (b ∈ u \ {w_1, ... w_n}) C * μ b` (by the doubling property of the measure), which is at most
    `C ε`. Letting `ε` tend to `0` shows that `s` is almost everywhere covered by the family `u`.
  
    For the real argument, the measure is only locally finite. Therefore, we implement the same
    strategy, but locally restricted to balls on which the measure is finite. For this, we do not
    use the whole family `t`, but a subfamily `t'` supported on small balls (which is possible since
    the family is assumed to be fine at every point of `s`).
    -/
  -- choose around each `x` a small ball on which the measure is finite
  have : ∀ x, ∃ R, 0 < R ∧ R ≤ 1 ∧ μ (closed_ball x (20 * R)) < ∞ :=
    by
    intro x
    obtain ⟨R, Rpos, μR⟩ : ∃ (R : ℝ)(hR : 0 < R), μ (closed_ball x R) < ∞ :=
      (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball
    refine' ⟨min 1 (R / 20), _, min_le_left _ _, _⟩
    · simp only [true_and_iff, lt_min_iff, zero_lt_one]
      linarith
    · apply lt_of_le_of_lt (measure_mono _) μR
      apply closed_ball_subset_closed_ball
      calc
        20 * min 1 (R / 20) ≤ 20 * (R / 20) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ = R := by ring
        
  choose R hR0 hR1 hRμ
  -- we restrict to a subfamily `t'` of `t`, made of elements small enough to ensure that
  -- they only see a finite part of the measure, and with a doubling property
  let t' := { a ∈ t | r a ≤ R (c a) }
  -- extract a disjoint subfamily `u` of `t'` thanks to the abstract Vitali covering theorem.
  obtain ⟨u, ut', u_disj, hu⟩ :
    ∃ (u : _)(_ : u ⊆ t'),
      u.PairwiseDisjoint B ∧ ∀ a ∈ t', ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ r a ≤ 2 * r b :=
    by
    have A : ∀ a ∈ t', r a ≤ 1 := by
      intro a ha
      apply ha.2.trans (hR1 (c a))
    have A' : ∀ a ∈ t', (B a).Nonempty := fun a hat' =>
      Set.Nonempty.mono interior_subset (ht a hat'.1)
    refine' exists_disjoint_subfamily_covering_enlargment B t' r 2 one_lt_two (fun a ha => _) 1 A A'
    exact nonempty_closed_ball.1 ((A' a ha).mono (hB a ha.1))
  have ut : u ⊆ t := fun a hau => (ut' hau).1
  -- As the space is second countable, the family is countable since all its sets have nonempty
  -- interior.
  have u_count : u.countable := u_disj.countable_of_nonempty_interior fun a ha => ht a (ut ha)
  -- the family `u` will be the desired family
  refine' ⟨u, fun a hat' => (ut' hat').1, u_count, u_disj, _⟩
  -- it suffices to show that it covers almost all `s` locally around each point `x`.
  refine' null_of_locally_null _ fun x hx => _
  -- let `v` be the subfamily of `u` made of those sets intersecting the small ball `ball x (r x)`
  let v := { a ∈ u | (B a ∩ ball x (R x)).Nonempty }
  have vu : v ⊆ u := fun a ha => ha.1
  -- they are all contained in a fixed ball of finite measure, thanks to our choice of `t'`
  obtain ⟨K, μK, hK⟩ :
    ∃ K, μ (closed_ball x K) < ∞ ∧ ∀ a ∈ u, (B a ∩ ball x (R x)).Nonempty → B a ⊆ closed_ball x K :=
    by
    have Idist_v : ∀ a ∈ v, dist (c a) x ≤ r a + R x :=
      by
      intro a hav
      apply dist_le_add_of_nonempty_closed_ball_inter_closed_ball
      refine' hav.2.mono _
      apply inter_subset_inter _ ball_subset_closed_ball
      exact hB a (ut (vu hav))
    set R0 := Sup (r '' v) with R0_def
    have R0_bdd : BddAbove (r '' v) :=
      by
      refine' ⟨1, fun r' hr' => _⟩
      rcases(mem_image _ _ _).1 hr' with ⟨b, hb, rfl⟩
      exact le_trans (ut' (vu hb)).2 (hR1 (c b))
    rcases le_total R0 (R x) with (H | H)
    · refine' ⟨20 * R x, hRμ x, fun a au hax => _⟩
      refine' (hB a (ut au)).trans _
      apply closed_ball_subset_closed_ball'
      have : r a ≤ R0 := le_csSup R0_bdd (mem_image_of_mem _ ⟨au, hax⟩)
      linarith [Idist_v a ⟨au, hax⟩, hR0 x]
    · have R0pos : 0 < R0 := (hR0 x).trans_le H
      have vnonempty : v.nonempty := by
        by_contra
        rw [nonempty_iff_ne_empty, Classical.not_not] at h
        simp only [h, Real.sSup_empty, image_empty] at R0_def
        exact lt_irrefl _ (R0pos.trans_le (le_of_eq R0_def))
      obtain ⟨a, hav, R0a⟩ : ∃ a ∈ v, R0 / 2 < r a :=
        by
        obtain ⟨r', r'mem, hr'⟩ : ∃ r' ∈ r '' v, R0 / 2 < r' :=
          exists_lt_of_lt_csSup (nonempty_image_iff.2 vnonempty) (half_lt_self R0pos)
        rcases(mem_image _ _ _).1 r'mem with ⟨a, hav, rfl⟩
        exact ⟨a, hav, hr'⟩
      refine' ⟨8 * R0, _, _⟩
      · apply lt_of_le_of_lt (measure_mono _) (hRμ (c a))
        apply closed_ball_subset_closed_ball'
        rw [dist_comm]
        linarith [Idist_v a hav, (ut' (vu hav)).2]
      · intro b bu hbx
        refine' (hB b (ut bu)).trans _
        apply closed_ball_subset_closed_ball'
        have : r b ≤ R0 := le_csSup R0_bdd (mem_image_of_mem _ ⟨bu, hbx⟩)
        linarith [Idist_v b ⟨bu, hbx⟩]
  -- we will show that, in `ball x (R x)`, almost all `s` is covered by the family `u`.
  refine'
    ⟨_ ∩ ball x (R x), inter_mem_nhdsWithin _ (ball_mem_nhds _ (hR0 _)),
      nonpos_iff_eq_zero.mp (le_of_forall_le_of_dense fun ε εpos => _)⟩
  -- the elements of `v` are disjoint and all contained in a finite volume ball, hence the sum
  -- of their measures is finite.
  have I : (∑' a : v, μ (B a)) < ∞ := by
    calc
      (∑' a : v, μ (B a)) = μ (⋃ a ∈ v, B a) :=
        by
        rw [measure_bUnion (u_count.mono vu) _ fun a ha => (h't _ (vu.trans ut ha)).MeasurableSet]
        exact u_disj.subset vu
      _ ≤ μ (closed_ball x K) := (measure_mono (Union₂_subset fun a ha => hK a (vu ha) ha.2))
      _ < ∞ := μK
      
  -- we can obtain a finite subfamily of `v`, such that the measures of the remaining elements
  -- add up to an arbitrarily small number, say `ε / C`.
  obtain ⟨w, hw⟩ : ∃ w : Finset ↥v, (∑' a : { a // a ∉ w }, μ (B a)) < ε / C :=
    haveI : 0 < ε / C := by
      simp only [ENNReal.div_pos_iff, εpos.ne', ENNReal.coe_ne_top, Ne.def, not_false_iff,
        and_self_iff]
    ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero I.ne)).2 _ this).exists
  -- main property: the points `z` of `s` which are not covered by `u` are contained in the
  -- enlargements of the elements not in `w`.
  have M : (s \ ⋃ a ∈ u, B a) ∩ ball x (R x) ⊆ ⋃ a : { a // a ∉ w }, closed_ball (c a) (3 * r a) :=
    by
    intro z hz
    set k := ⋃ (a : v) (ha : a ∈ w), B a with hk
    have k_closed : IsClosed k := isClosed_biUnion w.finite_to_set fun i hi => h't _ (ut (vu i.2))
    have z_notmem_k : z ∉ k :=
      by
      simp only [not_exists, exists_prop, mem_Union, mem_sep_iff, forall_exists_index,
        SetCoe.exists, not_and, exists_and_right, Subtype.coe_mk]
      intro b hbv h'b h'z
      have : z ∈ (s \ ⋃ a ∈ u, B a) ∩ ⋃ a ∈ u, B a :=
        mem_inter (mem_of_mem_inter_left hz) (mem_bUnion (vu hbv) h'z)
      simpa only [diff_inter_self]
    -- since the elements of `w` are closed and finitely many, one can find a small ball around `z`
    -- not intersecting them
    have : ball x (R x) \ k ∈ 𝓝 z :=
      by
      apply IsOpen.mem_nhds (is_open_ball.sdiff k_closed) _
      exact (mem_diff _).2 ⟨mem_of_mem_inter_right hz, z_notmem_k⟩
    obtain ⟨d, dpos, hd⟩ : ∃ (d : ℝ)(dpos : 0 < d), closed_ball z d ⊆ ball x (R x) \ k :=
      nhds_basis_closed_ball.mem_iff.1 this
    -- choose an element `a` of the family `t` contained in this small ball
    obtain ⟨a, hat, ad, rfl⟩ : ∃ a ∈ t, r a ≤ min d (R z) ∧ c a = z
    exact hf z ((mem_diff _).1 (mem_of_mem_inter_left hz)).1 (min d (R z)) (lt_min dpos (hR0 z))
    have ax : B a ⊆ ball x (R x) := by
      refine' (hB a hat).trans _
      refine' subset.trans _ (hd.trans (diff_subset (ball x (R x)) k))
      exact closed_ball_subset_closed_ball (ad.trans (min_le_left _ _))
    -- it intersects an element `b` of `u` with comparable diameter, by definition of `u`
    obtain ⟨b, bu, ab, bdiam⟩ : ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ r a ≤ 2 * r b
    exact hu a ⟨hat, ad.trans (min_le_right _ _)⟩
    have bv : b ∈ v := by
      refine' ⟨bu, ab.mono _⟩
      rw [inter_comm]
      exact inter_subset_inter_right _ ax
    let b' : v := ⟨b, bv⟩
    -- `b` can not belong to `w`, as the elements of `w` do not intersect `closed_ball z d`,
    -- contrary to `b`
    have b'_notmem_w : b' ∉ w := by
      intro b'w
      have b'k : B b' ⊆ k := @Finset.subset_set_biUnion_of_mem _ _ _ (fun y : v => B y) _ b'w
      have : (ball x (R x) \ k ∩ k).Nonempty :=
        by
        apply ab.mono (inter_subset_inter _ b'k)
        refine' ((hB _ hat).trans _).trans hd
        exact closed_ball_subset_closed_ball (ad.trans (min_le_left _ _))
      simpa only [diff_inter_self, not_nonempty_empty]
    let b'' : { a // a ∉ w } := ⟨b', b'_notmem_w⟩
    -- since `a` and `b` have comparable diameters, it follows that `z` belongs to the
    -- enlargement of `b`
    have zb : c a ∈ closed_ball (c b) (3 * r b) :=
      by
      rcases ab with ⟨e, ⟨ea, eb⟩⟩
      have A : dist (c a) e ≤ r a := mem_closed_ball'.1 (hB a hat ea)
      have B : dist e (c b) ≤ r b := mem_closed_ball.1 (hB b (ut bu) eb)
      simp only [mem_closed_ball]
      linarith [dist_triangle (c a) e (c b)]
    suffices H : closed_ball (c b'') (3 * r b'') ⊆ ⋃ a : { a // a ∉ w }, closed_ball (c a) (3 * r a)
    exact H zb
    exact subset_Union (fun a : { a // a ∉ w } => closed_ball (c a) (3 * r a)) b''
  -- now that we have proved our main inclusion, we can use it to estimate the measure of the points
  -- in `ball x (r x)` not covered by `u`.
  haveI : Encodable v := (u_count.mono vu).toEncodable
  calc
    μ ((s \ ⋃ a ∈ u, B a) ∩ ball x (R x)) ≤ μ (⋃ a : { a // a ∉ w }, closed_ball (c a) (3 * r a)) :=
      measure_mono M
    _ ≤ ∑' a : { a // a ∉ w }, μ (closed_ball (c a) (3 * r a)) := (measure_Union_le _)
    _ ≤ ∑' a : { a // a ∉ w }, C * μ (B a) := (ENNReal.tsum_le_tsum fun a => μB a (ut (vu a.1.2)))
    _ = C * ∑' a : { a // a ∉ w }, μ (B a) := ENNReal.tsum_mul_left
    _ ≤ C * (ε / C) := (mul_le_mul_left' hw.le _)
    _ ≤ ε := ENNReal.mul_div_le
    
#align vitali.exists_disjoint_covering_ae Vitali.exists_disjoint_covering_ae

/- warning: vitali.vitali_family -> Vitali.vitaliFamily is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : OpensMeasurableSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) _inst_2] [_inst_4 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_5 : MeasureTheory.LocallyFiniteMeasure.{u1} α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) μ] (C : NNReal), (forall (x : α), Filter.Frequently.{0} Real (fun (r : Real) => LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 3 (OfNat.mk.{0} Real 3 (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne)))) r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) C) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_2) (fun (_x : MeasureTheory.Measure.{u1} α _inst_2) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_2) μ (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r)))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) -> (VitaliFamily.{u1} α _inst_1 _inst_2 μ)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : OpensMeasurableSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) _inst_2] [_inst_4 : TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)))] (μ : MeasureTheory.Measure.{u1} α _inst_2) [_inst_5 : MeasureTheory.LocallyFiniteMeasure.{u1} α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) μ] (C : NNReal), (forall (x : α), Filter.Frequently.{0} Real (fun (r : Real) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 3 (instOfNat.{0} Real 3 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) r))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENNReal.some C) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α _inst_2 μ) (Metric.closedBall.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1) x r)))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) -> (VitaliFamily.{u1} α _inst_1 _inst_2 μ)
Case conversion may be inaccurate. Consider using '#align vitali.vitali_family Vitali.vitaliFamilyₓ'. -/
/-- Assume that around every point there are arbitrarily small scales at which the measure is
doubling. Then the set of closed sets `a` with nonempty interior contained in `closed_ball x r` and
covering a fixed proportion `1/C` of the ball `closed_ball x (3 * r)` forms a Vitali family.
This is essentially a restatement of the measurable Vitali theorem. -/
protected def vitaliFamily [MetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (μ : Measure α) [LocallyFiniteMeasure μ] (C : ℝ≥0)
    (h : ∀ x, ∃ᶠ r in 𝓝[>] 0, μ (closedBall x (3 * r)) ≤ C * μ (closedBall x r)) : VitaliFamily μ
    where
  setsAt x :=
    { a |
      IsClosed a ∧
        (interior a).Nonempty ∧ ∃ r, a ⊆ closedBall x r ∧ μ (closedBall x (3 * r)) ≤ C * μ a }
  MeasurableSet' x a ha := ha.1.MeasurableSet
  nonempty_interior x a ha := ha.2.1
  Nontrivial x ε εpos :=
    by
    obtain ⟨r, μr, rpos, rε⟩ :
      ∃ r, μ (closed_ball x (3 * r)) ≤ C * μ (closed_ball x r) ∧ r ∈ Ioc (0 : ℝ) ε :=
      ((h x).and_eventually (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, εpos⟩)).exists
    refine'
      ⟨closed_ball x r, ⟨is_closed_ball, _, ⟨r, subset.rfl, μr⟩⟩, closed_ball_subset_closed_ball rε⟩
    exact (nonempty_ball.2 rpos).mono ball_subset_interior_closed_ball
  covering := by
    intro s f fsubset ffine
    let t : Set (ℝ × α × Set α) :=
      { p |
        p.2.2 ⊆ closed_ball p.2.1 p.1 ∧
          μ (closed_ball p.2.1 (3 * p.1)) ≤ C * μ p.2.2 ∧
            (interior p.2.2).Nonempty ∧ IsClosed p.2.2 ∧ p.2.2 ∈ f p.2.1 ∧ p.2.1 ∈ s }
    have A : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ (p : ℝ × α × Set α)(Hp : p ∈ t), p.1 ≤ ε ∧ p.2.1 = x :=
      by
      intro x xs ε εpos
      rcases ffine x xs ε εpos with ⟨a, ha, h'a⟩
      rcases fsubset x xs ha with ⟨a_closed, a_int, ⟨r, ar, μr⟩⟩
      refine' ⟨⟨min r ε, x, a⟩, ⟨_, _, a_int, a_closed, ha, xs⟩, min_le_right _ _, rfl⟩
      · rcases min_cases r ε with (h' | h') <;> rwa [h'.1]
      · apply le_trans (measure_mono (closed_ball_subset_closed_ball _)) μr
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) zero_le_three
    rcases exists_disjoint_covering_ae μ s t C (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2)
        (fun p hp => hp.1) (fun p hp => hp.2.1) (fun p hp => hp.2.2.1) (fun p hp => hp.2.2.2.1)
        A with
      ⟨t', t't, t'_count, t'_disj, μt'⟩
    refine' ⟨(fun p : ℝ × α × Set α => p.2) '' t', _, _, _, _⟩
    · rintro - ⟨q, hq, rfl⟩
      exact (t't hq).2.2.2.2.2
    · rintro p ⟨q, hq, rfl⟩ p' ⟨q', hq', rfl⟩ hqq'
      exact t'_disj hq hq' (ne_of_apply_ne _ hqq')
    · rintro - ⟨q, hq, rfl⟩
      exact (t't hq).2.2.2.2.1
    · convert μt' using 3
      rw [bUnion_image]
#align vitali.vitali_family Vitali.vitaliFamily

end Vitali

