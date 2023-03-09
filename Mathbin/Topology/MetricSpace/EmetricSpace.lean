/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.emetric_space
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Real.Ennreal
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `pseudo_emetric_space`, where we don't require `edist x y = 0 → x = y` and we specialize
to `emetric_space` at the end.
-/


open Set Filter Classical

open uniformity Topology BigOperators Filter NNReal ENNReal

universe u v w

variable {α : Type u} {β : Type v} {X : Type _}

/- warning: uniformity_dist_of_mem_uniformity -> uniformity_dist_of_mem_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {U : Filter.{u1} (Prod.{u1, u1} α α)} (z : β) (D : α -> α -> β), (forall (s : Set.{u1} (Prod.{u1, u1} α α)), Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s U) (Exists.{succ u2} β (fun (ε : β) => Exists.{0} (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) ε z) (fun (H : GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) ε z) => forall {a : α} {b : α}, (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (D a b) ε) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) s))))) -> (Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) U (infᵢ.{u1, succ u2} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) β (fun (ε : β) => infᵢ.{u1, 0} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) ε z) (fun (H : GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) ε z) => Filter.principal.{u1} (Prod.{u1, u1} α α) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (D (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {U : Filter.{u1} (Prod.{u1, u1} α α)} (z : β) (D : α -> α -> β), (forall (s : Set.{u1} (Prod.{u1, u1} α α)), Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s U) (Exists.{succ u2} β (fun (ε : β) => And (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) ε z) (forall {a : α} {b : α}, (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (D a b) ε) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) s))))) -> (Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) U (infᵢ.{u1, succ u2} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) β (fun (ε : β) => infᵢ.{u1, 0} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) ε z) (fun (H : GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) ε z) => Filter.principal.{u1} (Prod.{u1, u1} α α) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (D (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))))))
Case conversion may be inaccurate. Consider using '#align uniformity_dist_of_mem_uniformity uniformity_dist_of_mem_uniformityₓ'. -/
/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [LinearOrder β] {U : Filter (α × α)} (z : β)
    (D : α → α → β) (H : ∀ s, s ∈ U ↔ ∃ ε > z, ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
    U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  HasBasis.eq_binfᵢ ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_set_of]⟩
#align uniformity_dist_of_mem_uniformity uniformity_dist_of_mem_uniformity

#print EDist /-
/-- `has_edist α` means that `α` is equipped with an extended distance. -/
class EDist (α : Type _) where
  edist : α → α → ℝ≥0∞
#align has_edist EDist
-/

export EDist (edist)

/- warning: uniform_space_of_edist -> uniformSpaceOfEDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (edist : α -> α -> ENNReal), (forall (x : α), Eq.{1} ENNReal (edist x x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall (x : α) (y : α), Eq.{1} ENNReal (edist x y) (edist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (edist x z) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (edist x y) (edist y z))) -> (UniformSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (edist : α -> α -> ENNReal), (forall (x : α), Eq.{1} ENNReal (edist x x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall (x : α) (y : α), Eq.{1} ENNReal (edist x y) (edist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (edist x z) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (edist x y) (edist y z))) -> (UniformSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align uniform_space_of_edist uniformSpaceOfEDistₓ'. -/
/-- Creating a uniform space from an extended distance. -/
noncomputable def uniformSpaceOfEDist (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : UniformSpace α :=
  UniformSpace.ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.lt.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩
#align uniform_space_of_edist uniformSpaceOfEDist

#print PseudoEMetricSpace /-
-- the uniform structure is embedded in the emetric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- Extended (pseudo) metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each pseudo_emetric space induces a canonical `uniform_space` and hence a canonical
`topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `pseudo_emetric_space` structure, the uniformity fields are not necessary, they
will be filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating a `pseudo_emetric_space` structure
on a product.

Continuity of `edist` is proved in `topology.instances.ennreal`
-/
class PseudoEMetricSpace (α : Type u) extends EDist α : Type u where
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist :
    𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α |
            edist p.1 p.2 < ε } := by
    intros
    rfl
#align pseudo_emetric_space PseudoEMetricSpace
-/

attribute [instance] PseudoEMetricSpace.toUniformSpace

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/
variable [PseudoEMetricSpace α]

export PseudoEMetricSpace (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/- warning: edist_triangle_left -> edist_triangle_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) z x) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) z y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) z x) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) z y))
Case conversion may be inaccurate. Consider using '#align edist_triangle_left edist_triangle_leftₓ'. -/
/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y := by
  rw [edist_comm z] <;> apply edist_triangle
#align edist_triangle_left edist_triangle_left

/- warning: edist_triangle_right -> edist_triangle_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x z) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x z) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align edist_triangle_right edist_triangle_rightₓ'. -/
theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z := by
  rw [edist_comm y] <;> apply edist_triangle
#align edist_triangle_right edist_triangle_right

/- warning: edist_congr_right -> edist_congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x z) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x z) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align edist_congr_right edist_congr_rightₓ'. -/
theorem edist_congr_right {x y z : α} (h : edist x y = 0) : edist x z = edist y z :=
  by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z), ← h]
    apply edist_triangle
#align edist_congr_right edist_congr_right

/- warning: edist_congr_left -> edist_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) z x) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) z y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) z x) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) z y))
Case conversion may be inaccurate. Consider using '#align edist_congr_left edist_congr_leftₓ'. -/
theorem edist_congr_left {x y z : α} (h : edist x y = 0) : edist z x = edist z y :=
  by
  rw [edist_comm z x, edist_comm z y]
  apply edist_congr_right h
#align edist_congr_left edist_congr_left

/- warning: edist_triangle4 -> edist_triangle4 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (z : α) (t : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y z)) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) z t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α) (z : α) (t : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x t) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y z)) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) z t))
Case conversion may be inaccurate. Consider using '#align edist_triangle4 edist_triangle4ₓ'. -/
theorem edist_triangle4 (x y z t : α) : edist x t ≤ edist x y + edist y z + edist z t :=
  calc
    edist x t ≤ edist x z + edist z t := edist_triangle x z t
    _ ≤ edist x y + edist y z + edist z t := add_le_add_right (edist_triangle x y z) _
    
#align edist_triangle4 edist_triangle4

/- warning: edist_le_Ico_sum_edist -> edist_le_Ico_sum_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (f : Nat -> α) {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (f : Nat -> α) {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align edist_le_Ico_sum_edist edist_le_Ico_sum_edistₓ'. -/
/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i in Finset.Ico m n, edist (f i) (f (i + 1)) :=
  by
  revert n
  refine' Nat.le_induction _ _
  · simp only [Finset.sum_empty, Finset.Ico_self, edist_self]
    -- TODO: Why doesn't Lean close this goal automatically? `exact le_rfl` fails too.
    exact le_refl (0 : ℝ≥0∞)
  · intro n hn hrec
    calc
      edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := (add_le_add hrec le_rfl)
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [Nat.Ico_succ_right_eq_insert_Ico hn, Finset.sum_insert, add_comm] <;> simp
      
#align edist_le_Ico_sum_edist edist_le_Ico_sum_edist

/- warning: edist_le_range_sum_edist -> edist_le_range_sum_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (f : Nat -> α) (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f n)) (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (f : Nat -> α) (n : Nat), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f n)) (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align edist_le_range_sum_edist edist_le_range_sum_edistₓ'. -/
/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i in Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)
#align edist_le_range_sum_edist edist_le_range_sum_edist

/- warning: edist_le_Ico_sum_of_edist_le -> edist_le_Ico_sum_of_edist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (forall {d : Nat -> ENNReal}, (forall {k : Nat}, (LE.le.{0} Nat Nat.hasLe m k) -> (LT.lt.{0} Nat Nat.hasLt k n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (d k))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => d i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (forall {d : Nat -> ENNReal}, (forall {k : Nat}, (LE.le.{0} Nat instLENat m k) -> (LT.lt.{0} Nat instLTNat k n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (d k))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => d i))))
Case conversion may be inaccurate. Consider using '#align edist_le_Ico_sum_of_edist_le edist_le_Ico_sum_of_edist_leₓ'. -/
/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
#align edist_le_Ico_sum_of_edist_le edist_le_Ico_sum_of_edist_le

/- warning: edist_le_range_sum_of_edist_le -> edist_le_range_sum_of_edist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (n : Nat) {d : Nat -> ENNReal}, (forall {k : Nat}, (LT.lt.{0} Nat Nat.hasLt k n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (d k))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f n)) (Finset.sum.{0, 0} ENNReal Nat (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) (Finset.range n) (fun (i : Nat) => d i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Nat -> α} (n : Nat) {d : Nat -> ENNReal}, (forall {k : Nat}, (LT.lt.{0} Nat instLTNat k n) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (d k))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f n)) (Finset.sum.{0, 0} ENNReal Nat (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) (Finset.range n) (fun (i : Nat) => d i)))
Case conversion may be inaccurate. Consider using '#align edist_le_range_sum_of_edist_le edist_le_range_sum_of_edist_leₓ'. -/
/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ _ => hd
#align edist_le_range_sum_of_edist_le edist_le_range_sum_of_edist_le

/- warning: uniformity_pseudoedist -> uniformity_pseudoedist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (infᵢ.{u1, 1} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) ENNReal (fun (ε : ENNReal) => infᵢ.{u1, 0} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => Filter.principal.{u1} (Prod.{u1, u1} α α) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (infᵢ.{u1, 1} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) ENNReal (fun (ε : ENNReal) => infᵢ.{u1, 0} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) => Filter.principal.{u1} (Prod.{u1, u1} α α) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))))
Case conversion may be inaccurate. Consider using '#align uniformity_pseudoedist uniformity_pseudoedistₓ'. -/
/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist
#align uniformity_pseudoedist uniformity_pseudoedist

#print uniformSpace_edist /-
theorem uniformSpace_edist :
    ‹PseudoEMetricSpace α›.toUniformSpace =
      uniformSpaceOfEDist edist edist_self edist_comm edist_triangle :=
  uniformSpace_eq uniformity_pseudoedist
#align uniform_space_edist uniformSpace_edist
-/

/- warning: uniformity_basis_edist -> uniformity_basis_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist uniformity_basis_edistₓ'. -/
theorem uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _
#align uniformity_basis_edist uniformity_basis_edist

/- warning: mem_uniformity_edist -> mem_uniformity_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))) (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b) ε) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))) (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b) ε) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) s))))
Case conversion may be inaccurate. Consider using '#align mem_uniformity_edist mem_uniformity_edistₓ'. -/
/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  uniformity_basis_edist.mem_uniformity_iff
#align mem_uniformity_edist mem_uniformity_edist

/- warning: emetric.mk_uniformity_basis -> EMetric.mk_uniformity_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {β : Type.{u2}} {p : β -> Prop} {f : β -> ENNReal}, (forall (x : β), (p x) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (f x))) -> (forall (ε : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Exists.{succ u2} β (fun (x : β) => Exists.{0} (p x) (fun (hx : p x) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) ε)))) -> (Filter.HasBasis.{u1, succ u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) p (fun (x : β) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (f x))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] {β : Type.{u1}} {p : β -> Prop} {f : β -> ENNReal}, (forall (x : β), (p x) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (f x))) -> (forall (ε : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Exists.{succ u1} β (fun (x : β) => And (p x) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) ε)))) -> (Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} α α) β (uniformity.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1)) p (fun (x : β) => setOf.{u2} (Prod.{u2, u2} α α) (fun (p : Prod.{u2, u2} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (Prod.fst.{u2, u2} α α p) (Prod.snd.{u2, u2} α α p)) (f x))))
Case conversion may be inaccurate. Consider using '#align emetric.mk_uniformity_basis EMetric.mk_uniformity_basisₓ'. -/
/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem EMetric.mk_uniformity_basis {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 < f x } :=
  by
  refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
#align emetric.mk_uniformity_basis EMetric.mk_uniformity_basis

/- warning: emetric.mk_uniformity_basis_le -> EMetric.mk_uniformity_basis_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {β : Type.{u2}} {p : β -> Prop} {f : β -> ENNReal}, (forall (x : β), (p x) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (f x))) -> (forall (ε : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Exists.{succ u2} β (fun (x : β) => Exists.{0} (p x) (fun (hx : p x) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (f x) ε)))) -> (Filter.HasBasis.{u1, succ u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) p (fun (x : β) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (f x))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] {β : Type.{u1}} {p : β -> Prop} {f : β -> ENNReal}, (forall (x : β), (p x) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (f x))) -> (forall (ε : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Exists.{succ u1} β (fun (x : β) => And (p x) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (f x) ε)))) -> (Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} α α) β (uniformity.{u2} α (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1)) p (fun (x : β) => setOf.{u2} (Prod.{u2, u2} α α) (fun (p : Prod.{u2, u2} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (Prod.fst.{u2, u2} α α p) (Prod.snd.{u2, u2} α α p)) (f x))))
Case conversion may be inaccurate. Consider using '#align emetric.mk_uniformity_basis_le EMetric.mk_uniformity_basis_leₓ'. -/
/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem EMetric.mk_uniformity_basis_le {β : Type _} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 ≤ f x } :=
  by
  refine' ⟨fun s => uniformity_basis_edist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_lt hx)⟩
#align emetric.mk_uniformity_basis_le EMetric.mk_uniformity_basis_le

/- warning: uniformity_basis_edist_le -> uniformity_basis_edist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist_le uniformity_basis_edist_leₓ'. -/
theorem uniformity_basis_edist_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩
#align uniformity_basis_edist_le uniformity_basis_edist_le

/- warning: uniformity_basis_edist' -> uniformity_basis_edist' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (ε' : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε') -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) ε (Set.Ioo.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε')) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (ε' : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε') -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) ε (Set.Ioo.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε')) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist' uniformity_basis_edist'ₓ'. -/
theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩
#align uniformity_basis_edist' uniformity_basis_edist'

/- warning: uniformity_basis_edist_le' -> uniformity_basis_edist_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (ε' : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε') -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => Membership.Mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.hasMem.{0} ENNReal) ε (Set.Ioo.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε')) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (ε' : ENNReal), (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε') -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => Membership.mem.{0, 0} ENNReal (Set.{0} ENNReal) (Set.instMembershipSet.{0} ENNReal) ε (Set.Ioo.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε')) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist_le' uniformity_basis_edist_le'ₓ'. -/
theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩
#align uniformity_basis_edist_le' uniformity_basis_edist_le'

/- warning: uniformity_basis_edist_nnreal -> uniformity_basis_edist_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) NNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) ε) (fun (ε : NNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) NNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) ε) (fun (ε : NNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (ENNReal.some ε)))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist_nnreal uniformity_basis_edist_nnrealₓ'. -/
theorem uniformity_basis_edist_nnreal :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩
#align uniformity_basis_edist_nnreal uniformity_basis_edist_nnreal

/- warning: uniformity_basis_edist_nnreal_le -> uniformity_basis_edist_nnreal_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) NNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) ε) (fun (ε : NNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) NNReal (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) ε) (fun (ε : NNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (ENNReal.some ε)))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist_nnreal_le uniformity_basis_edist_nnreal_leₓ'. -/
theorem uniformity_basis_edist_nnreal_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩
#align uniformity_basis_edist_nnreal_le uniformity_basis_edist_nnreal_le

/- warning: uniformity_basis_edist_inv_nat -> uniformity_basis_edist_inv_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (_x : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Inv.inv.{0} ENNReal ENNReal.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat ENNReal (HasLiftT.mk.{1, 1} Nat ENNReal (CoeTCₓ.coe.{1, 1} Nat ENNReal (Nat.castCoe.{0} ENNReal (AddMonoidWithOne.toNatCast.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))) n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (_x : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (Nat.cast.{0} ENNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) n))))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist_inv_nat uniformity_basis_edist_inv_natₓ'. -/
theorem uniformity_basis_edist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ } :=
  EMetric.mk_uniformity_basis (fun n _ => ENNReal.inv_pos.2 <| ENNReal.nat_ne_top n) fun ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩
#align uniformity_basis_edist_inv_nat uniformity_basis_edist_inv_nat

/- warning: uniformity_basis_edist_inv_two_pow -> uniformity_basis_edist_inv_two_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (_x : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (Inv.inv.{0} ENNReal ENNReal.hasInv (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (_x : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) (Inv.inv.{0} ENNReal ENNReal.instInvENNReal (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) n)))
Case conversion may be inaccurate. Consider using '#align uniformity_basis_edist_inv_two_pow uniformity_basis_edist_inv_two_powₓ'. -/
theorem uniformity_basis_edist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  EMetric.mk_uniformity_basis (fun n _ => ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.two_ne_top) _)
    fun ε ε₀ =>
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩
#align uniformity_basis_edist_inv_two_pow uniformity_basis_edist_inv_two_pow

/- warning: edist_mem_uniformity -> edist_mem_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)) (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)) (uniformity.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align edist_mem_uniformity edist_mem_uniformityₓ'. -/
/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, fun a b => id⟩
#align edist_mem_uniformity edist_mem_uniformity

namespace Emetric

instance (priority := 900) : IsCountablyGenerated (𝓤 α) :=
  isCountablyGenerated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_infᵢ⟩

/- warning: emetric.uniform_continuous_on_iff -> EMetric.uniformContinuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : α} {H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s} {b : α} {H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f a) (f b)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall {b : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f a) (f b)) ε))))))
Case conversion may be inaccurate. Consider using '#align emetric.uniform_continuous_on_iff EMetric.uniformContinuousOn_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection {a b «expr ∈ » s} -/
/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniformContinuousOn_iff [PseudoEMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a} {_ : a ∈ s} {b} {_ : b ∈ s}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist
#align emetric.uniform_continuous_on_iff EMetric.uniformContinuousOn_iff

/- warning: emetric.uniform_continuous_iff -> EMetric.uniformContinuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f a) (f b)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f a) (f b)) ε)))))
Case conversion may be inaccurate. Consider using '#align emetric.uniform_continuous_iff EMetric.uniformContinuous_iffₓ'. -/
/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniformContinuous_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist
#align emetric.uniform_continuous_iff EMetric.uniformContinuous_iff

/- warning: emetric.uniform_embedding_iff -> EMetric.uniformEmbedding_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (δ : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b) δ)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (δ : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b) δ)))))))
Case conversion may be inaccurate. Consider using '#align emetric.uniform_embedding_iff EMetric.uniformEmbedding_iffₓ'. -/
/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
theorem uniformEmbedding_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformEmbedding f ↔
      Function.Injective f ∧
        UniformContinuous f ∧
          ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  by
  simp only [uniformity_basis_edist.uniform_embedding_iff uniformity_basis_edist, exists_prop]
  rfl
#align emetric.uniform_embedding_iff EMetric.uniformEmbedding_iff

/- warning: emetric.controlled_of_uniform_embedding -> EMetric.controlled_of_uniformEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β}, (UniformEmbedding.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) -> (And (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f a) (f b)) ε))))) (forall (δ : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b) δ))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β}, (UniformEmbedding.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2) f) -> (And (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f a) (f b)) ε))))) (forall (δ : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : α} {b : α}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b) δ))))))
Case conversion may be inaccurate. Consider using '#align emetric.controlled_of_uniform_embedding EMetric.controlled_of_uniformEmbeddingₓ'. -/
/-- If a map between pseudoemetric spaces is a uniform embedding then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniformEmbedding [PseudoEMetricSpace β] {f : α → β} :
    UniformEmbedding f →
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  fun h => ⟨uniformContinuous_iff.1 (uniformEmbedding_iff.1 h).2.1, (uniformEmbedding_iff.1 h).2.2⟩
#align emetric.controlled_of_uniform_embedding EMetric.controlled_of_uniformEmbedding

/- warning: emetric.cauchy_iff -> EMetric.cauchy_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) f) (And (Ne.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) ε)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) f) (And (Ne.{succ u1} (Filter.{u1} α) f (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) ε)))))))
Case conversion may be inaccurate. Consider using '#align emetric.cauchy_iff EMetric.cauchy_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » t) -/
/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ (x) (_ : x ∈ t) (y) (_ : y ∈ t), edist x y < ε := by
  rw [← ne_bot_iff] <;> exact uniformity_basis_edist.cauchy_iff
#align emetric.cauchy_iff EMetric.cauchy_iff

/- warning: emetric.complete_of_convergent_controlled_sequences -> EMetric.complete_of_convergent_controlled_sequences is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (B : Nat -> ENNReal), (forall (n : Nat), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (B n)) -> (forall (u : Nat -> α), (forall (N : Nat) (n : Nat) (m : Nat), (LE.le.{0} Nat Nat.hasLe N n) -> (LE.le.{0} Nat Nat.hasLe N m) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (u n) (u m)) (B N))) -> (Exists.{succ u1} α (fun (x : α) => Filter.Tendsto.{0, u1} Nat α u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x)))) -> (CompleteSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (B : Nat -> ENNReal), (forall (n : Nat), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (B n)) -> (forall (u : Nat -> α), (forall (N : Nat) (n : Nat) (m : Nat), (LE.le.{0} Nat instLENat N n) -> (LE.le.{0} Nat instLENat N m) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (u n) (u m)) (B N))) -> (Exists.{succ u1} α (fun (x : α) => Filter.Tendsto.{0, u1} Nat α u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x)))) -> (CompleteSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align emetric.complete_of_convergent_controlled_sequences EMetric.complete_of_convergent_controlled_sequencesₓ'. -/
/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
    (H :
      ∀ u : ℕ → α,
        (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) → ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H
#align emetric.complete_of_convergent_controlled_sequences EMetric.complete_of_convergent_controlled_sequences

#print EMetric.complete_of_cauchySeq_tendsto /-
/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchySeq_tendsto
#align emetric.complete_of_cauchy_seq_tendsto EMetric.complete_of_cauchySeq_tendsto
-/

/- warning: emetric.tendsto_locally_uniformly_on_iff -> EMetric.tendstoLocallyUniformlyOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι} {s : Set.{u2} β}, Iff (TendstoLocallyUniformlyOn.{u2, u1, u3} β α ι (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_2 F f p s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhdsWithin.{u2} β _inst_2 x s)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhdsWithin.{u2} β _inst_2 x s)) => Filter.Eventually.{u3} ι (fun (n : ι) => forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f y) (F n y)) ε)) p)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι} {s : Set.{u3} β}, Iff (TendstoLocallyUniformlyOn.{u3, u2, u1} β α ι (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) _inst_2 F f p s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall (x : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x s) -> (Exists.{succ u3} (Set.{u3} β) (fun (t : Set.{u3} β) => And (Membership.mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (instMembershipSetFilter.{u3} β) t (nhdsWithin.{u3} β _inst_2 x s)) (Filter.Eventually.{u1} ι (fun (n : ι) => forall (y : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (f y) (F n y)) ε)) p)))))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_locally_uniformly_on_iff EMetric.tendstoLocallyUniformlyOn_iffₓ'. -/
/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendstoLocallyUniformlyOn_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => _⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩
#align emetric.tendsto_locally_uniformly_on_iff EMetric.tendstoLocallyUniformlyOn_iff

/- warning: emetric.tendsto_uniformly_on_iff -> EMetric.tendstoUniformlyOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ι : Type.{u3}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι} {s : Set.{u2} β}, Iff (TendstoUniformlyOn.{u2, u1, u3} β α ι (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) F f p s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.Eventually.{u3} ι (fun (n : ι) => forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f x) (F n x)) ε)) p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u2} α] {ι : Type.{u1}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι} {s : Set.{u3} β}, Iff (TendstoUniformlyOn.{u3, u2, u1} β α ι (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) F f p s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.Eventually.{u1} ι (fun (n : ι) => forall (x : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (f x) (F n x)) ε)) p))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_uniformly_on_iff EMetric.tendstoUniformlyOn_iffₓ'. -/
/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendstoUniformlyOn_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, edist (f x) (F n x) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)
#align emetric.tendsto_uniformly_on_iff EMetric.tendstoUniformlyOn_iff

/- warning: emetric.tendsto_locally_uniformly_iff -> EMetric.tendstoLocallyUniformly_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι}, Iff (TendstoLocallyUniformly.{u2, u1, u3} β α ι (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_2 F f p) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (forall (x : β), Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 x)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 x)) => Filter.Eventually.{u3} ι (fun (n : ι) => forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f y) (F n y)) ε)) p))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι}, Iff (TendstoLocallyUniformly.{u3, u2, u1} β α ι (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) _inst_2 F f p) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (forall (x : β), Exists.{succ u3} (Set.{u3} β) (fun (t : Set.{u3} β) => And (Membership.mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (instMembershipSetFilter.{u3} β) t (nhds.{u3} β _inst_2 x)) (Filter.Eventually.{u1} ι (fun (n : ι) => forall (y : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y t) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (f y) (F n y)) ε)) p))))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_locally_uniformly_iff EMetric.tendstoLocallyUniformly_iffₓ'. -/
/-- Expressing locally uniform convergence using `edist`. -/
theorem tendstoLocallyUniformly_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε :=
  by
  simp only [← tendstoLocallyUniformlyOn_univ, tendsto_locally_uniformly_on_iff, mem_univ,
    forall_const, exists_prop, nhdsWithin_univ]
#align emetric.tendsto_locally_uniformly_iff EMetric.tendstoLocallyUniformly_iff

/- warning: emetric.tendsto_uniformly_iff -> EMetric.tendstoUniformly_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ι : Type.{u3}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι}, Iff (TendstoUniformly.{u2, u1, u3} β α ι (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) F f p) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.Eventually.{u3} ι (fun (n : ι) => forall (x : β), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f x) (F n x)) ε) p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoEMetricSpace.{u2} α] {ι : Type.{u1}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι}, Iff (TendstoUniformly.{u3, u2, u1} β α ι (PseudoEMetricSpace.toUniformSpace.{u2} α _inst_1) F f p) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.Eventually.{u1} ι (fun (n : ι) => forall (x : β), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (f x) (F n x)) ε) p))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_uniformly_iff EMetric.tendstoUniformly_iffₓ'. -/
/-- Expressing uniform convergence using `edist`. -/
theorem tendstoUniformly_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε := by
  simp only [← tendstoUniformlyOn_univ, tendsto_uniformly_on_iff, mem_univ, forall_const]
#align emetric.tendsto_uniformly_iff EMetric.tendstoUniformly_iff

end Emetric

open Emetric

#print PseudoEMetricSpace.replaceUniformity /-
/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def PseudoEMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoEMetricSpace α
    where
  edist := @edist _ m.toHasEdist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)
#align pseudo_emetric_space.replace_uniformity PseudoEMetricSpace.replaceUniformity
-/

#print PseudoEMetricSpace.induced /-
/-- The extended pseudometric induced by a function taking values in a pseudoemetric space. -/
def PseudoEMetricSpace.induced {α β} (f : α → β) (m : PseudoEMetricSpace β) : PseudoEMetricSpace α
    where
  edist x y := edist (f x) (f y)
  edist_self x := edist_self _
  edist_comm x y := edist_comm _ _
  edist_triangle x y z := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap _).eq_binfᵢ
#align pseudo_emetric_space.induced PseudoEMetricSpace.induced
-/

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type _} {p : α → Prop} [PseudoEMetricSpace α] : PseudoEMetricSpace (Subtype p) :=
  PseudoEMetricSpace.induced coe ‹_›

#print Subtype.edist_eq /-
/-- The extended psuedodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition -/
theorem Subtype.edist_eq {p : α → Prop} (x y : Subtype p) : edist x y = edist (x : α) y :=
  rfl
#align subtype.edist_eq Subtype.edist_eq
-/

namespace MulOpposite

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive "Pseudoemetric space instance on the additive opposite of a pseudoemetric space."]
instance {α : Type _} [PseudoEMetricSpace α] : PseudoEMetricSpace αᵐᵒᵖ :=
  PseudoEMetricSpace.induced unop ‹_›

#print MulOpposite.edist_unop /-
@[to_additive]
theorem edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y :=
  rfl
#align mul_opposite.edist_unop MulOpposite.edist_unop
#align add_opposite.edist_unop AddOpposite.edist_unop
-/

#print MulOpposite.edist_op /-
@[to_additive]
theorem edist_op (x y : α) : edist (op x) (op y) = edist x y :=
  rfl
#align mul_opposite.edist_op MulOpposite.edist_op
#align add_opposite.edist_op AddOpposite.edist_op
-/

end MulOpposite

section ULift

instance : PseudoEMetricSpace (ULift α) :=
  PseudoEMetricSpace.induced ULift.down ‹_›

/- warning: ulift.edist_eq -> ULift.edist_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : ULift.{u2, u1} α) (y : ULift.{u2, u1} α), Eq.{1} ENNReal (EDist.edist.{max u1 u2} (ULift.{u2, u1} α) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (ULift.{u2, u1} α) (ULift.pseudoEmetricSpace.{u1, u2} α _inst_1)) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (ULift.down.{u2, u1} α x) (ULift.down.{u2, u1} α y))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] (x : ULift.{u1, u2} α) (y : ULift.{u1, u2} α), Eq.{1} ENNReal (EDist.edist.{max u2 u1} (ULift.{u1, u2} α) (PseudoEMetricSpace.toEDist.{max u2 u1} (ULift.{u1, u2} α) (instPseudoEMetricSpaceULift.{u2, u1} α _inst_1)) x y) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) (ULift.down.{u1, u2} α x) (ULift.down.{u1, u2} α y))
Case conversion may be inaccurate. Consider using '#align ulift.edist_eq ULift.edist_eqₓ'. -/
theorem ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down :=
  rfl
#align ulift.edist_eq ULift.edist_eq

/- warning: ulift.edist_up_up -> ULift.edist_up_up is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (y : α), Eq.{1} ENNReal (EDist.edist.{max u1 u2} (ULift.{u2, u1} α) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (ULift.{u2, u1} α) (ULift.pseudoEmetricSpace.{u1, u2} α _inst_1)) (ULift.up.{u2, u1} α x) (ULift.up.{u2, u1} α y)) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] (x : α) (y : α), Eq.{1} ENNReal (EDist.edist.{max u2 u1} (ULift.{u1, u2} α) (PseudoEMetricSpace.toEDist.{max u2 u1} (ULift.{u1, u2} α) (instPseudoEMetricSpaceULift.{u2, u1} α _inst_1)) (ULift.up.{u1, u2} α x) (ULift.up.{u1, u2} α y)) (EDist.edist.{u2} α (PseudoEMetricSpace.toEDist.{u2} α _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align ulift.edist_up_up ULift.edist_up_upₓ'. -/
@[simp]
theorem ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y :=
  rfl
#align ulift.edist_up_up ULift.edist_up_up

end ULift

#print Prod.pseudoEMetricSpaceMax /-
/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] : PseudoEMetricSpace (α × β)
    where
  edist x y := edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle x y z :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
  uniformity_edist := by
    refine' uniformity_prod.trans _
    simp only [PseudoEMetricSpace.uniformity_edist, comap_infi]
    rw [← infᵢ_inf_eq]; congr ; funext
    rw [← infᵢ_inf_eq]; congr ; funext
    simp [inf_principal, ext_iff, max_lt_iff]
  toUniformSpace := Prod.uniformSpace
#align prod.pseudo_emetric_space_max Prod.pseudoEMetricSpaceMax
-/

/- warning: prod.edist_eq -> Prod.edist_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] (x : Prod.{u1, u2} α β) (y : Prod.{u1, u2} α β), Eq.{1} ENNReal (EDist.edist.{max u1 u2} (Prod.{u1, u2} α β) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (Prod.{u1, u2} α β) (Prod.pseudoEMetricSpaceMax.{u1, u2} α β _inst_1 _inst_2)) x y) (LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] (x : Prod.{u1, u2} α β) (y : Prod.{u1, u2} α β), Eq.{1} ENNReal (EDist.edist.{max u1 u2} (Prod.{u1, u2} α β) (PseudoEMetricSpace.toEDist.{max u1 u2} (Prod.{u1, u2} α β) (Prod.pseudoEMetricSpaceMax.{u1, u2} α β _inst_1 _inst_2)) x y) (Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)))
Case conversion may be inaccurate. Consider using '#align prod.edist_eq Prod.edist_eqₓ'. -/
theorem Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) :
    edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl
#align prod.edist_eq Prod.edist_eq

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

#print pseudoEMetricSpacePi /-
/-- The product of a finite number of pseudoemetric spaces, with the max distance, is still
a pseudoemetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance pseudoEMetricSpacePi [∀ b, PseudoEMetricSpace (π b)] : PseudoEMetricSpace (∀ b, π b)
    where
  edist f g := Finset.sup univ fun b => edist (f b) (g b)
  edist_self f := bot_unique <| Finset.sup_le <| by simp
  edist_comm f g := by unfold edist <;> congr <;> funext a <;> exact edist_comm _ _
  edist_triangle f g h := by
    simp only [Finset.sup_le_iff]
    intro b hb
    exact le_trans (edist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist :=
    by
    simp only [Pi.uniformity, PseudoEMetricSpace.uniformity_edist, comap_infi, gt_iff_lt,
      preimage_set_of_eq, comap_principal]
    rw [infᵢ_comm]; congr ; funext ε
    rw [infᵢ_comm]; congr ; funext εpos
    change 0 < ε at εpos
    simp [Set.ext_iff, εpos]
#align pseudo_emetric_space_pi pseudoEMetricSpacePi
-/

/- warning: edist_pi_def -> edist_pi_def is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u2} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b), Eq.{1} ENNReal (EDist.edist.{max u1 u2} (forall (b : β), π b) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (forall (b : β), π b) (pseudoEMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) (Finset.sup.{0, u1} ENNReal β ENNReal.semilatticeSup ENNReal.orderBot (Finset.univ.{u1} β _inst_2) (fun (b : β) => EDist.edist.{u2} (π b) (PseudoEMetricSpace.toHasEdist.{u2} (π b) (_inst_3 b)) (f b) (g b)))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), EDist.{u1} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b), Eq.{1} ENNReal (EDist.edist.{max u2 u1} (forall (b : β), π b) (instEDistForAll.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) f g) (Finset.sup.{0, u2} ENNReal β instENNRealSemilatticeSup ENNReal.instOrderBotENNRealToLEToPreorderToPartialOrderToSemilatticeInfToLatticeInstENNRealDistribLattice (Finset.univ.{u2} β _inst_2) (fun (b : β) => EDist.edist.{u1} (π b) (_inst_3 b) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align edist_pi_def edist_pi_defₓ'. -/
theorem edist_pi_def [∀ b, PseudoEMetricSpace (π b)] (f g : ∀ b, π b) :
    edist f g = Finset.sup univ fun b => edist (f b) (g b) :=
  rfl
#align edist_pi_def edist_pi_def

/- warning: edist_le_pi_edist -> edist_le_pi_edist is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u2} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b) (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} (π b) (PseudoEMetricSpace.toHasEdist.{u2} (π b) (_inst_3 b)) (f b) (g b)) (EDist.edist.{max u1 u2} (forall (b : β), π b) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (forall (b : β), π b) (pseudoEMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), EDist.{u1} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b) (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} (π b) (_inst_3 b) (f b) (g b)) (EDist.edist.{max u2 u1} (forall (b : β), π b) (instEDistForAll.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) f g)
Case conversion may be inaccurate. Consider using '#align edist_le_pi_edist edist_le_pi_edistₓ'. -/
theorem edist_le_pi_edist [∀ b, PseudoEMetricSpace (π b)] (f g : ∀ b, π b) (b : β) :
    edist (f b) (g b) ≤ edist f g :=
  Finset.le_sup (Finset.mem_univ b)
#align edist_le_pi_edist edist_le_pi_edist

/- warning: edist_pi_le_iff -> edist_pi_le_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u2} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{max u1 u2} (forall (b : β), π b) (PseudoEMetricSpace.toHasEdist.{max u1 u2} (forall (b : β), π b) (pseudoEMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) d) (forall (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} (π b) (PseudoEMetricSpace.toHasEdist.{u2} (π b) (_inst_3 b)) (f b) (g b)) d)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), EDist.{u1} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{max u2 u1} (forall (b : β), π b) (instEDistForAll.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) f g) d) (forall (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} (π b) (_inst_3 b) (f b) (g b)) d)
Case conversion may be inaccurate. Consider using '#align edist_pi_le_iff edist_pi_le_iffₓ'. -/
theorem edist_pi_le_iff [∀ b, PseudoEMetricSpace (π b)] {f g : ∀ b, π b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by simp only [Finset.mem_univ, forall_const]
#align edist_pi_le_iff edist_pi_le_iff

/- warning: edist_pi_const_le -> edist_pi_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Fintype.{u2} β] (a : α) (b : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{max u2 u1} (β -> α) (PseudoEMetricSpace.toHasEdist.{max u2 u1} (β -> α) (pseudoEMetricSpacePi.{u2, u1} β (fun (_x : β) => α) _inst_2 (fun (b : β) => _inst_1))) (fun (_x : β) => a) (fun (_x : β) => b)) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Fintype.{u2} β] (a : α) (b : α), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{max u1 u2} (β -> α) (instEDistForAll.{u2, u1} β (fun (x._@.Mathlib.Topology.MetricSpace.EMetricSpace._hyg.5043 : β) => α) _inst_2 (fun (b : β) => PseudoEMetricSpace.toEDist.{u1} α _inst_1)) (fun (_x : β) => a) (fun (_x : β) => b)) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align edist_pi_const_le edist_pi_const_leₓ'. -/
theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) ≤ edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl
#align edist_pi_const_le edist_pi_const_le

#print edist_pi_const /-
@[simp]
theorem edist_pi_const [Nonempty β] (a b : α) : (edist (fun x : β => a) fun _ => b) = edist a b :=
  Finset.sup_const univ_nonempty (edist a b)
#align edist_pi_const edist_pi_const
-/

end Pi

namespace Emetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

#print EMetric.ball /-
/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def ball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | edist y x < ε }
#align emetric.ball EMetric.ball
-/

/- warning: emetric.mem_ball -> EMetric.mem_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y x) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y x) ε)
Case conversion may be inaccurate. Consider using '#align emetric.mem_ball EMetric.mem_ballₓ'. -/
@[simp]
theorem mem_ball : y ∈ ball x ε ↔ edist y x < ε :=
  Iff.rfl
#align emetric.mem_ball EMetric.mem_ball

/- warning: emetric.mem_ball' -> EMetric.mem_ball' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) ε)
Case conversion may be inaccurate. Consider using '#align emetric.mem_ball' EMetric.mem_ball'ₓ'. -/
theorem mem_ball' : y ∈ ball x ε ↔ edist x y < ε := by rw [edist_comm, mem_ball]
#align emetric.mem_ball' EMetric.mem_ball'

#print EMetric.closedBall /-
/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }
#align emetric.closed_ball EMetric.closedBall
-/

/- warning: emetric.mem_closed_ball -> EMetric.mem_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (EMetric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y x) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (EMetric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y x) ε)
Case conversion may be inaccurate. Consider using '#align emetric.mem_closed_ball EMetric.mem_closedBallₓ'. -/
@[simp]
theorem mem_closedBall : y ∈ closedBall x ε ↔ edist y x ≤ ε :=
  Iff.rfl
#align emetric.mem_closed_ball EMetric.mem_closedBall

/- warning: emetric.mem_closed_ball' -> EMetric.mem_closedBall' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (EMetric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (EMetric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) ε)
Case conversion may be inaccurate. Consider using '#align emetric.mem_closed_ball' EMetric.mem_closedBall'ₓ'. -/
theorem mem_closedBall' : y ∈ closedBall x ε ↔ edist x y ≤ ε := by rw [edist_comm, mem_closed_ball]
#align emetric.mem_closed_ball' EMetric.mem_closedBall'

/- warning: emetric.closed_ball_top -> EMetric.closedBall_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align emetric.closed_ball_top EMetric.closedBall_topₓ'. -/
@[simp]
theorem closedBall_top (x : α) : closedBall x ∞ = univ :=
  eq_univ_of_forall fun y => le_top
#align emetric.closed_ball_top EMetric.closedBall_top

#print EMetric.ball_subset_closedBall /-
theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun y hy => le_of_lt hy
#align emetric.ball_subset_closed_ball EMetric.ball_subset_closedBall
-/

/- warning: emetric.pos_of_mem_ball -> EMetric.pos_of_mem_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε)
Case conversion may be inaccurate. Consider using '#align emetric.pos_of_mem_ball EMetric.pos_of_mem_ballₓ'. -/
theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  lt_of_le_of_lt (zero_le _) hy
#align emetric.pos_of_mem_ball EMetric.pos_of_mem_ball

/- warning: emetric.mem_ball_self -> EMetric.mem_ball_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (EMetric.ball.{u1} α _inst_1 x ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (EMetric.ball.{u1} α _inst_1 x ε))
Case conversion may be inaccurate. Consider using '#align emetric.mem_ball_self EMetric.mem_ball_selfₓ'. -/
theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
  show edist x x < ε by rw [edist_self] <;> assumption
#align emetric.mem_ball_self EMetric.mem_ball_self

#print EMetric.mem_closedBall_self /-
theorem mem_closedBall_self : x ∈ closedBall x ε :=
  show edist x x ≤ ε by rw [edist_self] <;> exact bot_le
#align emetric.mem_closed_ball_self EMetric.mem_closedBall_self
-/

#print EMetric.mem_ball_comm /-
theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]
#align emetric.mem_ball_comm EMetric.mem_ball_comm
-/

#print EMetric.mem_closedBall_comm /-
theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closed_ball', mem_closed_ball]
#align emetric.mem_closed_ball_comm EMetric.mem_closedBall_comm
-/

/- warning: emetric.ball_subset_ball -> EMetric.ball_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε₁) (EMetric.ball.{u1} α _inst_1 x ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε₁) (EMetric.ball.{u1} α _inst_1 x ε₂))
Case conversion may be inaccurate. Consider using '#align emetric.ball_subset_ball EMetric.ball_subset_ballₓ'. -/
theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h
#align emetric.ball_subset_ball EMetric.ball_subset_ball

/- warning: emetric.closed_ball_subset_closed_ball -> EMetric.closedBall_subset_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x ε₁) (EMetric.closedBall.{u1} α _inst_1 x ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x ε₁) (EMetric.closedBall.{u1} α _inst_1 x ε₂))
Case conversion may be inaccurate. Consider using '#align emetric.closed_ball_subset_closed_ball EMetric.closedBall_subset_closedBallₓ'. -/
theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun y (yx : _ ≤ ε₁) => le_trans yx h
#align emetric.closed_ball_subset_closed_ball EMetric.closedBall_subset_closedBall

/- warning: emetric.ball_disjoint -> EMetric.ball_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ε₁ ε₂) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (EMetric.ball.{u1} α _inst_1 x ε₁) (EMetric.ball.{u1} α _inst_1 y ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) ε₁ ε₂) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (EMetric.ball.{u1} α _inst_1 x ε₁) (EMetric.ball.{u1} α _inst_1 y ε₂))
Case conversion may be inaccurate. Consider using '#align emetric.ball_disjoint EMetric.ball_disjointₓ'. -/
theorem ball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : Disjoint (ball x ε₁) (ball y ε₂) :=
  Set.disjoint_left.mpr fun z h₁ h₂ =>
    (edist_triangle_left x y z).not_lt <| (ENNReal.add_lt_add h₁ h₂).trans_le h
#align emetric.ball_disjoint EMetric.ball_disjoint

/- warning: emetric.ball_subset -> EMetric.ball_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) ε₁) ε₂) -> (Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε₁) (EMetric.ball.{u1} α _inst_1 y ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : ENNReal} {ε₂ : ENNReal}, (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) ε₁) ε₂) -> (Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε₁) (EMetric.ball.{u1} α _inst_1 y ε₂))
Case conversion may be inaccurate. Consider using '#align emetric.ball_subset EMetric.ball_subsetₓ'. -/
theorem ball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y ≠ ∞) : ball x ε₁ ⊆ ball y ε₂ :=
  fun z zx =>
  calc
    edist z y ≤ edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := (add_comm _ _)
    _ < edist x y + ε₁ := (ENNReal.add_lt_add_left h' zx)
    _ ≤ ε₂ := h
    
#align emetric.ball_subset EMetric.ball_subset

/- warning: emetric.exists_ball_subset_ball -> EMetric.exists_ball_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) -> (Exists.{1} ENNReal (fun (ε' : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε' (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε' (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.ball.{u1} α _inst_1 y ε') (EMetric.ball.{u1} α _inst_1 x ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {ε : ENNReal}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (EMetric.ball.{u1} α _inst_1 x ε)) -> (Exists.{1} ENNReal (fun (ε' : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε' (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.ball.{u1} α _inst_1 y ε') (EMetric.ball.{u1} α _inst_1 x ε))))
Case conversion may be inaccurate. Consider using '#align emetric.exists_ball_subset_ball EMetric.exists_ball_subset_ballₓ'. -/
theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
  by
  have : 0 < ε - edist y x := by simpa using h
  refine' ⟨ε - edist y x, this, ball_subset _ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_ball.mp h).le).le
#align emetric.exists_ball_subset_ball EMetric.exists_ball_subset_ball

/- warning: emetric.ball_eq_empty_iff -> EMetric.ball_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε : ENNReal}, Iff (Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {ε : ENNReal}, Iff (Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{1} ENNReal ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align emetric.ball_eq_empty_iff EMetric.ball_eq_empty_iffₓ'. -/
theorem ball_eq_empty_iff : ball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_not_mem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_ball_self ε0)), fun ε0 y h =>
      not_lt_of_le (le_of_eq ε0) (pos_of_mem_ball h)⟩
#align emetric.ball_eq_empty_iff EMetric.ball_eq_empty_iff

/- warning: emetric.ord_connected_set_of_closed_ball_subset -> EMetric.ordConnected_setOf_closedBall_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (s : Set.{u1} α), Set.OrdConnected.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (setOf.{0} ENNReal (fun (r : ENNReal) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x r) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (s : Set.{u1} α), Set.OrdConnected.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (setOf.{0} ENNReal (fun (r : ENNReal) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x r) s))
Case conversion may be inaccurate. Consider using '#align emetric.ord_connected_set_of_closed_ball_subset EMetric.ordConnected_setOf_closedBall_subsetₓ'. -/
theorem ordConnected_setOf_closedBall_subset (x : α) (s : Set α) :
    OrdConnected { r | closedBall x r ⊆ s } :=
  ⟨fun r₁ hr₁ r₂ hr₂ r hr => (closedBall_subset_closedBall hr.2).trans hr₂⟩
#align emetric.ord_connected_set_of_closed_ball_subset EMetric.ordConnected_setOf_closedBall_subset

/- warning: emetric.ord_connected_set_of_ball_subset -> EMetric.ordConnected_setOf_ball_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (s : Set.{u1} α), Set.OrdConnected.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (setOf.{0} ENNReal (fun (r : ENNReal) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.ball.{u1} α _inst_1 x r) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) (s : Set.{u1} α), Set.OrdConnected.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (setOf.{0} ENNReal (fun (r : ENNReal) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x r) s))
Case conversion may be inaccurate. Consider using '#align emetric.ord_connected_set_of_ball_subset EMetric.ordConnected_setOf_ball_subsetₓ'. -/
theorem ordConnected_setOf_ball_subset (x : α) (s : Set α) : OrdConnected { r | ball x r ⊆ s } :=
  ⟨fun r₁ hr₁ r₂ hr₂ r hr => (ball_subset_ball hr.2).trans hr₂⟩
#align emetric.ord_connected_set_of_ball_subset EMetric.ordConnected_setOf_ball_subset

#print EMetric.edistLtTopSetoid /-
/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
def edistLtTopSetoid : Setoid α where
  R x y := edist x y < ⊤
  iseqv :=
    ⟨fun x => by
      rw [edist_self]
      exact ENNReal.coe_lt_top, fun x y h => by rwa [edist_comm], fun x y z hxy hyz =>
      lt_of_le_of_lt (edist_triangle x y z) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩)⟩
#align emetric.edist_lt_top_setoid EMetric.edistLtTopSetoid
-/

/- warning: emetric.ball_zero -> EMetric.ball_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α _inst_1 x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α _inst_1 x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align emetric.ball_zero EMetric.ball_zeroₓ'. -/
@[simp]
theorem ball_zero : ball x 0 = ∅ := by rw [EMetric.ball_eq_empty_iff]
#align emetric.ball_zero EMetric.ball_zero

/- warning: emetric.nhds_basis_eball -> EMetric.nhds_basis_eball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α ENNReal (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (EMetric.ball.{u1} α _inst_1 x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α ENNReal (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (EMetric.ball.{u1} α _inst_1 x)
Case conversion may be inaccurate. Consider using '#align emetric.nhds_basis_eball EMetric.nhds_basis_eballₓ'. -/
theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_edist
#align emetric.nhds_basis_eball EMetric.nhds_basis_eball

/- warning: emetric.nhds_within_basis_eball -> EMetric.nhdsWithin_basis_eball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Filter.HasBasis.{u1, 1} α ENNReal (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x s) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (fun (ε : ENNReal) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Filter.HasBasis.{u1, 1} α ENNReal (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x s) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (fun (ε : ENNReal) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) s)
Case conversion may be inaccurate. Consider using '#align emetric.nhds_within_basis_eball EMetric.nhdsWithin_basis_eballₓ'. -/
theorem nhdsWithin_basis_eball : (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => ball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_eball s
#align emetric.nhds_within_basis_eball EMetric.nhdsWithin_basis_eball

/- warning: emetric.nhds_basis_closed_eball -> EMetric.nhds_basis_closed_eball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α ENNReal (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (EMetric.closedBall.{u1} α _inst_1 x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α ENNReal (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (EMetric.closedBall.{u1} α _inst_1 x)
Case conversion may be inaccurate. Consider using '#align emetric.nhds_basis_closed_eball EMetric.nhds_basis_closed_eballₓ'. -/
theorem nhds_basis_closed_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (closedBall x) :=
  nhds_basis_uniformity uniformity_basis_edist_le
#align emetric.nhds_basis_closed_eball EMetric.nhds_basis_closed_eball

/- warning: emetric.nhds_within_basis_closed_eball -> EMetric.nhdsWithin_basis_closed_eball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Filter.HasBasis.{u1, 1} α ENNReal (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x s) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (fun (ε : ENNReal) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x ε) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Filter.HasBasis.{u1, 1} α ENNReal (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x s) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (fun (ε : ENNReal) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x ε) s)
Case conversion may be inaccurate. Consider using '#align emetric.nhds_within_basis_closed_eball EMetric.nhdsWithin_basis_closed_eballₓ'. -/
theorem nhdsWithin_basis_closed_eball :
    (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => closedBall x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_closed_eball s
#align emetric.nhds_within_basis_closed_eball EMetric.nhdsWithin_basis_closed_eball

/- warning: emetric.nhds_eq -> EMetric.nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (infᵢ.{u1, 1} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) ENNReal (fun (ε : ENNReal) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => Filter.principal.{u1} α (EMetric.ball.{u1} α _inst_1 x ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (infᵢ.{u1, 1} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) ENNReal (fun (ε : ENNReal) => infᵢ.{u1, 0} (Filter.{u1} α) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) => Filter.principal.{u1} α (EMetric.ball.{u1} α _inst_1 x ε))))
Case conversion may be inaccurate. Consider using '#align emetric.nhds_eq EMetric.nhds_eqₓ'. -/
theorem nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (ball x ε) :=
  nhds_basis_eball.eq_binfᵢ
#align emetric.nhds_eq EMetric.nhds_eq

/- warning: emetric.mem_nhds_iff -> EMetric.mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) s)))
Case conversion may be inaccurate. Consider using '#align emetric.mem_nhds_iff EMetric.mem_nhds_iffₓ'. -/
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, ball x ε ⊆ s :=
  nhds_basis_eball.mem_iff
#align emetric.mem_nhds_iff EMetric.mem_nhds_iff

/- warning: emetric.mem_nhds_within_iff -> EMetric.mem_nhdsWithin_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x t)) (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) t) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x t)) (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) t) s)))
Case conversion may be inaccurate. Consider using '#align emetric.mem_nhds_within_iff EMetric.mem_nhdsWithin_iffₓ'. -/
theorem mem_nhdsWithin_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_eball.mem_iff
#align emetric.mem_nhds_within_iff EMetric.mem_nhdsWithin_iff

section

variable [PseudoEMetricSpace β] {f : α → β}

/- warning: emetric.tendsto_nhds_within_nhds_within -> EMetric.tendsto_nhdsWithin_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {t : Set.{u2} β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhdsWithin.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2)) b t)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x a) δ) -> (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f x) b) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {t : Set.{u2} β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhdsWithin.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2)) b t)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x a) δ) -> (And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (f x) t) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f x) b) ε))))))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_nhds_within_nhds_within EMetric.tendsto_nhdsWithin_nhdsWithinₓ'. -/
theorem tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
  (nhdsWithin_basis_eball.tendsto_iffₓ nhdsWithin_basis_eball).trans <|
    forall₂_congr fun ε hε => exists₂_congr fun δ hδ => forall_congr' fun x => by simp <;> itauto
#align emetric.tendsto_nhds_within_nhds_within EMetric.tendsto_nhdsWithin_nhdsWithin

/- warning: emetric.tendsto_nhds_within_nhds -> EMetric.tendsto_nhdsWithin_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f x) b) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f x) b) ε)))))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_nhds_within_nhds EMetric.tendsto_nhdsWithin_nhdsₓ'. -/
theorem tendsto_nhdsWithin_nhds {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → edist x a < δ → edist (f x) b < ε :=
  by
  rw [← nhdsWithin_univ b, tendsto_nhds_within_nhds_within]
  simp only [mem_univ, true_and_iff]
#align emetric.tendsto_nhds_within_nhds EMetric.tendsto_nhdsWithin_nhds

/- warning: emetric.tendsto_nhds_nhds -> EMetric.tendsto_nhds_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {{x : α}}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toHasEdist.{u2} β _inst_2) (f x) b) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : PseudoEMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoEMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {{x : α}}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} β (PseudoEMetricSpace.toEDist.{u2} β _inst_2) (f x) b) ε)))))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_nhds_nhds EMetric.tendsto_nhds_nhdsₓ'. -/
theorem tendsto_nhds_nhds {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
  nhds_basis_eball.tendsto_iffₓ nhds_basis_eball
#align emetric.tendsto_nhds_nhds EMetric.tendsto_nhds_nhds

end

/- warning: emetric.is_open_iff -> EMetric.isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) s))))
Case conversion may be inaccurate. Consider using '#align emetric.is_open_iff EMetric.isOpen_iffₓ'. -/
theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp [isOpen_iff_nhds, mem_nhds_iff]
#align emetric.is_open_iff EMetric.isOpen_iff

#print EMetric.isOpen_ball /-
theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun y => exists_ball_subset_ball
#align emetric.is_open_ball EMetric.isOpen_ball
-/

/- warning: emetric.is_closed_ball_top -> EMetric.isClosed_ball_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (EMetric.ball.{u1} α _inst_1 x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) (EMetric.ball.{u1} α _inst_1 x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align emetric.is_closed_ball_top EMetric.isClosed_ball_topₓ'. -/
theorem isClosed_ball_top : IsClosed (ball x ⊤) :=
  isOpen_compl_iff.1 <|
    isOpen_iff.2 fun y hy =>
      ⟨⊤, ENNReal.coe_lt_top,
        (ball_disjoint <| by
            rw [top_add]
            exact le_of_not_lt hy).subset_compl_right⟩
#align emetric.is_closed_ball_top EMetric.isClosed_ball_top

/- warning: emetric.ball_mem_nhds -> EMetric.ball_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (EMetric.ball.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align emetric.ball_mem_nhds EMetric.ball_mem_nhdsₓ'. -/
theorem ball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  isOpen_ball.mem_nhds (mem_ball_self ε0)
#align emetric.ball_mem_nhds EMetric.ball_mem_nhds

/- warning: emetric.closed_ball_mem_nhds -> EMetric.closedBall_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (x : α) {ε : ENNReal}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (EMetric.closedBall.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align emetric.closed_ball_mem_nhds EMetric.closedBall_mem_nhdsₓ'. -/
theorem closedBall_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : closedBall x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall
#align emetric.closed_ball_mem_nhds EMetric.closedBall_mem_nhds

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print EMetric.ball_prod_same /-
theorem ball_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => max_lt_iff.symm
#align emetric.ball_prod_same EMetric.ball_prod_same
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print EMetric.closedBall_prod_same /-
theorem closedBall_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r :=
  ext fun z => max_le_iff.symm
#align emetric.closed_ball_prod_same EMetric.closedBall_prod_same
-/

/- warning: emetric.mem_closure_iff -> EMetric.mem_closure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) ε))))
Case conversion may be inaccurate. Consider using '#align emetric.mem_closure_iff EMetric.mem_closure_iffₓ'. -/
/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, edist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans <| by simp only [mem_ball, edist_comm x]
#align emetric.mem_closure_iff EMetric.mem_closure_iff

/- warning: emetric.tendsto_nhds -> EMetric.tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Filter.{u2} β} {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (u x) a) ε) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {f : Filter.{u2} β} {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (u x) a) ε) f))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_nhds EMetric.tendsto_nhdsₓ'. -/
theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff
#align emetric.tendsto_nhds EMetric.tendsto_nhds

/- warning: emetric.tendsto_at_top -> EMetric.tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (u n) a) ε))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (u n) a) ε))))
Case conversion may be inaccurate. Consider using '#align emetric.tendsto_at_top EMetric.tendsto_atTopₓ'. -/
theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, edist (u n) a < ε :=
  (atTop_basis.tendsto_iffₓ nhds_basis_eball).trans <| by
    simp only [exists_prop, true_and_iff, mem_Ici, mem_ball]
#align emetric.tendsto_at_top EMetric.tendsto_atTop

/- warning: emetric.inseparable_iff -> EMetric.inseparable_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α}, Iff (Inseparable.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x y) (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α}, Iff (Inseparable.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) x y) (Eq.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align emetric.inseparable_iff EMetric.inseparable_iffₓ'. -/
theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_lt_iff_le']
#align emetric.inseparable_iff EMetric.inseparable_iff

/- warning: emetric.cauchy_seq_iff -> EMetric.cauchySeq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (m : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) m N) -> (forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (u m) (u n)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u2} β (fun (N : β) => forall (m : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N m) -> (forall (n : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (u m) (u n)) ε)))))
Case conversion may be inaccurate. Consider using '#align emetric.cauchy_seq_iff EMetric.cauchySeq_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (m n «expr ≥ » N) -/
-- see Note [nolint_ge]
/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
@[nolint ge_or_gt]
theorem cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ (m) (_ : m ≥ N) (n) (_ : n ≥ N), edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchySeq_iff
#align emetric.cauchy_seq_iff EMetric.cauchySeq_iff

/- warning: emetric.cauchy_seq_iff' -> EMetric.cauchySeq_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (u n) (u N)) ε))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (u n) (u N)) ε))))
Case conversion may be inaccurate. Consider using '#align emetric.cauchy_seq_iff' EMetric.cauchySeq_iff'ₓ'. -/
/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ n ≥ N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchySeq_iff'
#align emetric.cauchy_seq_iff' EMetric.cauchySeq_iff'

/- warning: emetric.cauchy_seq_iff_nnreal -> EMetric.cauchySeq_iff_NNReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) ε) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (u n) (u N)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) ε) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (u n) (u N)) (ENNReal.some ε)))))
Case conversion may be inaccurate. Consider using '#align emetric.cauchy_seq_iff_nnreal EMetric.cauchySeq_iff_NNRealₓ'. -/
/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchySeq_iff_NNReal [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchySeq_iff'
#align emetric.cauchy_seq_iff_nnreal EMetric.cauchySeq_iff_NNReal

/- warning: emetric.totally_bounded_iff -> EMetric.totallyBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => EMetric.ball.{u1} α _inst_1 y ε)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => EMetric.ball.{u1} α _inst_1 y ε)))))))
Case conversion may be inaccurate. Consider using '#align emetric.totally_bounded_iff EMetric.totallyBounded_iffₓ'. -/
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H ε ε0 => H _ (edist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| unionᵢ₂_mono fun y yt z => hε⟩⟩
#align emetric.totally_bounded_iff EMetric.totallyBounded_iff

/- warning: emetric.totally_bounded_iff' -> EMetric.totallyBounded_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => EMetric.ball.{u1} α _inst_1 y ε))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1) s) (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (h._@.Mathlib.Topology.MetricSpace.EMetricSpace._hyg.9103 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => EMetric.ball.{u1} α _inst_1 y ε))))))))
Case conversion may be inaccurate. Consider using '#align emetric.totally_bounded_iff' EMetric.totallyBounded_iff'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem totallyBounded_iff' {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| unionᵢ₂_mono fun y yt z => hε⟩⟩
#align emetric.totally_bounded_iff' EMetric.totallyBounded_iff'

section Compact

/- warning: emetric.subset_countable_closure_of_almost_dense_set -> EMetric.subset_countable_closure_of_almost_dense_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (s : Set.{u1} α), (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => EMetric.closedBall.{u1} α _inst_1 x ε))))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] (s : Set.{u1} α), (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) => EMetric.closedBall.{u1} α _inst_1 x ε))))))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t)))))
Case conversion may be inaccurate. Consider using '#align emetric.subset_countable_closure_of_almost_dense_set EMetric.subset_countable_closure_of_almost_dense_setₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, closedBall x ε) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ closure t :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨x₀, hx₀⟩)
  · exact ⟨∅, empty_subset _, countable_empty, empty_subset _⟩
  choose! T hTc hsT using fun n : ℕ => hs n⁻¹ (by simp)
  have : ∀ r x, ∃ y ∈ s, closed_ball x r ∩ s ⊆ closed_ball y (r * 2) :=
    by
    intro r x
    rcases(closed_ball x r ∩ s).eq_empty_or_nonempty with (he | ⟨y, hxy, hys⟩)
    · refine' ⟨x₀, hx₀, _⟩
      rw [he]
      exact empty_subset _
    · refine' ⟨y, hys, fun z hz => _⟩
      calc
        edist z y ≤ edist z x + edist y x := edist_triangle_right _ _ _
        _ ≤ r + r := (add_le_add hz.1 hxy)
        _ = r * 2 := (mul_two r).symm
        
  choose f hfs hf
  refine'
    ⟨⋃ n : ℕ, f n⁻¹ '' T n, Union_subset fun n => image_subset_iff.2 fun z hz => hfs _ _,
      countable_Union fun n => (hTc n).image _, _⟩
  refine' fun x hx => mem_closure_iff.2 fun ε ε0 => _
  rcases ENNReal.exists_inv_nat_lt (ENNReal.half_pos ε0.lt.ne').ne' with ⟨n, hn⟩
  rcases mem_Union₂.1 (hsT n hx) with ⟨y, hyn, hyx⟩
  refine' ⟨f n⁻¹ y, mem_Union.2 ⟨n, mem_image_of_mem _ hyn⟩, _⟩
  calc
    edist x (f n⁻¹ y) ≤ n⁻¹ * 2 := hf _ _ ⟨hyx, hx⟩
    _ < ε := ENNReal.mul_lt_of_lt_div hn
    
#align emetric.subset_countable_closure_of_almost_dense_set EMetric.subset_countable_closure_of_almost_dense_set

/- warning: emetric.subset_countable_closure_of_compact -> EMetric.subset_countable_closure_of_compact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Countable.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) t)))))
Case conversion may be inaccurate. Consider using '#align emetric.subset_countable_closure_of_compact EMetric.subset_countable_closure_of_compactₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set.  -/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s ⊆ closure t :=
  by
  refine' subset_countable_closure_of_almost_dense_set s fun ε hε => _
  rcases totally_bounded_iff'.1 hs.totally_bounded ε hε with ⟨t, hts, htf, hst⟩
  exact ⟨t, htf.countable, subset.trans hst <| Union₂_mono fun _ _ => ball_subset_closed_ball⟩
#align emetric.subset_countable_closure_of_compact EMetric.subset_countable_closure_of_compact

end Compact

section SecondCountable

open _Root_.TopologicalSpace

variable (α)

#print EMetric.secondCountable_of_sigmaCompact /-
/-- A sigma compact pseudo emetric space has second countable topology. This is not an instance
to avoid a loop with `sigma_compact_space_of_locally_compact_second_countable`.  -/
theorem secondCountable_of_sigmaCompact [SigmaCompactSpace α] : SecondCountableTopology α :=
  by
  suffices separable_space α by exact UniformSpace.secondCountable_of_separable α
  choose T hTsub hTc hsubT using fun n =>
    subset_countable_closure_of_compact (isCompact_compactCovering α n)
  refine' ⟨⟨⋃ n, T n, countable_Union hTc, fun x => _⟩⟩
  rcases Union_eq_univ_iff.1 (unionᵢ_compactCovering α) x with ⟨n, hn⟩
  exact closure_mono (subset_Union _ n) (hsubT _ hn)
#align emetric.second_countable_of_sigma_compact EMetric.secondCountable_of_sigmaCompact
-/

variable {α}

/- warning: emetric.second_countable_of_almost_dense_set -> EMetric.secondCountable_of_almost_dense_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Countable.{u1} α t) (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => EMetric.closedBall.{u1} α _inst_1 x ε))) (Set.univ.{u1} α))))) -> (TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Countable.{u1} α t) (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) => EMetric.closedBall.{u1} α _inst_1 x ε))) (Set.univ.{u1} α))))) -> (TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align emetric.second_countable_of_almost_dense_set EMetric.secondCountable_of_almost_dense_setₓ'. -/
theorem secondCountable_of_almost_dense_set
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ (⋃ x ∈ t, closedBall x ε) = univ) :
    SecondCountableTopology α :=
  by
  suffices separable_space α by exact UniformSpace.secondCountable_of_separable α
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) fun ε ε0 => _ with
    ⟨t, -, htc, ht⟩
  · exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩
  · rcases hs ε ε0 with ⟨t, htc, ht⟩
    exact ⟨t, htc, univ_subset_iff.2 ht⟩
#align emetric.second_countable_of_almost_dense_set EMetric.secondCountable_of_almost_dense_set

end SecondCountable

section Diam

#print EMetric.diam /-
/-- The diameter of a set in a pseudoemetric space, named `emetric.diam` -/
noncomputable def diam (s : Set α) :=
  ⨆ (x ∈ s) (y ∈ s), edist x y
#align emetric.diam EMetric.diam
-/

/- warning: emetric.diam_le_iff -> EMetric.diam_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 s) d) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {d : ENNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 s) d) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) d)))
Case conversion may be inaccurate. Consider using '#align emetric.diam_le_iff EMetric.diam_le_iffₓ'. -/
theorem diam_le_iff {d : ℝ≥0∞} : diam s ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d := by
  simp only [diam, supᵢ_le_iff]
#align emetric.diam_le_iff EMetric.diam_le_iff

/- warning: emetric.diam_image_le_iff -> EMetric.diam_image_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {d : ENNReal} {f : β -> α} {s : Set.{u2} β}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (Set.image.{u2, u1} β α f s)) d) (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) (f x) (f y)) d)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u1} α] {d : ENNReal} {f : β -> α} {s : Set.{u2} β}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (Set.image.{u2, u1} β α f s)) d) (forall (x : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x s) -> (forall (y : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) (f x) (f y)) d)))
Case conversion may be inaccurate. Consider using '#align emetric.diam_image_le_iff EMetric.diam_image_le_iffₓ'. -/
theorem diam_image_le_iff {d : ℝ≥0∞} {f : β → α} {s : Set β} :
    diam (f '' s) ≤ d ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ d := by
  simp only [diam_le_iff, ball_image_iff]
#align emetric.diam_image_le_iff EMetric.diam_image_le_iff

/- warning: emetric.edist_le_of_diam_le -> EMetric.edist_le_of_diam_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α} {d : ENNReal}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 s) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) d)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α} {d : ENNReal}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 s) d) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) d)
Case conversion may be inaccurate. Consider using '#align emetric.edist_le_of_diam_le EMetric.edist_le_of_diam_leₓ'. -/
theorem edist_le_of_diam_le {d} (hx : x ∈ s) (hy : y ∈ s) (hd : diam s ≤ d) : edist x y ≤ d :=
  diam_le_iff.1 hd x hx y hy
#align emetric.edist_le_of_diam_le EMetric.edist_le_of_diam_le

/- warning: emetric.edist_le_diam_of_mem -> EMetric.edist_le_diam_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (EMetric.diam.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (EMetric.diam.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align emetric.edist_le_diam_of_mem EMetric.edist_le_diam_of_memₓ'. -/
/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
theorem edist_le_diam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ diam s :=
  edist_le_of_diam_le hx hy le_rfl
#align emetric.edist_le_diam_of_mem EMetric.edist_le_diam_of_mem

/- warning: emetric.diam_le -> EMetric.diam_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {d : ENNReal}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) d))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 s) d)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {d : ENNReal}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) d))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 s) d)
Case conversion may be inaccurate. Consider using '#align emetric.diam_le EMetric.diam_leₓ'. -/
/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
theorem diam_le {d : ℝ≥0∞} (h : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ d) : diam s ≤ d :=
  diam_le_iff.2 h
#align emetric.diam_le EMetric.diam_le

/- warning: emetric.diam_subsingleton -> EMetric.diam_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align emetric.diam_subsingleton EMetric.diam_subsingletonₓ'. -/
/-- The diameter of a subsingleton vanishes. -/
theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 :=
  nonpos_iff_eq_zero.1 <| diam_le fun x hx y hy => (hs hx hy).symm ▸ edist_self y ▸ le_rfl
#align emetric.diam_subsingleton EMetric.diam_subsingleton

/- warning: emetric.diam_empty -> EMetric.diam_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α], Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align emetric.diam_empty EMetric.diam_emptyₓ'. -/
/-- The diameter of the empty set vanishes -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty
#align emetric.diam_empty EMetric.diam_empty

/- warning: emetric.diam_singleton -> EMetric.diam_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α}, Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align emetric.diam_singleton EMetric.diam_singletonₓ'. -/
/-- The diameter of a singleton vanishes -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton
#align emetric.diam_singleton EMetric.diam_singleton

/- warning: emetric.diam_Union_mem_option -> EMetric.diam_unionᵢ_mem_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {ι : Type.{u2}} (o : Option.{u2} ι) (s : ι -> (Set.{u1} α)), Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) (fun (H : Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) => s i)))) (supᵢ.{0, succ u2} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) ι (fun (i : ι) => supᵢ.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) (fun (H : Membership.Mem.{u2, u2} ι (Option.{u2} ι) (Option.hasMem.{u2} ι) i o) => EMetric.diam.{u1} α _inst_1 (s i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoEMetricSpace.{u2} α] {ι : Type.{u1}} (o : Option.{u1} ι) (s : ι -> (Set.{u2} α)), Eq.{1} ENNReal (EMetric.diam.{u2} α _inst_1 (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Option.{u1} ι) (Option.instMembershipOption.{u1} ι) i o) (fun (H : Membership.mem.{u1, u1} ι (Option.{u1} ι) (Option.instMembershipOption.{u1} ι) i o) => s i)))) (supᵢ.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ι (fun (i : ι) => supᵢ.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} ι (Option.{u1} ι) (Option.instMembershipOption.{u1} ι) i o) (fun (H : Membership.mem.{u1, u1} ι (Option.{u1} ι) (Option.instMembershipOption.{u1} ι) i o) => EMetric.diam.{u2} α _inst_1 (s i))))
Case conversion may be inaccurate. Consider using '#align emetric.diam_Union_mem_option EMetric.diam_unionᵢ_mem_optionₓ'. -/
theorem diam_unionᵢ_mem_option {ι : Type _} (o : Option ι) (s : ι → Set α) :
    diam (⋃ i ∈ o, s i) = ⨆ i ∈ o, diam (s i) := by cases o <;> simp
#align emetric.diam_Union_mem_option EMetric.diam_unionᵢ_mem_option

/- warning: emetric.diam_insert -> EMetric.diam_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) (LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) (supᵢ.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) α (fun (y : α) => supᵢ.{0, 0} ENNReal (ConditionallyCompleteLattice.toHasSup.{0} ENNReal (CompleteLattice.toConditionallyCompleteLattice.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y))) (EMetric.diam.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s)) (Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (supᵢ.{0, succ u1} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) α (fun (y : α) => supᵢ.{0, 0} ENNReal (ConditionallyCompleteLattice.toSupSet.{0} ENNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y))) (EMetric.diam.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align emetric.diam_insert EMetric.diam_insertₓ'. -/
theorem diam_insert : diam (insert x s) = max (⨆ y ∈ s, edist x y) (diam s) :=
  eq_of_forall_ge_iff fun d => by
    simp only [diam_le_iff, ball_insert_iff, edist_self, edist_comm x, max_le_iff, supᵢ_le_iff,
      zero_le, true_and_iff, forall_and, and_self_iff, ← and_assoc']
#align emetric.diam_insert EMetric.diam_insert

#print EMetric.diam_pair /-
theorem diam_pair : diam ({x, y} : Set α) = edist x y := by
  simp only [supᵢ_singleton, diam_insert, diam_singleton, ENNReal.max_zero_right]
#align emetric.diam_pair EMetric.diam_pair
-/

/- warning: emetric.diam_triple -> EMetric.diam_triple is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) z)))) (LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) (LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x z)) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {z : α}, Eq.{1} ENNReal (EMetric.diam.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) z)))) (Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x z)) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align emetric.diam_triple EMetric.diam_tripleₓ'. -/
theorem diam_triple : diam ({x, y, z} : Set α) = max (max (edist x y) (edist x z)) (edist y z) := by
  simp only [diam_insert, supᵢ_insert, supᵢ_singleton, diam_singleton, ENNReal.max_zero_right,
    ENNReal.sup_eq_max]
#align emetric.diam_triple EMetric.diam_triple

/- warning: emetric.diam_mono -> EMetric.diam_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 s) (EMetric.diam.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 s) (EMetric.diam.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align emetric.diam_mono EMetric.diam_monoₓ'. -/
/-- The diameter is monotonous with respect to inclusion -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) : diam s ≤ diam t :=
  diam_le fun x hx y hy => edist_le_diam_of_mem (h hx) (h hy)
#align emetric.diam_mono EMetric.diam_mono

/- warning: emetric.diam_union -> EMetric.diam_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.diam.{u1} α _inst_1 s) (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α _inst_1) x y)) (EMetric.diam.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {y : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.diam.{u1} α _inst_1 s) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α _inst_1) x y)) (EMetric.diam.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align emetric.diam_union EMetric.diam_unionₓ'. -/
/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
theorem diam_union {t : Set α} (xs : x ∈ s) (yt : y ∈ t) :
    diam (s ∪ t) ≤ diam s + edist x y + diam t :=
  by
  have A : ∀ a ∈ s, ∀ b ∈ t, edist a b ≤ diam s + edist x y + diam t := fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist x y + edist y b := edist_triangle4 _ _ _ _
      _ ≤ diam s + edist x y + diam t :=
        add_le_add (add_le_add (edist_le_diam_of_mem ha xs) le_rfl) (edist_le_diam_of_mem yt hb)
      
  refine' diam_le fun a ha b hb => _
  cases' (mem_union _ _ _).1 ha with h'a h'a <;> cases' (mem_union _ _ _).1 hb with h'b h'b
  ·
    calc
      edist a b ≤ diam s := edist_le_diam_of_mem h'a h'b
      _ ≤ diam s + (edist x y + diam t) := le_self_add
      _ = diam s + edist x y + diam t := (add_assoc _ _ _).symm
      
  · exact A a h'a b h'b
  · have Z := A b h'b a h'a
    rwa [edist_comm] at Z
  ·
    calc
      edist a b ≤ diam t := edist_le_diam_of_mem h'a h'b
      _ ≤ diam s + edist x y + diam t := le_add_self
      
#align emetric.diam_union EMetric.diam_union

/- warning: emetric.diam_union' -> EMetric.diam_union' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EMetric.diam.{u1} α _inst_1 s) (EMetric.diam.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (EMetric.diam.{u1} α _inst_1 s) (EMetric.diam.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align emetric.diam_union' EMetric.diam_union'ₓ'. -/
theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s + diam t :=
  by
  let ⟨x, ⟨xs, xt⟩⟩ := h
  simpa using diam_union xs xt
#align emetric.diam_union' EMetric.diam_union'

/- warning: emetric.diam_closed_ball -> EMetric.diam_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {r : ENNReal}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (EMetric.closedBall.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {r : ENNReal}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (EMetric.closedBall.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) r)
Case conversion may be inaccurate. Consider using '#align emetric.diam_closed_ball EMetric.diam_closedBallₓ'. -/
theorem diam_closedBall {r : ℝ≥0∞} : diam (closedBall x r) ≤ 2 * r :=
  diam_le fun a ha b hb =>
    calc
      edist a b ≤ edist a x + edist b x := edist_triangle_right _ _ _
      _ ≤ r + r := (add_le_add ha hb)
      _ = 2 * r := (two_mul r).symm
      
#align emetric.diam_closed_ball EMetric.diam_closedBall

/- warning: emetric.diam_ball -> EMetric.diam_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {r : ENNReal}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α _inst_1 (EMetric.ball.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (OfNat.ofNat.{0} ENNReal 2 (OfNat.mk.{0} ENNReal 2 (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {x : α} {r : ENNReal}, LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α _inst_1 (EMetric.ball.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (OfNat.ofNat.{0} ENNReal 2 (instOfNat.{0} ENNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) r)
Case conversion may be inaccurate. Consider using '#align emetric.diam_ball EMetric.diam_ballₓ'. -/
theorem diam_ball {r : ℝ≥0∞} : diam (ball x r) ≤ 2 * r :=
  le_trans (diam_mono ball_subset_closedBall) diam_closedBall
#align emetric.diam_ball EMetric.diam_ball

/- warning: emetric.diam_pi_le_of_le -> EMetric.diam_pi_le_of_le is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u2} (π b)] {s : forall (b : β), Set.{u2} (π b)} {c : ENNReal}, (forall (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u2} (π b) (_inst_3 b) (s b)) c) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{max u1 u2} (forall (i : β), π i) (pseudoEMetricSpacePi.{u1, u2} β (fun (i : β) => π i) _inst_2 (fun (b : β) => _inst_3 b)) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) s)) c)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoEMetricSpace.{u1} (π b)] {s : forall (b : β), Set.{u1} (π b)} {c : ENNReal}, (forall (b : β), LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} (π b) (_inst_3 b) (s b)) c) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{max u1 u2} (forall (i : β), π i) (pseudoEMetricSpacePi.{u2, u1} β (fun (i : β) => π i) _inst_2 (fun (b : β) => _inst_3 b)) (Set.pi.{u2, u1} β (fun (b : β) => π b) (Set.univ.{u2} β) s)) c)
Case conversion may be inaccurate. Consider using '#align emetric.diam_pi_le_of_le EMetric.diam_pi_le_of_leₓ'. -/
theorem diam_pi_le_of_le {π : β → Type _} [Fintype β] [∀ b, PseudoEMetricSpace (π b)]
    {s : ∀ b : β, Set (π b)} {c : ℝ≥0∞} (h : ∀ b, diam (s b) ≤ c) : diam (Set.pi univ s) ≤ c :=
  by
  apply diam_le fun x hx y hy => edist_pi_le_iff.mpr _
  rw [mem_univ_pi] at hx hy
  exact fun b => diam_le_iff.1 (h b) (x b) (hx b) (y b) (hy b)
#align emetric.diam_pi_le_of_le EMetric.diam_pi_le_of_le

end Diam

end Emetric

#print EMetricSpace /-
--namespace
/-- We now define `emetric_space`, extending `pseudo_emetric_space`. -/
class EMetricSpace (α : Type u) extends PseudoEMetricSpace α : Type u where
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y
#align emetric_space EMetricSpace
-/

variable {γ : Type w} [EMetricSpace γ]

export EMetricSpace (eq_of_edist_eq_zero)

/- warning: edist_eq_zero -> edist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} ENNReal (EDist.edist.{u1} γ (PseudoEMetricSpace.toHasEdist.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} ENNReal (EDist.edist.{u1} γ (PseudoEMetricSpace.toEDist.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align edist_eq_zero edist_eq_zeroₓ'. -/
/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  Iff.intro eq_of_edist_eq_zero fun this : x = y => this ▸ edist_self _
#align edist_eq_zero edist_eq_zero

/- warning: zero_eq_edist -> zero_eq_edist is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} ENNReal (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toHasEdist.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2)) x y)) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} ENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (EDist.edist.{u1} γ (PseudoEMetricSpace.toEDist.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2)) x y)) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align zero_eq_edist zero_eq_edistₓ'. -/
@[simp]
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y :=
  Iff.intro (fun h => eq_of_edist_eq_zero h.symm) fun this : x = y => this ▸ (edist_self _).symm
#align zero_eq_edist zero_eq_edist

/- warning: edist_le_zero -> edist_le_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toHasEdist.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toEDist.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align edist_le_zero edist_le_zeroₓ'. -/
theorem edist_le_zero {x y : γ} : edist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero
#align edist_le_zero edist_le_zero

/- warning: edist_pos -> edist_pos is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toHasEdist.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2)) x y)) (Ne.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (EDist.edist.{u1} γ (PseudoEMetricSpace.toEDist.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2)) x y)) (Ne.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align edist_pos edist_posₓ'. -/
@[simp]
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y := by simp [← not_le]
#align edist_pos edist_pos

/- warning: eq_of_forall_edist_le -> eq_of_forall_edist_le is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toHasEdist.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2)) x y) ε)) -> (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {x : γ} {y : γ}, (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toEDist.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2)) x y) ε)) -> (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align eq_of_forall_edist_le eq_of_forall_edist_leₓ'. -/
/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀ ε > 0, edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense bot_le h)
#align eq_of_forall_edist_le eq_of_forall_edist_le

#print to_separated /-
-- see Note [lower instance priority]
/-- An emetric space is separated -/
instance (priority := 100) to_separated : SeparatedSpace γ :=
  separated_def.2 fun x y h =>
    eq_of_forall_edist_le fun ε ε0 => le_of_lt (h _ (edist_mem_uniformity ε0))
#align to_separated to_separated
-/

/- warning: emetric.uniform_embedding_iff' -> EMetric.uniformEmbedding_iff' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : EMetricSpace.{u2} γ] [_inst_3 : EMetricSpace.{u1} β] {f : γ -> β}, Iff (UniformEmbedding.{u2, u1} γ β (PseudoEMetricSpace.toUniformSpace.{u2} γ (EMetricSpace.toPseudoEmetricSpace.{u2} γ _inst_2)) (PseudoEMetricSpace.toUniformSpace.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_3)) f) (And (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : γ} {b : γ}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} γ (PseudoEMetricSpace.toHasEdist.{u2} γ (EMetricSpace.toPseudoEmetricSpace.{u2} γ _inst_2)) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} β (PseudoEMetricSpace.toHasEdist.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_3)) (f a) (f b)) ε))))) (forall (δ : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) δ (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => Exists.{0} (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => forall {a : γ} {b : γ}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} β (PseudoEMetricSpace.toHasEdist.{u1} β (EMetricSpace.toPseudoEmetricSpace.{u1} β _inst_3)) (f a) (f b)) ε) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u2} γ (PseudoEMetricSpace.toHasEdist.{u2} γ (EMetricSpace.toPseudoEmetricSpace.{u2} γ _inst_2)) a b) δ))))))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : EMetricSpace.{u2} γ] [_inst_3 : EMetricSpace.{u1} β] {f : γ -> β}, Iff (UniformEmbedding.{u2, u1} γ β (PseudoEMetricSpace.toUniformSpace.{u2} γ (EMetricSpace.toPseudoEMetricSpace.{u2} γ _inst_2)) (PseudoEMetricSpace.toUniformSpace.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_3)) f) (And (forall (ε : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (δ : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : γ} {b : γ}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} γ (PseudoEMetricSpace.toEDist.{u2} γ (EMetricSpace.toPseudoEMetricSpace.{u2} γ _inst_2)) a b) δ) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} β (PseudoEMetricSpace.toEDist.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_3)) (f a) (f b)) ε))))) (forall (δ : ENNReal), (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) δ (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (Exists.{1} ENNReal (fun (ε : ENNReal) => And (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (forall {a : γ} {b : γ}, (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} β (PseudoEMetricSpace.toEDist.{u1} β (EMetricSpace.toPseudoEMetricSpace.{u1} β _inst_3)) (f a) (f b)) ε) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u2} γ (PseudoEMetricSpace.toEDist.{u2} γ (EMetricSpace.toPseudoEMetricSpace.{u2} γ _inst_2)) a b) δ))))))
Case conversion may be inaccurate. Consider using '#align emetric.uniform_embedding_iff' EMetric.uniformEmbedding_iff'ₓ'. -/
/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem EMetric.uniformEmbedding_iff' [EMetricSpace β] {f : γ → β} :
    UniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ :=
  by
  simp only [uniformEmbedding_iff_uniformInducing,
    uniformity_basis_edist.uniform_inducing_iff uniformity_basis_edist, exists_prop]
  rfl
#align emetric.uniform_embedding_iff' EMetric.uniformEmbedding_iff'

#print EMetricSpace.ofT0PseudoEMetricSpace /-
/-- If a `pseudo_emetric_space` is a T₀ space, then it is an `emetric_space`. -/
def EMetricSpace.ofT0PseudoEMetricSpace (α : Type _) [PseudoEMetricSpace α] [T0Space α] :
    EMetricSpace α :=
  { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun x y hdist => (EMetric.inseparable_iff.2 hdist).Eq }
#align emetric_space.of_t0_pseudo_emetric_space EMetricSpace.ofT0PseudoEMetricSpace
-/

#print EMetricSpace.replaceUniformity /-
/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
-/
def EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ
    where
  edist := @edist _ m.toHasEdist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)
#align emetric_space.replace_uniformity EMetricSpace.replaceUniformity
-/

#print EMetricSpace.induced /-
/-- The extended metric induced by an injective function taking values in a emetric space. -/
def EMetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EMetricSpace β) :
    EMetricSpace γ where
  edist x y := edist (f x) (f y)
  edist_self x := edist_self _
  eq_of_edist_eq_zero x y h := hf (edist_eq_zero.1 h)
  edist_comm x y := edist_comm _ _
  edist_triangle x y z := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap _).eq_binfᵢ
#align emetric_space.induced EMetricSpace.induced
-/

/-- Emetric space instance on subsets of emetric spaces -/
instance {α : Type _} {p : α → Prop} [EMetricSpace α] : EMetricSpace (Subtype p) :=
  EMetricSpace.induced coe Subtype.coe_injective ‹_›

/-- Emetric space instance on the multiplicative opposite of an emetric space. -/
@[to_additive "Emetric space instance on the additive opposite of an emetric space."]
instance {α : Type _} [EMetricSpace α] : EMetricSpace αᵐᵒᵖ :=
  EMetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance {α : Type _} [EMetricSpace α] : EMetricSpace (ULift α) :=
  EMetricSpace.induced ULift.down ULift.down_injective ‹_›

#print Prod.emetricSpaceMax /-
/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β) :=
  { Prod.pseudoEMetricSpaceMax with
    eq_of_edist_eq_zero := fun x y h =>
      by
      cases' max_le_iff.1 (le_of_eq h) with h₁ h₂
      have A : x.fst = y.fst := edist_le_zero.1 h₁
      have B : x.snd = y.snd := edist_le_zero.1 h₂
      exact Prod.ext_iff.2 ⟨A, B⟩ }
#align prod.emetric_space_max Prod.emetricSpaceMax
-/

/- warning: uniformity_edist -> uniformity_edist is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (uniformity.{u1} γ (PseudoEMetricSpace.toUniformSpace.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2))) (infᵢ.{u1, 1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (Filter.completeLattice.{u1} (Prod.{u1, u1} γ γ)))) ENNReal (fun (ε : ENNReal) => infᵢ.{u1, 0} (Filter.{u1} (Prod.{u1, u1} γ γ)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (Filter.completeLattice.{u1} (Prod.{u1, u1} γ γ)))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => Filter.principal.{u1} (Prod.{u1, u1} γ γ) (setOf.{u1} (Prod.{u1, u1} γ γ) (fun (p : Prod.{u1, u1} γ γ) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toHasEdist.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2)) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) ε)))))
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (uniformity.{u1} γ (PseudoEMetricSpace.toUniformSpace.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2))) (infᵢ.{u1, 1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} γ γ)))) ENNReal (fun (ε : ENNReal) => infᵢ.{u1, 0} (Filter.{u1} (Prod.{u1, u1} γ γ)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} γ γ)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} γ γ)))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) => Filter.principal.{u1} (Prod.{u1, u1} γ γ) (setOf.{u1} (Prod.{u1, u1} γ γ) (fun (p : Prod.{u1, u1} γ γ) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} γ (PseudoEMetricSpace.toEDist.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2)) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) ε)))))
Case conversion may be inaccurate. Consider using '#align uniformity_edist uniformity_edistₓ'. -/
/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist
#align uniformity_edist uniformity_edist

section Pi

open Finset

variable {π : β → Type _} [Fintype β]

#print emetricSpacePi /-
/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetricSpacePi [∀ b, EMetricSpace (π b)] : EMetricSpace (∀ b, π b) :=
  { pseudoEMetricSpacePi with
    eq_of_edist_eq_zero := fun f g eq0 =>
      by
      have eq1 : (sup univ fun b : β => edist (f b) (g b)) ≤ 0 := le_of_eq eq0
      simp only [Finset.sup_le_iff] at eq1
      exact funext fun b => edist_le_zero.1 <| eq1 b <| mem_univ b }
#align emetric_space_pi emetricSpacePi
-/

end Pi

namespace Emetric

/- warning: emetric.countable_closure_of_compact -> EMetric.countable_closure_of_compact is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {s : Set.{u1} γ}, (IsCompact.{u1} γ (UniformSpace.toTopologicalSpace.{u1} γ (PseudoEMetricSpace.toUniformSpace.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2))) s) -> (Exists.{succ u1} (Set.{u1} γ) (fun (t : Set.{u1} γ) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} γ) (Set.hasSubset.{u1} γ) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} γ) (Set.hasSubset.{u1} γ) t s) => And (Set.Countable.{u1} γ t) (Eq.{succ u1} (Set.{u1} γ) s (closure.{u1} γ (UniformSpace.toTopologicalSpace.{u1} γ (PseudoEMetricSpace.toUniformSpace.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2))) t)))))
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {s : Set.{u1} γ}, (IsCompact.{u1} γ (UniformSpace.toTopologicalSpace.{u1} γ (PseudoEMetricSpace.toUniformSpace.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2))) s) -> (Exists.{succ u1} (Set.{u1} γ) (fun (t : Set.{u1} γ) => And (HasSubset.Subset.{u1} (Set.{u1} γ) (Set.instHasSubsetSet.{u1} γ) t s) (And (Set.Countable.{u1} γ t) (Eq.{succ u1} (Set.{u1} γ) s (closure.{u1} γ (UniformSpace.toTopologicalSpace.{u1} γ (PseudoEMetricSpace.toUniformSpace.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2))) t)))))
Case conversion may be inaccurate. Consider using '#align emetric.countable_closure_of_compact EMetric.countable_closure_of_compactₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    ∃ (t : _)(_ : t ⊆ s), t.Countable ∧ s = closure t :=
  by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, subset.antisymm hsub (closure_minimal hts hs.is_closed)⟩
#align emetric.countable_closure_of_compact EMetric.countable_closure_of_compact

section Diam

variable {s : Set γ}

/- warning: emetric.diam_eq_zero_iff -> EMetric.diam_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {s : Set.{u1} γ}, Iff (Eq.{1} ENNReal (EMetric.diam.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2) s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Set.Subsingleton.{u1} γ s)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {s : Set.{u1} γ}, Iff (Eq.{1} ENNReal (EMetric.diam.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Set.Subsingleton.{u1} γ s)
Case conversion may be inaccurate. Consider using '#align emetric.diam_eq_zero_iff EMetric.diam_eq_zero_iffₓ'. -/
theorem diam_eq_zero_iff : diam s = 0 ↔ s.Subsingleton :=
  ⟨fun h x hx y hy => edist_le_zero.1 <| h ▸ edist_le_diam_of_mem hx hy, diam_subsingleton⟩
#align emetric.diam_eq_zero_iff EMetric.diam_eq_zero_iff

/- warning: emetric.diam_pos_iff -> EMetric.diam_pos_iff' is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {s : Set.{u1} γ}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) (EMetric.diam.{u1} γ (EMetricSpace.toPseudoEmetricSpace.{u1} γ _inst_2) s)) (Exists.{succ u1} γ (fun (x : γ) => Exists.{0} (Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x s) (fun (H : Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) x s) => Exists.{succ u1} γ (fun (y : γ) => Exists.{0} (Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) y s) (fun (H : Membership.Mem.{u1, u1} γ (Set.{u1} γ) (Set.hasMem.{u1} γ) y s) => Ne.{succ u1} γ x y)))))
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : EMetricSpace.{u1} γ] {s : Set.{u1} γ}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) (EMetric.diam.{u1} γ (EMetricSpace.toPseudoEMetricSpace.{u1} γ _inst_2) s)) (Exists.{succ u1} γ (fun (x : γ) => And (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) (Exists.{succ u1} γ (fun (y : γ) => And (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) y s) (Ne.{succ u1} γ x y)))))
Case conversion may be inaccurate. Consider using '#align emetric.diam_pos_iff EMetric.diam_pos_iff'ₓ'. -/
theorem diam_pos_iff' : 0 < diam s ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  simp only [pos_iff_ne_zero, Ne.def, diam_eq_zero_iff, Set.Subsingleton, not_forall]
#align emetric.diam_pos_iff EMetric.diam_pos_iff'

end Diam

end Emetric

/-!
### Separation quotient
-/


instance [PseudoEMetricSpace X] : EDist (UniformSpace.SeparationQuotient X) :=
  ⟨fun x y =>
    Quotient.liftOn₂' x y edist fun x y x' y' hx hy =>
      calc
        edist x y = edist x' y :=
          edist_congr_right <| EMetric.inseparable_iff.1 <| separationRel_iff_inseparable.1 hx
        _ = edist x' y' :=
          edist_congr_left <| EMetric.inseparable_iff.1 <| separationRel_iff_inseparable.1 hy
        ⟩

#print UniformSpace.SeparationQuotient.edist_mk /-
@[simp]
theorem UniformSpace.SeparationQuotient.edist_mk [PseudoEMetricSpace X] (x y : X) :
    @edist (UniformSpace.SeparationQuotient X) _ (Quot.mk _ x) (Quot.mk _ y) = edist x y :=
  rfl
#align uniform_space.separation_quotient.edist_mk UniformSpace.SeparationQuotient.edist_mk
-/

instance [PseudoEMetricSpace X] : EMetricSpace (UniformSpace.SeparationQuotient X) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (UniformSpace.SeparationQuotient X)
    { edist_self := fun x => Quotient.inductionOn' x edist_self
      edist_comm := fun x y => Quotient.inductionOn₂' x y edist_comm
      edist_triangle := fun x y z => Quotient.inductionOn₃' x y z edist_triangle
      toUniformSpace := inferInstance
      uniformity_edist :=
        (uniformity_basis_edist.map _).eq_binfᵢ.trans <|
          infᵢ_congr fun ε =>
            infᵢ_congr fun hε =>
              congr_arg 𝓟
                (by
                  ext ⟨⟨x⟩, ⟨y⟩⟩
                  refine' ⟨_, fun h => ⟨(x, y), h, rfl⟩⟩
                  rintro ⟨⟨x', y'⟩, h', h⟩
                  simp only [Prod.ext_iff] at h
                  rwa [← h.1, ← h.2]) }
    _

/-!
### `additive`, `multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [EDist X]

instance : EDist (Additive X) :=
  ‹EDist X›

instance : EDist (Multiplicative X) :=
  ‹EDist X›

#print edist_ofMul /-
@[simp]
theorem edist_ofMul (a b : X) : edist (ofMul a) (ofMul b) = edist a b :=
  rfl
#align edist_of_mul edist_ofMul
-/

#print edist_ofAdd /-
@[simp]
theorem edist_ofAdd (a b : X) : edist (ofAdd a) (ofAdd b) = edist a b :=
  rfl
#align edist_of_add edist_ofAdd
-/

#print edist_toMul /-
@[simp]
theorem edist_toMul (a b : Additive X) : edist (toMul a) (toMul b) = edist a b :=
  rfl
#align edist_to_mul edist_toMul
-/

#print edist_toAdd /-
@[simp]
theorem edist_toAdd (a b : Multiplicative X) : edist (toAdd a) (toAdd b) = edist a b :=
  rfl
#align edist_to_add edist_toAdd
-/

end

instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Additive X) :=
  ‹PseudoEMetricSpace X›

instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Multiplicative X) :=
  ‹PseudoEMetricSpace X›

instance [EMetricSpace X] : EMetricSpace (Additive X) :=
  ‹EMetricSpace X›

instance [EMetricSpace X] : EMetricSpace (Multiplicative X) :=
  ‹EMetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/


open OrderDual

section

variable [EDist X]

instance : EDist Xᵒᵈ :=
  ‹EDist X›

#print edist_toDual /-
@[simp]
theorem edist_toDual (a b : X) : edist (toDual a) (toDual b) = edist a b :=
  rfl
#align edist_to_dual edist_toDual
-/

#print edist_ofDual /-
@[simp]
theorem edist_ofDual (a b : Xᵒᵈ) : edist (ofDual a) (ofDual b) = edist a b :=
  rfl
#align edist_of_dual edist_ofDual
-/

end

instance [PseudoEMetricSpace X] : PseudoEMetricSpace Xᵒᵈ :=
  ‹PseudoEMetricSpace X›

instance [EMetricSpace X] : EMetricSpace Xᵒᵈ :=
  ‹EMetricSpace X›

