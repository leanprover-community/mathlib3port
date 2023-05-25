/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.basic
! leanprover-community/mathlib commit 8000bbbe2e9d39b84edb993d88781f536a8a3fa8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Positivity
import Mathbin.Topology.Algebra.Order.Compact
import Mathbin.Topology.MetricSpace.EmetricSpace
import Mathbin.Topology.Bornology.Constructions

/-!
# Metric spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines metric spaces. Many definitions and theorems expected
on metric spaces are already introduced on uniform spaces and topological spaces.
For example: open and closed sets, compactness, completeness, continuity and uniform continuity

## Main definitions

* `has_dist α`: Endows a space `α` with a function `dist a b`.
* `pseudo_metric_space α`: A space endowed with a distance function, which can
  be zero even if the two elements are non-equal.
* `metric.ball x ε`: The set of all points `y` with `dist y x < ε`.
* `metric.bounded s`: Whether a subset of a `pseudo_metric_space` is bounded.
* `metric_space α`: A `pseudo_metric_space` with the guarantee `dist x y = 0 → x = y`.

Additional useful definitions:

* `nndist a b`: `dist` as a function to the non-negative reals.
* `metric.closed_ball x ε`: The set of all points `y` with `dist y x ≤ ε`.
* `metric.sphere x ε`: The set of all points `y` with `dist y x = ε`.
* `proper_space α`: A `pseudo_metric_space` where all closed balls are compact.
* `metric.diam s` : The `supr` of the distances of members of `s`.
  Defined in terms of `emetric.diam`, for better handling of the case when it should be infinite.

TODO (anyone): Add "Main results" section.

## Implementation notes

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory of `pseudo_metric_space`, where we don't require `dist x y = 0 → x = y` and we specialize
to `metric_space` at the end.

## Tags

metric, pseudo_metric, dist
-/


open Set Filter TopologicalSpace Bornology

open uniformity Topology BigOperators Filter NNReal ENNReal

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type _}

/- warning: uniform_space_of_dist -> UniformSpace.ofDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (dist : α -> α -> Real), (forall (x : α), Eq.{1} Real (dist x x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (dist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (dist x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (dist x y) (dist y z))) -> (UniformSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (dist : α -> α -> Real), (forall (x : α), Eq.{1} Real (dist x x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (dist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (dist x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (dist x y) (dist y z))) -> (UniformSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align uniform_space_of_dist UniformSpace.ofDistₓ'. -/
/-- Construct a uniform structure from a distance function and metric space axioms -/
def UniformSpace.ofDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : UniformSpace α :=
  UniformSpace.ofFun dist dist_self dist_comm dist_triangle fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun x hx y hy => add_halves ε ▸ add_lt_add hx hy⟩
#align uniform_space_of_dist UniformSpace.ofDist

/-- This is an internal lemma used to construct a bornology from a metric in `bornology.of_dist`. -/
private theorem bounded_iff_aux {α : Type _} (dist : α → α → ℝ)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) (s : Set α) (a : α) :
    (∃ c, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ c) ↔ ∃ r, ∀ ⦃x⦄, x ∈ s → dist x a ≤ r :=
  by
  constructor <;> rintro ⟨C, hC⟩
  · rcases s.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨C + dist x a, fun y hy => (dist_triangle y x a).trans (add_le_add_right (hC hy hx) _)⟩
  ·
    exact
      ⟨C + C, fun x hx y hy =>
        (dist_triangle x a y).trans
          (add_le_add (hC hx)
            (by
              rw [dist_comm]
              exact hC hy))⟩
#align bounded_iff_aux bounded_iff_aux

/-- Construct a bornology from a distance function and metric space axioms. -/
def Bornology.ofDist {α : Type _} (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C }
    ⟨0, fun x hx y => hx.elim⟩ (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with (rfl | ⟨z, hz⟩)
      · exact (empty_union t).symm ▸ ht
      · simp only [fun u => bounded_iff_aux dist dist_comm dist_triangle u z] at hs ht⊢
        rcases hs, ht with ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩
        exact
          ⟨max r₁ r₂, fun x hx =>
            Or.elim hx (fun hx' => (hr₁ hx').trans (le_max_left _ _)) fun hx' =>
              (hr₂ hx').trans (le_max_right _ _)⟩)
    fun z =>
    ⟨0, fun x hx y hy => by
      rw [eq_of_mem_singleton hx, eq_of_mem_singleton hy]
      exact (dist_self z).le⟩
#align bornology.of_dist Bornology.ofDistₓ

#print Dist /-
/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
@[ext]
class Dist (α : Type _) where
  dist : α → α → ℝ
#align has_dist Dist
-/

export Dist (dist)

-- the uniform structure and the emetric space structure are embedded in the metric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- This is an internal lemma used inside the default of `pseudo_metric_space.edist`. -/
private theorem pseudo_metric_space.dist_nonneg' {α} {x y : α} (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : 0 ≤ dist x y :=
  have : 2 * dist x y ≥ 0 :=
    calc
      2 * dist x y = dist x y + dist y x := by rw [dist_comm x y, two_mul]
      _ ≥ 0 := by rw [← dist_self x] <;> apply dist_triangle
      
  nonneg_of_mul_nonneg_right this zero_lt_two
#align pseudo_metric_space.dist_nonneg' pseudo_metric_space.dist_nonneg'

/- warning: pseudo_metric_space.edist_dist_tac clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align pseudo_metric_space.edist_dist_tac [anonymous]ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:330:4: warning: unsupported (TODO): `[tacs] -/
#print [anonymous] /-
/-- This tactic is used to populate `pseudo_metric_space.edist_dist` when the default `edist` is
used. -/
protected unsafe def [anonymous] : tactic Unit :=
  tactic.intros >> sorry
#align pseudo_metric_space.edist_dist_tac [anonymous]
-/

#print PseudoMetricSpace /-
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic pseudo_metric_space.edist_dist_tac -/
/-- Pseudo metric and Metric spaces

A pseudo metric space is endowed with a distance for which the requirement `d(x,y)=0 → x = y` might
not hold. A metric space is a pseudo metric space such that `d(x,y)=0 → x = y`.
Each pseudo metric space induces a canonical `uniform_space` and hence a canonical
`topological_space` This is enforced in the type class definition, by extending the `uniform_space`
structure. When instantiating a `pseudo_metric_space` structure, the uniformity fields are not
necessary, they will be filled in by default. In the same way, each (pseudo) metric space induces a
(pseudo) emetric space structure. It is included in the structure, but filled in by default.
-/
class PseudoMetricSpace (α : Type u) extends Dist α : Type u where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  edist : α → α → ℝ≥0∞ := fun x y =>
    @coe ℝ≥0 _ _ ⟨dist x y, PseudoMetricSpace.dist_nonneg' _ ‹_› ‹_› ‹_›⟩
  edist_dist : ∀ x y : α, edist x y = ENNReal.ofReal (dist x y) := by
    run_tac
      [anonymous]
  toUniformSpace : UniformSpace α := UniformSpace.ofDist dist dist_self dist_comm dist_triangle
  uniformity_dist :
    𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α |
            dist p.1 p.2 < ε } := by
    intros
    rfl
  toBornology : Bornology α := Bornology.ofDist dist dist_self dist_comm dist_triangle
  cobounded_sets :
    (Bornology.cobounded α).sets =
      { s | ∃ C, ∀ ⦃x⦄, x ∈ sᶜ →
              ∀ ⦃y⦄, y ∈ sᶜ → dist x y ≤ C } := by
    intros
    rfl
#align pseudo_metric_space PseudoMetricSpace
-/

#print PseudoMetricSpace.ext /-
/-- Two pseudo metric space structures with the same distance function coincide. -/
@[ext]
theorem PseudoMetricSpace.ext {α : Type _} {m m' : PseudoMetricSpace α}
    (h : m.toHasDist = m'.toHasDist) : m = m' :=
  by
  rcases m with ⟨⟩
  rcases m' with ⟨⟩
  dsimp at h
  subst h
  congr
  · ext (x y) : 2
    dsimp at m_edist_dist m'_edist_dist
    simp [m_edist_dist, m'_edist_dist]
  · dsimp at m_uniformity_dist m'_uniformity_dist
    rw [← m'_uniformity_dist] at m_uniformity_dist
    exact uniformSpace_eq m_uniformity_dist
  · ext1
    dsimp at m_cobounded_sets m'_cobounded_sets
    rw [← m'_cobounded_sets] at m_cobounded_sets
    exact filter_eq m_cobounded_sets
#align pseudo_metric_space.ext PseudoMetricSpace.ext
-/

variable [PseudoMetricSpace α]

attribute [instance] PseudoMetricSpace.toUniformSpace

attribute [instance] PseudoMetricSpace.toBornology

#print PseudoMetricSpace.toEDist /-
-- see Note [lower instance priority]
instance (priority := 200) PseudoMetricSpace.toEDist : EDist α :=
  ⟨PseudoMetricSpace.edist⟩
#align pseudo_metric_space.to_has_edist PseudoMetricSpace.toEDist
-/

/- warning: pseudo_metric_space.of_dist_topology -> PseudoMetricSpace.ofDistTopology is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α), Eq.{1} Real (dist x x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (dist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (dist x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (dist x y) (dist y z))) -> (forall (s : Set.{u1} α), Iff (IsOpen.{u1} α _inst_2 s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (y : α), (LT.lt.{0} Real Real.hasLt (dist x y) ε) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s)))))) -> (PseudoMetricSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α), Eq.{1} Real (dist x x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (dist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (dist x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (dist x y) (dist y z))) -> (forall (s : Set.{u1} α), Iff (IsOpen.{u1} α _inst_2 s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (y : α), (LT.lt.{0} Real Real.instLTReal (dist x y) ε) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s)))))) -> (PseudoMetricSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align pseudo_metric_space.of_dist_topology PseudoMetricSpace.ofDistTopologyₓ'. -/
/-- Construct a pseudo-metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s) :
    PseudoMetricSpace α :=
  { dist
    dist_self
    dist_comm
    dist_triangle
    toUniformSpace :=
      { isOpen_uniformity := fun s =>
          (H s).trans <|
            forall₂_congr fun x _ =>
              ((UniformSpace.hasBasis_ofFun (exists_gt (0 : ℝ)) dist _ _ _ _).comap
                        (Prod.mk x)).mem_iff.symm.trans
                mem_comap_prod_mk
        toCore := (UniformSpace.ofDist dist dist_self dist_comm dist_triangle).toCore }
    uniformity_dist := rfl
    toBornology := Bornology.ofDist dist dist_self dist_comm dist_triangle
    cobounded_sets := rfl }
#align pseudo_metric_space.of_dist_topology PseudoMetricSpace.ofDistTopology

/- warning: dist_self -> dist_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align dist_self dist_selfₓ'. -/
@[simp]
theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetricSpace.dist_self x
#align dist_self dist_self

#print dist_comm /-
theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetricSpace.dist_comm x y
#align dist_comm dist_comm
-/

#print edist_dist /-
theorem edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y) :=
  PseudoMetricSpace.edist_dist x y
#align edist_dist edist_dist
-/

/- warning: dist_triangle -> dist_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align dist_triangle dist_triangleₓ'. -/
theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
  PseudoMetricSpace.dist_triangle x y z
#align dist_triangle dist_triangle

/- warning: dist_triangle_left -> dist_triangle_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) z x) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) z y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) z x) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) z y))
Case conversion may be inaccurate. Consider using '#align dist_triangle_left dist_triangle_leftₓ'. -/
theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y := by
  rw [dist_comm z] <;> apply dist_triangle
#align dist_triangle_left dist_triangle_left

/- warning: dist_triangle_right -> dist_triangle_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x z) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x z) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align dist_triangle_right dist_triangle_rightₓ'. -/
theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z := by
  rw [dist_comm y] <;> apply dist_triangle
#align dist_triangle_right dist_triangle_right

/- warning: dist_triangle4 -> dist_triangle4 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α) (w : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x w) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y z)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) z w))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α) (w : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x w) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) z w))
Case conversion may be inaccurate. Consider using '#align dist_triangle4 dist_triangle4ₓ'. -/
theorem dist_triangle4 (x y z w : α) : dist x w ≤ dist x y + dist y z + dist z w :=
  calc
    dist x w ≤ dist x z + dist z w := dist_triangle x z w
    _ ≤ dist x y + dist y z + dist z w := add_le_add_right (dist_triangle x y z) _
    
#align dist_triangle4 dist_triangle4

/- warning: dist_triangle4_left -> dist_triangle4_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x₁ : α) (y₁ : α) (x₂ : α) (y₂ : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₂ y₂) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₁ y₁) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₁ x₂) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y₁ y₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x₁ : α) (y₁ : α) (x₂ : α) (y₂ : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₂ y₂) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₁ y₁) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₁ x₂) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y₁ y₂)))
Case conversion may be inaccurate. Consider using '#align dist_triangle4_left dist_triangle4_leftₓ'. -/
theorem dist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    dist x₂ y₂ ≤ dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) :=
  by
  rw [add_left_comm, dist_comm x₁, ← add_assoc]
  apply dist_triangle4
#align dist_triangle4_left dist_triangle4_left

/- warning: dist_triangle4_right -> dist_triangle4_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x₁ : α) (y₁ : α) (x₂ : α) (y₂ : α), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₁ y₁) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₁ x₂) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y₁ y₂)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x₂ y₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x₁ : α) (y₁ : α) (x₂ : α) (y₂ : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₁ y₁) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₁ x₂) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y₁ y₂)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x₂ y₂))
Case conversion may be inaccurate. Consider using '#align dist_triangle4_right dist_triangle4_rightₓ'. -/
theorem dist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    dist x₁ y₁ ≤ dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ :=
  by
  rw [add_right_comm, dist_comm y₁]
  apply dist_triangle4
#align dist_triangle4_right dist_triangle4_right

/- warning: dist_le_Ico_sum_dist -> dist_le_Ico_sum_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (f : Nat -> α) {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (f : Nat -> α) {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align dist_le_Ico_sum_dist dist_le_Ico_sum_distₓ'. -/
/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i in Finset.Ico m n, dist (f i) (f (i + 1)) :=
  by
  revert n
  apply Nat.le_induction
  · simp only [Finset.sum_empty, Finset.Ico_self, dist_self]
  · intro n hn hrec
    calc
      dist (f m) (f (n + 1)) ≤ dist (f m) (f n) + dist _ _ := dist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := (add_le_add hrec le_rfl)
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
        rw [Nat.Ico_succ_right_eq_insert_Ico hn, Finset.sum_insert, add_comm] <;> simp
      
#align dist_le_Ico_sum_dist dist_le_Ico_sum_dist

/- warning: dist_le_range_sum_dist -> dist_le_range_sum_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (f : Nat -> α) (n : Nat), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f n)) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (f : Nat -> α) (n : Nat), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f n)) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align dist_le_range_sum_dist dist_le_range_sum_distₓ'. -/
/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ i in Finset.range n, dist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)
#align dist_le_range_sum_dist dist_le_range_sum_dist

/- warning: dist_le_Ico_sum_of_dist_le -> dist_le_Ico_sum_of_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {m : Nat} {n : Nat}, (LE.le.{0} Nat Nat.hasLe m n) -> (forall {d : Nat -> Real}, (forall {k : Nat}, (LE.le.{0} Nat Nat.hasLe m k) -> (LT.lt.{0} Nat Nat.hasLt k n) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (d k))) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder m n) (fun (i : Nat) => d i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} {m : Nat} {n : Nat}, (LE.le.{0} Nat instLENat m n) -> (forall {d : Nat -> Real}, (forall {k : Nat}, (LE.le.{0} Nat instLENat m k) -> (LT.lt.{0} Nat instLTNat k n) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (d k))) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f m) (f n)) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring m n) (fun (i : Nat) => d i))))
Case conversion may be inaccurate. Consider using '#align dist_le_Ico_sum_of_dist_le dist_le_Ico_sum_of_dist_leₓ'. -/
/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
    (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (dist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
#align dist_le_Ico_sum_of_dist_le dist_le_Ico_sum_of_dist_le

/- warning: dist_le_range_sum_of_dist_le -> dist_le_range_sum_of_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} (n : Nat) {d : Nat -> Real}, (forall {k : Nat}, (LT.lt.{0} Nat Nat.hasLt k n) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (d k))) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f n)) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => d i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Nat -> α} (n : Nat) {d : Nat -> Real}, (forall {k : Nat}, (LT.lt.{0} Nat instLTNat k n) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f k) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (d k))) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f n)) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => d i)))
Case conversion may be inaccurate. Consider using '#align dist_le_range_sum_of_dist_le dist_le_range_sum_of_dist_leₓ'. -/
/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ}
    (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_of_dist_le (zero_le n) fun _ _ => hd
#align dist_le_range_sum_of_dist_le dist_le_range_sum_of_dist_le

#print swap_dist /-
theorem swap_dist : Function.swap (@dist α _) = dist := by funext x y <;> exact dist_comm _ _
#align swap_dist swap_dist
-/

/- warning: abs_dist_sub_le -> abs_dist_sub_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x z) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y z))) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x z) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z))) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align abs_dist_sub_le abs_dist_sub_leₓ'. -/
theorem abs_dist_sub_le (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩
#align abs_dist_sub_le abs_dist_sub_le

/- warning: dist_nonneg -> dist_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align dist_nonneg dist_nonnegₓ'. -/
theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
  PseudoMetricSpace.dist_nonneg' dist dist_self dist_comm dist_triangle
#align dist_nonneg dist_nonneg

section

open Tactic Tactic.Positivity

/-- Extension for the `positivity` tactic: distances are nonnegative. -/
@[positivity]
unsafe def _root_.tactic.positivity_dist : expr → tactic strictness
  | q(dist $(a) $(b)) => nonnegative <$> mk_app `` dist_nonneg [a, b]
  | _ => failed
#align tactic.positivity_dist tactic.positivity_dist

end

/- warning: abs_dist -> abs_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {a : α} {b : α}, Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {a : α} {b : α}, Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align abs_dist abs_distₓ'. -/
@[simp]
theorem abs_dist {a b : α} : |dist a b| = dist a b :=
  abs_of_nonneg dist_nonneg
#align abs_dist abs_dist

#print NNDist /-
/-- A version of `has_dist` that takes value in `ℝ≥0`. -/
class NNDist (α : Type _) where
  nndist : α → α → ℝ≥0
#align has_nndist NNDist
-/

export NNDist (nndist)

#print PseudoMetricSpace.toNNDist /-
-- see Note [lower instance priority]
/-- Distance as a nonnegative real number. -/
instance (priority := 100) PseudoMetricSpace.toNNDist : NNDist α :=
  ⟨fun a b => ⟨dist a b, dist_nonneg⟩⟩
#align pseudo_metric_space.to_has_nndist PseudoMetricSpace.toNNDist
-/

#print nndist_edist /-
/-- Express `nndist` in terms of `edist`-/
theorem nndist_edist (x y : α) : nndist x y = (edist x y).toNNReal := by
  simp [nndist, edist_dist, Real.toNNReal, max_eq_left dist_nonneg, ENNReal.ofReal]
#align nndist_edist nndist_edist
-/

#print edist_nndist /-
/-- Express `edist` in terms of `nndist`-/
theorem edist_nndist (x y : α) : edist x y = ↑(nndist x y) := by
  simpa only [edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg]
#align edist_nndist edist_nndist
-/

#print coe_nnreal_ennreal_nndist /-
@[simp, norm_cast]
theorem coe_nnreal_ennreal_nndist (x y : α) : ↑(nndist x y) = edist x y :=
  (edist_nndist x y).symm
#align coe_nnreal_ennreal_nndist coe_nnreal_ennreal_nndist
-/

/- warning: edist_lt_coe -> edist_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) c)) (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.some c)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
Case conversion may be inaccurate. Consider using '#align edist_lt_coe edist_lt_coeₓ'. -/
@[simp, norm_cast]
theorem edist_lt_coe {x y : α} {c : ℝ≥0} : edist x y < c ↔ nndist x y < c := by
  rw [edist_nndist, ENNReal.coe_lt_coe]
#align edist_lt_coe edist_lt_coe

/- warning: edist_le_coe -> edist_le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) c)) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.some c)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
Case conversion may be inaccurate. Consider using '#align edist_le_coe edist_le_coeₓ'. -/
@[simp, norm_cast]
theorem edist_le_coe {x y : α} {c : ℝ≥0} : edist x y ≤ c ↔ nndist x y ≤ c := by
  rw [edist_nndist, ENNReal.coe_le_coe]
#align edist_le_coe edist_le_coe

/- warning: edist_lt_top -> edist_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (x : α) (y : α), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_2) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] (x : α) (y : α), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_2) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align edist_lt_top edist_lt_topₓ'. -/
/-- In a pseudometric space, the extended distance is always finite-/
theorem edist_lt_top {α : Type _} [PseudoMetricSpace α] (x y : α) : edist x y < ⊤ :=
  (edist_dist x y).symm ▸ ENNReal.ofReal_lt_top
#align edist_lt_top edist_lt_top

/- warning: edist_ne_top -> edist_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align edist_ne_top edist_ne_topₓ'. -/
/-- In a pseudometric space, the extended distance is always finite-/
theorem edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
  (edist_lt_top x y).Ne
#align edist_ne_top edist_ne_top

/- warning: nndist_self -> nndist_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (a : α), Eq.{1} NNReal (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) a a) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (a : α), Eq.{1} NNReal (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) a a) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nndist_self nndist_selfₓ'. -/
/-- `nndist x x` vanishes-/
@[simp]
theorem nndist_self (a : α) : nndist a a = 0 :=
  (NNReal.coe_eq_zero _).1 (dist_self a)
#align nndist_self nndist_self

/- warning: dist_nndist -> dist_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α), Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α), Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (NNReal.toReal (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y))
Case conversion may be inaccurate. Consider using '#align dist_nndist dist_nndistₓ'. -/
/-- Express `dist` in terms of `nndist`-/
theorem dist_nndist (x y : α) : dist x y = ↑(nndist x y) :=
  rfl
#align dist_nndist dist_nndist

/- warning: coe_nndist -> coe_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α), Eq.{1} Real (NNReal.toReal (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)
Case conversion may be inaccurate. Consider using '#align coe_nndist coe_nndistₓ'. -/
@[simp, norm_cast]
theorem coe_nndist (x y : α) : ↑(nndist x y) = dist x y :=
  (dist_nndist x y).symm
#align coe_nndist coe_nndist

/- warning: dist_lt_coe -> dist_lt_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) c)) (LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (NNReal.toReal c)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
Case conversion may be inaccurate. Consider using '#align dist_lt_coe dist_lt_coeₓ'. -/
@[simp, norm_cast]
theorem dist_lt_coe {x y : α} {c : ℝ≥0} : dist x y < c ↔ nndist x y < c :=
  Iff.rfl
#align dist_lt_coe dist_lt_coe

/- warning: dist_le_coe -> dist_le_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) c)) (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {c : NNReal}, Iff (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (NNReal.toReal c)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) c)
Case conversion may be inaccurate. Consider using '#align dist_le_coe dist_le_coeₓ'. -/
@[simp, norm_cast]
theorem dist_le_coe {x y : α} {c : ℝ≥0} : dist x y ≤ c ↔ nndist x y ≤ c :=
  Iff.rfl
#align dist_le_coe dist_le_coe

/- warning: edist_lt_of_real -> edist_lt_ofReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {r : Real}, Iff (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.ofReal r)) (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {r : Real}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.ofReal r)) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r)
Case conversion may be inaccurate. Consider using '#align edist_lt_of_real edist_lt_ofRealₓ'. -/
@[simp]
theorem edist_lt_ofReal {x y : α} {r : ℝ} : edist x y < ENNReal.ofReal r ↔ dist x y < r := by
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
#align edist_lt_of_real edist_lt_ofReal

/- warning: edist_le_of_real -> edist_le_ofReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Iff (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.ofReal r)) (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) r))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) x y) (ENNReal.ofReal r)) (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) r))
Case conversion may be inaccurate. Consider using '#align edist_le_of_real edist_le_ofRealₓ'. -/
@[simp]
theorem edist_le_ofReal {x y : α} {r : ℝ} (hr : 0 ≤ r) :
    edist x y ≤ ENNReal.ofReal r ↔ dist x y ≤ r := by
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr]
#align edist_le_of_real edist_le_ofReal

#print nndist_dist /-
/-- Express `nndist` in terms of `dist`-/
theorem nndist_dist (x y : α) : nndist x y = Real.toNNReal (dist x y) := by
  rw [dist_nndist, Real.toNNReal_coe]
#align nndist_dist nndist_dist
-/

#print nndist_comm /-
theorem nndist_comm (x y : α) : nndist x y = nndist y x := by
  simpa only [dist_nndist, NNReal.coe_eq] using dist_comm x y
#align nndist_comm nndist_comm
-/

/- warning: nndist_triangle -> nndist_triangle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x z) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x z) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align nndist_triangle nndist_triangleₓ'. -/
/-- Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
  dist_triangle _ _ _
#align nndist_triangle nndist_triangle

/- warning: nndist_triangle_left -> nndist_triangle_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) z x) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) z y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) z x) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) z y))
Case conversion may be inaccurate. Consider using '#align nndist_triangle_left nndist_triangle_leftₓ'. -/
theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
  dist_triangle_left _ _ _
#align nndist_triangle_left nndist_triangle_left

/- warning: nndist_triangle_right -> nndist_triangle_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x z) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x z) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align nndist_triangle_right nndist_triangle_rightₓ'. -/
theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
  dist_triangle_right _ _ _
#align nndist_triangle_right nndist_triangle_right

#print dist_edist /-
/-- Express `dist` in terms of `edist`-/
theorem dist_edist (x y : α) : dist x y = (edist x y).toReal := by
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
#align dist_edist dist_edist
-/

namespace Metric

-- instantiate pseudometric space as a topology
variable {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : Set α}

#print Metric.ball /-
/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }
#align metric.ball Metric.ball
-/

/- warning: metric.mem_ball -> Metric.mem_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y x) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y x) ε)
Case conversion may be inaccurate. Consider using '#align metric.mem_ball Metric.mem_ballₓ'. -/
@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl
#align metric.mem_ball Metric.mem_ball

/- warning: metric.mem_ball' -> Metric.mem_ball' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) ε)
Case conversion may be inaccurate. Consider using '#align metric.mem_ball' Metric.mem_ball'ₓ'. -/
theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw [dist_comm, mem_ball]
#align metric.mem_ball' Metric.mem_ball'

/- warning: metric.pos_of_mem_ball -> Metric.pos_of_mem_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε)
Case conversion may be inaccurate. Consider using '#align metric.pos_of_mem_ball Metric.pos_of_mem_ballₓ'. -/
theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  dist_nonneg.trans_lt hy
#align metric.pos_of_mem_ball Metric.pos_of_mem_ball

/- warning: metric.mem_ball_self -> Metric.mem_ball_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.ball.{u1} α _inst_1 x ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.ball.{u1} α _inst_1 x ε))
Case conversion may be inaccurate. Consider using '#align metric.mem_ball_self Metric.mem_ball_selfₓ'. -/
theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
  show dist x x < ε by rw [dist_self] <;> assumption
#align metric.mem_ball_self Metric.mem_ball_self

/- warning: metric.nonempty_ball -> Metric.nonempty_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Set.Nonempty.{u1} α (Metric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Set.Nonempty.{u1} α (Metric.ball.{u1} α _inst_1 x ε)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε)
Case conversion may be inaccurate. Consider using '#align metric.nonempty_ball Metric.nonempty_ballₓ'. -/
@[simp]
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩
#align metric.nonempty_ball Metric.nonempty_ball

/- warning: metric.ball_eq_empty -> Metric.ball_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Eq.{succ u1} (Set.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (LE.le.{0} Real Real.hasLe ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Eq.{succ u1} (Set.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (LE.le.{0} Real Real.instLEReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.ball_eq_empty Metric.ball_eq_emptyₓ'. -/
@[simp]
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]
#align metric.ball_eq_empty Metric.ball_eq_empty

/- warning: metric.ball_zero -> Metric.ball_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Eq.{succ u1} (Set.{u1} α) (Metric.ball.{u1} α _inst_1 x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Eq.{succ u1} (Set.{u1} α) (Metric.ball.{u1} α _inst_1 x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align metric.ball_zero Metric.ball_zeroₓ'. -/
@[simp]
theorem ball_zero : ball x 0 = ∅ := by rw [ball_eq_empty]
#align metric.ball_zero Metric.ball_zero

/- warning: metric.exists_lt_mem_ball_of_mem_ball -> Metric.exists_lt_mem_ball_of_mem_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.ball.{u1} α _inst_1 y ε)) -> (Exists.{1} Real (fun (ε' : Real) => Exists.{0} (LT.lt.{0} Real Real.hasLt ε' ε) (fun (H : LT.lt.{0} Real Real.hasLt ε' ε) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.ball.{u1} α _inst_1 y ε'))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.ball.{u1} α _inst_1 y ε)) -> (Exists.{1} Real (fun (ε' : Real) => And (LT.lt.{0} Real Real.instLTReal ε' ε) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.ball.{u1} α _inst_1 y ε'))))
Case conversion may be inaccurate. Consider using '#align metric.exists_lt_mem_ball_of_mem_ball Metric.exists_lt_mem_ball_of_mem_ballₓ'. -/
/-- If a point belongs to an open ball, then there is a strictly smaller radius whose ball also
contains it.

See also `exists_lt_subset_ball`. -/
theorem exists_lt_mem_ball_of_mem_ball (h : x ∈ ball y ε) : ∃ ε' < ε, x ∈ ball y ε' :=
  by
  simp only [mem_ball] at h⊢
  exact ⟨(ε + dist x y) / 2, by linarith, by linarith⟩
#align metric.exists_lt_mem_ball_of_mem_ball Metric.exists_lt_mem_ball_of_mem_ball

/- warning: metric.ball_eq_ball -> Metric.ball_eq_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (ε : Real) (x : α), Eq.{succ u1} (Set.{u1} α) (UniformSpace.ball.{u1} α x (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.snd.{u1, u1} α α p) (Prod.fst.{u1, u1} α α p)) ε))) (Metric.ball.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (ε : Real) (x : α), Eq.{succ u1} (Set.{u1} α) (UniformSpace.ball.{u1} α x (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.snd.{u1, u1} α α p) (Prod.fst.{u1, u1} α α p)) ε))) (Metric.ball.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.ball_eq_ball Metric.ball_eq_ballₓ'. -/
theorem ball_eq_ball (ε : ℝ) (x : α) :
    UniformSpace.ball x { p | dist p.2 p.1 < ε } = Metric.ball x ε :=
  rfl
#align metric.ball_eq_ball Metric.ball_eq_ball

/- warning: metric.ball_eq_ball' -> Metric.ball_eq_ball' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (ε : Real) (x : α), Eq.{succ u1} (Set.{u1} α) (UniformSpace.ball.{u1} α x (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))) (Metric.ball.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (ε : Real) (x : α), Eq.{succ u1} (Set.{u1} α) (UniformSpace.ball.{u1} α x (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))) (Metric.ball.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.ball_eq_ball' Metric.ball_eq_ball'ₓ'. -/
theorem ball_eq_ball' (ε : ℝ) (x : α) :
    UniformSpace.ball x { p | dist p.1 p.2 < ε } = Metric.ball x ε :=
  by
  ext
  simp [dist_comm, UniformSpace.ball]
#align metric.ball_eq_ball' Metric.ball_eq_ball'

/- warning: metric.Union_ball_nat -> Metric.iUnion_ball_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (Nat.cast.{0} Real Real.natCast n))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align metric.Union_ball_nat Metric.iUnion_ball_natₓ'. -/
@[simp]
theorem iUnion_ball_nat (x : α) : (⋃ n : ℕ, ball x n) = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_gt (dist y x)
#align metric.Union_ball_nat Metric.iUnion_ball_nat

/- warning: metric.Union_ball_nat_succ -> Metric.iUnion_ball_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align metric.Union_ball_nat_succ Metric.iUnion_ball_nat_succₓ'. -/
@[simp]
theorem iUnion_ball_nat_succ (x : α) : (⋃ n : ℕ, ball x (n + 1)) = univ :=
  iUnion_eq_univ_iff.2 fun y => (exists_nat_gt (dist y x)).imp fun n hn => hn.trans (lt_add_one _)
#align metric.Union_ball_nat_succ Metric.iUnion_ball_nat_succ

#print Metric.closedBall /-
/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }
#align metric.closed_ball Metric.closedBall
-/

/- warning: metric.mem_closed_ball -> Metric.mem_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y x) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y x) ε)
Case conversion may be inaccurate. Consider using '#align metric.mem_closed_ball Metric.mem_closedBallₓ'. -/
@[simp]
theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε :=
  Iff.rfl
#align metric.mem_closed_ball Metric.mem_closedBall

/- warning: metric.mem_closed_ball' -> Metric.mem_closedBall' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) ε)
Case conversion may be inaccurate. Consider using '#align metric.mem_closed_ball' Metric.mem_closedBall'ₓ'. -/
theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closed_ball]
#align metric.mem_closed_ball' Metric.mem_closedBall'

#print Metric.sphere /-
/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : ℝ) :=
  { y | dist y x = ε }
#align metric.sphere Metric.sphere
-/

#print Metric.mem_sphere /-
@[simp]
theorem mem_sphere : y ∈ sphere x ε ↔ dist y x = ε :=
  Iff.rfl
#align metric.mem_sphere Metric.mem_sphere
-/

#print Metric.mem_sphere' /-
theorem mem_sphere' : y ∈ sphere x ε ↔ dist x y = ε := by rw [dist_comm, mem_sphere]
#align metric.mem_sphere' Metric.mem_sphere'
-/

/- warning: metric.ne_of_mem_sphere -> Metric.ne_of_mem_sphere is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.sphere.{u1} α _inst_1 x ε)) -> (Ne.{1} Real ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Ne.{succ u1} α y x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.sphere.{u1} α _inst_1 x ε)) -> (Ne.{1} Real ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Ne.{succ u1} α y x)
Case conversion may be inaccurate. Consider using '#align metric.ne_of_mem_sphere Metric.ne_of_mem_sphereₓ'. -/
theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : y ≠ x :=
  by
  contrapose! hε
  symm
  simpa [hε] using h
#align metric.ne_of_mem_sphere Metric.ne_of_mem_sphere

/- warning: metric.sphere_eq_empty_of_subsingleton -> Metric.sphere_eq_empty_of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real} [_inst_2 : Subsingleton.{succ u1} α], (Ne.{1} Real ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{succ u1} (Set.{u1} α) (Metric.sphere.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real} [_inst_2 : Subsingleton.{succ u1} α], (Ne.{1} Real ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{succ u1} (Set.{u1} α) (Metric.sphere.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align metric.sphere_eq_empty_of_subsingleton Metric.sphere_eq_empty_of_subsingletonₓ'. -/
theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun y hy => ne_of_mem_sphere hy hε (Subsingleton.elim _ _)
#align metric.sphere_eq_empty_of_subsingleton Metric.sphere_eq_empty_of_subsingleton

/- warning: metric.sphere_is_empty_of_subsingleton -> Metric.sphere_isEmpty_of_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real} [_inst_2 : Subsingleton.{succ u1} α], (Ne.{1} Real ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (IsEmpty.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Metric.sphere.{u1} α _inst_1 x ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real} [_inst_2 : Subsingleton.{succ u1} α], (Ne.{1} Real ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (IsEmpty.{succ u1} (Set.Elem.{u1} α (Metric.sphere.{u1} α _inst_1 x ε)))
Case conversion may be inaccurate. Consider using '#align metric.sphere_is_empty_of_subsingleton Metric.sphere_isEmpty_of_subsingletonₓ'. -/
theorem sphere_isEmpty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : IsEmpty (sphere x ε) := by
  simp only [sphere_eq_empty_of_subsingleton hε, Set.hasEmptyc.Emptyc.isEmpty α]
#align metric.sphere_is_empty_of_subsingleton Metric.sphere_isEmpty_of_subsingleton

/- warning: metric.mem_closed_ball_self -> Metric.mem_closedBall_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Metric.closedBall.{u1} α _inst_1 x ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Metric.closedBall.{u1} α _inst_1 x ε))
Case conversion may be inaccurate. Consider using '#align metric.mem_closed_ball_self Metric.mem_closedBall_selfₓ'. -/
theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall x ε :=
  show dist x x ≤ ε by rw [dist_self] <;> assumption
#align metric.mem_closed_ball_self Metric.mem_closedBall_self

/- warning: metric.nonempty_closed_ball -> Metric.nonempty_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Set.Nonempty.{u1} α (Metric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Set.Nonempty.{u1} α (Metric.closedBall.{u1} α _inst_1 x ε)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε)
Case conversion may be inaccurate. Consider using '#align metric.nonempty_closed_ball Metric.nonempty_closedBallₓ'. -/
@[simp]
theorem nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩
#align metric.nonempty_closed_ball Metric.nonempty_closedBall

/- warning: metric.closed_ball_eq_empty -> Metric.closedBall_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Eq.{succ u1} (Set.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (LT.lt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Iff (Eq.{succ u1} (Set.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (LT.lt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_eq_empty Metric.closedBall_eq_emptyₓ'. -/
@[simp]
theorem closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_closed_ball, not_le]
#align metric.closed_ball_eq_empty Metric.closedBall_eq_empty

#print Metric.ball_subset_closedBall /-
theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun y (hy : _ < _) => le_of_lt hy
#align metric.ball_subset_closed_ball Metric.ball_subset_closedBall
-/

#print Metric.sphere_subset_closedBall /-
theorem sphere_subset_closedBall : sphere x ε ⊆ closedBall x ε := fun y => le_of_eq
#align metric.sphere_subset_closed_ball Metric.sphere_subset_closedBall
-/

/- warning: metric.closed_ball_disjoint_ball -> Metric.closedBall_disjoint_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.closedBall.{u1} α _inst_1 x δ) (Metric.ball.{u1} α _inst_1 y ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.closedBall.{u1} α _inst_1 x δ) (Metric.ball.{u1} α _inst_1 y ε))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_disjoint_ball Metric.closedBall_disjoint_ballₓ'. -/
theorem closedBall_disjoint_ball (h : δ + ε ≤ dist x y) : Disjoint (closedBall x δ) (ball y ε) :=
  Set.disjoint_left.mpr fun a ha1 ha2 =>
    (h.trans <| dist_triangle_left _ _ _).not_lt <| add_lt_add_of_le_of_lt ha1 ha2
#align metric.closed_ball_disjoint_ball Metric.closedBall_disjoint_ball

/- warning: metric.ball_disjoint_closed_ball -> Metric.ball_disjoint_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.ball.{u1} α _inst_1 x δ) (Metric.closedBall.{u1} α _inst_1 y ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.ball.{u1} α _inst_1 x δ) (Metric.closedBall.{u1} α _inst_1 y ε))
Case conversion may be inaccurate. Consider using '#align metric.ball_disjoint_closed_ball Metric.ball_disjoint_closedBallₓ'. -/
theorem ball_disjoint_closedBall (h : δ + ε ≤ dist x y) : Disjoint (ball x δ) (closedBall y ε) :=
  (closedBall_disjoint_ball <| by rwa [add_comm, dist_comm]).symm
#align metric.ball_disjoint_closed_ball Metric.ball_disjoint_closedBall

/- warning: metric.ball_disjoint_ball -> Metric.ball_disjoint_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.ball.{u1} α _inst_1 x δ) (Metric.ball.{u1} α _inst_1 y ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.ball.{u1} α _inst_1 x δ) (Metric.ball.{u1} α _inst_1 y ε))
Case conversion may be inaccurate. Consider using '#align metric.ball_disjoint_ball Metric.ball_disjoint_ballₓ'. -/
theorem ball_disjoint_ball (h : δ + ε ≤ dist x y) : Disjoint (ball x δ) (ball y ε) :=
  (closedBall_disjoint_ball h).mono_left ball_subset_closedBall
#align metric.ball_disjoint_ball Metric.ball_disjoint_ball

/- warning: metric.closed_ball_disjoint_closed_ball -> Metric.closedBall_disjoint_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LT.lt.{0} Real Real.hasLt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.closedBall.{u1} α _inst_1 x δ) (Metric.closedBall.{u1} α _inst_1 y ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {δ : Real} {ε : Real}, (LT.lt.{0} Real Real.instLTReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) δ ε) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) -> (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.closedBall.{u1} α _inst_1 x δ) (Metric.closedBall.{u1} α _inst_1 y ε))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_disjoint_closed_ball Metric.closedBall_disjoint_closedBallₓ'. -/
theorem closedBall_disjoint_closedBall (h : δ + ε < dist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) :=
  Set.disjoint_left.mpr fun a ha1 ha2 =>
    h.not_le <| (dist_triangle_left _ _ _).trans <| add_le_add ha1 ha2
#align metric.closed_ball_disjoint_closed_ball Metric.closedBall_disjoint_closedBall

/- warning: metric.sphere_disjoint_ball -> Metric.sphere_disjoint_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Metric.sphere.{u1} α _inst_1 x ε) (Metric.ball.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Metric.sphere.{u1} α _inst_1 x ε) (Metric.ball.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.sphere_disjoint_ball Metric.sphere_disjoint_ballₓ'. -/
theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
  Set.disjoint_left.mpr fun y hy₁ hy₂ => absurd hy₁ <| ne_of_lt hy₂
#align metric.sphere_disjoint_ball Metric.sphere_disjoint_ball

/- warning: metric.ball_union_sphere -> Metric.ball_union_sphere is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) (Metric.sphere.{u1} α _inst_1 x ε)) (Metric.closedBall.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) (Metric.sphere.{u1} α _inst_1 x ε)) (Metric.closedBall.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.ball_union_sphere Metric.ball_union_sphereₓ'. -/
@[simp]
theorem ball_union_sphere : ball x ε ∪ sphere x ε = closedBall x ε :=
  Set.ext fun y => (@le_iff_lt_or_eq ℝ _ _ _).symm
#align metric.ball_union_sphere Metric.ball_union_sphere

/- warning: metric.sphere_union_ball -> Metric.sphere_union_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Metric.sphere.{u1} α _inst_1 x ε) (Metric.ball.{u1} α _inst_1 x ε)) (Metric.closedBall.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Metric.sphere.{u1} α _inst_1 x ε) (Metric.ball.{u1} α _inst_1 x ε)) (Metric.closedBall.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.sphere_union_ball Metric.sphere_union_ballₓ'. -/
@[simp]
theorem sphere_union_ball : sphere x ε ∪ ball x ε = closedBall x ε := by
  rw [union_comm, ball_union_sphere]
#align metric.sphere_union_ball Metric.sphere_union_ball

/- warning: metric.closed_ball_diff_sphere -> Metric.closedBall_diff_sphere is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Metric.closedBall.{u1} α _inst_1 x ε) (Metric.sphere.{u1} α _inst_1 x ε)) (Metric.ball.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (Metric.sphere.{u1} α _inst_1 x ε)) (Metric.ball.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_diff_sphere Metric.closedBall_diff_sphereₓ'. -/
@[simp]
theorem closedBall_diff_sphere : closedBall x ε \ sphere x ε = ball x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_right sphere_disjoint_ball.symm.le_bot]
#align metric.closed_ball_diff_sphere Metric.closedBall_diff_sphere

/- warning: metric.closed_ball_diff_ball -> Metric.closedBall_diff_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Metric.closedBall.{u1} α _inst_1 x ε) (Metric.ball.{u1} α _inst_1 x ε)) (Metric.sphere.{u1} α _inst_1 x ε)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (Metric.ball.{u1} α _inst_1 x ε)) (Metric.sphere.{u1} α _inst_1 x ε)
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_diff_ball Metric.closedBall_diff_ballₓ'. -/
@[simp]
theorem closedBall_diff_ball : closedBall x ε \ ball x ε = sphere x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_left sphere_disjoint_ball.symm.le_bot]
#align metric.closed_ball_diff_ball Metric.closedBall_diff_ball

#print Metric.mem_ball_comm /-
theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]
#align metric.mem_ball_comm Metric.mem_ball_comm
-/

#print Metric.mem_closedBall_comm /-
theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closed_ball', mem_closed_ball]
#align metric.mem_closed_ball_comm Metric.mem_closedBall_comm
-/

#print Metric.mem_sphere_comm /-
theorem mem_sphere_comm : x ∈ sphere y ε ↔ y ∈ sphere x ε := by rw [mem_sphere', mem_sphere]
#align metric.mem_sphere_comm Metric.mem_sphere_comm
-/

/- warning: metric.ball_subset_ball -> Metric.ball_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.hasLe ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 x ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.instLEReal ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 x ε₂))
Case conversion may be inaccurate. Consider using '#align metric.ball_subset_ball Metric.ball_subset_ballₓ'. -/
theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h
#align metric.ball_subset_ball Metric.ball_subset_ball

/- warning: metric.closed_ball_eq_bInter_ball -> Metric.closedBall_eq_bInter_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (GT.gt.{0} Real Real.hasLt δ ε) (fun (H : GT.gt.{0} Real Real.hasLt δ ε) => Metric.ball.{u1} α _inst_1 x δ)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, Eq.{succ u1} (Set.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (Set.iInter.{u1, 1} α Real (fun (δ : Real) => Set.iInter.{u1, 0} α (GT.gt.{0} Real Real.instLTReal δ ε) (fun (H : GT.gt.{0} Real Real.instLTReal δ ε) => Metric.ball.{u1} α _inst_1 x δ)))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_eq_bInter_ball Metric.closedBall_eq_bInter_ballₓ'. -/
theorem closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ := by
  ext y <;> rw [mem_closed_ball, ← forall_lt_iff_le', mem_Inter₂] <;> rfl
#align metric.closed_ball_eq_bInter_ball Metric.closedBall_eq_bInter_ball

/- warning: metric.ball_subset_ball' -> Metric.ball_subset_ball' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))
Case conversion may be inaccurate. Consider using '#align metric.ball_subset_ball' Metric.ball_subset_ball'ₓ'. -/
theorem ball_subset_ball' (h : ε₁ + dist x y ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < ε₁ + dist x y := (add_lt_add_right hz _)
    _ ≤ ε₂ := h
    
#align metric.ball_subset_ball' Metric.ball_subset_ball'

/- warning: metric.closed_ball_subset_closed_ball -> Metric.closedBall_subset_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.hasLe ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 x ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.instLEReal ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 x ε₂))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_subset_closed_ball Metric.closedBall_subset_closedBallₓ'. -/
theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun y (yx : _ ≤ ε₁) => le_trans yx h
#align metric.closed_ball_subset_closed_ball Metric.closedBall_subset_closedBall

/- warning: metric.closed_ball_subset_closed_ball' -> Metric.closedBall_subset_closedBall' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.hasLe (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 y ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.instLEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 y ε₂))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_subset_closed_ball' Metric.closedBall_subset_closedBall'ₓ'. -/
theorem closedBall_subset_closedBall' (h : ε₁ + dist x y ≤ ε₂) :
    closedBall x ε₁ ⊆ closedBall y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := (add_le_add_right hz _)
    _ ≤ ε₂ := h
    
#align metric.closed_ball_subset_closed_ball' Metric.closedBall_subset_closedBall'

/- warning: metric.closed_ball_subset_ball -> Metric.closedBall_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε₁ : Real} {ε₂ : Real}, (LT.lt.{0} Real Real.hasLt ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 x ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε₁ : Real} {ε₂ : Real}, (LT.lt.{0} Real Real.instLTReal ε₁ ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 x ε₂))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_subset_ball Metric.closedBall_subset_ballₓ'. -/
theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ ⊆ ball x ε₂ :=
  fun y (yh : dist y x ≤ ε₁) => lt_of_le_of_lt yh h
#align metric.closed_ball_subset_ball Metric.closedBall_subset_ball

/- warning: metric.closed_ball_subset_ball' -> Metric.closedBall_subset_ball' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LT.lt.{0} Real Real.hasLt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LT.lt.{0} Real Real.instLTReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) ε₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_subset_ball' Metric.closedBall_subset_ball'ₓ'. -/
theorem closedBall_subset_ball' (h : ε₁ + dist x y < ε₂) : closedBall x ε₁ ⊆ ball y ε₂ :=
  fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := (add_le_add_right hz _)
    _ < ε₂ := h
    
#align metric.closed_ball_subset_ball' Metric.closedBall_subset_ball'

/- warning: metric.dist_le_add_of_nonempty_closed_ball_inter_closed_ball -> Metric.dist_le_add_of_nonempty_closedBall_inter_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 y ε₂))) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 y ε₂))) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ ε₂))
Case conversion may be inaccurate. Consider using '#align metric.dist_le_add_of_nonempty_closed_ball_inter_closed_ball Metric.dist_le_add_of_nonempty_closedBall_inter_closedBallₓ'. -/
theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall x ε₁ ∩ closedBall y ε₂).Nonempty) : dist x y ≤ ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hz.1 hz.2
    
#align metric.dist_le_add_of_nonempty_closed_ball_inter_closed_ball Metric.dist_le_add_of_nonempty_closedBall_inter_closedBall

/- warning: metric.dist_lt_add_of_nonempty_closed_ball_inter_ball -> Metric.dist_lt_add_of_nonempty_closedBall_inter_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ ε₂))
Case conversion may be inaccurate. Consider using '#align metric.dist_lt_add_of_nonempty_closed_ball_inter_ball Metric.dist_lt_add_of_nonempty_closedBall_inter_ballₓ'. -/
theorem dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2
    
#align metric.dist_lt_add_of_nonempty_closed_ball_inter_ball Metric.dist_lt_add_of_nonempty_closedBall_inter_ball

/- warning: metric.dist_lt_add_of_nonempty_ball_inter_closed_ball -> Metric.dist_lt_add_of_nonempty_ball_inter_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 y ε₂))) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.closedBall.{u1} α _inst_1 y ε₂))) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ ε₂))
Case conversion may be inaccurate. Consider using '#align metric.dist_lt_add_of_nonempty_ball_inter_closed_ball Metric.dist_lt_add_of_nonempty_ball_inter_closedBallₓ'. -/
theorem dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ ∩ closedBall y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm, dist_comm]
  exact dist_lt_add_of_nonempty_closed_ball_inter_ball h
#align metric.dist_lt_add_of_nonempty_ball_inter_closed_ball Metric.dist_lt_add_of_nonempty_ball_inter_closedBall

/- warning: metric.dist_lt_add_of_nonempty_ball_inter_ball -> Metric.dist_lt_add_of_nonempty_ball_inter_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ε₁ ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) ε₁ ε₂))
Case conversion may be inaccurate. Consider using '#align metric.dist_lt_add_of_nonempty_ball_inter_ball Metric.dist_lt_add_of_nonempty_ball_inter_ballₓ'. -/
theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  dist_lt_add_of_nonempty_closedBall_inter_ball <|
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)
#align metric.dist_lt_add_of_nonempty_ball_inter_ball Metric.dist_lt_add_of_nonempty_ball_inter_ball

/- warning: metric.Union_closed_ball_nat -> Metric.iUnion_closedBall_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Metric.closedBall.{u1} α _inst_1 x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Metric.closedBall.{u1} α _inst_1 x (Nat.cast.{0} Real Real.natCast n))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align metric.Union_closed_ball_nat Metric.iUnion_closedBall_natₓ'. -/
@[simp]
theorem iUnion_closedBall_nat (x : α) : (⋃ n : ℕ, closedBall x n) = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_ge (dist y x)
#align metric.Union_closed_ball_nat Metric.iUnion_closedBall_nat

/- warning: metric.Union_inter_closed_ball_nat -> Metric.iUnion_inter_closedBall_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α) (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Metric.closedBall.{u1} α _inst_1 x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (s : Set.{u1} α) (x : α), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (n : Nat) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Metric.closedBall.{u1} α _inst_1 x (Nat.cast.{0} Real Real.natCast n)))) s
Case conversion may be inaccurate. Consider using '#align metric.Union_inter_closed_ball_nat Metric.iUnion_inter_closedBall_natₓ'. -/
theorem iUnion_inter_closedBall_nat (s : Set α) (x : α) : (⋃ n : ℕ, s ∩ closedBall x n) = s := by
  rw [← inter_Union, Union_closed_ball_nat, inter_univ]
#align metric.Union_inter_closed_ball_nat Metric.iUnion_inter_closedBall_nat

/- warning: metric.ball_subset -> Metric.ball_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ε₂ ε₁)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε₁ : Real} {ε₂ : Real}, (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) ε₂ ε₁)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε₁) (Metric.ball.{u1} α _inst_1 y ε₂))
Case conversion may be inaccurate. Consider using '#align metric.ball_subset Metric.ball_subsetₓ'. -/
theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ := fun z zx => by
  rw [← add_sub_cancel'_right ε₁ ε₂] <;>
    exact lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)
#align metric.ball_subset Metric.ball_subset

/- warning: metric.ball_half_subset -> Metric.ball_half_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real} (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.ball.{u1} α _inst_1 x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ε (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ε (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Metric.ball.{u1} α _inst_1 x ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real} (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.ball.{u1} α _inst_1 x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) ε (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) ε (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Metric.ball.{u1} α _inst_1 x ε))
Case conversion may be inaccurate. Consider using '#align metric.ball_half_subset Metric.ball_half_subsetₓ'. -/
theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
  ball_subset <| by rw [sub_self_div_two] <;> exact le_of_lt h
#align metric.ball_half_subset Metric.ball_half_subset

/- warning: metric.exists_ball_subset_ball -> Metric.exists_ball_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) -> (Exists.{1} Real (fun (ε' : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε' (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε' (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 y ε') (Metric.ball.{u1} α _inst_1 x ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {ε : Real}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) -> (Exists.{1} Real (fun (ε' : Real) => And (GT.gt.{0} Real Real.instLTReal ε' (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 y ε') (Metric.ball.{u1} α _inst_1 x ε))))
Case conversion may be inaccurate. Consider using '#align metric.exists_ball_subset_ball Metric.exists_ball_subset_ballₓ'. -/
theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
  ⟨_, sub_pos.2 h, ball_subset <| by rw [sub_sub_self]⟩
#align metric.exists_ball_subset_ball Metric.exists_ball_subset_ball

#print Metric.forall_of_forall_mem_closedBall /-
/-- If a property holds for all points in closed balls of arbitrarily large radii, then it holds for
all points. -/
theorem forall_of_forall_mem_closedBall (p : α → Prop) (x : α)
    (H : ∃ᶠ R : ℝ in atTop, ∀ y ∈ closedBall x R, p y) (y : α) : p y :=
  by
  obtain ⟨R, hR, h⟩ : ∃ (R : ℝ)(H : dist y x ≤ R), ∀ z : α, z ∈ closed_ball x R → p z :=
    frequently_iff.1 H (Ici_mem_at_top (dist y x))
  exact h _ hR
#align metric.forall_of_forall_mem_closed_ball Metric.forall_of_forall_mem_closedBall
-/

#print Metric.forall_of_forall_mem_ball /-
/-- If a property holds for all points in balls of arbitrarily large radii, then it holds for all
points. -/
theorem forall_of_forall_mem_ball (p : α → Prop) (x : α)
    (H : ∃ᶠ R : ℝ in atTop, ∀ y ∈ ball x R, p y) (y : α) : p y :=
  by
  obtain ⟨R, hR, h⟩ : ∃ (R : ℝ)(H : dist y x < R), ∀ z : α, z ∈ ball x R → p z :=
    frequently_iff.1 H (Ioi_mem_at_top (dist y x))
  exact h _ hR
#align metric.forall_of_forall_mem_ball Metric.forall_of_forall_mem_ball
-/

/- warning: metric.is_bounded_iff -> Metric.isBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Exists.{1} Real (fun (C : Real) => forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {{y : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) C))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Exists.{1} Real (fun (C : Real) => forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {{y : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) C))))
Case conversion may be inaccurate. Consider using '#align metric.is_bounded_iff Metric.isBounded_iffₓ'. -/
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [is_bounded_def, ← Filter.mem_sets, (@PseudoMetricSpace.cobounded_sets α _).out, mem_set_of_eq,
    compl_compl]
#align metric.is_bounded_iff Metric.isBounded_iff

/- warning: metric.is_bounded_iff_eventually -> Metric.isBounded_iff_eventually is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Filter.Eventually.{0} Real (fun (C : Real) => forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {{y : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) C))) (Filter.atTop.{0} Real Real.preorder))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Filter.Eventually.{0} Real (fun (C : Real) => forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {{y : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) C))) (Filter.atTop.{0} Real Real.instPreorderReal))
Case conversion may be inaccurate. Consider using '#align metric.is_bounded_iff_eventually Metric.isBounded_iff_eventuallyₓ'. -/
theorem isBounded_iff_eventually {s : Set α} :
    IsBounded s ↔ ∀ᶠ C in atTop, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
  isBounded_iff.trans
    ⟨fun ⟨C, h⟩ => eventually_atTop.2 ⟨C, fun C' hC' x hx y hy => (h hx hy).trans hC'⟩,
      Eventually.exists⟩
#align metric.is_bounded_iff_eventually Metric.isBounded_iff_eventually

/- warning: metric.is_bounded_iff_exists_ge -> Metric.isBounded_iff_exists_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} (c : Real), Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Exists.{1} Real (fun (C : Real) => And (LE.le.{0} Real Real.hasLe c C) (forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {{y : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) C)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} (c : Real), Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Exists.{1} Real (fun (C : Real) => And (LE.le.{0} Real Real.instLEReal c C) (forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {{y : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) C)))))
Case conversion may be inaccurate. Consider using '#align metric.is_bounded_iff_exists_ge Metric.isBounded_iff_exists_geₓ'. -/
theorem isBounded_iff_exists_ge {s : Set α} (c : ℝ) :
    IsBounded s ↔ ∃ C, c ≤ C ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
  ⟨fun h => ((eventually_ge_atTop c).And (isBounded_iff_eventually.1 h)).exists, fun h =>
    isBounded_iff.2 <| h.imp fun _ => And.right⟩
#align metric.is_bounded_iff_exists_ge Metric.isBounded_iff_exists_ge

/- warning: metric.is_bounded_iff_nndist -> Metric.isBounded_iff_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Exists.{1} NNReal (fun (C : NNReal) => forall {{x : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall {{y : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) C))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (PseudoMetricSpace.toBornology.{u1} α _inst_1) s) (Exists.{1} NNReal (fun (C : NNReal) => forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {{y : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) x y) C))))
Case conversion may be inaccurate. Consider using '#align metric.is_bounded_iff_nndist Metric.isBounded_iff_nndistₓ'. -/
theorem isBounded_iff_nndist {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ≥0, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → nndist x y ≤ C := by
  simp only [is_bounded_iff_exists_ge 0, NNReal.exists, ← NNReal.coe_le_coe, ← dist_nndist,
    NNReal.coe_mk, exists_prop]
#align metric.is_bounded_iff_nndist Metric.isBounded_iff_nndist

#print Metric.toUniformSpace_eq /-
theorem toUniformSpace_eq :
    ‹PseudoMetricSpace α›.toUniformSpace =
      UniformSpace.ofDist dist dist_self dist_comm dist_triangle :=
  uniformSpace_eq PseudoMetricSpace.uniformity_dist
#align metric.to_uniform_space_eq Metric.toUniformSpace_eq
-/

/- warning: metric.uniformity_basis_dist -> Metric.uniformity_basis_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Real (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) (fun (ε : Real) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Real (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) (fun (ε : Real) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist Metric.uniformity_basis_distₓ'. -/
theorem uniformity_basis_dist :
    (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε } :=
  by
  rw [to_uniform_space_eq]
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _
#align metric.uniformity_basis_dist Metric.uniformity_basis_dist

/- warning: metric.mk_uniformity_basis -> Metric.mk_uniformity_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {β : Type.{u2}} {p : β -> Prop} {f : β -> Real}, (forall (i : β), (p i) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f i))) -> (forall {{ε : Real}}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{succ u2} β (fun (i : β) => Exists.{0} (p i) (fun (hi : p i) => LE.le.{0} Real Real.hasLe (f i) ε)))) -> (Filter.HasBasis.{u1, succ u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) p (fun (i : β) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (f i))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {β : Type.{u1}} {p : β -> Prop} {f : β -> Real}, (forall (i : β), (p i) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f i))) -> (forall {{ε : Real}}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{succ u1} β (fun (i : β) => And (p i) (LE.le.{0} Real Real.instLEReal (f i) ε)))) -> (Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} α α) β (uniformity.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) p (fun (i : β) => setOf.{u2} (Prod.{u2, u2} α α) (fun (p : Prod.{u2, u2} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (Prod.fst.{u2, u2} α α p) (Prod.snd.{u2, u2} α α p)) (f i))))
Case conversion may be inaccurate. Consider using '#align metric.mk_uniformity_basis Metric.mk_uniformity_basisₓ'. -/
/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_succ`,
and `uniformity_basis_dist_inv_nat_pos`. -/
protected theorem mk_uniformity_basis {β : Type _} {p : β → Prop} {f : β → ℝ}
    (hf₀ : ∀ i, p i → 0 < f i) (hf : ∀ ⦃ε⦄, 0 < ε → ∃ (i : _)(hi : p i), f i ≤ ε) :
    (𝓤 α).HasBasis p fun i => { p : α × α | dist p.1 p.2 < f i } :=
  by
  refine' ⟨fun s => uniformity_basis_dist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    obtain ⟨i, hi, H⟩ : ∃ (i : _)(hi : p i), f i ≤ ε
    exact hf ε₀
    exact ⟨i, hi, fun x (hx : _ < _) => hε <| lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
#align metric.mk_uniformity_basis Metric.mk_uniformity_basis

/- warning: metric.uniformity_basis_dist_rat -> Metric.uniformity_basis_dist_rat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Rat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (r : Rat) => LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) r) (fun (r : Rat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Rat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (r : Rat) => LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) r) (fun (r : Rat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Rat.cast.{0} Real Real.ratCast r)))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_rat Metric.uniformity_basis_dist_ratₓ'. -/
theorem uniformity_basis_dist_rat :
    (𝓤 α).HasBasis (fun r : ℚ => 0 < r) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => Rat.cast_pos.2) fun ε hε =>
    let ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    ⟨r, Rat.cast_pos.1 hr0, hrε.le⟩
#align metric.uniformity_basis_dist_rat Metric.uniformity_basis_dist_rat

/- warning: metric.uniformity_basis_dist_inv_nat_succ -> Metric.uniformity_basis_dist_inv_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (_x : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (_x : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_inv_nat_succ Metric.uniformity_basis_dist_inv_nat_succₓ'. -/
theorem uniformity_basis_dist_inv_nat_succ :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n) fun ε ε0 =>
    (exists_nat_one_div_lt ε0).imp fun n hn => ⟨trivial, le_of_lt hn⟩
#align metric.uniformity_basis_dist_inv_nat_succ Metric.uniformity_basis_dist_inv_nat_succ

/- warning: metric.uniformity_basis_dist_inv_nat_pos -> Metric.uniformity_basis_dist_inv_nat_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Nat.cast.{0} Real Real.natCast n))))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_inv_nat_pos Metric.uniformity_basis_dist_inv_nat_posₓ'. -/
theorem uniformity_basis_dist_inv_nat_pos :
    (𝓤 α).HasBasis (fun n : ℕ => 0 < n) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / ↑n } :=
  Metric.mk_uniformity_basis (fun n hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun ε ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, Nat.succ_pos n, by exact_mod_cast hn.le⟩
#align metric.uniformity_basis_dist_inv_nat_pos Metric.uniformity_basis_dist_inv_nat_pos

/- warning: metric.uniformity_basis_dist_pow -> Metric.uniformity_basis_dist_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (n : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (n : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_pow Metric.uniformity_basis_dist_powₓ'. -/
theorem uniformity_basis_dist_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun n : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < r ^ n } :=
  Metric.mk_uniformity_basis (fun n hn => pow_pos h0 _) fun ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩
#align metric.uniformity_basis_dist_pow Metric.uniformity_basis_dist_pow

/- warning: metric.uniformity_basis_dist_lt -> Metric.uniformity_basis_dist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {R : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) R) -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Real (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (r : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) (LT.lt.{0} Real Real.hasLt r R)) (fun (r : Real) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) r)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {R : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) R) -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Real (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (r : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (LT.lt.{0} Real Real.instLTReal r R)) (fun (r : Real) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) r)))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_lt Metric.uniformity_basis_dist_ltₓ'. -/
theorem uniformity_basis_dist_lt {R : ℝ} (hR : 0 < R) :
    (𝓤 α).HasBasis (fun r : ℝ => 0 < r ∧ r < R) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun r => And.left) fun r hr =>
    ⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 <| Or.inr (half_lt_self hR)⟩,
      min_le_left _ _⟩
#align metric.uniformity_basis_dist_lt Metric.uniformity_basis_dist_lt

/- warning: metric.mk_uniformity_basis_le -> Metric.mk_uniformity_basis_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {β : Type.{u2}} {p : β -> Prop} {f : β -> Real}, (forall (x : β), (p x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f x))) -> (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{succ u2} β (fun (x : β) => Exists.{0} (p x) (fun (hx : p x) => LE.le.{0} Real Real.hasLe (f x) ε)))) -> (Filter.HasBasis.{u1, succ u2} (Prod.{u1, u1} α α) β (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) p (fun (x : β) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (f x))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {β : Type.{u1}} {p : β -> Prop} {f : β -> Real}, (forall (x : β), (p x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f x))) -> (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{succ u1} β (fun (x : β) => And (p x) (LE.le.{0} Real Real.instLEReal (f x) ε)))) -> (Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} α α) β (uniformity.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) p (fun (x : β) => setOf.{u2} (Prod.{u2, u2} α α) (fun (p : Prod.{u2, u2} α α) => LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (Prod.fst.{u2, u2} α α p) (Prod.snd.{u2, u2} α α p)) (f x))))
Case conversion may be inaccurate. Consider using '#align metric.mk_uniformity_basis_le Metric.mk_uniformity_basis_leₓ'. -/
/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i | p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on this constructor.
More can be easily added if needed in the future. -/
protected theorem mk_uniformity_basis_le {β : Type _} {p : β → Prop} {f : β → ℝ}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ (x : _)(hx : p x), f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | dist p.1 p.2 ≤ f x } :=
  by
  refine' ⟨fun s => uniformity_basis_dist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x (hx : _ ≤ _) => hε <| lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x (hx : _ < _) => H (le_of_lt hx)⟩
#align metric.mk_uniformity_basis_le Metric.mk_uniformity_basis_le

/- warning: metric.uniformity_basis_dist_le -> Metric.uniformity_basis_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Real (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) (fun (ε : Real) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Real (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) (fun (ε : Real) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_le Metric.uniformity_basis_dist_leₓ'. -/
/-- Contant size closed neighborhoods of the diagonal form a basis
of the uniformity filter. -/
theorem uniformity_basis_dist_le :
    (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 ≤ ε } :=
  Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩
#align metric.uniformity_basis_dist_le Metric.uniformity_basis_dist_le

/- warning: metric.uniformity_basis_dist_le_pow -> Metric.uniformity_basis_dist_le_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (n : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) Nat (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (n : Nat) => True) (fun (n : Nat) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n))))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_basis_dist_le_pow Metric.uniformity_basis_dist_le_powₓ'. -/
theorem uniformity_basis_dist_le_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun n : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ r ^ n } :=
  Metric.mk_uniformity_basis_le (fun n hn => pow_pos h0 _) fun ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩
#align metric.uniformity_basis_dist_le_pow Metric.uniformity_basis_dist_le_pow

/- warning: metric.mem_uniformity_dist -> Metric.mem_uniformity_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) ε) -> (Membership.Mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasMem.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} (Prod.{u1, u1} α α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) s (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : α} {b : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) ε) -> (Membership.mem.{u1, u1} (Prod.{u1, u1} α α) (Set.{u1} (Prod.{u1, u1} α α)) (Set.instMembershipSet.{u1} (Prod.{u1, u1} α α)) (Prod.mk.{u1, u1} α α a b) s))))
Case conversion may be inaccurate. Consider using '#align metric.mem_uniformity_dist Metric.mem_uniformity_distₓ'. -/
theorem mem_uniformity_dist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, dist a b < ε → (a, b) ∈ s :=
  uniformity_basis_dist.mem_uniformity_iff
#align metric.mem_uniformity_dist Metric.mem_uniformity_dist

/- warning: metric.dist_mem_uniformity -> Metric.dist_mem_uniformity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.hasMem.{u1} (Prod.{u1, u1} α α)) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)) (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} α α)) (Filter.{u1} (Prod.{u1, u1} α α)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} α α)) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)) (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align metric.dist_mem_uniformity Metric.dist_mem_uniformityₓ'. -/
/-- A constant size neighborhood of the diagonal is an entourage. -/
theorem dist_mem_uniformity {ε : ℝ} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_dist.2 ⟨ε, ε0, fun a b => id⟩
#align metric.dist_mem_uniformity Metric.dist_mem_uniformity

/- warning: metric.uniform_continuous_iff -> Metric.uniformContinuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f a) (f b)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, Iff (UniformContinuous.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : α} {b : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f a) (f b)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_continuous_iff Metric.uniformContinuous_iffₓ'. -/
theorem uniformContinuous_iff [PseudoMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε :=
  uniformity_basis_dist.uniformContinuous_iff uniformity_basis_dist
#align metric.uniform_continuous_iff Metric.uniformContinuous_iff

/- warning: metric.uniform_continuous_on_iff -> Metric.uniformContinuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f y)) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) (f y)) ε))))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_continuous_on_iff Metric.uniformContinuousOn_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem uniformContinuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformity_basis_dist.uniformContinuousOn_iff Metric.uniformity_basis_dist
#align metric.uniform_continuous_on_iff Metric.uniformContinuousOn_iff

/- warning: metric.uniform_continuous_on_iff_le -> Metric.uniformContinuousOn_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) δ) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f y)) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (UniformContinuousOn.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) δ) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) (f y)) ε))))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_continuous_on_iff_le Metric.uniformContinuousOn_iff_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem uniformContinuousOn_iff_le [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), dist x y ≤ δ → dist (f x) (f y) ≤ ε :=
  Metric.uniformity_basis_dist_le.uniformContinuousOn_iff Metric.uniformity_basis_dist_le
#align metric.uniform_continuous_on_iff_le Metric.uniformContinuousOn_iff_le

/- warning: metric.uniform_embedding_iff -> Metric.uniformEmbedding_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (δ : Real), (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) δ)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, Iff (UniformEmbedding.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) (And (Function.Injective.{succ u1, succ u2} α β f) (And (UniformContinuous.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) (forall (δ : Real), (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : α} {b : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) δ)))))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_embedding_iff Metric.uniformEmbedding_iffₓ'. -/
theorem uniformEmbedding_iff [PseudoMetricSpace β] {f : α → β} :
    UniformEmbedding f ↔
      Function.Injective f ∧
        UniformContinuous f ∧ ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  by
  simp only [uniformity_basis_dist.uniform_embedding_iff uniformity_basis_dist, exists_prop]
  rfl
#align metric.uniform_embedding_iff Metric.uniformEmbedding_iff

/- warning: metric.controlled_of_uniform_embedding -> Metric.controlled_of_uniformEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, (UniformEmbedding.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) -> (And (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f a) (f b)) ε))))) (forall (δ : Real), (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : α} {b : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) δ))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, (UniformEmbedding.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2) f) -> (And (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : α} {b : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f a) (f b)) ε))))) (forall (δ : Real), (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : α} {b : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f a) (f b)) ε) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) δ))))))
Case conversion may be inaccurate. Consider using '#align metric.controlled_of_uniform_embedding Metric.controlled_of_uniformEmbeddingₓ'. -/
/-- If a map between pseudometric spaces is a uniform embedding then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniformEmbedding [PseudoMetricSpace β] {f : α → β} :
    UniformEmbedding f →
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  by
  intro h
  exact ⟨uniformContinuous_iff.1 (uniformEmbedding_iff.1 h).2.1, (uniformEmbedding_iff.1 h).2.2⟩
#align metric.controlled_of_uniform_embedding Metric.controlled_of_uniformEmbedding

/- warning: metric.totally_bounded_iff -> Metric.totallyBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (y : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => Metric.ball.{u1} α _inst_1 y ε)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (TotallyBounded.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (y : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => Metric.ball.{u1} α _inst_1 y ε)))))))
Case conversion may be inaccurate. Consider using '#align metric.totally_bounded_iff Metric.totallyBounded_iffₓ'. -/
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  ⟨fun H ε ε0 => H _ (dist_mem_uniformity ε0), fun H r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun y yt z => hε⟩⟩
#align metric.totally_bounded_iff Metric.totallyBounded_iff

/- warning: metric.totally_bounded_of_finite_discretization -> Metric.totallyBounded_of_finite_discretization is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Fintype.{u1} β) (fun (_x : Fintype.{u1} β) => Exists.{succ u1} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (fun (F : (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) => forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (y : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), (Eq.{succ u1} β (F x) (F y)) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) y)) ε)))))) -> (TotallyBounded.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Fintype.{u1} β) (fun (_x : Fintype.{u1} β) => Exists.{succ u1} ((Set.Elem.{u1} α s) -> β) (fun (F : (Set.Elem.{u1} α s) -> β) => forall (x : Set.Elem.{u1} α s) (y : Set.Elem.{u1} α s), (Eq.{succ u1} β (F x) (F y)) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) x) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) y)) ε)))))) -> (TotallyBounded.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align metric.totally_bounded_of_finite_discretization Metric.totallyBounded_of_finite_discretizationₓ'. -/
/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
theorem totallyBounded_of_finite_discretization {s : Set α}
    (H :
      ∀ ε > (0 : ℝ),
        ∃ (β : Type u)(_ : Fintype β)(F : s → β), ∀ x y, F x = F y → dist (x : α) y < ε) :
    TotallyBounded s := by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  haveI : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine' totally_bounded_iff.2 fun ε ε0 => _
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  skip
  let Finv := Function.invFun F
  refine' ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => _⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩
#align metric.totally_bounded_of_finite_discretization Metric.totallyBounded_of_finite_discretization

/- warning: metric.finite_approx_of_totally_bounded -> Metric.finite_approx_of_totallyBounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (TotallyBounded.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) s) -> (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (y : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) => Metric.ball.{u1} α _inst_1 y ε))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (TotallyBounded.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) s) -> (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (y : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) (fun (h._@.Mathlib.Topology.MetricSpace.Basic._hyg.11021 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) => Metric.ball.{u1} α _inst_1 y ε))))))))
Case conversion may be inaccurate. Consider using '#align metric.finite_approx_of_totally_bounded Metric.finite_approx_of_totallyBoundedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) :
    ∀ ε > 0, ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)
#align metric.finite_approx_of_totally_bounded Metric.finite_approx_of_totallyBounded

/- warning: metric.tendsto_uniformly_on_filter_iff -> Metric.tendstoUniformlyOnFilter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι} {p' : Filter.{u2} β}, Iff (TendstoUniformlyOnFilter.{u2, u1, u3} β α ι (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F f p p') (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{max u3 u2} (Prod.{u3, u2} ι β) (fun (n : Prod.{u3, u2} ι β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (Prod.snd.{u3, u2} ι β n)) (F (Prod.fst.{u3, u2} ι β n) (Prod.snd.{u3, u2} ι β n))) ε) (Filter.prod.{u3, u2} ι β p p')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι} {p' : Filter.{u3} β}, Iff (TendstoUniformlyOnFilter.{u3, u2, u1} β α ι (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1) F f p p') (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{max u3 u1} (Prod.{u1, u3} ι β) (fun (n : Prod.{u1, u3} ι β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f (Prod.snd.{u1, u3} ι β n)) (F (Prod.fst.{u1, u3} ι β n) (Prod.snd.{u1, u3} ι β n))) ε) (Filter.prod.{u1, u3} ι β p p')))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_uniformly_on_filter_iff Metric.tendstoUniformlyOnFilter_iffₓ'. -/
/-- Expressing uniform convergence using `dist` -/
theorem tendstoUniformlyOnFilter_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι}
    {p' : Filter β} :
    TendstoUniformlyOnFilter F f p p' ↔
      ∀ ε > 0, ∀ᶠ n : ι × β in p ×ᶠ p', dist (f n.snd) (F n.fst n.snd) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  refine' (H ε εpos).mono fun n hn => hε hn
#align metric.tendsto_uniformly_on_filter_iff Metric.tendstoUniformlyOnFilter_iff

/- warning: metric.tendsto_locally_uniformly_on_iff -> Metric.tendstoLocallyUniformlyOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι} {s : Set.{u2} β}, Iff (TendstoLocallyUniformlyOn.{u2, u1, u3} β α ι (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_2 F f p s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhdsWithin.{u2} β _inst_2 x s)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhdsWithin.{u2} β _inst_2 x s)) => Filter.Eventually.{u3} ι (fun (n : ι) => forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f y) (F n y)) ε)) p)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι} {s : Set.{u3} β}, Iff (TendstoLocallyUniformlyOn.{u3, u2, u1} β α ι (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1) _inst_2 F f p s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x s) -> (Exists.{succ u3} (Set.{u3} β) (fun (t : Set.{u3} β) => And (Membership.mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (instMembershipSetFilter.{u3} β) t (nhdsWithin.{u3} β _inst_2 x s)) (Filter.Eventually.{u1} ι (fun (n : ι) => forall (y : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y t) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f y) (F n y)) ε)) p)))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_locally_uniformly_on_iff Metric.tendstoLocallyUniformlyOn_iffₓ'. -/
/-- Expressing locally uniform convergence on a set using `dist`. -/
theorem tendstoLocallyUniformlyOn_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => _⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩
#align metric.tendsto_locally_uniformly_on_iff Metric.tendstoLocallyUniformlyOn_iff

/- warning: metric.tendsto_uniformly_on_iff -> Metric.tendstoUniformlyOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι} {s : Set.{u2} β}, Iff (TendstoUniformlyOn.{u2, u1, u3} β α ι (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F f p s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u3} ι (fun (n : ι) => forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (F n x)) ε)) p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι} {s : Set.{u3} β}, Iff (TendstoUniformlyOn.{u3, u2, u1} β α ι (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1) F f p s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u1} ι (fun (n : ι) => forall (x : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) x s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f x) (F n x)) ε)) p))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_uniformly_on_iff Metric.tendstoUniformlyOn_iffₓ'. -/
/-- Expressing uniform convergence on a set using `dist`. -/
theorem tendstoUniformlyOn_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, dist (f x) (F n x) < ε :=
  by
  refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)
#align metric.tendsto_uniformly_on_iff Metric.tendstoUniformlyOn_iff

/- warning: metric.tendsto_locally_uniformly_iff -> Metric.tendstoLocallyUniformly_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι}, Iff (TendstoLocallyUniformly.{u2, u1, u3} β α ι (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_2 F f p) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : β), Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => Exists.{0} (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 x)) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) t (nhds.{u2} β _inst_2 x)) => Filter.Eventually.{u3} ι (fun (n : ι) => forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f y) (F n y)) ε)) p))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι}, Iff (TendstoLocallyUniformly.{u3, u2, u1} β α ι (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1) _inst_2 F f p) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : β), Exists.{succ u3} (Set.{u3} β) (fun (t : Set.{u3} β) => And (Membership.mem.{u3, u3} (Set.{u3} β) (Filter.{u3} β) (instMembershipSetFilter.{u3} β) t (nhds.{u3} β _inst_2 x)) (Filter.Eventually.{u1} ι (fun (n : ι) => forall (y : β), (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) y t) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f y) (F n y)) ε)) p))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_locally_uniformly_iff Metric.tendstoLocallyUniformly_iffₓ'. -/
/-- Expressing locally uniform convergence using `dist`. -/
theorem tendstoLocallyUniformly_iff {ι : Type _} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε :=
  by
  simp only [← tendstoLocallyUniformlyOn_univ, tendsto_locally_uniformly_on_iff, nhdsWithin_univ,
    mem_univ, forall_const, exists_prop]
#align metric.tendsto_locally_uniformly_iff Metric.tendstoLocallyUniformly_iff

/- warning: metric.tendsto_uniformly_iff -> Metric.tendstoUniformly_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u3}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u3} ι}, Iff (TendstoUniformly.{u2, u1, u3} β α ι (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F f p) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u3} ι (fun (n : ι) => forall (x : β), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (F n x)) ε) p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {F : ι -> β -> α} {f : β -> α} {p : Filter.{u1} ι}, Iff (TendstoUniformly.{u3, u2, u1} β α ι (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1) F f p) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u1} ι (fun (n : ι) => forall (x : β), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f x) (F n x)) ε) p))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_uniformly_iff Metric.tendstoUniformly_iffₓ'. -/
/-- Expressing uniform convergence using `dist`. -/
theorem tendstoUniformly_iff {ι : Type _} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, dist (f x) (F n x) < ε :=
  by
  rw [← tendstoUniformlyOn_univ, tendsto_uniformly_on_iff]
  simp
#align metric.tendsto_uniformly_iff Metric.tendstoUniformly_iff

/- warning: metric.cauchy_iff -> Metric.cauchy_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) f) (And (Filter.NeBot.{u1} α f) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) t f) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ε)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Filter.{u1} α}, Iff (Cauchy.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) f) (And (Filter.NeBot.{u1} α f) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) t f) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) ε)))))))
Case conversion may be inaccurate. Consider using '#align metric.cauchy_iff Metric.cauchy_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » t) -/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ NeBot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ (x) (_ : x ∈ t) (y) (_ : y ∈ t), dist x y < ε :=
  uniformity_basis_dist.cauchy_iff
#align metric.cauchy_iff Metric.cauchy_iff

/- warning: metric.nhds_basis_ball -> Metric.nhds_basis_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Real (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) (Metric.ball.{u1} α _inst_1 x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Real (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) (Metric.ball.{u1} α _inst_1 x)
Case conversion may be inaccurate. Consider using '#align metric.nhds_basis_ball Metric.nhds_basis_ballₓ'. -/
theorem nhds_basis_ball : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_dist
#align metric.nhds_basis_ball Metric.nhds_basis_ball

/- warning: metric.mem_nhds_iff -> Metric.mem_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s)))
Case conversion may be inaccurate. Consider using '#align metric.mem_nhds_iff Metric.mem_nhds_iffₓ'. -/
theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, ball x ε ⊆ s :=
  nhds_basis_ball.mem_iff
#align metric.mem_nhds_iff Metric.mem_nhds_iff

/- warning: metric.eventually_nhds_iff -> Metric.eventually_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (y : α) => p y) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {{y : α}}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y x) ε) -> (p y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (y : α) => p y) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {{y : α}}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y x) ε) -> (p y))))
Case conversion may be inaccurate. Consider using '#align metric.eventually_nhds_iff Metric.eventually_nhds_iffₓ'. -/
theorem eventually_nhds_iff {p : α → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ ⦃y⦄, dist y x < ε → p y :=
  mem_nhds_iff
#align metric.eventually_nhds_iff Metric.eventually_nhds_iff

/- warning: metric.eventually_nhds_iff_ball -> Metric.eventually_nhds_iff_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (y : α) => p y) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) -> (p y))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {p : α -> Prop}, Iff (Filter.Eventually.{u1} α (fun (y : α) => p y) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Metric.ball.{u1} α _inst_1 x ε)) -> (p y))))
Case conversion may be inaccurate. Consider using '#align metric.eventually_nhds_iff_ball Metric.eventually_nhds_iff_ballₓ'. -/
theorem eventually_nhds_iff_ball {p : α → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε > 0, ∀ y ∈ ball x ε, p y :=
  mem_nhds_iff
#align metric.eventually_nhds_iff_ball Metric.eventually_nhds_iff_ball

/- warning: metric.eventually_prod_nhds_iff -> Metric.eventually_prod_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Filter.{u2} ι} {x₀ : α} {p : (Prod.{u2, u1} ι α) -> Prop}, Iff (Filter.Eventually.{max u2 u1} (Prod.{u2, u1} ι α) (fun (x : Prod.{u2, u1} ι α) => p x) (Filter.prod.{u2, u1} ι α f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x₀))) (Exists.{succ u2} (ι -> Prop) (fun (pa : ι -> Prop) => Exists.{0} (Filter.Eventually.{u2} ι (fun (i : ι) => pa i) f) (fun (ha : Filter.Eventually.{u2} ι (fun (i : ι) => pa i) f) => Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {i : ι}, (pa i) -> (forall {x : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x x₀) ε) -> (p (Prod.mk.{u2, u1} ι α i x))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u2} α] {f : Filter.{u1} ι} {x₀ : α} {p : (Prod.{u1, u2} ι α) -> Prop}, Iff (Filter.Eventually.{max u2 u1} (Prod.{u1, u2} ι α) (fun (x : Prod.{u1, u2} ι α) => p x) (Filter.prod.{u1, u2} ι α f (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) x₀))) (Exists.{succ u1} (ι -> Prop) (fun (pa : ι -> Prop) => And (Filter.Eventually.{u1} ι (fun (i : ι) => pa i) f) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {i : ι}, (pa i) -> (forall {x : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) x x₀) ε) -> (p (Prod.mk.{u1, u2} ι α i x))))))))
Case conversion may be inaccurate. Consider using '#align metric.eventually_prod_nhds_iff Metric.eventually_prod_nhds_iffₓ'. -/
/-- A version of `filter.eventually_prod_iff` where the second filter consists of neighborhoods
in a pseudo-metric space.-/
theorem eventually_prod_nhds_iff {f : Filter ι} {x₀ : α} {p : ι × α → Prop} :
    (∀ᶠ x in f ×ᶠ 𝓝 x₀, p x) ↔
      ∃ (pa : ι → Prop)(ha : ∀ᶠ i in f, pa i),
        ∃ ε > 0, ∀ {i}, pa i → ∀ {x}, dist x x₀ < ε → p (i, x) :=
  by
  simp_rw [eventually_prod_iff, Metric.eventually_nhds_iff]
  refine' exists_congr fun q => exists_congr fun hq => _
  constructor
  · rintro ⟨r, ⟨ε, hε, hεr⟩, hp⟩
    exact ⟨ε, hε, fun i hi x hx => hp hi <| hεr hx⟩
  · rintro ⟨ε, hε, hp⟩
    exact ⟨fun x => dist x x₀ < ε, ⟨ε, hε, fun y => id⟩, @hp⟩
#align metric.eventually_prod_nhds_iff Metric.eventually_prod_nhds_iff

/- warning: metric.eventually_nhds_prod_iff -> Metric.eventually_nhds_prod_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_2 : PseudoMetricSpace.{u2} α] {f : Filter.{u1} ι} {x₀ : α} {p : (Prod.{u2, u1} α ι) -> Prop}, Iff (Filter.Eventually.{max u2 u1} (Prod.{u2, u1} α ι) (fun (x : Prod.{u2, u1} α ι) => p x) (Filter.prod.{u2, u1} α ι (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_2)) x₀) f)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => Exists.{succ u1} (ι -> Prop) (fun (pa : ι -> Prop) => Exists.{0} (Filter.Eventually.{u1} ι (fun (i : ι) => pa i) f) (fun (ha : Filter.Eventually.{u1} ι (fun (i : ι) => pa i) f) => forall {x : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} α (PseudoMetricSpace.toHasDist.{u2} α _inst_2) x x₀) ε) -> (forall {i : ι}, (pa i) -> (p (Prod.mk.{u2, u1} α ι x i))))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {f : Filter.{u2} ι} {x₀ : α} {p : (Prod.{u1, u2} α ι) -> Prop}, Iff (Filter.Eventually.{max u1 u2} (Prod.{u1, u2} α ι) (fun (x : Prod.{u1, u2} α ι) => p x) (Filter.prod.{u1, u2} α ι (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) x₀) f)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Exists.{succ u2} (ι -> Prop) (fun (pa : ι -> Prop) => And (Filter.Eventually.{u2} ι (fun (i : ι) => pa i) f) (forall {x : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_2) x x₀) ε) -> (forall {i : ι}, (pa i) -> (p (Prod.mk.{u1, u2} α ι x i))))))))
Case conversion may be inaccurate. Consider using '#align metric.eventually_nhds_prod_iff Metric.eventually_nhds_prod_iffₓ'. -/
/-- A version of `filter.eventually_prod_iff` where the first filter consists of neighborhoods
in a pseudo-metric space.-/
theorem eventually_nhds_prod_iff {ι α} [PseudoMetricSpace α] {f : Filter ι} {x₀ : α}
    {p : α × ι → Prop} :
    (∀ᶠ x in 𝓝 x₀ ×ᶠ f, p x) ↔
      ∃ ε > (0 : ℝ),
        ∃ (pa : ι → Prop)(ha : ∀ᶠ i in f, pa i), ∀ {x}, dist x x₀ < ε → ∀ {i}, pa i → p (x, i) :=
  by
  rw [eventually_swap_iff, Metric.eventually_prod_nhds_iff]
  constructor <;>
    · rintro ⟨a1, a2, a3, a4, a5⟩
      refine' ⟨a3, a4, a1, a2, fun b1 b2 b3 b4 => a5 b4 b2⟩
#align metric.eventually_nhds_prod_iff Metric.eventually_nhds_prod_iff

/- warning: metric.nhds_basis_closed_ball -> Metric.nhds_basis_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Real (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) (Metric.closedBall.{u1} α _inst_1 x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Real (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (ε : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) (Metric.closedBall.{u1} α _inst_1 x)
Case conversion may be inaccurate. Consider using '#align metric.nhds_basis_closed_ball Metric.nhds_basis_closedBallₓ'. -/
theorem nhds_basis_closedBall : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) (closedBall x) :=
  nhds_basis_uniformity uniformity_basis_dist_le
#align metric.nhds_basis_closed_ball Metric.nhds_basis_closedBall

/- warning: metric.nhds_basis_ball_inv_nat_succ -> Metric.nhds_basis_ball_inv_nat_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (_x : Nat) => True) (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (_x : Nat) => True) (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))
Case conversion may be inaccurate. Consider using '#align metric.nhds_basis_ball_inv_nat_succ Metric.nhds_basis_ball_inv_nat_succₓ'. -/
theorem nhds_basis_ball_inv_nat_succ :
    (𝓝 x).HasBasis (fun _ => True) fun n : ℕ => ball x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ
#align metric.nhds_basis_ball_inv_nat_succ Metric.nhds_basis_ball_inv_nat_succ

/- warning: metric.nhds_basis_ball_inv_nat_pos -> Metric.nhds_basis_ball_inv_nat_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Nat.cast.{0} Real Real.natCast n)))
Case conversion may be inaccurate. Consider using '#align metric.nhds_basis_ball_inv_nat_pos Metric.nhds_basis_ball_inv_nat_posₓ'. -/
theorem nhds_basis_ball_inv_nat_pos :
    (𝓝 x).HasBasis (fun n => 0 < n) fun n : ℕ => ball x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos
#align metric.nhds_basis_ball_inv_nat_pos Metric.nhds_basis_ball_inv_nat_pos

/- warning: metric.nhds_basis_ball_pow -> Metric.nhds_basis_ball_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (n : Nat) => True) (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (n : Nat) => True) (fun (n : Nat) => Metric.ball.{u1} α _inst_1 x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)))
Case conversion may be inaccurate. Consider using '#align metric.nhds_basis_ball_pow Metric.nhds_basis_ball_powₓ'. -/
theorem nhds_basis_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun n => True) fun n : ℕ => ball x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)
#align metric.nhds_basis_ball_pow Metric.nhds_basis_ball_pow

/- warning: metric.nhds_basis_closed_ball_pow -> Metric.nhds_basis_closedBall_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (n : Nat) => True) (fun (n : Nat) => Metric.closedBall.{u1} α _inst_1 x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) r n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Filter.HasBasis.{u1, 1} α Nat (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x) (fun (n : Nat) => True) (fun (n : Nat) => Metric.closedBall.{u1} α _inst_1 x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) r n)))
Case conversion may be inaccurate. Consider using '#align metric.nhds_basis_closed_ball_pow Metric.nhds_basis_closedBall_powₓ'. -/
theorem nhds_basis_closedBall_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓝 x).HasBasis (fun n => True) fun n : ℕ => closedBall x (r ^ n) :=
  nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)
#align metric.nhds_basis_closed_ball_pow Metric.nhds_basis_closedBall_pow

/- warning: metric.is_open_iff -> Metric.isOpen_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s))))
Case conversion may be inaccurate. Consider using '#align metric.is_open_iff Metric.isOpen_iffₓ'. -/
theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s := by
  simp only [isOpen_iff_mem_nhds, mem_nhds_iff]
#align metric.is_open_iff Metric.isOpen_iff

#print Metric.isOpen_ball /-
theorem isOpen_ball : IsOpen (ball x ε) :=
  isOpen_iff.2 fun y => exists_ball_subset_ball
#align metric.is_open_ball Metric.isOpen_ball
-/

/- warning: metric.ball_mem_nhds -> Metric.ball_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align metric.ball_mem_nhds Metric.ball_mem_nhdsₓ'. -/
theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
  isOpen_ball.mem_nhds (mem_ball_self ε0)
#align metric.ball_mem_nhds Metric.ball_mem_nhds

/- warning: metric.closed_ball_mem_nhds -> Metric.closedBall_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α) {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_mem_nhds Metric.closedBall_mem_nhdsₓ'. -/
theorem closedBall_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : closedBall x ε ∈ 𝓝 x :=
  mem_of_superset (ball_mem_nhds x ε0) ball_subset_closedBall
#align metric.closed_ball_mem_nhds Metric.closedBall_mem_nhds

#print Metric.closedBall_mem_nhds_of_mem /-
theorem closedBall_mem_nhds_of_mem {x c : α} {ε : ℝ} (h : x ∈ ball c ε) : closedBall c ε ∈ 𝓝 x :=
  mem_of_superset (isOpen_ball.mem_nhds h) ball_subset_closedBall
#align metric.closed_ball_mem_nhds_of_mem Metric.closedBall_mem_nhds_of_mem
-/

/- warning: metric.nhds_within_basis_ball -> Metric.nhdsWithin_basis_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Filter.HasBasis.{u1, 1} α Real (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x s) (fun (ε : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) (fun (ε : Real) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {s : Set.{u1} α}, Filter.HasBasis.{u1, 1} α Real (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x s) (fun (ε : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) (fun (ε : Real) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s)
Case conversion may be inaccurate. Consider using '#align metric.nhds_within_basis_ball Metric.nhdsWithin_basis_ballₓ'. -/
theorem nhdsWithin_basis_ball {s : Set α} :
    (𝓝[s] x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => ball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_ball s
#align metric.nhds_within_basis_ball Metric.nhdsWithin_basis_ball

/- warning: metric.mem_nhds_within_iff -> Metric.mem_nhdsWithin_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x t)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) t) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x t)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) t) s)))
Case conversion may be inaccurate. Consider using '#align metric.mem_nhds_within_iff Metric.mem_nhdsWithin_iffₓ'. -/
theorem mem_nhdsWithin_iff {t : Set α} : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_ball.mem_iff
#align metric.mem_nhds_within_iff Metric.mem_nhdsWithin_iff

/- warning: metric.tendsto_nhds_within_nhds_within -> Metric.tendsto_nhdsWithin_nhdsWithin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoMetricSpace.{u2} β] {t : Set.{u2} β} {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhdsWithin.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) b t)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x a) δ) -> (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t) (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) b) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoMetricSpace.{u2} β] {t : Set.{u2} β} {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhdsWithin.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) b t)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x a) δ) -> (And (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (f x) t) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) b) ε))))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_nhds_within_nhds_within Metric.tendsto_nhdsWithin_nhdsWithinₓ'. -/
theorem tendsto_nhdsWithin_nhdsWithin [PseudoMetricSpace β] {t : Set β} {f : α → β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → dist x a < δ → f x ∈ t ∧ dist (f x) b < ε :=
  (nhdsWithin_basis_ball.tendsto_iffₓ nhdsWithin_basis_ball).trans <|
    forall₂_congr fun ε hε => exists₂_congr fun δ hδ => forall_congr' fun x => by simp <;> itauto
#align metric.tendsto_nhds_within_nhds_within Metric.tendsto_nhdsWithin_nhdsWithin

/- warning: metric.tendsto_nhds_within_nhds -> Metric.tendsto_nhdsWithin_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) b) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhdsWithin.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a s) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) b) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_nhds_within_nhds Metric.tendsto_nhdsWithin_nhdsₓ'. -/
theorem tendsto_nhdsWithin_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) b < ε :=
  by
  rw [← nhdsWithin_univ b, tendsto_nhds_within_nhds_within]
  simp only [mem_univ, true_and_iff]
#align metric.tendsto_nhds_within_nhds Metric.tendsto_nhdsWithin_nhds

/- warning: metric.tendsto_nhds_nhds -> Metric.tendsto_nhds_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {x : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) b) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α} {b : β}, Iff (Filter.Tendsto.{u1, u2} α β f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) b)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {x : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) b) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_nhds_nhds Metric.tendsto_nhds_nhdsₓ'. -/
theorem tendsto_nhds_nhds [PseudoMetricSpace β] {f : α → β} {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, dist x a < δ → dist (f x) b < ε :=
  nhds_basis_ball.tendsto_iffₓ nhds_basis_ball
#align metric.tendsto_nhds_nhds Metric.tendsto_nhds_nhds

/- warning: metric.continuous_at_iff -> Metric.continuousAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α}, Iff (ContinuousAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f a) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {x : α}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f a)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α}, Iff (ContinuousAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f a) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {x : α}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) (f a)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.continuous_at_iff Metric.continuousAt_iffₓ'. -/
theorem continuousAt_iff [PseudoMetricSpace β] {f : α → β} {a : α} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, dist x a < δ → dist (f x) (f a) < ε := by
  rw [ContinuousAt, tendsto_nhds_nhds]
#align metric.continuous_at_iff Metric.continuousAt_iff

/- warning: metric.continuous_within_at_iff -> Metric.continuousWithinAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, Iff (ContinuousWithinAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f s a) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (f a)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {a : α} {s : Set.{u1} α}, Iff (ContinuousWithinAt.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f s a) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x a) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f x) (f a)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.continuous_within_at_iff Metric.continuousWithinAt_iffₓ'. -/
theorem continuousWithinAt_iff [PseudoMetricSpace β] {f : α → β} {a : α} {s : Set α} :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) (f a) < ε :=
  by rw [ContinuousWithinAt, tendsto_nhds_within_nhds]
#align metric.continuous_within_at_iff Metric.continuousWithinAt_iff

/- warning: metric.continuous_on_iff -> Metric.continuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f s) (forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (a : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f a) (f b)) ε))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (ContinuousOn.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f s) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (a : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f a) (f b)) ε))))))
Case conversion may be inaccurate. Consider using '#align metric.continuous_on_iff Metric.continuousOn_iffₓ'. -/
theorem continuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, dist a b < δ → dist (f a) (f b) < ε := by
  simp [ContinuousOn, continuous_within_at_iff]
#align metric.continuous_on_iff Metric.continuousOn_iff

/- warning: metric.continuous_iff -> Metric.continuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f) (forall (b : α) (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (a : α), (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f a) (f b)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β}, Iff (Continuous.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) f) (forall (b : α) (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (a : α), (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (f a) (f b)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.continuous_iff Metric.continuous_iffₓ'. -/
theorem continuous_iff [PseudoMetricSpace β] {f : α → β} :
    Continuous f ↔ ∀ (b), ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b < δ → dist (f a) (f b) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun b => tendsto_nhds_nhds
#align metric.continuous_iff Metric.continuous_iff

/- warning: metric.tendsto_nhds -> Metric.tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Filter.{u2} β} {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u x) a) ε) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : Filter.{u2} β} {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u f (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u x) a) ε) f))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_nhds Metric.tendsto_nhdsₓ'. -/
theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, dist (u x) a < ε :=
  nhds_basis_ball.tendsto_right_iff
#align metric.tendsto_nhds Metric.tendsto_nhds

/- warning: metric.continuous_at_iff' -> Metric.continuousAt_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {b : β}, Iff (ContinuousAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f b) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (f b)) ε) (nhds.{u2} β _inst_2 b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {b : β}, Iff (ContinuousAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f b) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f x) (f b)) ε) (nhds.{u2} β _inst_2 b)))
Case conversion may be inaccurate. Consider using '#align metric.continuous_at_iff' Metric.continuousAt_iff'ₓ'. -/
theorem continuousAt_iff' [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 b, dist (f x) (f b) < ε := by
  rw [ContinuousAt, tendsto_nhds]
#align metric.continuous_at_iff' Metric.continuousAt_iff'

/- warning: metric.continuous_within_at_iff' -> Metric.continuousWithinAt_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {s : Set.{u2} β}, Iff (ContinuousWithinAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s b) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (f b)) ε) (nhdsWithin.{u2} β _inst_2 b s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {s : Set.{u2} β}, Iff (ContinuousWithinAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s b) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f x) (f b)) ε) (nhdsWithin.{u2} β _inst_2 b s)))
Case conversion may be inaccurate. Consider using '#align metric.continuous_within_at_iff' Metric.continuousWithinAt_iff'ₓ'. -/
theorem continuousWithinAt_iff' [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  rw [ContinuousWithinAt, tendsto_nhds]
#align metric.continuous_within_at_iff' Metric.continuousWithinAt_iff'

/- warning: metric.continuous_on_iff' -> Metric.continuousOn_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {s : Set.{u2} β}, Iff (ContinuousOn.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s) (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) -> (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (f b)) ε) (nhdsWithin.{u2} β _inst_2 b s))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {s : Set.{u2} β}, Iff (ContinuousOn.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s) (forall (b : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s) -> (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f x) (f b)) ε) (nhdsWithin.{u2} β _inst_2 b s))))
Case conversion may be inaccurate. Consider using '#align metric.continuous_on_iff' Metric.continuousOn_iff'ₓ'. -/
theorem continuousOn_iff' [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε := by
  simp [ContinuousOn, continuous_within_at_iff']
#align metric.continuous_on_iff' Metric.continuousOn_iff'

/- warning: metric.continuous_iff' -> Metric.continuous_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α}, Iff (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f) (forall (a : β) (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (f a)) ε) (nhds.{u2} β _inst_2 a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α}, Iff (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f) (forall (a : β) (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Eventually.{u2} β (fun (x : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f x) (f a)) ε) (nhds.{u2} β _inst_2 a)))
Case conversion may be inaccurate. Consider using '#align metric.continuous_iff' Metric.continuous_iff'ₓ'. -/
theorem continuous_iff' [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ (a), ∀ ε > 0, ∀ᶠ x in 𝓝 a, dist (f x) (f a) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun b => tendsto_nhds
#align metric.continuous_iff' Metric.continuous_iff'

/- warning: metric.tendsto_at_top -> Metric.tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u n) a) ε))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u n) a) ε))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_at_top Metric.tendsto_atTopₓ'. -/
theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  (atTop_basis.tendsto_iffₓ nhds_basis_ball).trans <|
    by
    simp only [exists_prop, true_and_iff]
    rfl
#align metric.tendsto_at_top Metric.tendsto_atTop

/- warning: metric.tendsto_at_top' -> Metric.tendsto_atTop' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] [_inst_4 : NoMaxOrder.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))] {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GT.gt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u n) a) ε))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] [_inst_4 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))] {u : β -> α} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α u (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u n) a) ε))))
Case conversion may be inaccurate. Consider using '#align metric.tendsto_at_top' Metric.tendsto_atTop'ₓ'. -/
/-- A variant of `tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem tendsto_atTop' [Nonempty β] [SemilatticeSup β] [NoMaxOrder β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n > N, dist (u n) a < ε :=
  (atTop_basis_Ioi.tendsto_iffₓ nhds_basis_ball).trans <|
    by
    simp only [exists_prop, true_and_iff]
    rfl
#align metric.tendsto_at_top' Metric.tendsto_atTop'

/- warning: metric.is_open_singleton_iff -> Metric.isOpen_singleton_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {x : α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (y : α), (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_2) y x) ε) -> (Eq.{succ u1} α y x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {x : α}, Iff (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (y : α), (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_2) y x) ε) -> (Eq.{succ u1} α y x))))
Case conversion may be inaccurate. Consider using '#align metric.is_open_singleton_iff Metric.isOpen_singleton_iffₓ'. -/
theorem isOpen_singleton_iff {α : Type _} [PseudoMetricSpace α] {x : α} :
    IsOpen ({x} : Set α) ↔ ∃ ε > 0, ∀ y, dist y x < ε → y = x := by
  simp [is_open_iff, subset_singleton_iff, mem_ball]
#align metric.is_open_singleton_iff Metric.isOpen_singleton_iff

/- warning: metric.exists_ball_inter_eq_singleton_of_mem_discrete -> Metric.exists_ball_inter_eq_singleton_of_mem_discrete is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : DiscreteTopology.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))] {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : DiscreteTopology.{u1} (Set.Elem.{u1} α s) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))] {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.ball.{u1} α _inst_1 x ε) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))))
Case conversion may be inaccurate. Consider using '#align metric.exists_ball_inter_eq_singleton_of_mem_discrete Metric.exists_ball_inter_eq_singleton_of_mem_discreteₓ'. -/
/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
theorem exists_ball_inter_eq_singleton_of_mem_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.ball x ε ∩ s = {x} :=
  nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hx
#align metric.exists_ball_inter_eq_singleton_of_mem_discrete Metric.exists_ball_inter_eq_singleton_of_mem_discrete

/- warning: metric.exists_closed_ball_inter_eq_singleton_of_discrete -> Metric.exists_closedBall_inter_eq_singleton_of_discrete is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : DiscreteTopology.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))] {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} [_inst_2 : DiscreteTopology.{u1} (Set.Elem.{u1} α s) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))] {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x ε) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))))
Case conversion may be inaccurate. Consider using '#align metric.exists_closed_ball_inter_eq_singleton_of_discrete Metric.exists_closedBall_inter_eq_singleton_of_discreteₓ'. -/
/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
theorem exists_closedBall_inter_eq_singleton_of_discrete [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ ε > 0, Metric.closedBall x ε ∩ s = {x} :=
  nhds_basis_closedBall.exists_inter_eq_singleton_of_mem_discrete hx
#align metric.exists_closed_ball_inter_eq_singleton_of_discrete Metric.exists_closedBall_inter_eq_singleton_of_discrete

/- warning: dense.exists_dist_lt -> Dense.exists_dist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall (x : α) {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Dense.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall (x : α) {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) ε))))
Case conversion may be inaccurate. Consider using '#align dense.exists_dist_lt Dense.exists_dist_ltₓ'. -/
theorem Dense.exists_dist_lt {s : Set α} (hs : Dense s) (x : α) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ s, dist x y < ε :=
  by
  have : (ball x ε).Nonempty := by simp [hε]
  simpa only [mem_ball'] using hs.exists_mem_open is_open_ball this
#align dense.exists_dist_lt Dense.exists_dist_lt

/- warning: dense_range.exists_dist_lt -> DenseRange.exists_dist_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {β : Type.{u2}} {f : β -> α}, (DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) β f) -> (forall (x : α) {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{succ u2} β (fun (y : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x (f y)) ε)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {β : Type.{u1}} {f : β -> α}, (DenseRange.{u2, u1} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) β f) -> (forall (x : α) {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{succ u1} β (fun (y : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) x (f y)) ε)))
Case conversion may be inaccurate. Consider using '#align dense_range.exists_dist_lt DenseRange.exists_dist_ltₓ'. -/
theorem DenseRange.exists_dist_lt {β : Type _} {f : β → α} (hf : DenseRange f) (x : α) {ε : ℝ}
    (hε : 0 < ε) : ∃ y, dist x (f y) < ε :=
  exists_range_iff.1 (hf.exists_dist_lt x hε)
#align dense_range.exists_dist_lt DenseRange.exists_dist_lt

end Metric

open Metric

/- warning: pseudo_metric.uniformity_basis_edist -> Metric.uniformity_basis_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Filter.HasBasis.{u1, 1} (Prod.{u1, u1} α α) ENNReal (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (fun (ε : ENNReal) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) (fun (ε : ENNReal) => setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1)) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε))
Case conversion may be inaccurate. Consider using '#align pseudo_metric.uniformity_basis_edist Metric.uniformity_basis_edistₓ'. -/
/-Instantiate a pseudometric space as a pseudoemetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/
/-- Expressing the uniformity in terms of `edist` -/
protected theorem Metric.uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p | edist p.1 p.2 < ε } :=
  ⟨by
    intro t
    refine' mem_uniformity_dist.trans ⟨_, _⟩ <;> rintro ⟨ε, ε0, Hε⟩
    · use ENNReal.ofReal ε, ENNReal.ofReal_pos.2 ε0
      rintro ⟨a, b⟩
      simp only [edist_dist, ENNReal.ofReal_lt_ofReal_iff ε0]
      exact Hε
    · rcases ENNReal.lt_iff_exists_real_btwn.1 ε0 with ⟨ε', _, ε0', hε⟩
      rw [ENNReal.ofReal_pos] at ε0'
      refine' ⟨ε', ε0', fun a b h => Hε (lt_trans _ hε)⟩
      rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff ε0']⟩
#align pseudo_metric.uniformity_basis_edist Metric.uniformity_basis_edist

/- warning: metric.uniformity_edist -> Metric.uniformity_edist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (iInf.{u1, 1} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) ENNReal (fun (ε : ENNReal) => iInf.{u1, 0} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toHasInf.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.completeLattice.{u1} (Prod.{u1, u1} α α)))) (GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (fun (H : GT.gt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ε (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) => Filter.principal.{u1} (Prod.{u1, u1} α α) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (iInf.{u1, 1} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) ENNReal (fun (ε : ENNReal) => iInf.{u1, 0} (Filter.{u1} (Prod.{u1, u1} α α)) (ConditionallyCompleteLattice.toInfSet.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Prod.{u1, u1} α α)) (Filter.instCompleteLatticeFilter.{u1} (Prod.{u1, u1} α α)))) (GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (fun (H : GT.gt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) ε (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) => Filter.principal.{u1} (Prod.{u1, u1} α α) (setOf.{u1} (Prod.{u1, u1} α α) (fun (p : Prod.{u1, u1} α α) => LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EDist.edist.{u1} α (PseudoMetricSpace.toEDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_edist Metric.uniformity_edistₓ'. -/
theorem Metric.uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  Metric.uniformity_basis_edist.eq_biInf
#align metric.uniformity_edist Metric.uniformity_edist

#print PseudoMetricSpace.toPseudoEMetricSpace /-
-- see Note [lower instance priority]
/-- A pseudometric space induces a pseudoemetric space -/
instance (priority := 100) PseudoMetricSpace.toPseudoEMetricSpace : PseudoEMetricSpace α :=
  { ‹PseudoMetricSpace α› with
    edist := edist
    edist_self := by simp [edist_dist]
    edist_comm := by simp only [edist_dist, dist_comm] <;> simp
    edist_triangle := fun x y z =>
      by
      simp only [edist_dist, ← ENNReal.ofReal_add, dist_nonneg]
      rw [ENNReal.ofReal_le_ofReal_iff _]
      · exact dist_triangle _ _ _
      · simpa using add_le_add (dist_nonneg : 0 ≤ dist x y) dist_nonneg
    uniformity_edist := Metric.uniformity_edist }
#align pseudo_metric_space.to_pseudo_emetric_space PseudoMetricSpace.toPseudoEMetricSpace
-/

/- warning: metric.eball_top_eq_univ -> Metric.eball_top_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align metric.eball_top_eq_univ Metric.eball_top_eq_univₓ'. -/
/-- In a pseudometric space, an open ball of infinite radius is the whole space -/
theorem Metric.eball_top_eq_univ (x : α) : EMetric.ball x ∞ = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun y => edist_lt_top y x
#align metric.eball_top_eq_univ Metric.eball_top_eq_univ

#print Metric.emetric_ball /-
/-- Balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_ball {x : α} {ε : ℝ} : EMetric.ball x (ENNReal.ofReal ε) = ball x ε :=
  by
  ext y
  simp only [EMetric.mem_ball, mem_ball, edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg
#align metric.emetric_ball Metric.emetric_ball
-/

/- warning: metric.emetric_ball_nnreal -> Metric.emetric_ball_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : NNReal}, Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)) (Metric.ball.{u1} α _inst_1 x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : NNReal}, Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (ENNReal.some ε)) (Metric.ball.{u1} α _inst_1 x (NNReal.toReal ε))
Case conversion may be inaccurate. Consider using '#align metric.emetric_ball_nnreal Metric.emetric_ball_nnrealₓ'. -/
/-- Balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_ball_nnreal {x : α} {ε : ℝ≥0} : EMetric.ball x ε = ball x ε :=
  by
  convert Metric.emetric_ball
  simp
#align metric.emetric_ball_nnreal Metric.emetric_ball_nnreal

/- warning: metric.emetric_closed_ball -> Metric.emetric_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Eq.{succ u1} (Set.{u1} α) (EMetric.closedBall.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (ENNReal.ofReal ε)) (Metric.closedBall.{u1} α _inst_1 x ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Eq.{succ u1} (Set.{u1} α) (EMetric.closedBall.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (ENNReal.ofReal ε)) (Metric.closedBall.{u1} α _inst_1 x ε))
Case conversion may be inaccurate. Consider using '#align metric.emetric_closed_ball Metric.emetric_closedBallₓ'. -/
/-- Closed balls defined using the distance or the edistance coincide -/
theorem Metric.emetric_closedBall {x : α} {ε : ℝ} (h : 0 ≤ ε) :
    EMetric.closedBall x (ENNReal.ofReal ε) = closedBall x ε := by
  ext y <;> simp [edist_dist] <;> rw [ENNReal.ofReal_le_ofReal_iff h]
#align metric.emetric_closed_ball Metric.emetric_closedBall

/- warning: metric.emetric_closed_ball_nnreal -> Metric.emetric_closedBall_nnreal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : NNReal}, Eq.{succ u1} (Set.{u1} α) (EMetric.closedBall.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) ε)) (Metric.closedBall.{u1} α _inst_1 x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) ε))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {ε : NNReal}, Eq.{succ u1} (Set.{u1} α) (EMetric.closedBall.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (ENNReal.some ε)) (Metric.closedBall.{u1} α _inst_1 x (NNReal.toReal ε))
Case conversion may be inaccurate. Consider using '#align metric.emetric_closed_ball_nnreal Metric.emetric_closedBall_nnrealₓ'. -/
/-- Closed balls defined using the distance or the edistance coincide -/
@[simp]
theorem Metric.emetric_closedBall_nnreal {x : α} {ε : ℝ≥0} :
    EMetric.closedBall x ε = closedBall x ε :=
  by
  convert Metric.emetric_closedBall ε.2
  simp
#align metric.emetric_closed_ball_nnreal Metric.emetric_closedBall_nnreal

/- warning: metric.emetric_ball_top -> Metric.emetric_ball_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (EMetric.ball.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align metric.emetric_ball_top Metric.emetric_ball_topₓ'. -/
@[simp]
theorem Metric.emetric_ball_top (x : α) : EMetric.ball x ⊤ = univ :=
  eq_univ_of_forall fun y => edist_lt_top _ _
#align metric.emetric_ball_top Metric.emetric_ball_top

/- warning: metric.inseparable_iff -> Metric.inseparable_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α}, Iff (Inseparable.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x y) (Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α}, Iff (Inseparable.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x y) (Eq.{1} Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.inseparable_iff Metric.inseparable_iffₓ'. -/
theorem Metric.inseparable_iff {x y : α} : Inseparable x y ↔ dist x y = 0 := by
  rw [EMetric.inseparable_iff, edist_nndist, dist_nndist, ENNReal.coe_eq_zero, NNReal.coe_eq_zero]
#align metric.inseparable_iff Metric.inseparable_iff

#print PseudoMetricSpace.replaceUniformity /-
/-- Build a new pseudometric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def PseudoMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoMetricSpace α
    where
  dist := @dist _ m.toHasDist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  edist := edist
  edist_dist := edist_dist
  toUniformSpace := U
  uniformity_dist := H.trans PseudoMetricSpace.uniformity_dist
#align pseudo_metric_space.replace_uniformity PseudoMetricSpace.replaceUniformity
-/

#print PseudoMetricSpace.replaceUniformity_eq /-
theorem PseudoMetricSpace.replaceUniformity_eq {α} [U : UniformSpace α] (m : PseudoMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m :=
  by
  ext
  rfl
#align pseudo_metric_space.replace_uniformity_eq PseudoMetricSpace.replaceUniformity_eq
-/

#print PseudoMetricSpace.replaceTopology /-
/-- Build a new pseudo metric space from an old one where the bundled topological structure is
provably (but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible]
def PseudoMetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : PseudoMetricSpace γ :=
  @PseudoMetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align pseudo_metric_space.replace_topology PseudoMetricSpace.replaceTopology
-/

#print PseudoMetricSpace.replaceTopology_eq /-
theorem PseudoMetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ)
    (H : U = m.toUniformSpace.toTopologicalSpace) : m.replaceTopology H = m :=
  by
  ext
  rfl
#align pseudo_metric_space.replace_topology_eq PseudoMetricSpace.replaceTopology_eq
-/

/- warning: pseudo_emetric_space.to_pseudo_metric_space_of_dist -> PseudoEMetricSpace.toPseudoMetricSpaceOfDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [e : PseudoEMetricSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α e) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (ENNReal.toReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α e) x y))) -> (PseudoMetricSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [e : PseudoEMetricSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α e) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (ENNReal.toReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α e) x y))) -> (PseudoMetricSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align pseudo_emetric_space.to_pseudo_metric_space_of_dist PseudoEMetricSpace.toPseudoMetricSpaceOfDistₓ'. -/
/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In this definition, the
distance is given separately, to be able to prescribe some expression which is not defeq to the
push-forward of the edistance to reals. -/
def PseudoEMetricSpace.toPseudoMetricSpaceOfDist {α : Type u} [e : PseudoEMetricSpace α]
    (dist : α → α → ℝ) (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤)
    (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) : PseudoMetricSpace α :=
  let m : PseudoMetricSpace α :=
    { dist
      dist_self := fun x => by simp [h]
      dist_comm := fun x y => by simp [h, PseudoEMetricSpace.edist_comm]
      dist_triangle := fun x y z => by
        simp only [h]
        rw [← ENNReal.toReal_add (edist_ne_top _ _) (edist_ne_top _ _),
          ENNReal.toReal_le_toReal (edist_ne_top _ _)]
        · exact edist_triangle _ _ _
        · simp [ENNReal.add_eq_top, edist_ne_top]
      edist := edist
      edist_dist := fun x y => by simp [h, ENNReal.ofReal_toReal, edist_ne_top] }
  m.replaceUniformity <|
    by
    rw [uniformity_pseudoedist, Metric.uniformity_edist]
    rfl
#align pseudo_emetric_space.to_pseudo_metric_space_of_dist PseudoEMetricSpace.toPseudoMetricSpaceOfDist

/- warning: pseudo_emetric_space.to_pseudo_metric_space -> PseudoEMetricSpace.toPseudoMetricSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [e : PseudoEMetricSpace.{u1} α], (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α e) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (PseudoMetricSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [e : PseudoEMetricSpace.{u1} α], (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α e) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (PseudoMetricSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align pseudo_emetric_space.to_pseudo_metric_space PseudoEMetricSpace.toPseudoMetricSpaceₓ'. -/
/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the emetric space. -/
def PseudoEMetricSpace.toPseudoMetricSpace {α : Type u} [e : PseudoEMetricSpace α]
    (h : ∀ x y : α, edist x y ≠ ⊤) : PseudoMetricSpace α :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun x y =>
    rfl
#align pseudo_emetric_space.to_pseudo_metric_space PseudoEMetricSpace.toPseudoMetricSpace

#print PseudoMetricSpace.replaceBornology /-
/-- Build a new pseudometric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
def PseudoMetricSpace.replaceBornology {α} [B : Bornology α] (m : PseudoMetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace α :=
  { m with
    toBornology := B
    cobounded_sets :=
      Set.ext <|
        compl_surjective.forall.2 fun s =>
          (H s).trans <| by rw [is_bounded_iff, mem_set_of_eq, compl_compl] }
#align pseudo_metric_space.replace_bornology PseudoMetricSpace.replaceBornology
-/

#print PseudoMetricSpace.replaceBornology_eq /-
theorem PseudoMetricSpace.replaceBornology_eq {α} [m : PseudoMetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    PseudoMetricSpace.replaceBornology _ H = m :=
  by
  ext
  rfl
#align pseudo_metric_space.replace_bornology_eq PseudoMetricSpace.replaceBornology_eq
-/

/- warning: metric.complete_of_convergent_controlled_sequences -> Metric.complete_of_convergent_controlled_sequences is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (B : Nat -> Real), (forall (n : Nat), LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (B n)) -> (forall (u : Nat -> α), (forall (N : Nat) (n : Nat) (m : Nat), (LE.le.{0} Nat Nat.hasLe N n) -> (LE.le.{0} Nat Nat.hasLe N m) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u n) (u m)) (B N))) -> (Exists.{succ u1} α (fun (x : α) => Filter.Tendsto.{0, u1} Nat α u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)))) -> (CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (B : Nat -> Real), (forall (n : Nat), LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (B n)) -> (forall (u : Nat -> α), (forall (N : Nat) (n : Nat) (m : Nat), (LE.le.{0} Nat instLENat N n) -> (LE.le.{0} Nat instLENat N m) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u n) (u m)) (B N))) -> (Exists.{succ u1} α (fun (x : α) => Filter.Tendsto.{0, u1} Nat α u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)))) -> (CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align metric.complete_of_convergent_controlled_sequences Metric.complete_of_convergent_controlled_sequencesₓ'. -/
/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem Metric.complete_of_convergent_controlled_sequences (B : ℕ → Real) (hB : ∀ n, 0 < B n)
    (H :
      ∀ u : ℕ → α,
        (∀ N n m : ℕ, N ≤ n → N ≤ m → dist (u n) (u m) < B N) → ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | dist p.1 p.2 < B n }) (fun n => dist_mem_uniformity <| hB n) H
#align metric.complete_of_convergent_controlled_sequences Metric.complete_of_convergent_controlled_sequences

#print Metric.complete_of_cauchySeq_tendsto /-
theorem Metric.complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  EMetric.complete_of_cauchySeq_tendsto
#align metric.complete_of_cauchy_seq_tendsto Metric.complete_of_cauchySeq_tendsto
-/

section Real

#print Real.pseudoMetricSpace /-
/-- Instantiate the reals as a pseudometric space. -/
instance Real.pseudoMetricSpace : PseudoMetricSpace ℝ
    where
  dist x y := |x - y|
  dist_self := by simp [abs_zero]
  dist_comm x y := abs_sub_comm _ _
  dist_triangle x y z := abs_sub_le _ _ _
#align real.pseudo_metric_space Real.pseudoMetricSpace
-/

/- warning: real.dist_eq -> Real.dist_eq is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x y) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y))
Case conversion may be inaccurate. Consider using '#align real.dist_eq Real.dist_eqₓ'. -/
theorem Real.dist_eq (x y : ℝ) : dist x y = |x - y| :=
  rfl
#align real.dist_eq Real.dist_eq

/- warning: real.nndist_eq -> Real.nndist_eq is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} NNReal (NNDist.nndist.{0} Real (PseudoMetricSpace.toNNDist.{0} Real Real.pseudoMetricSpace) x y) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} NNReal (NNDist.nndist.{0} Real (PseudoMetricSpace.toNNDist.{0} Real Real.pseudoMetricSpace) x y) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y))
Case conversion may be inaccurate. Consider using '#align real.nndist_eq Real.nndist_eqₓ'. -/
theorem Real.nndist_eq (x y : ℝ) : nndist x y = Real.nnabs (x - y) :=
  rfl
#align real.nndist_eq Real.nndist_eq

/- warning: real.nndist_eq' -> Real.nndist_eq' is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} NNReal (NNDist.nndist.{0} Real (PseudoMetricSpace.toNNDist.{0} Real Real.pseudoMetricSpace) x y) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y x))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} NNReal (NNDist.nndist.{0} Real (PseudoMetricSpace.toNNDist.{0} Real Real.pseudoMetricSpace) x y) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y x))
Case conversion may be inaccurate. Consider using '#align real.nndist_eq' Real.nndist_eq'ₓ'. -/
theorem Real.nndist_eq' (x y : ℝ) : nndist x y = Real.nnabs (y - x) :=
  nndist_comm _ _
#align real.nndist_eq' Real.nndist_eq'

/- warning: real.dist_0_eq_abs -> Real.dist_0_eq_abs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)
Case conversion may be inaccurate. Consider using '#align real.dist_0_eq_abs Real.dist_0_eq_absₓ'. -/
theorem Real.dist_0_eq_abs (x : ℝ) : dist x 0 = |x| := by simp [Real.dist_eq]
#align real.dist_0_eq_abs Real.dist_0_eq_abs

/- warning: real.dist_left_le_of_mem_uIcc -> Real.dist_left_le_of_mem_uIcc is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.uIcc.{0} Real Real.lattice x z)) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x y) (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.uIcc.{0} Real Real.lattice x z)) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x y) (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x z))
Case conversion may be inaccurate. Consider using '#align real.dist_left_le_of_mem_uIcc Real.dist_left_le_of_mem_uIccₓ'. -/
theorem Real.dist_left_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist x y ≤ dist x z := by
  simpa only [dist_comm x] using abs_sub_left_of_mem_uIcc h
#align real.dist_left_le_of_mem_uIcc Real.dist_left_le_of_mem_uIcc

/- warning: real.dist_right_le_of_mem_uIcc -> Real.dist_right_le_of_mem_uIcc is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {z : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.uIcc.{0} Real Real.lattice x z)) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) y z) (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x z))
but is expected to have type
  forall {x : Real} {y : Real} {z : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.uIcc.{0} Real Real.lattice x z)) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) y z) (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x z))
Case conversion may be inaccurate. Consider using '#align real.dist_right_le_of_mem_uIcc Real.dist_right_le_of_mem_uIccₓ'. -/
theorem Real.dist_right_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist y z ≤ dist x z := by
  simpa only [dist_comm _ z] using abs_sub_right_of_mem_uIcc h
#align real.dist_right_le_of_mem_uIcc Real.dist_right_le_of_mem_uIcc

/- warning: real.dist_le_of_mem_uIcc -> Real.dist_le_of_mem_uIcc is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {x' : Real} {y' : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.uIcc.{0} Real Real.lattice x' y')) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.uIcc.{0} Real Real.lattice x' y')) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x y) (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x' y'))
but is expected to have type
  forall {x : Real} {y : Real} {x' : Real} {y' : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.uIcc.{0} Real Real.lattice x' y')) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.uIcc.{0} Real Real.lattice x' y')) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x y) (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x' y'))
Case conversion may be inaccurate. Consider using '#align real.dist_le_of_mem_uIcc Real.dist_le_of_mem_uIccₓ'. -/
theorem Real.dist_le_of_mem_uIcc {x y x' y' : ℝ} (hx : x ∈ uIcc x' y') (hy : y ∈ uIcc x' y') :
    dist x y ≤ dist x' y' :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])
#align real.dist_le_of_mem_uIcc Real.dist_le_of_mem_uIcc

/- warning: real.dist_le_of_mem_Icc -> Real.dist_le_of_mem_Icc is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real} {x' : Real} {y' : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder x' y')) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Icc.{0} Real Real.preorder x' y')) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y' x'))
but is expected to have type
  forall {x : Real} {y : Real} {x' : Real} {y' : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal x' y')) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Icc.{0} Real Real.instPreorderReal x' y')) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y' x'))
Case conversion may be inaccurate. Consider using '#align real.dist_le_of_mem_Icc Real.dist_le_of_mem_Iccₓ'. -/
theorem Real.dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ y' - x' := by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
#align real.dist_le_of_mem_Icc Real.dist_le_of_mem_Icc

/- warning: real.dist_le_of_mem_Icc_01 -> Real.dist_le_of_mem_Icc_01 is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{0} Real (PseudoMetricSpace.toHasDist.{0} Real Real.pseudoMetricSpace) x y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{0} Real (PseudoMetricSpace.toDist.{0} Real Real.pseudoMetricSpace) x y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.dist_le_of_mem_Icc_01 Real.dist_le_of_mem_Icc_01ₓ'. -/
theorem Real.dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist x y ≤ 1 := by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy
#align real.dist_le_of_mem_Icc_01 Real.dist_le_of_mem_Icc_01

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_binfi, ball, Real.dist_eq, abs_sub_comm]

/- warning: real.ball_eq_Ioo -> Real.ball_eq_Ioo is a dubious translation:
lean 3 declaration is
  forall (x : Real) (r : Real), Eq.{1} (Set.{0} Real) (Metric.ball.{0} Real Real.pseudoMetricSpace x r) (Set.Ioo.{0} Real Real.preorder (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x r) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x r))
but is expected to have type
  forall (x : Real) (r : Real), Eq.{1} (Set.{0} Real) (Metric.ball.{0} Real Real.pseudoMetricSpace x r) (Set.Ioo.{0} Real Real.instPreorderReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x r) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x r))
Case conversion may be inaccurate. Consider using '#align real.ball_eq_Ioo Real.ball_eq_Iooₓ'. -/
theorem Real.ball_eq_Ioo (x r : ℝ) : ball x r = Ioo (x - r) (x + r) :=
  Set.ext fun y => by
    rw [mem_ball, dist_comm, Real.dist_eq, abs_sub_lt_iff, mem_Ioo, ← sub_lt_iff_lt_add',
      sub_lt_comm]
#align real.ball_eq_Ioo Real.ball_eq_Ioo

/- warning: real.closed_ball_eq_Icc -> Real.closedBall_eq_Icc is a dubious translation:
lean 3 declaration is
  forall {x : Real} {r : Real}, Eq.{1} (Set.{0} Real) (Metric.closedBall.{0} Real Real.pseudoMetricSpace x r) (Set.Icc.{0} Real Real.preorder (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x r) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x r))
but is expected to have type
  forall {x : Real} {r : Real}, Eq.{1} (Set.{0} Real) (Metric.closedBall.{0} Real Real.pseudoMetricSpace x r) (Set.Icc.{0} Real Real.instPreorderReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x r) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x r))
Case conversion may be inaccurate. Consider using '#align real.closed_ball_eq_Icc Real.closedBall_eq_Iccₓ'. -/
theorem Real.closedBall_eq_Icc {x r : ℝ} : closedBall x r = Icc (x - r) (x + r) := by
  ext y <;>
    rw [mem_closed_ball, dist_comm, Real.dist_eq, abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add',
      sub_le_comm]
#align real.closed_ball_eq_Icc Real.closedBall_eq_Icc

/- warning: real.Ioo_eq_ball -> Real.Ioo_eq_ball is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} (Set.{0} Real) (Set.Ioo.{0} Real Real.preorder x y) (Metric.ball.{0} Real Real.pseudoMetricSpace (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y x) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} (Set.{0} Real) (Set.Ioo.{0} Real Real.instPreorderReal x y) (Metric.ball.{0} Real Real.pseudoMetricSpace (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y x) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.Ioo_eq_ball Real.Ioo_eq_ballₓ'. -/
theorem Real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.ball_eq_Ioo, ← sub_div, add_comm, ← sub_add, add_sub_cancel', add_self_div_two, ←
    add_div, add_assoc, add_sub_cancel'_right, add_self_div_two]
#align real.Ioo_eq_ball Real.Ioo_eq_ball

/- warning: real.Icc_eq_closed_ball -> Real.Icc_eq_closedBall is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} (Set.{0} Real) (Set.Icc.{0} Real Real.preorder x y) (Metric.closedBall.{0} Real Real.pseudoMetricSpace (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) y x) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} (Set.{0} Real) (Set.Icc.{0} Real Real.instPreorderReal x y) (Metric.closedBall.{0} Real Real.pseudoMetricSpace (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) y x) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.Icc_eq_closed_ball Real.Icc_eq_closedBallₓ'. -/
theorem Real.Icc_eq_closedBall (x y : ℝ) : Icc x y = closedBall ((x + y) / 2) ((y - x) / 2) := by
  rw [Real.closedBall_eq_Icc, ← sub_div, add_comm, ← sub_add, add_sub_cancel', add_self_div_two, ←
    add_div, add_assoc, add_sub_cancel'_right, add_self_div_two]
#align real.Icc_eq_closed_ball Real.Icc_eq_closedBall

section MetricOrdered

variable [Preorder α] [CompactIccSpace α]

#print totallyBounded_Icc /-
theorem totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.TotallyBounded
#align totally_bounded_Icc totallyBounded_Icc
-/

#print totallyBounded_Ico /-
theorem totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  totallyBounded_subset Ico_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ico totallyBounded_Ico
-/

#print totallyBounded_Ioc /-
theorem totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  totallyBounded_subset Ioc_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioc totallyBounded_Ioc
-/

#print totallyBounded_Ioo /-
theorem totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  totallyBounded_subset Ioo_subset_Icc_self (totallyBounded_Icc a b)
#align totally_bounded_Ioo totallyBounded_Ioo
-/

end MetricOrdered

/- warning: squeeze_zero' -> squeeze_zero' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real} {g : α -> Real} {t₀ : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (t : α) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f t)) t₀) -> (Filter.Eventually.{u1} α (fun (t : α) => LE.le.{0} Real Real.hasLe (f t) (g t)) t₀) -> (Filter.Tendsto.{u1, 0} α Real g t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Filter.Tendsto.{u1, 0} α Real f t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real} {g : α -> Real} {t₀ : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (t : α) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f t)) t₀) -> (Filter.Eventually.{u1} α (fun (t : α) => LE.le.{0} Real Real.instLEReal (f t) (g t)) t₀) -> (Filter.Tendsto.{u1, 0} α Real g t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Filter.Tendsto.{u1, 0} α Real f t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align squeeze_zero' squeeze_zero'ₓ'. -/
/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
theorem squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (nhds 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft
#align squeeze_zero' squeeze_zero'

/- warning: squeeze_zero -> squeeze_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real} {g : α -> Real} {t₀ : Filter.{u1} α}, (forall (t : α), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f t)) -> (forall (t : α), LE.le.{0} Real Real.hasLe (f t) (g t)) -> (Filter.Tendsto.{u1, 0} α Real g t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Filter.Tendsto.{u1, 0} α Real f t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real} {g : α -> Real} {t₀ : Filter.{u1} α}, (forall (t : α), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f t)) -> (forall (t : α), LE.le.{0} Real Real.instLEReal (f t) (g t)) -> (Filter.Tendsto.{u1, 0} α Real g t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Filter.Tendsto.{u1, 0} α Real f t₀ (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align squeeze_zero squeeze_zeroₓ'. -/
/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
theorem squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (eventually_of_forall hf) (eventually_of_forall hft) g0
#align squeeze_zero squeeze_zero

/- warning: metric.uniformity_eq_comap_nhds_zero -> Metric.uniformity_eq_comap_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Filter.comap.{u1, 0} (Prod.{u1, u1} α α) Real (fun (p : Prod.{u1, u1} α α) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Eq.{succ u1} (Filter.{u1} (Prod.{u1, u1} α α)) (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Filter.comap.{u1, 0} (Prod.{u1, u1} α α) Real (fun (p : Prod.{u1, u1} α α) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align metric.uniformity_eq_comap_nhds_zero Metric.uniformity_eq_comap_nhds_zeroₓ'. -/
theorem Metric.uniformity_eq_comap_nhds_zero :
    𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : ℝ)) :=
  by
  ext s
  simp [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff, subset_def, Real.dist_0_eq_abs]
#align metric.uniformity_eq_comap_nhds_zero Metric.uniformity_eq_comap_nhds_zero

/- warning: cauchy_seq_iff_tendsto_dist_at_top_0 -> cauchySeq_iff_tendsto_dist_atTop_0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (Filter.Tendsto.{u2, 0} (Prod.{u2, u2} β β) Real (fun (n : Prod.{u2, u2} β β) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u (Prod.fst.{u2, u2} β β n)) (u (Prod.snd.{u2, u2} β β n))) (Filter.atTop.{u2} (Prod.{u2, u2} β β) (Prod.preorder.{u2, u2} β β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (Filter.Tendsto.{u2, 0} (Prod.{u2, u2} β β) Real (fun (n : Prod.{u2, u2} β β) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u (Prod.fst.{u2, u2} β β n)) (u (Prod.snd.{u2, u2} β β n))) (Filter.atTop.{u2} (Prod.{u2, u2} β β) (Prod.instPreorderProd.{u2, u2} β β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)) (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_iff_tendsto_dist_at_top_0 cauchySeq_iff_tendsto_dist_atTop_0ₓ'. -/
theorem cauchySeq_iff_tendsto_dist_atTop_0 [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ Tendsto (fun n : β × β => dist (u n.1) (u n.2)) atTop (𝓝 0) := by
  rw [cauchySeq_iff_tendsto, Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff, Prod.map_def]
#align cauchy_seq_iff_tendsto_dist_at_top_0 cauchySeq_iff_tendsto_dist_atTop_0

/- warning: tendsto_uniformity_iff_dist_tendsto_zero -> tendsto_uniformity_iff_dist_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u2}} {f : ι -> (Prod.{u1, u1} α α)} {p : Filter.{u2} ι}, Iff (Filter.Tendsto.{u2, u1} ι (Prod.{u1, u1} α α) f p (uniformity.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (Filter.Tendsto.{u2, 0} ι Real (fun (x : ι) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α (f x)) (Prod.snd.{u1, u1} α α (f x))) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {f : ι -> (Prod.{u2, u2} α α)} {p : Filter.{u1} ι}, Iff (Filter.Tendsto.{u1, u2} ι (Prod.{u2, u2} α α) f p (uniformity.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1))) (Filter.Tendsto.{u1, 0} ι Real (fun (x : ι) => Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (Prod.fst.{u2, u2} α α (f x)) (Prod.snd.{u2, u2} α α (f x))) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_uniformity_iff_dist_tendsto_zero tendsto_uniformity_iff_dist_tendsto_zeroₓ'. -/
theorem tendsto_uniformity_iff_dist_tendsto_zero {ι : Type _} {f : ι → α × α} {p : Filter ι} :
    Tendsto f p (𝓤 α) ↔ Tendsto (fun x => dist (f x).1 (f x).2) p (𝓝 0) := by
  rw [Metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
#align tendsto_uniformity_iff_dist_tendsto_zero tendsto_uniformity_iff_dist_tendsto_zero

/- warning: filter.tendsto.congr_dist -> Filter.Tendsto.congr_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u2}} {f₁ : ι -> α} {f₂ : ι -> α} {p : Filter.{u2} ι} {a : α}, (Filter.Tendsto.{u2, u1} ι α f₁ p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (Filter.Tendsto.{u2, 0} ι Real (fun (x : ι) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f₁ x) (f₂ x)) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Filter.Tendsto.{u2, u1} ι α f₂ p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {f₁ : ι -> α} {f₂ : ι -> α} {p : Filter.{u1} ι} {a : α}, (Filter.Tendsto.{u1, u2} ι α f₁ p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) a)) -> (Filter.Tendsto.{u1, 0} ι Real (fun (x : ι) => Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f₁ x) (f₂ x)) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Filter.Tendsto.{u1, u2} ι α f₂ p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.congr_dist Filter.Tendsto.congr_distₓ'. -/
theorem Filter.Tendsto.congr_dist {ι : Type _} {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) :
    Tendsto f₂ p (𝓝 a) :=
  h₁.congr_uniformity <| tendsto_uniformity_iff_dist_tendsto_zero.2 h
#align filter.tendsto.congr_dist Filter.Tendsto.congr_dist

/- warning: tendsto_of_tendsto_of_dist -> tendsto_of_tendsto_of_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u2}} {f₁ : ι -> α} {f₂ : ι -> α} {p : Filter.{u2} ι} {a : α}, (Filter.Tendsto.{u2, u1} ι α f₁ p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (Filter.Tendsto.{u2, 0} ι Real (fun (x : ι) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f₁ x) (f₂ x)) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Filter.Tendsto.{u2, u1} ι α f₂ p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {f₁ : ι -> α} {f₂ : ι -> α} {p : Filter.{u1} ι} {a : α}, (Filter.Tendsto.{u1, u2} ι α f₁ p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) a)) -> (Filter.Tendsto.{u1, 0} ι Real (fun (x : ι) => Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f₁ x) (f₂ x)) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Filter.Tendsto.{u1, u2} ι α f₂ p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align tendsto_of_tendsto_of_dist tendsto_of_tendsto_of_distₓ'. -/
alias Filter.Tendsto.congr_dist ← tendsto_of_tendsto_of_dist
#align tendsto_of_tendsto_of_dist tendsto_of_tendsto_of_dist

/- warning: tendsto_iff_of_dist -> tendsto_iff_of_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {ι : Type.{u2}} {f₁ : ι -> α} {f₂ : ι -> α} {p : Filter.{u2} ι} {a : α}, (Filter.Tendsto.{u2, 0} ι Real (fun (x : ι) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f₁ x) (f₂ x)) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Iff (Filter.Tendsto.{u2, u1} ι α f₁ p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (Filter.Tendsto.{u2, u1} ι α f₂ p (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {ι : Type.{u1}} {f₁ : ι -> α} {f₂ : ι -> α} {p : Filter.{u1} ι} {a : α}, (Filter.Tendsto.{u1, 0} ι Real (fun (x : ι) => Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f₁ x) (f₂ x)) p (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Iff (Filter.Tendsto.{u1, u2} ι α f₁ p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) a)) (Filter.Tendsto.{u1, u2} ι α f₂ p (nhds.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) a)))
Case conversion may be inaccurate. Consider using '#align tendsto_iff_of_dist tendsto_iff_of_distₓ'. -/
theorem tendsto_iff_of_dist {ι : Type _} {f₁ f₂ : ι → α} {p : Filter ι} {a : α}
    (h : Tendsto (fun x => dist (f₁ x) (f₂ x)) p (𝓝 0)) : Tendsto f₁ p (𝓝 a) ↔ Tendsto f₂ p (𝓝 a) :=
  Uniform.tendsto_congr <| tendsto_uniformity_iff_dist_tendsto_zero.2 h
#align tendsto_iff_of_dist tendsto_iff_of_dist

/- warning: eventually_closed_ball_subset -> eventually_closedBall_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {u : Set.{u1} α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) u (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) -> (Filter.Eventually.{0} Real (fun (r : Real) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.closedBall.{u1} α _inst_1 x r) u) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {u : Set.{u1} α}, (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) u (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) x)) -> (Filter.Eventually.{0} Real (fun (r : Real) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.closedBall.{u1} α _inst_1 x r) u) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align eventually_closed_ball_subset eventually_closedBall_subsetₓ'. -/
/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`closed_ball x r` is contained in `u`. -/
theorem eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u :=
  by
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : _)(hε : 0 < ε), closed_ball x ε ⊆ u :=
    nhds_basis_closed_ball.mem_iff.1 hu
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos
  filter_upwards [this]with _ hr using subset.trans (closed_ball_subset_closed_ball hr) hε
#align eventually_closed_ball_subset eventually_closedBall_subset

end Real

section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/- warning: metric.cauchy_seq_iff -> Metric.cauchySeq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (m : β), (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) m N) -> (forall (n : β), (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u m) (u n)) ε)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} β (fun (N : β) => forall (m : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) m N) -> (forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u m) (u n)) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.cauchy_seq_iff Metric.cauchySeq_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (m n «expr ≥ » N) -/
-- see Note [nolint_ge]
/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
@[nolint ge_or_gt]
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ (m) (_ : m ≥ N) (n) (_ : n ≥ N), dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff
#align metric.cauchy_seq_iff Metric.cauchySeq_iff

/- warning: metric.cauchy_seq_iff' -> Metric.cauchySeq_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u n) (u N)) ε))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {u : β -> α}, Iff (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 u) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} β (fun (N : β) => forall (n : β), (GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u n) (u N)) ε))))
Case conversion may be inaccurate. Consider using '#align metric.cauchy_seq_iff' Metric.cauchySeq_iff'ₓ'. -/
/-- A variation around the pseudometric characterization of Cauchy sequences -/
theorem Metric.cauchySeq_iff' {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε :=
  uniformity_basis_dist.cauchySeq_iff'
#align metric.cauchy_seq_iff' Metric.cauchySeq_iff'

/- warning: metric.uniform_cauchy_seq_on_iff -> Metric.uniformCauchySeqOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {γ : Type.{u3}} {F : β -> γ -> α} {s : Set.{u3} γ}, Iff (UniformCauchySeqOn.{u3, u1, u2} γ α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) F (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (N : β) => forall (m : β), (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) m N) -> (forall (n : β), (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n N) -> (forall (x : γ), (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) x s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (F m x) (F n x)) ε))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : Nonempty.{succ u3} β] [_inst_3 : SemilatticeSup.{u3} β] {γ : Type.{u1}} {F : β -> γ -> α} {s : Set.{u1} γ}, Iff (UniformCauchySeqOn.{u1, u2, u3} γ α β (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1) F (Filter.atTop.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u3} β (fun (N : β) => forall (m : β), (GE.ge.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) m N) -> (forall (n : β), (GE.ge.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_3))) n N) -> (forall (x : γ), (Membership.mem.{u1, u1} γ (Set.{u1} γ) (Set.instMembershipSet.{u1} γ) x s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (F m x) (F n x)) ε))))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_cauchy_seq_on_iff Metric.uniformCauchySeqOn_iffₓ'. -/
-- see Note [nolint_ge]
/-- In a pseudometric space, unifom Cauchy sequences are characterized by the fact that, eventually,
the distance between all its elements is uniformly, arbitrarily small -/
@[nolint ge_or_gt]
theorem Metric.uniformCauchySeqOn_iff {γ : Type _} {F : β → γ → α} {s : Set γ} :
    UniformCauchySeqOn F atTop s ↔
      ∀ ε : ℝ,
        ε > 0 →
          ∃ N : β, ∀ m : β, m ≥ N → ∀ n : β, n ≥ N → ∀ x : γ, x ∈ s → dist (F m x) (F n x) < ε :=
  by
  constructor
  · intro h ε hε
    let u := { a : α × α | dist a.fst a.snd < ε }
    have hu : u ∈ 𝓤 α := metric.mem_uniformity_dist.mpr ⟨ε, hε, fun a b => by simp⟩
    rw [←
      @Filter.eventually_atTop_prod_self' _ _ _ fun m =>
        ∀ x : γ, x ∈ s → dist (F m.fst x) (F m.snd x) < ε]
    specialize h u hu
    rw [prod_at_top_at_top_eq] at h
    exact h.mono fun n h x hx => set.mem_set_of_eq.mp (h x hx)
  · intro h u hu
    rcases metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hab⟩
    rcases h ε hε with ⟨N, hN⟩
    rw [prod_at_top_at_top_eq, eventually_at_top]
    use (N, N)
    intro b hb x hx
    rcases hb with ⟨hbl, hbr⟩
    exact hab (hN b.fst hbl.ge b.snd hbr.ge x hx)
#align metric.uniform_cauchy_seq_on_iff Metric.uniformCauchySeqOn_iff

/- warning: cauchy_seq_of_le_tendsto_0' -> cauchySeq_of_le_tendsto_0' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {s : β -> α} (b : β -> Real), (forall (n : β) (m : β), (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n m) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (s n) (s m)) (b n))) -> (Filter.Tendsto.{u2, 0} β Real b (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {s : β -> α} (b : β -> Real), (forall (n : β) (m : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) n m) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (s n) (s m)) (b n))) -> (Filter.Tendsto.{u2, 0} β Real b (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 s)
Case conversion may be inaccurate. Consider using '#align cauchy_seq_of_le_tendsto_0' cauchySeq_of_le_tendsto_0'ₓ'. -/
/-- If the distance between `s n` and `s m`, `n ≤ m` is bounded above by `b n`
and `b` converges to zero, then `s` is a Cauchy sequence.  -/
theorem cauchySeq_of_le_tendsto_0' {s : β → α} (b : β → ℝ)
    (h : ∀ n m : β, n ≤ m → dist (s n) (s m) ≤ b n) (h₀ : Tendsto b atTop (𝓝 0)) : CauchySeq s :=
  Metric.cauchySeq_iff'.2 fun ε ε0 =>
    (h₀.Eventually (gt_mem_nhds ε0)).exists.imp fun N hN n hn =>
      calc
        dist (s n) (s N) = dist (s N) (s n) := dist_comm _ _
        _ ≤ b N := (h _ _ hn)
        _ < ε := hN
        
#align cauchy_seq_of_le_tendsto_0' cauchySeq_of_le_tendsto_0'

/- warning: cauchy_seq_of_le_tendsto_0 -> cauchySeq_of_le_tendsto_0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {s : β -> α} (b : β -> Real), (forall (n : β) (m : β) (N : β), (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N m) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (s n) (s m)) (b N))) -> (Filter.Tendsto.{u2, 0} β Real b (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Nonempty.{succ u2} β] [_inst_3 : SemilatticeSup.{u2} β] {s : β -> α} (b : β -> Real), (forall (n : β) (m : β) (N : β), (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N n) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) N m) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (s n) (s m)) (b N))) -> (Filter.Tendsto.{u2, 0} β Real b (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_3))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (CauchySeq.{u1, u2} α β (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) _inst_3 s)
Case conversion may be inaccurate. Consider using '#align cauchy_seq_of_le_tendsto_0 cauchySeq_of_le_tendsto_0ₓ'. -/
/-- If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence.  -/
theorem cauchySeq_of_le_tendsto_0 {s : β → α} (b : β → ℝ)
    (h : ∀ n m N : β, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) (h₀ : Tendsto b atTop (𝓝 0)) :
    CauchySeq s :=
  cauchySeq_of_le_tendsto_0' b (fun n m hnm => h _ _ _ le_rfl hnm) h₀
#align cauchy_seq_of_le_tendsto_0 cauchySeq_of_le_tendsto_0

/- warning: cauchy_seq_bdd -> cauchySeq_bdd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {u : Nat -> α}, (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) u) -> (Exists.{1} Real (fun (R : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt R (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (m : Nat) (n : Nat), LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (u m) (u n)) R)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {u : Nat -> α}, (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (Lattice.toSemilatticeSup.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)) u) -> (Exists.{1} Real (fun (R : Real) => And (GT.gt.{0} Real Real.instLTReal R (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (m : Nat) (n : Nat), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (u m) (u n)) R)))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_bdd cauchySeq_bddₓ'. -/
/-- A Cauchy sequence on the natural numbers is bounded. -/
theorem cauchySeq_bdd {u : ℕ → α} (hu : CauchySeq u) : ∃ R > 0, ∀ m n, dist (u m) (u n) < R :=
  by
  rcases Metric.cauchySeq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩
  rsuffices ⟨R, R0, H⟩ : ∃ R > 0, ∀ n, dist (u n) (u N) < R
  ·
    exact
      ⟨_, add_pos R0 R0, fun m n =>
        lt_of_le_of_lt (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩
  let R := Finset.sup (Finset.range N) fun n => nndist (u n) (u N)
  refine' ⟨↑R + 1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, fun n => _⟩
  cases le_or_lt N n
  · exact lt_of_lt_of_le (hN _ h) (le_add_of_nonneg_left R.2)
  · have : _ ≤ R := Finset.le_sup (Finset.mem_range.2 h)
    exact lt_of_le_of_lt this (lt_add_of_pos_right _ zero_lt_one)
#align cauchy_seq_bdd cauchySeq_bdd

/- warning: cauchy_seq_iff_le_tendsto_0 -> cauchySeq_iff_le_tendsto_0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Nat -> α}, Iff (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (CanonicallyLinearOrderedAddMonoid.semilatticeSup.{0} Nat Nat.canonicallyLinearOrderedAddMonoid) s) (Exists.{1} (Nat -> Real) (fun (b : Nat -> Real) => And (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (b n)) (And (forall (n : Nat) (m : Nat) (N : Nat), (LE.le.{0} Nat Nat.hasLe N n) -> (LE.le.{0} Nat Nat.hasLe N m) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (s n) (s m)) (b N))) (Filter.Tendsto.{0, 0} Nat Real b (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Nat -> α}, Iff (CauchySeq.{u1, 0} α Nat (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (Lattice.toSemilatticeSup.{0} Nat (DistribLattice.toLattice.{0} Nat instDistribLatticeNat)) s) (Exists.{1} (Nat -> Real) (fun (b : Nat -> Real) => And (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (b n)) (And (forall (n : Nat) (m : Nat) (N : Nat), (LE.le.{0} Nat instLENat N n) -> (LE.le.{0} Nat instLENat N m) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (s n) (s m)) (b N))) (Filter.Tendsto.{0, 0} Nat Real b (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))))
Case conversion may be inaccurate. Consider using '#align cauchy_seq_iff_le_tendsto_0 cauchySeq_iff_le_tendsto_0ₓ'. -/
/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem cauchySeq_iff_le_tendsto_0 {s : ℕ → α} :
    CauchySeq s ↔
      ∃ b : ℕ → ℝ,
        (∀ n, 0 ≤ b n) ∧
          (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧ Tendsto b atTop (𝓝 0) :=
  ⟨fun hs =>
    by
    /- `s` is a Cauchy sequence. The sequence `b` will be constructed by taking
      the supremum of the distances between `s n` and `s m` for `n m ≥ N`.
      First, we prove that all these distances are bounded, as otherwise the Sup
      would not make sense. -/
    let S N := (fun p : ℕ × ℕ => dist (s p.1) (s p.2)) '' { p | p.1 ≥ N ∧ p.2 ≥ N }
    have hS : ∀ N, ∃ x, ∀ y ∈ S N, y ≤ x :=
      by
      rcases cauchySeq_bdd hs with ⟨R, R0, hR⟩
      refine' fun N => ⟨R, _⟩
      rintro _ ⟨⟨m, n⟩, _, rfl⟩
      exact le_of_lt (hR m n)
    have bdd : BddAbove (range fun p : ℕ × ℕ => dist (s p.1) (s p.2)) :=
      by
      rcases cauchySeq_bdd hs with ⟨R, R0, hR⟩
      use R
      rintro _ ⟨⟨m, n⟩, rfl⟩
      exact le_of_lt (hR m n)
    -- Prove that it bounds the distances of points in the Cauchy sequence
    have ub : ∀ m n N, N ≤ m → N ≤ n → dist (s m) (s n) ≤ Sup (S N) := fun m n N hm hn =>
      le_csSup (hS N) ⟨⟨_, _⟩, ⟨hm, hn⟩, rfl⟩
    have S0m : ∀ n, (0 : ℝ) ∈ S n := fun n => ⟨⟨n, n⟩, ⟨le_rfl, le_rfl⟩, dist_self _⟩
    have S0 := fun n => le_csSup (hS n) (S0m n)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    refine' ⟨fun N => Sup (S N), S0, ub, Metric.tendsto_atTop.2 fun ε ε0 => _⟩
    refine' (Metric.cauchySeq_iff.1 hs (ε / 2) (half_pos ε0)).imp fun N hN n hn => _
    rw [Real.dist_0_eq_abs, abs_of_nonneg (S0 n)]
    refine' lt_of_le_of_lt (csSup_le ⟨_, S0m _⟩ _) (half_lt_self ε0)
    rintro _ ⟨⟨m', n'⟩, ⟨hm', hn'⟩, rfl⟩
    exact le_of_lt (hN _ (le_trans hn hm') _ (le_trans hn hn')), fun ⟨b, _, b_bound, b_lim⟩ =>
    cauchySeq_of_le_tendsto_0 b b_bound b_lim⟩
#align cauchy_seq_iff_le_tendsto_0 cauchySeq_iff_le_tendsto_0

end CauchySeq

#print PseudoMetricSpace.induced /-
/-- Pseudometric space structure pulled back by a function. -/
def PseudoMetricSpace.induced {α β} (f : α → β) (m : PseudoMetricSpace β) : PseudoMetricSpace α
    where
  dist x y := dist (f x) (f y)
  dist_self x := dist_self _
  dist_comm x y := dist_comm _ _
  dist_triangle x y z := dist_triangle _ _ _
  edist x y := edist (f x) (f y)
  edist_dist x y := edist_dist _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_dist := (uniformity_basis_dist.comap _).eq_biInf
  toBornology := Bornology.induced f
  cobounded_sets :=
    Set.ext <|
      compl_surjective.forall.2 fun s => by
        simp only [compl_mem_comap, Filter.mem_sets, ← is_bounded_def, mem_set_of_eq, compl_compl,
          is_bounded_iff, ball_image_iff]
#align pseudo_metric_space.induced PseudoMetricSpace.induced
-/

#print Inducing.comapPseudoMetricSpace /-
/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`pseudo_metric_space.induced` useful in case if the domain already has a `topological_space`
structure. -/
def Inducing.comapPseudoMetricSpace {α β} [TopologicalSpace α] [PseudoMetricSpace β] {f : α → β}
    (hf : Inducing f) : PseudoMetricSpace α :=
  (PseudoMetricSpace.induced f ‹_›).replaceTopology hf.induced
#align inducing.comap_pseudo_metric_space Inducing.comapPseudoMetricSpace
-/

#print UniformInducing.comapPseudoMetricSpace /-
/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`pseudo_metric_space.induced` useful in case if the domain already has a `uniform_space`
structure. -/
def UniformInducing.comapPseudoMetricSpace {α β} [UniformSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : UniformInducing f) : PseudoMetricSpace α :=
  (PseudoMetricSpace.induced f ‹_›).replaceUniformity h.comap_uniformity.symm
#align uniform_inducing.comap_pseudo_metric_space UniformInducing.comapPseudoMetricSpace
-/

#print Subtype.pseudoMetricSpace /-
instance Subtype.pseudoMetricSpace {p : α → Prop} : PseudoMetricSpace (Subtype p) :=
  PseudoMetricSpace.induced coe ‹_›
#align subtype.pseudo_metric_space Subtype.pseudoMetricSpace
-/

#print Subtype.dist_eq /-
theorem Subtype.dist_eq {p : α → Prop} (x y : Subtype p) : dist x y = dist (x : α) y :=
  rfl
#align subtype.dist_eq Subtype.dist_eq
-/

#print Subtype.nndist_eq /-
theorem Subtype.nndist_eq {p : α → Prop} (x y : Subtype p) : nndist x y = nndist (x : α) y :=
  rfl
#align subtype.nndist_eq Subtype.nndist_eq
-/

namespace MulOpposite

@[to_additive]
instance : PseudoMetricSpace αᵐᵒᵖ :=
  PseudoMetricSpace.induced MulOpposite.unop ‹_›

#print MulOpposite.dist_unop /-
@[simp, to_additive]
theorem dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y :=
  rfl
#align mul_opposite.dist_unop MulOpposite.dist_unop
#align add_opposite.dist_unop AddOpposite.dist_unop
-/

#print MulOpposite.dist_op /-
@[simp, to_additive]
theorem dist_op (x y : α) : dist (op x) (op y) = dist x y :=
  rfl
#align mul_opposite.dist_op MulOpposite.dist_op
#align add_opposite.dist_op AddOpposite.dist_op
-/

#print MulOpposite.nndist_unop /-
@[simp, to_additive]
theorem nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y :=
  rfl
#align mul_opposite.nndist_unop MulOpposite.nndist_unop
#align add_opposite.nndist_unop AddOpposite.nndist_unop
-/

#print MulOpposite.nndist_op /-
@[simp, to_additive]
theorem nndist_op (x y : α) : nndist (op x) (op y) = nndist x y :=
  rfl
#align mul_opposite.nndist_op MulOpposite.nndist_op
#align add_opposite.nndist_op AddOpposite.nndist_op
-/

end MulOpposite

section NNReal

instance : PseudoMetricSpace ℝ≥0 :=
  Subtype.pseudoMetricSpace

/- warning: nnreal.dist_eq -> NNReal.dist_eq is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal), Eq.{1} Real (Dist.dist.{0} NNReal (PseudoMetricSpace.toHasDist.{0} NNReal NNReal.pseudoMetricSpace) a b) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) b)))
but is expected to have type
  forall (a : NNReal) (b : NNReal), Eq.{1} Real (Dist.dist.{0} NNReal (PseudoMetricSpace.toDist.{0} NNReal instPseudoMetricSpaceNNReal) a b) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (NNReal.toReal a) (NNReal.toReal b)))
Case conversion may be inaccurate. Consider using '#align nnreal.dist_eq NNReal.dist_eqₓ'. -/
theorem NNReal.dist_eq (a b : ℝ≥0) : dist a b = |(a : ℝ) - b| :=
  rfl
#align nnreal.dist_eq NNReal.dist_eq

/- warning: nnreal.nndist_eq -> NNReal.nndist_eq is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal), Eq.{1} NNReal (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal NNReal.pseudoMetricSpace) a b) (LinearOrder.max.{0} NNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot)) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) a b) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) b a))
but is expected to have type
  forall (a : NNReal) (b : NNReal), Eq.{1} NNReal (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal instPseudoMetricSpaceNNReal) a b) (Max.max.{0} NNReal (CanonicallyLinearOrderedSemifield.toMax.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) a b) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) b a))
Case conversion may be inaccurate. Consider using '#align nnreal.nndist_eq NNReal.nndist_eqₓ'. -/
theorem NNReal.nndist_eq (a b : ℝ≥0) : nndist a b = max (a - b) (b - a) :=
  by
  wlog h : b ≤ a
  · rw [nndist_comm, max_comm]
    exact this b a (le_of_not_le h)
  rw [← NNReal.coe_eq, ← dist_nndist, NNReal.dist_eq, tsub_eq_zero_iff_le.2 h,
    max_eq_left (zero_le <| a - b), ← NNReal.coe_sub h, abs_of_nonneg (a - b).coe_nonneg]
#align nnreal.nndist_eq NNReal.nndist_eq

/- warning: nnreal.nndist_zero_eq_val -> NNReal.nndist_zero_eq_val is a dubious translation:
lean 3 declaration is
  forall (z : NNReal), Eq.{1} NNReal (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal NNReal.pseudoMetricSpace) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) z) z
but is expected to have type
  forall (z : NNReal), Eq.{1} NNReal (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal instPseudoMetricSpaceNNReal) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) z) z
Case conversion may be inaccurate. Consider using '#align nnreal.nndist_zero_eq_val NNReal.nndist_zero_eq_valₓ'. -/
@[simp]
theorem NNReal.nndist_zero_eq_val (z : ℝ≥0) : nndist 0 z = z := by
  simp only [NNReal.nndist_eq, max_eq_right, tsub_zero, zero_tsub, zero_le']
#align nnreal.nndist_zero_eq_val NNReal.nndist_zero_eq_val

/- warning: nnreal.nndist_zero_eq_val' -> NNReal.nndist_zero_eq_val' is a dubious translation:
lean 3 declaration is
  forall (z : NNReal), Eq.{1} NNReal (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal NNReal.pseudoMetricSpace) z (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) z
but is expected to have type
  forall (z : NNReal), Eq.{1} NNReal (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal instPseudoMetricSpaceNNReal) z (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) z
Case conversion may be inaccurate. Consider using '#align nnreal.nndist_zero_eq_val' NNReal.nndist_zero_eq_val'ₓ'. -/
@[simp]
theorem NNReal.nndist_zero_eq_val' (z : ℝ≥0) : nndist z 0 = z :=
  by
  rw [nndist_comm]
  exact NNReal.nndist_zero_eq_val z
#align nnreal.nndist_zero_eq_val' NNReal.nndist_zero_eq_val'

/- warning: nnreal.le_add_nndist -> NNReal.le_add_nndist is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal NNReal.pseudoMetricSpace) a b))
but is expected to have type
  forall (a : NNReal) (b : NNReal), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) b (NNDist.nndist.{0} NNReal (PseudoMetricSpace.toNNDist.{0} NNReal instPseudoMetricSpaceNNReal) a b))
Case conversion may be inaccurate. Consider using '#align nnreal.le_add_nndist NNReal.le_add_nndistₓ'. -/
theorem NNReal.le_add_nndist (a b : ℝ≥0) : a ≤ b + nndist a b :=
  by
  suffices (a : ℝ) ≤ (b : ℝ) + dist a b by exact nnreal.coe_le_coe.mp this
  linarith [le_of_abs_le (by rfl : abs (a - b : ℝ) ≤ dist a b)]
#align nnreal.le_add_nndist NNReal.le_add_nndist

end NNReal

section ULift

variable [PseudoMetricSpace β]

instance : PseudoMetricSpace (ULift β) :=
  PseudoMetricSpace.induced ULift.down ‹_›

/- warning: ulift.dist_eq -> ULift.dist_eq is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] (x : ULift.{u2, u1} β) (y : ULift.{u2, u1} β), Eq.{1} Real (Dist.dist.{max u1 u2} (ULift.{u2, u1} β) (PseudoMetricSpace.toHasDist.{max u1 u2} (ULift.{u2, u1} β) (ULift.pseudoMetricSpace.{u1, u2} β _inst_2)) x y) (Dist.dist.{u1} β (PseudoMetricSpace.toHasDist.{u1} β _inst_2) (ULift.down.{u2, u1} β x) (ULift.down.{u2, u1} β y))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : PseudoMetricSpace.{u2} β] (x : ULift.{u1, u2} β) (y : ULift.{u1, u2} β), Eq.{1} Real (Dist.dist.{max u2 u1} (ULift.{u1, u2} β) (PseudoMetricSpace.toDist.{max u2 u1} (ULift.{u1, u2} β) (instPseudoMetricSpaceULift.{u2, u1} β _inst_2)) x y) (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (ULift.down.{u1, u2} β x) (ULift.down.{u1, u2} β y))
Case conversion may be inaccurate. Consider using '#align ulift.dist_eq ULift.dist_eqₓ'. -/
theorem ULift.dist_eq (x y : ULift β) : dist x y = dist x.down y.down :=
  rfl
#align ulift.dist_eq ULift.dist_eq

/- warning: ulift.nndist_eq -> ULift.nndist_eq is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] (x : ULift.{u2, u1} β) (y : ULift.{u2, u1} β), Eq.{1} NNReal (NNDist.nndist.{max u1 u2} (ULift.{u2, u1} β) (PseudoMetricSpace.toNNDist.{max u1 u2} (ULift.{u2, u1} β) (ULift.pseudoMetricSpace.{u1, u2} β _inst_2)) x y) (NNDist.nndist.{u1} β (PseudoMetricSpace.toNNDist.{u1} β _inst_2) (ULift.down.{u2, u1} β x) (ULift.down.{u2, u1} β y))
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : PseudoMetricSpace.{u2} β] (x : ULift.{u1, u2} β) (y : ULift.{u1, u2} β), Eq.{1} NNReal (NNDist.nndist.{max u2 u1} (ULift.{u1, u2} β) (PseudoMetricSpace.toNNDist.{max u2 u1} (ULift.{u1, u2} β) (instPseudoMetricSpaceULift.{u2, u1} β _inst_2)) x y) (NNDist.nndist.{u2} β (PseudoMetricSpace.toNNDist.{u2} β _inst_2) (ULift.down.{u1, u2} β x) (ULift.down.{u1, u2} β y))
Case conversion may be inaccurate. Consider using '#align ulift.nndist_eq ULift.nndist_eqₓ'. -/
theorem ULift.nndist_eq (x y : ULift β) : nndist x y = nndist x.down y.down :=
  rfl
#align ulift.nndist_eq ULift.nndist_eq

/- warning: ulift.dist_up_up -> ULift.dist_up_up is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] (x : β) (y : β), Eq.{1} Real (Dist.dist.{max u1 u2} (ULift.{u2, u1} β) (PseudoMetricSpace.toHasDist.{max u1 u2} (ULift.{u2, u1} β) (ULift.pseudoMetricSpace.{u1, u2} β _inst_2)) (ULift.up.{u2, u1} β x) (ULift.up.{u2, u1} β y)) (Dist.dist.{u1} β (PseudoMetricSpace.toHasDist.{u1} β _inst_2) x y)
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : PseudoMetricSpace.{u2} β] (x : β) (y : β), Eq.{1} Real (Dist.dist.{max u2 u1} (ULift.{u1, u2} β) (PseudoMetricSpace.toDist.{max u2 u1} (ULift.{u1, u2} β) (instPseudoMetricSpaceULift.{u2, u1} β _inst_2)) (ULift.up.{u1, u2} β x) (ULift.up.{u1, u2} β y)) (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) x y)
Case conversion may be inaccurate. Consider using '#align ulift.dist_up_up ULift.dist_up_upₓ'. -/
@[simp]
theorem ULift.dist_up_up (x y : β) : dist (ULift.up x) (ULift.up y) = dist x y :=
  rfl
#align ulift.dist_up_up ULift.dist_up_up

/- warning: ulift.nndist_up_up -> ULift.nndist_up_up is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] (x : β) (y : β), Eq.{1} NNReal (NNDist.nndist.{max u1 u2} (ULift.{u2, u1} β) (PseudoMetricSpace.toNNDist.{max u1 u2} (ULift.{u2, u1} β) (ULift.pseudoMetricSpace.{u1, u2} β _inst_2)) (ULift.up.{u2, u1} β x) (ULift.up.{u2, u1} β y)) (NNDist.nndist.{u1} β (PseudoMetricSpace.toNNDist.{u1} β _inst_2) x y)
but is expected to have type
  forall {β : Type.{u2}} [_inst_2 : PseudoMetricSpace.{u2} β] (x : β) (y : β), Eq.{1} NNReal (NNDist.nndist.{max u2 u1} (ULift.{u1, u2} β) (PseudoMetricSpace.toNNDist.{max u2 u1} (ULift.{u1, u2} β) (instPseudoMetricSpaceULift.{u2, u1} β _inst_2)) (ULift.up.{u1, u2} β x) (ULift.up.{u1, u2} β y)) (NNDist.nndist.{u2} β (PseudoMetricSpace.toNNDist.{u2} β _inst_2) x y)
Case conversion may be inaccurate. Consider using '#align ulift.nndist_up_up ULift.nndist_up_upₓ'. -/
@[simp]
theorem ULift.nndist_up_up (x y : β) : nndist (ULift.up x) (ULift.up y) = nndist x y :=
  rfl
#align ulift.nndist_up_up ULift.nndist_up_up

end ULift

section Prod

variable [PseudoMetricSpace β]

#print Prod.pseudoMetricSpaceMax /-
instance Prod.pseudoMetricSpaceMax : PseudoMetricSpace (α × β) :=
  (PseudoEMetricSpace.toPseudoMetricSpaceOfDist (fun x y : α × β => dist x.1 y.1 ⊔ dist x.2 y.2)
        (fun x y => (max_lt (edist_lt_top _ _) (edist_lt_top _ _)).Ne) fun x y => by
        simp only [sup_eq_max, dist_edist, ←
          ENNReal.toReal_max (edist_ne_top _ _) (edist_ne_top _ _), Prod.edist_eq]).replaceBornology
    fun s =>
    by
    simp only [← is_bounded_image_fst_and_snd, is_bounded_iff_eventually, ball_image_iff, ←
      eventually_and, ← forall_and, ← max_le_iff]
    rfl
#align prod.pseudo_metric_space_max Prod.pseudoMetricSpaceMax
-/

/- warning: prod.dist_eq -> Prod.dist_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Eq.{1} Real (Dist.dist.{max u1 u2} (Prod.{u1, u2} α β) (PseudoMetricSpace.toHasDist.{max u1 u2} (Prod.{u1, u2} α β) (Prod.pseudoMetricSpaceMax.{u1, u2} α β _inst_1 _inst_2)) x y) (LinearOrder.max.{0} Real Real.linearOrder (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : PseudoMetricSpace.{u2} β] {x : Prod.{u1, u2} α β} {y : Prod.{u1, u2} α β}, Eq.{1} Real (Dist.dist.{max u1 u2} (Prod.{u1, u2} α β) (PseudoMetricSpace.toDist.{max u1 u2} (Prod.{u1, u2} α β) (Prod.pseudoMetricSpaceMax.{u1, u2} α β _inst_1 _inst_2)) x y) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u2} α β x) (Prod.fst.{u1, u2} α β y)) (Dist.dist.{u2} β (PseudoMetricSpace.toDist.{u2} β _inst_2) (Prod.snd.{u1, u2} α β x) (Prod.snd.{u1, u2} α β y)))
Case conversion may be inaccurate. Consider using '#align prod.dist_eq Prod.dist_eqₓ'. -/
theorem Prod.dist_eq {x y : α × β} : dist x y = max (dist x.1 y.1) (dist x.2 y.2) :=
  rfl
#align prod.dist_eq Prod.dist_eq

#print dist_prod_same_left /-
@[simp]
theorem dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ := by
  simp [Prod.dist_eq, dist_nonneg]
#align dist_prod_same_left dist_prod_same_left
-/

#print dist_prod_same_right /-
@[simp]
theorem dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ := by
  simp [Prod.dist_eq, dist_nonneg]
#align dist_prod_same_right dist_prod_same_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print ball_prod_same /-
theorem ball_prod_same (x : α) (y : β) (r : ℝ) : ball x r ×ˢ ball y r = ball (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]
#align ball_prod_same ball_prod_same
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print closedBall_prod_same /-
theorem closedBall_prod_same (x : α) (y : β) (r : ℝ) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r :=
  ext fun z => by simp [Prod.dist_eq]
#align closed_ball_prod_same closedBall_prod_same
-/

end Prod

/- warning: uniform_continuous_dist -> uniformContinuous_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], UniformContinuous.{u1, 0} (Prod.{u1, u1} α α) Real (Prod.uniformSpace.{u1, u1} α α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (fun (p : Prod.{u1, u1} α α) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], UniformContinuous.{u1, 0} (Prod.{u1, u1} α α) Real (instUniformSpaceProd.{u1, u1} α α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace) (fun (p : Prod.{u1, u1} α α) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_dist uniformContinuous_distₓ'. -/
theorem uniformContinuous_dist : UniformContinuous fun p : α × α => dist p.1 p.2 :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, by
      suffices
      · intro p q h
        cases' p with p₁ p₂
        cases' q with q₁ q₂
        cases' max_lt_iff.1 h with h₁ h₂
        clear h
        dsimp at h₁ h₂⊢
        rw [Real.dist_eq]
        refine' abs_sub_lt_iff.2 ⟨_, _⟩
        · revert p₁ p₂ q₁ q₂ h₁ h₂
          exact this
        · apply this <;> rwa [dist_comm]
      intro p₁ p₂ q₁ q₂ h₁ h₂
      have :=
        add_lt_add (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₁ q₁ p₂) h₁)).1
          (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₂ q₂ q₁) h₂)).1
      rwa [add_halves, dist_comm p₂, sub_add_sub_cancel, dist_comm q₂] at this⟩
#align uniform_continuous_dist uniformContinuous_dist

#print UniformContinuous.dist /-
theorem UniformContinuous.dist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => dist (f b) (g b) :=
  uniformContinuous_dist.comp (hf.prod_mk hg)
#align uniform_continuous.dist UniformContinuous.dist
-/

/- warning: continuous_dist -> continuous_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Continuous.{u1, 0} (Prod.{u1, u1} α α) Real (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{u1, u1} α α) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Continuous.{u1, 0} (Prod.{u1, u1} α α) Real (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (p : Prod.{u1, u1} α α) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align continuous_dist continuous_distₓ'. -/
@[continuity]
theorem continuous_dist : Continuous fun p : α × α => dist p.1 p.2 :=
  uniformContinuous_dist.Continuous
#align continuous_dist continuous_dist

#print Continuous.dist /-
@[continuity]
theorem Continuous.dist [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => dist (f b) (g b) :=
  continuous_dist.comp (hf.prod_mk hg : _)
#align continuous.dist Continuous.dist
-/

#print Filter.Tendsto.dist /-
theorem Filter.Tendsto.dist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => dist (f x) (g x)) x (𝓝 (dist a b)) :=
  (continuous_dist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.dist Filter.Tendsto.dist
-/

/- warning: nhds_comap_dist -> nhds_comap_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, 0} α Real (fun (a' : α) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a' a) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (a : α), Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, 0} α Real (fun (a' : α) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a' a) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align nhds_comap_dist nhds_comap_distₓ'. -/
theorem nhds_comap_dist (a : α) : ((𝓝 (0 : ℝ)).comap fun a' => dist a' a) = 𝓝 a := by
  simp only [@nhds_eq_comap_uniformity α, Metric.uniformity_eq_comap_nhds_zero, comap_comap,
    (· ∘ ·), dist_comm]
#align nhds_comap_dist nhds_comap_dist

/- warning: tendsto_iff_dist_tendsto_zero -> tendsto_iff_dist_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α} {x : Filter.{u2} β} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α f x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (Filter.Tendsto.{u2, 0} β Real (fun (b : β) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f b) a) x (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α} {x : Filter.{u2} β} {a : α}, Iff (Filter.Tendsto.{u2, u1} β α f x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) (Filter.Tendsto.{u2, 0} β Real (fun (b : β) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f b) a) x (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align tendsto_iff_dist_tendsto_zero tendsto_iff_dist_tendsto_zeroₓ'. -/
theorem tendsto_iff_dist_tendsto_zero {f : β → α} {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x (𝓝 0) := by
  rw [← nhds_comap_dist a, tendsto_comap_iff]
#align tendsto_iff_dist_tendsto_zero tendsto_iff_dist_tendsto_zero

/- warning: continuous_iff_continuous_dist -> continuous_iff_continuous_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α}, Iff (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f) (Continuous.{u2, 0} (Prod.{u2, u2} β β) Real (Prod.topologicalSpace.{u2, u2} β β _inst_2 _inst_2) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Prod.{u2, u2} β β) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f (Prod.fst.{u2, u2} β β x)) (f (Prod.snd.{u2, u2} β β x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α}, Iff (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f) (Continuous.{u2, 0} (Prod.{u2, u2} β β) Real (instTopologicalSpaceProd.{u2, u2} β β _inst_2 _inst_2) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Prod.{u2, u2} β β) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f (Prod.fst.{u2, u2} β β x)) (f (Prod.snd.{u2, u2} β β x))))
Case conversion may be inaccurate. Consider using '#align continuous_iff_continuous_dist continuous_iff_continuous_distₓ'. -/
theorem continuous_iff_continuous_dist [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ Continuous fun x : β × β => dist (f x.1) (f x.2) :=
  ⟨fun h => (h.comp continuous_fst).dist (h.comp continuous_snd), fun h =>
    continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_dist_tendsto_zero.2 <|
        (h.comp (continuous_id.prod_mk continuous_const)).tendsto' _ _ <| dist_self _⟩
#align continuous_iff_continuous_dist continuous_iff_continuous_dist

/- warning: uniform_continuous_nndist -> uniformContinuous_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], UniformContinuous.{u1, 0} (Prod.{u1, u1} α α) NNReal (Prod.uniformSpace.{u1, u1} α α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace) (fun (p : Prod.{u1, u1} α α) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], UniformContinuous.{u1, 0} (Prod.{u1, u1} α α) NNReal (instUniformSpaceProd.{u1, u1} α α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal) (fun (p : Prod.{u1, u1} α α) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align uniform_continuous_nndist uniformContinuous_nndistₓ'. -/
theorem uniformContinuous_nndist : UniformContinuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_dist.subtype_mk _
#align uniform_continuous_nndist uniformContinuous_nndist

/- warning: uniform_continuous.nndist -> UniformContinuous.nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : β -> α} {g : β -> α}, (UniformContinuous.{u2, u1} β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) f) -> (UniformContinuous.{u2, u1} β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) g) -> (UniformContinuous.{u2, 0} β NNReal _inst_2 (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace) (fun (b : β) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (f b) (g b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {f : β -> α} {g : β -> α}, (UniformContinuous.{u2, u1} β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) f) -> (UniformContinuous.{u2, u1} β α _inst_2 (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) g) -> (UniformContinuous.{u2, 0} β NNReal _inst_2 (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal) (fun (b : β) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align uniform_continuous.nndist UniformContinuous.nndistₓ'. -/
theorem UniformContinuous.nndist [UniformSpace β] {f g : β → α} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous fun b => nndist (f b) (g b) :=
  uniformContinuous_nndist.comp (hf.prod_mk hg)
#align uniform_continuous.nndist UniformContinuous.nndist

/- warning: continuous_nndist -> continuous_nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Continuous.{u1, 0} (Prod.{u1, u1} α α) NNReal (Prod.topologicalSpace.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace)) (fun (p : Prod.{u1, u1} α α) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Continuous.{u1, 0} (Prod.{u1, u1} α α) NNReal (instTopologicalSpaceProd.{u1, u1} α α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))) (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (fun (p : Prod.{u1, u1} α α) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p))
Case conversion may be inaccurate. Consider using '#align continuous_nndist continuous_nndistₓ'. -/
theorem continuous_nndist : Continuous fun p : α × α => nndist p.1 p.2 :=
  uniformContinuous_nndist.Continuous
#align continuous_nndist continuous_nndist

/- warning: continuous.nndist -> Continuous.nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {g : β -> α}, (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f) -> (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) g) -> (Continuous.{u2, 0} β NNReal _inst_2 (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace)) (fun (b : β) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (f b) (g b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {f : β -> α} {g : β -> α}, (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f) -> (Continuous.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) g) -> (Continuous.{u2, 0} β NNReal _inst_2 (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (fun (b : β) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align continuous.nndist Continuous.nndistₓ'. -/
theorem Continuous.nndist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => nndist (f b) (g b) :=
  continuous_nndist.comp (hf.prod_mk hg : _)
#align continuous.nndist Continuous.nndist

/- warning: filter.tendsto.nndist -> Filter.Tendsto.nndist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α} {g : β -> α} {x : Filter.{u2} β} {a : α} {b : α}, (Filter.Tendsto.{u2, u1} β α f x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (Filter.Tendsto.{u2, u1} β α g x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) b)) -> (Filter.Tendsto.{u2, 0} β NNReal (fun (x : β) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (f x) (g x)) x (nhds.{0} NNReal (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal NNReal.pseudoMetricSpace)) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α} {g : β -> α} {x : Filter.{u2} β} {a : α} {b : α}, (Filter.Tendsto.{u2, u1} β α f x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) a)) -> (Filter.Tendsto.{u2, u1} β α g x (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) b)) -> (Filter.Tendsto.{u2, 0} β NNReal (fun (x : β) => NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) (f x) (g x)) x (nhds.{0} NNReal (UniformSpace.toTopologicalSpace.{0} NNReal (PseudoMetricSpace.toUniformSpace.{0} NNReal instPseudoMetricSpaceNNReal)) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.nndist Filter.Tendsto.nndistₓ'. -/
theorem Filter.Tendsto.nndist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
  (continuous_nndist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.nndist Filter.Tendsto.nndist

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

#print Metric.isClosed_ball /-
theorem isClosed_ball : IsClosed (closedBall x ε) :=
  isClosed_le (continuous_id.dist continuous_const) continuous_const
#align metric.is_closed_ball Metric.isClosed_ball
-/

#print Metric.isClosed_sphere /-
theorem isClosed_sphere : IsClosed (sphere x ε) :=
  isClosed_eq (continuous_id.dist continuous_const) continuous_const
#align metric.is_closed_sphere Metric.isClosed_sphere
-/

#print Metric.closure_closedBall /-
@[simp]
theorem closure_closedBall : closure (closedBall x ε) = closedBall x ε :=
  isClosed_ball.closure_eq
#align metric.closure_closed_ball Metric.closure_closedBall
-/

#print Metric.closure_sphere /-
@[simp]
theorem closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq
#align metric.closure_sphere Metric.closure_sphere
-/

#print Metric.closure_ball_subset_closedBall /-
theorem closure_ball_subset_closedBall : closure (ball x ε) ⊆ closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_ball
#align metric.closure_ball_subset_closed_ball Metric.closure_ball_subset_closedBall
-/

#print Metric.frontier_ball_subset_sphere /-
theorem frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (continuous_id.dist continuous_const) continuous_const
#align metric.frontier_ball_subset_sphere Metric.frontier_ball_subset_sphere
-/

#print Metric.frontier_closedBall_subset_sphere /-
theorem frontier_closedBall_subset_sphere : frontier (closedBall x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (continuous_id.dist continuous_const) continuous_const
#align metric.frontier_closed_ball_subset_sphere Metric.frontier_closedBall_subset_sphere
-/

#print Metric.ball_subset_interior_closedBall /-
theorem ball_subset_interior_closedBall : ball x ε ⊆ interior (closedBall x ε) :=
  interior_maximal ball_subset_closedBall isOpen_ball
#align metric.ball_subset_interior_closed_ball Metric.ball_subset_interior_closedBall
-/

/- warning: metric.mem_closure_iff -> Metric.mem_closure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) ε))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s)) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) ε))))
Case conversion may be inaccurate. Consider using '#align metric.mem_closure_iff Metric.mem_closure_iffₓ'. -/
/-- ε-characterization of the closure in pseudometric spaces-/
theorem mem_closure_iff {s : Set α} {a : α} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, dist a b < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_ball).trans <| by simp only [mem_ball, dist_comm]
#align metric.mem_closure_iff Metric.mem_closure_iff

/- warning: metric.mem_closure_range_iff -> Metric.mem_closure_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {e : β -> α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Set.range.{u1, succ u2} α β e))) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (k : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a (e k)) ε)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {e : β -> α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Set.range.{u1, succ u2} α β e))) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} β (fun (k : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a (e k)) ε)))
Case conversion may be inaccurate. Consider using '#align metric.mem_closure_range_iff Metric.mem_closure_range_iffₓ'. -/
theorem mem_closure_range_iff {e : β → α} {a : α} :
    a ∈ closure (range e) ↔ ∀ ε > 0, ∃ k : β, dist a (e k) < ε := by
  simp only [mem_closure_iff, exists_range_iff]
#align metric.mem_closure_range_iff Metric.mem_closure_range_iff

/- warning: metric.mem_closure_range_iff_nat -> Metric.mem_closure_range_iff_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {e : β -> α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Set.range.{u1, succ u2} α β e))) (forall (n : Nat), Exists.{succ u2} β (fun (k : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a (e k)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {e : β -> α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Set.range.{u1, succ u2} α β e))) (forall (n : Nat), Exists.{succ u2} β (fun (k : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a (e k)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))))
Case conversion may be inaccurate. Consider using '#align metric.mem_closure_range_iff_nat Metric.mem_closure_range_iff_natₓ'. -/
theorem mem_closure_range_iff_nat {e : β → α} {a : α} :
    a ∈ closure (range e) ↔ ∀ n : ℕ, ∃ k : β, dist a (e k) < 1 / ((n : ℝ) + 1) :=
  (mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans <| by
    simp only [mem_ball, dist_comm, exists_range_iff, forall_const]
#align metric.mem_closure_range_iff_nat Metric.mem_closure_range_iff_nat

/- warning: metric.mem_of_closed' -> Metric.mem_of_closed' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b) ε)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b) ε)))))
Case conversion may be inaccurate. Consider using '#align metric.mem_of_closed' Metric.mem_of_closed'ₓ'. -/
theorem mem_of_closed' {s : Set α} (hs : IsClosed s) {a : α} :
    a ∈ s ↔ ∀ ε > 0, ∃ b ∈ s, dist a b < ε := by
  simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a
#align metric.mem_of_closed' Metric.mem_of_closed'

/- warning: metric.closed_ball_zero' -> Metric.closedBall_zero' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Metric.closedBall.{u1} α _inst_1 x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), Eq.{succ u1} (Set.{u1} α) (Metric.closedBall.{u1} α _inst_1 x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (closure.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_zero' Metric.closedBall_zero'ₓ'. -/
theorem closedBall_zero' (x : α) : closedBall x 0 = closure {x} :=
  Subset.antisymm
    (fun y hy =>
      mem_closure_iff.2 fun ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_ball)
#align metric.closed_ball_zero' Metric.closedBall_zero'

/- warning: metric.dense_iff -> Metric.dense_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Dense.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (forall (x : α) (r : Real), (GT.gt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Metric.ball.{u1} α _inst_1 x r) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Dense.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) (forall (x : α) (r : Real), (GT.gt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Metric.ball.{u1} α _inst_1 x r) s)))
Case conversion may be inaccurate. Consider using '#align metric.dense_iff Metric.dense_iffₓ'. -/
theorem dense_iff {s : Set α} : Dense s ↔ ∀ x, ∀ r > 0, (ball x r ∩ s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, exists_prop, mem_inter_iff, mem_ball', and_comm']
#align metric.dense_iff Metric.dense_iff

/- warning: metric.dense_range_iff -> Metric.denseRange_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α}, Iff (DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) β f) (forall (x : α) (r : Real), (GT.gt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u2} β (fun (y : β) => LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x (f y)) r)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α}, Iff (DenseRange.{u1, u2} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) β f) (forall (x : α) (r : Real), (GT.gt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u2} β (fun (y : β) => LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x (f y)) r)))
Case conversion may be inaccurate. Consider using '#align metric.dense_range_iff Metric.denseRange_iffₓ'. -/
theorem denseRange_iff {f : β → α} : DenseRange f ↔ ∀ x, ∀ r > 0, ∃ y, dist x (f y) < r :=
  forall_congr' fun x => by simp only [mem_closure_iff, exists_range_iff]
#align metric.dense_range_iff Metric.denseRange_iff

/- warning: topological_space.is_separable.separable_space -> TopologicalSpace.IsSeparable.separableSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (TopologicalSpace.IsSeparable.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (TopologicalSpace.SeparableSpace.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoEMetricSpace.{u1} α] {s : Set.{u1} α}, (TopologicalSpace.IsSeparable.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (TopologicalSpace.SeparableSpace.{u1} (Set.Elem.{u1} α s) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (UniformSpace.toTopologicalSpace.{u1} α (PseudoEMetricSpace.toUniformSpace.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align topological_space.is_separable.separable_space TopologicalSpace.IsSeparable.separableSpaceₓ'. -/
/-- If a set `s` is separable, then the corresponding subtype is separable in a metric space.
This is not obvious, as the countable set whose closure covers `s` does not need in general to
be contained in `s`. -/
theorem TopologicalSpace.IsSeparable.separableSpace {s : Set α} (hs : IsSeparable s) :
    SeparableSpace s := by
  classical
    rcases eq_empty_or_nonempty s with (rfl | ⟨⟨x₀, x₀s⟩⟩)
    · infer_instance
    rcases hs with ⟨c, hc, h'c⟩
    haveI : Encodable c := hc.to_encodable
    obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
      exists_seq_strictAnti_tendsto (0 : ℝ)
    let f : c × ℕ → α := fun p =>
      if h : (Metric.ball (p.1 : α) (u p.2) ∩ s).Nonempty then h.some else x₀
    have fs : ∀ p, f p ∈ s := by
      rintro ⟨y, n⟩
      by_cases h : (ball (y : α) (u n) ∩ s).Nonempty
      · simpa only [f, h, dif_pos] using h.some_spec.2
      · simpa only [f, h, not_false_iff, dif_neg]
    let g : c × ℕ → s := fun p => ⟨f p, fs p⟩
    apply separable_space_of_dense_range g
    apply Metric.denseRange_iff.2
    rintro ⟨x, xs⟩ r (rpos : 0 < r)
    obtain ⟨n, hn⟩ : ∃ n, u n < r / 2 := ((tendsto_order.1 u_lim).2 _ (half_pos rpos)).exists
    obtain ⟨z, zc, hz⟩ : ∃ z ∈ c, dist x z < u n := Metric.mem_closure_iff.1 (h'c xs) _ (u_pos n)
    refine' ⟨(⟨z, zc⟩, n), _⟩
    change dist x (f (⟨z, zc⟩, n)) < r
    have A : (Metric.ball z (u n) ∩ s).Nonempty := ⟨x, hz, xs⟩
    dsimp [f]
    simp only [A, dif_pos]
    calc
      dist x A.some ≤ dist x z + dist z A.some := dist_triangle _ _ _
      _ < r / 2 + r / 2 := (add_lt_add (hz.trans hn) ((Metric.mem_ball'.1 A.some_spec.1).trans hn))
      _ = r := add_halves _
      
#align topological_space.is_separable.separable_space TopologicalSpace.IsSeparable.separableSpace

#print Inducing.isSeparable_preimage /-
/-- The preimage of a separable set by an inducing map is separable. -/
protected theorem Inducing.isSeparable_preimage {f : β → α} [TopologicalSpace β] (hf : Inducing f)
    {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  by
  have : second_countable_topology s :=
    haveI : separable_space s := hs.separable_space
    UniformSpace.secondCountable_of_separable _
  let g : f ⁻¹' s → s := cod_restrict (f ∘ coe) s fun x => x.2
  have : Inducing g := (hf.comp inducing_subtype_val).codRestrict _
  haveI : second_countable_topology (f ⁻¹' s) := this.second_countable_topology
  rw [show f ⁻¹' s = coe '' (univ : Set (f ⁻¹' s)) by
      simpa only [image_univ, Subtype.range_coe_subtype] ]
  exact (is_separable_of_separable_space _).image continuous_subtype_val
#align inducing.is_separable_preimage Inducing.isSeparable_preimage
-/

#print Embedding.isSeparable_preimage /-
protected theorem Embedding.isSeparable_preimage {f : β → α} [TopologicalSpace β] (hf : Embedding f)
    {s : Set α} (hs : IsSeparable s) : IsSeparable (f ⁻¹' s) :=
  hf.to_inducing.isSeparable_preimage hs
#align embedding.is_separable_preimage Embedding.isSeparable_preimage
-/

#print ContinuousOn.isSeparable_image /-
/-- If a map is continuous on a separable set `s`, then the image of `s` is also separable. -/
theorem ContinuousOn.isSeparable_image [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) (hs : IsSeparable s) : IsSeparable (f '' s) :=
  by
  rw [show f '' s = s.restrict f '' univ by ext <;> simp]
  exact
    (is_separable_univ_iff.2 hs.separable_space).image (continuousOn_iff_continuous_restrict.1 hf)
#align continuous_on.is_separable_image ContinuousOn.isSeparable_image
-/

end Metric

section Pi

open Finset

variable {π : β → Type _} [Fintype β] [∀ b, PseudoMetricSpace (π b)]

#print pseudoMetricSpacePi /-
/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
instance pseudoMetricSpacePi : PseudoMetricSpace (∀ b, π b) :=
  by
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice formula
    for the distance -/
  refine'
    (PseudoEMetricSpace.toPseudoMetricSpaceOfDist
          (fun f g : ∀ b, π b => ((sup univ fun b => nndist (f b) (g b) : ℝ≥0) : ℝ)) (fun f g => _)
          fun f g => _).replaceBornology
      fun s => _
  show edist f g ≠ ⊤
  exact ne_of_lt ((Finset.sup_lt_iff bot_lt_top).2 fun b hb => edist_lt_top _ _)
  show ↑(sup univ fun b => nndist (f b) (g b)) = (sup univ fun b => edist (f b) (g b)).toReal
  · simp only [edist_nndist, ← ENNReal.coe_finset_sup, ENNReal.coe_toReal]
  show @is_bounded _ Pi.bornology s ↔ @is_bounded _ PseudoMetricSpace.toBornology _
  · simp only [← is_bounded_def, is_bounded_iff_eventually, ← forall_is_bounded_image_eval_iff,
      ball_image_iff, ← eventually_all, Function.eval_apply, @dist_nndist (π _)]
    refine' eventually_congr ((eventually_ge_at_top 0).mono fun C hC => _)
    lift C to ℝ≥0 using hC
    refine'
      ⟨fun H x hx y hy => NNReal.coe_le_coe.2 <| Finset.sup_le fun b hb => H b x hx y hy,
        fun H b x hx y hy => NNReal.coe_le_coe.2 _⟩
    simpa only using Finset.sup_le_iff.1 (NNReal.coe_le_coe.1 <| H hx hy) b (Finset.mem_univ b)
#align pseudo_metric_space_pi pseudoMetricSpacePi
-/

/- warning: nndist_pi_def -> nndist_pi_def is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b), Eq.{1} NNReal (NNDist.nndist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toNNDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) (Finset.sup.{0, u1} NNReal β NNReal.semilatticeSup NNReal.orderBot (Finset.univ.{u1} β _inst_2) (fun (b : β) => NNDist.nndist.{u2} (π b) (PseudoMetricSpace.toNNDist.{u2} (π b) (_inst_3 b)) (f b) (g b)))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b), Eq.{1} NNReal (NNDist.nndist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toNNDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) (Finset.sup.{0, u2} NNReal β instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring (Finset.univ.{u2} β _inst_2) (fun (b : β) => NNDist.nndist.{u1} (π b) (PseudoMetricSpace.toNNDist.{u1} (π b) (_inst_3 b)) (f b) (g b)))
Case conversion may be inaccurate. Consider using '#align nndist_pi_def nndist_pi_defₓ'. -/
theorem nndist_pi_def (f g : ∀ b, π b) : nndist f g = sup univ fun b => nndist (f b) (g b) :=
  NNReal.eq rfl
#align nndist_pi_def nndist_pi_def

/- warning: dist_pi_def -> dist_pi_def is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b), Eq.{1} Real (Dist.dist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toHasDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Finset.sup.{0, u1} NNReal β NNReal.semilatticeSup NNReal.orderBot (Finset.univ.{u1} β _inst_2) (fun (b : β) => NNDist.nndist.{u2} (π b) (PseudoMetricSpace.toNNDist.{u2} (π b) (_inst_3 b)) (f b) (g b))))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b), Eq.{1} Real (Dist.dist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) (NNReal.toReal (Finset.sup.{0, u2} NNReal β instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring (Finset.univ.{u2} β _inst_2) (fun (b : β) => NNDist.nndist.{u1} (π b) (PseudoMetricSpace.toNNDist.{u1} (π b) (_inst_3 b)) (f b) (g b))))
Case conversion may be inaccurate. Consider using '#align dist_pi_def dist_pi_defₓ'. -/
theorem dist_pi_def (f g : ∀ b, π b) : dist f g = (sup univ fun b => nndist (f b) (g b) : ℝ≥0) :=
  rfl
#align dist_pi_def dist_pi_def

/- warning: nndist_pi_le_iff -> nndist_pi_le_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toNNDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u2} (π b) (PseudoMetricSpace.toNNDist.{u2} (π b) (_inst_3 b)) (f b) (g b)) r)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toNNDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} (π b) (PseudoMetricSpace.toNNDist.{u1} (π b) (_inst_3 b)) (f b) (g b)) r)
Case conversion may be inaccurate. Consider using '#align nndist_pi_le_iff nndist_pi_le_iffₓ'. -/
theorem nndist_pi_le_iff {f g : ∀ b, π b} {r : ℝ≥0} :
    nndist f g ≤ r ↔ ∀ b, nndist (f b) (g b) ≤ r := by simp [nndist_pi_def]
#align nndist_pi_le_iff nndist_pi_le_iff

/- warning: dist_pi_lt_iff -> dist_pi_lt_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Iff (LT.lt.{0} Real Real.hasLt (Dist.dist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toHasDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} (π b) (PseudoMetricSpace.toHasDist.{u2} (π b) (_inst_3 b)) (f b) (g b)) r))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Iff (LT.lt.{0} Real Real.instLTReal (Dist.dist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} (π b) (PseudoMetricSpace.toDist.{u1} (π b) (_inst_3 b)) (f b) (g b)) r))
Case conversion may be inaccurate. Consider using '#align dist_pi_lt_iff dist_pi_lt_iffₓ'. -/
theorem dist_pi_lt_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 < r) :
    dist f g < r ↔ ∀ b, dist (f b) (g b) < r :=
  by
  lift r to ℝ≥0 using hr.le
  simp [dist_pi_def, Finset.sup_lt_iff (show ⊥ < r from hr)]
#align dist_pi_lt_iff dist_pi_lt_iff

/- warning: dist_pi_le_iff -> dist_pi_le_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Iff (LE.le.{0} Real Real.hasLe (Dist.dist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toHasDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} (π b) (PseudoMetricSpace.toHasDist.{u2} (π b) (_inst_3 b)) (f b) (g b)) r))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Iff (LE.le.{0} Real Real.instLEReal (Dist.dist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} (π b) (PseudoMetricSpace.toDist.{u1} (π b) (_inst_3 b)) (f b) (g b)) r))
Case conversion may be inaccurate. Consider using '#align dist_pi_le_iff dist_pi_le_iffₓ'. -/
theorem dist_pi_le_iff {f g : ∀ b, π b} {r : ℝ} (hr : 0 ≤ r) :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r :=
  by
  lift r to ℝ≥0 using hr
  exact nndist_pi_le_iff
#align dist_pi_le_iff dist_pi_le_iff

/- warning: dist_pi_le_iff' -> dist_pi_le_iff' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] [_inst_4 : Nonempty.{succ u1} β] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : Real}, Iff (LE.le.{0} Real Real.hasLe (Dist.dist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toHasDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} (π b) (PseudoMetricSpace.toHasDist.{u2} (π b) (_inst_3 b)) (f b) (g b)) r)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] [_inst_4 : Nonempty.{succ u2} β] {f : forall (b : β), π b} {g : forall (b : β), π b} {r : Real}, Iff (LE.le.{0} Real Real.instLEReal (Dist.dist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g) r) (forall (b : β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} (π b) (PseudoMetricSpace.toDist.{u1} (π b) (_inst_3 b)) (f b) (g b)) r)
Case conversion may be inaccurate. Consider using '#align dist_pi_le_iff' dist_pi_le_iff'ₓ'. -/
theorem dist_pi_le_iff' [Nonempty β] {f g : ∀ b, π b} {r : ℝ} :
    dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r :=
  by
  by_cases hr : 0 ≤ r
  · exact dist_pi_le_iff hr
  ·
    exact
      iff_of_false (fun h => hr <| dist_nonneg.trans h) fun h =>
        hr <| dist_nonneg.trans <| h <| Classical.arbitrary _
#align dist_pi_le_iff' dist_pi_le_iff'

/- warning: dist_pi_const_le -> dist_pi_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Fintype.{u2} β] (a : α) (b : α), LE.le.{0} Real Real.hasLe (Dist.dist.{max u2 u1} (β -> α) (PseudoMetricSpace.toHasDist.{max u2 u1} (β -> α) (pseudoMetricSpacePi.{u2, u1} β (fun (_x : β) => α) _inst_2 (fun (b : β) => _inst_1))) (fun (_x : β) => a) (fun (_x : β) => b)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Fintype.{u2} β] (a : α) (b : α), LE.le.{0} Real Real.instLEReal (Dist.dist.{max u1 u2} (β -> α) (PseudoMetricSpace.toDist.{max u1 u2} (β -> α) (pseudoMetricSpacePi.{u2, u1} β (fun (_x : β) => α) _inst_2 (fun (b : β) => _inst_1))) (fun (_x : β) => a) (fun (_x : β) => b)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align dist_pi_const_le dist_pi_const_leₓ'. -/
theorem dist_pi_const_le (a b : α) : (dist (fun _ : β => a) fun _ => b) ≤ dist a b :=
  (dist_pi_le_iff dist_nonneg).2 fun _ => le_rfl
#align dist_pi_const_le dist_pi_const_le

/- warning: nndist_pi_const_le -> nndist_pi_const_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Fintype.{u2} β] (a : α) (b : α), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{max u2 u1} (β -> α) (PseudoMetricSpace.toNNDist.{max u2 u1} (β -> α) (pseudoMetricSpacePi.{u2, u1} β (fun (_x : β) => α) _inst_2 (fun (b : β) => _inst_1))) (fun (_x : β) => a) (fun (_x : β) => b)) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : Fintype.{u2} β] (a : α) (b : α), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{max u1 u2} (β -> α) (PseudoMetricSpace.toNNDist.{max u1 u2} (β -> α) (pseudoMetricSpacePi.{u2, u1} β (fun (_x : β) => α) _inst_2 (fun (b : β) => _inst_1))) (fun (_x : β) => a) (fun (_x : β) => b)) (NNDist.nndist.{u1} α (PseudoMetricSpace.toNNDist.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align nndist_pi_const_le nndist_pi_const_leₓ'. -/
theorem nndist_pi_const_le (a b : α) : (nndist (fun _ : β => a) fun _ => b) ≤ nndist a b :=
  nndist_pi_le_iff.2 fun _ => le_rfl
#align nndist_pi_const_le nndist_pi_const_le

#print dist_pi_const /-
@[simp]
theorem dist_pi_const [Nonempty β] (a b : α) : (dist (fun x : β => a) fun _ => b) = dist a b := by
  simpa only [dist_edist] using congr_arg ENNReal.toReal (edist_pi_const a b)
#align dist_pi_const dist_pi_const
-/

#print nndist_pi_const /-
@[simp]
theorem nndist_pi_const [Nonempty β] (a b : α) :
    (nndist (fun x : β => a) fun _ => b) = nndist a b :=
  NNReal.eq <| dist_pi_const a b
#align nndist_pi_const nndist_pi_const
-/

/- warning: nndist_le_pi_nndist -> nndist_le_pi_nndist is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b) (b : β), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNDist.nndist.{u2} (π b) (PseudoMetricSpace.toNNDist.{u2} (π b) (_inst_3 b)) (f b) (g b)) (NNDist.nndist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toNNDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b) (b : β), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNDist.nndist.{u1} (π b) (PseudoMetricSpace.toNNDist.{u1} (π b) (_inst_3 b)) (f b) (g b)) (NNDist.nndist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toNNDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g)
Case conversion may be inaccurate. Consider using '#align nndist_le_pi_nndist nndist_le_pi_nndistₓ'. -/
theorem nndist_le_pi_nndist (f g : ∀ b, π b) (b : β) : nndist (f b) (g b) ≤ nndist f g :=
  by
  rw [nndist_pi_def]
  exact Finset.le_sup (Finset.mem_univ b)
#align nndist_le_pi_nndist nndist_le_pi_nndist

/- warning: dist_le_pi_dist -> dist_le_pi_dist is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b) (b : β), LE.le.{0} Real Real.hasLe (Dist.dist.{u2} (π b) (PseudoMetricSpace.toHasDist.{u2} (π b) (_inst_3 b)) (f b) (g b)) (Dist.dist.{max u1 u2} (forall (b : β), π b) (PseudoMetricSpace.toHasDist.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g)
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] (f : forall (b : β), π b) (g : forall (b : β), π b) (b : β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} (π b) (PseudoMetricSpace.toDist.{u1} (π b) (_inst_3 b)) (f b) (g b)) (Dist.dist.{max u2 u1} (forall (b : β), π b) (PseudoMetricSpace.toDist.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b))) f g)
Case conversion may be inaccurate. Consider using '#align dist_le_pi_dist dist_le_pi_distₓ'. -/
theorem dist_le_pi_dist (f g : ∀ b, π b) (b : β) : dist (f b) (g b) ≤ dist f g := by
  simp only [dist_nndist, NNReal.coe_le_coe, nndist_le_pi_nndist f g b]
#align dist_le_pi_dist dist_le_pi_dist

/- warning: ball_pi -> ball_pi is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] (x : forall (b : β), π b) {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (b : β), π b)) (Metric.ball.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) (fun (b : β) => Metric.ball.{u2} (π b) (_inst_3 b) (x b) r)))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] (x : forall (b : β), π b) {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (b : β), π b)) (Metric.ball.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u2, u1} β (fun (b : β) => π b) (Set.univ.{u2} β) (fun (b : β) => Metric.ball.{u1} (π b) (_inst_3 b) (x b) r)))
Case conversion may be inaccurate. Consider using '#align ball_pi ball_piₓ'. -/
/-- An open ball in a product space is a product of open balls. See also `metric.ball_pi'`
for a version assuming `nonempty β` instead of `0 < r`. -/
theorem ball_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 < r) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  by
  ext p
  simp [dist_pi_lt_iff hr]
#align ball_pi ball_pi

/- warning: ball_pi' -> ball_pi' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] [_inst_4 : Nonempty.{succ u1} β] (x : forall (b : β), π b) (r : Real), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (b : β), π b)) (Metric.ball.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) (fun (b : β) => Metric.ball.{u2} (π b) (_inst_3 b) (x b) r))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] [_inst_4 : Nonempty.{succ u2} β] (x : forall (b : β), π b) (r : Real), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (b : β), π b)) (Metric.ball.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u2, u1} β (fun (b : β) => π b) (Set.univ.{u2} β) (fun (b : β) => Metric.ball.{u1} (π b) (_inst_3 b) (x b) r))
Case conversion may be inaccurate. Consider using '#align ball_pi' ball_pi'ₓ'. -/
/-- An open ball in a product space is a product of open balls. See also `metric.ball_pi`
for a version assuming `0 < r` instead of `nonempty β`. -/
theorem ball_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
    ball x r = Set.pi univ fun b => ball (x b) r :=
  (lt_or_le 0 r).elim (ball_pi x) fun hr => by simp [ball_eq_empty.2 hr]
#align ball_pi' ball_pi'

/- warning: closed_ball_pi -> closedBall_pi is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] (x : forall (b : β), π b) {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (b : β), π b)) (Metric.closedBall.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) (fun (b : β) => Metric.closedBall.{u2} (π b) (_inst_3 b) (x b) r)))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] (x : forall (b : β), π b) {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (b : β), π b)) (Metric.closedBall.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u2, u1} β (fun (b : β) => π b) (Set.univ.{u2} β) (fun (b : β) => Metric.closedBall.{u1} (π b) (_inst_3 b) (x b) r)))
Case conversion may be inaccurate. Consider using '#align closed_ball_pi closedBall_piₓ'. -/
/-- A closed ball in a product space is a product of closed balls. See also `metric.closed_ball_pi'`
for a version assuming `nonempty β` instead of `0 ≤ r`. -/
theorem closedBall_pi (x : ∀ b, π b) {r : ℝ} (hr : 0 ≤ r) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  by
  ext p
  simp [dist_pi_le_iff hr]
#align closed_ball_pi closedBall_pi

/- warning: closed_ball_pi' -> closedBall_pi' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {π : β -> Type.{u2}} [_inst_2 : Fintype.{u1} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u2} (π b)] [_inst_4 : Nonempty.{succ u1} β] (x : forall (b : β), π b) (r : Real), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (b : β), π b)) (Metric.closedBall.{max u1 u2} (forall (b : β), π b) (pseudoMetricSpacePi.{u1, u2} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u1, u2} β (fun (b : β) => π b) (Set.univ.{u1} β) (fun (b : β) => Metric.closedBall.{u2} (π b) (_inst_3 b) (x b) r))
but is expected to have type
  forall {β : Type.{u2}} {π : β -> Type.{u1}} [_inst_2 : Fintype.{u2} β] [_inst_3 : forall (b : β), PseudoMetricSpace.{u1} (π b)] [_inst_4 : Nonempty.{succ u2} β] (x : forall (b : β), π b) (r : Real), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (b : β), π b)) (Metric.closedBall.{max u2 u1} (forall (b : β), π b) (pseudoMetricSpacePi.{u2, u1} β (fun (b : β) => π b) _inst_2 (fun (b : β) => _inst_3 b)) x r) (Set.pi.{u2, u1} β (fun (b : β) => π b) (Set.univ.{u2} β) (fun (b : β) => Metric.closedBall.{u1} (π b) (_inst_3 b) (x b) r))
Case conversion may be inaccurate. Consider using '#align closed_ball_pi' closedBall_pi'ₓ'. -/
/-- A closed ball in a product space is a product of closed balls. See also `metric.closed_ball_pi`
for a version assuming `0 ≤ r` instead of `nonempty β`. -/
theorem closedBall_pi' [Nonempty β] (x : ∀ b, π b) (r : ℝ) :
    closedBall x r = Set.pi univ fun b => closedBall (x b) r :=
  (le_or_lt 0 r).elim (closedBall_pi x) fun hr => by simp [closed_ball_eq_empty.2 hr]
#align closed_ball_pi' closedBall_pi'

/- warning: fin.nndist_insert_nth_insert_nth -> Fin.nndist_insertNth_insertNth is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} [_inst_4 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), PseudoMetricSpace.{u1} (α i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (x : α i) (y : α i) (f : forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (g : forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)), Eq.{1} NNReal (NNDist.nndist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j) (PseudoMetricSpace.toNNDist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j) (pseudoMetricSpacePi.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α j) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_4 b))) (Fin.insertNth.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) i x f) (Fin.insertNth.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α j) i y g)) (LinearOrder.max.{0} NNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot)) (NNDist.nndist.{u1} (α i) (PseudoMetricSpace.toNNDist.{u1} (α i) (_inst_4 i)) x y) (NNDist.nndist.{u1} (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (PseudoMetricSpace.toNNDist.{u1} (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (pseudoMetricSpacePi.{0, u1} (Fin n) (fun (j : Fin n) => α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (Fin.fintype n) (fun (b : Fin n) => _inst_4 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) b)))) f g))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_4 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), PseudoMetricSpace.{u1} (α i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x : α i) (y : α i) (f : forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (g : forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)), Eq.{1} NNReal (NNDist.nndist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j) (PseudoMetricSpace.toNNDist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j) (pseudoMetricSpacePi.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α j) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_4 b))) (Fin.insertNth.{u1} n α i x f) (Fin.insertNth.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α j) i y g)) (Max.max.{0} NNReal (CanonicallyLinearOrderedSemifield.toMax.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (NNDist.nndist.{u1} (α i) (PseudoMetricSpace.toNNDist.{u1} (α i) (_inst_4 i)) x y) (NNDist.nndist.{u1} (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (PseudoMetricSpace.toNNDist.{u1} (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (pseudoMetricSpacePi.{0, u1} (Fin n) (fun (j : Fin n) => α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (Fin.fintype n) (fun (b : Fin n) => _inst_4 (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) b)))) f g))
Case conversion may be inaccurate. Consider using '#align fin.nndist_insert_nth_insert_nth Fin.nndist_insertNth_insertNthₓ'. -/
@[simp]
theorem Fin.nndist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type _}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    nndist (i.insertNth x f) (i.insertNth y g) = max (nndist x y) (nndist f g) :=
  eq_of_forall_ge_iff fun c => by simp [nndist_pi_le_iff, i.forall_iff_succ_above]
#align fin.nndist_insert_nth_insert_nth Fin.nndist_insertNth_insertNth

/- warning: fin.dist_insert_nth_insert_nth -> Fin.dist_insertNth_insertNth is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}} [_inst_4 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), PseudoMetricSpace.{u1} (α i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (x : α i) (y : α i) (f : forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (g : forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)), Eq.{1} Real (Dist.dist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j) (PseudoMetricSpace.toHasDist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), α j) (pseudoMetricSpacePi.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α j) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => _inst_4 b))) (Fin.insertNth.{u1} n (fun (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α i) i x f) (Fin.insertNth.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => α j) i y g)) (LinearOrder.max.{0} Real Real.linearOrder (Dist.dist.{u1} (α i) (PseudoMetricSpace.toHasDist.{u1} (α i) (_inst_4 i)) x y) (Dist.dist.{u1} (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (PseudoMetricSpace.toHasDist.{u1} (forall (j : Fin n), α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (pseudoMetricSpacePi.{0, u1} (Fin n) (fun (j : Fin n) => α (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) j)) (Fin.fintype n) (fun (b : Fin n) => _inst_4 (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toHasLe.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove n i) b)))) f g))
but is expected to have type
  forall {n : Nat} {α : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_4 : forall (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), PseudoMetricSpace.{u1} (α i)] (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x : α i) (y : α i) (f : forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (g : forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)), Eq.{1} Real (Dist.dist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j) (PseudoMetricSpace.toDist.{u1} (forall (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), α j) (pseudoMetricSpacePi.{0, u1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α j) (Fin.fintype (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (b : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => _inst_4 b))) (Fin.insertNth.{u1} n α i x f) (Fin.insertNth.{u1} n (fun (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => α j) i y g)) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (Dist.dist.{u1} (α i) (PseudoMetricSpace.toDist.{u1} (α i) (_inst_4 i)) x y) (Dist.dist.{u1} (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (PseudoMetricSpace.toDist.{u1} (forall (j : Fin n), α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (pseudoMetricSpacePi.{0, u1} (Fin n) (fun (j : Fin n) => α (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) j)) (Fin.fintype n) (fun (b : Fin n) => _inst_4 (FunLike.coe.{1, 1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Order.Hom.Lattice._hyg.494 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (InfHomClass.toFunLike.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Lattice.toInf.{0} (Fin n) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n)))) (Lattice.toInf.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n)) (LatticeHomClass.toInfHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (DistribLattice.toLattice.{0} (Fin n) (instDistribLattice.{0} (Fin n) (Fin.instLinearOrderFin n))) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (OrderHomClass.toLatticeHomClass.{0, 0, 0} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin n) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin.instLinearOrderFin n) (Fin.instLatticeFinHAddNatInstHAddInstAddNatOfNat n) (RelEmbedding.instRelHomClassRelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))))) (Fin.succAbove n i) b)))) f g))
Case conversion may be inaccurate. Consider using '#align fin.dist_insert_nth_insert_nth Fin.dist_insertNth_insertNthₓ'. -/
@[simp]
theorem Fin.dist_insertNth_insertNth {n : ℕ} {α : Fin (n + 1) → Type _}
    [∀ i, PseudoMetricSpace (α i)] (i : Fin (n + 1)) (x y : α i) (f g : ∀ j, α (i.succAbove j)) :
    dist (i.insertNth x f) (i.insertNth y g) = max (dist x y) (dist f g) := by
  simp only [dist_nndist, Fin.nndist_insertNth_insertNth, NNReal.coe_max]
#align fin.dist_insert_nth_insert_nth Fin.dist_insertNth_insertNth

/- warning: real.dist_le_of_mem_pi_Icc -> Real.dist_le_of_mem_pi_Icc is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : Fintype.{u1} β] {x : β -> Real} {y : β -> Real} {x' : β -> Real} {y' : β -> Real}, (Membership.Mem.{u1, u1} (β -> Real) (Set.{u1} (β -> Real)) (Set.hasMem.{u1} (β -> Real)) x (Set.Icc.{u1} (β -> Real) (Pi.preorder.{u1, 0} β (fun (ᾰ : β) => Real) (fun (i : β) => Real.preorder)) x' y')) -> (Membership.Mem.{u1, u1} (β -> Real) (Set.{u1} (β -> Real)) (Set.hasMem.{u1} (β -> Real)) y (Set.Icc.{u1} (β -> Real) (Pi.preorder.{u1, 0} β (fun (ᾰ : β) => Real) (fun (i : β) => Real.preorder)) x' y')) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} (β -> Real) (PseudoMetricSpace.toHasDist.{u1} (β -> Real) (pseudoMetricSpacePi.{u1, 0} β (fun (ᾰ : β) => Real) _inst_2 (fun (b : β) => Real.pseudoMetricSpace))) x y) (Dist.dist.{u1} (β -> Real) (PseudoMetricSpace.toHasDist.{u1} (β -> Real) (pseudoMetricSpacePi.{u1, 0} β (fun (ᾰ : β) => Real) _inst_2 (fun (b : β) => Real.pseudoMetricSpace))) x' y'))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : Fintype.{u1} β] {x : β -> Real} {y : β -> Real} {x' : β -> Real} {y' : β -> Real}, (Membership.mem.{u1, u1} (β -> Real) (Set.{u1} (β -> Real)) (Set.instMembershipSet.{u1} (β -> Real)) x (Set.Icc.{u1} (β -> Real) (Pi.preorder.{u1, 0} β (fun (ᾰ : β) => Real) (fun (i : β) => Real.instPreorderReal)) x' y')) -> (Membership.mem.{u1, u1} (β -> Real) (Set.{u1} (β -> Real)) (Set.instMembershipSet.{u1} (β -> Real)) y (Set.Icc.{u1} (β -> Real) (Pi.preorder.{u1, 0} β (fun (ᾰ : β) => Real) (fun (i : β) => Real.instPreorderReal)) x' y')) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} (β -> Real) (PseudoMetricSpace.toDist.{u1} (β -> Real) (pseudoMetricSpacePi.{u1, 0} β (fun (ᾰ : β) => Real) _inst_2 (fun (b : β) => Real.pseudoMetricSpace))) x y) (Dist.dist.{u1} (β -> Real) (PseudoMetricSpace.toDist.{u1} (β -> Real) (pseudoMetricSpacePi.{u1, 0} β (fun (ᾰ : β) => Real) _inst_2 (fun (b : β) => Real.pseudoMetricSpace))) x' y'))
Case conversion may be inaccurate. Consider using '#align real.dist_le_of_mem_pi_Icc Real.dist_le_of_mem_pi_Iccₓ'. -/
theorem Real.dist_le_of_mem_pi_Icc {x y x' y' : β → ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ dist x' y' :=
  by
  refine'
      (dist_pi_le_iff dist_nonneg).2 fun b =>
        (Real.dist_le_of_mem_uIcc _ _).trans (dist_le_pi_dist _ _ b) <;>
    refine' Icc_subset_uIcc _
  exacts[⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]
#align real.dist_le_of_mem_pi_Icc Real.dist_le_of_mem_pi_Icc

end Pi

section Compact

/- warning: finite_cover_balls_of_compact -> finite_cover_balls_of_compact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) s) -> (forall {e : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) e) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => Metric.ball.{u1} α _inst_2 x e))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) s) -> (forall {e : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) e) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (fun (h._@.Mathlib.Topology.MetricSpace.Basic._hyg.25799 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) => Metric.ball.{u1} α _inst_2 x e))))))))
Case conversion may be inaccurate. Consider using '#align finite_cover_balls_of_compact finite_cover_balls_of_compactₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
theorem finite_cover_balls_of_compact {α : Type u} [PseudoMetricSpace α] {s : Set α}
    (hs : IsCompact s) {e : ℝ} (he : 0 < e) :
    ∃ (t : _)(_ : t ⊆ s), Set.Finite t ∧ s ⊆ ⋃ x ∈ t, ball x e :=
  by
  apply hs.elim_finite_subcover_image
  · simp [is_open_ball]
  · intro x xs
    simp
    exact ⟨x, ⟨xs, by simpa⟩⟩
#align finite_cover_balls_of_compact finite_cover_balls_of_compact

/- warning: is_compact.finite_cover_balls -> IsCompact.finite_cover_balls is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) s) -> (forall {e : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) e) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (fun (H : HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) => And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => Metric.ball.{u1} α _inst_2 x e))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_2)) s) -> (forall {e : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) e) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (And (Set.Finite.{u1} α t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.iUnion.{u1, succ u1} α α (fun (x : α) => Set.iUnion.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (fun (h._@.Mathlib.Topology.MetricSpace.Basic._hyg.25799 : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) => Metric.ball.{u1} α _inst_2 x e))))))))
Case conversion may be inaccurate. Consider using '#align is_compact.finite_cover_balls IsCompact.finite_cover_ballsₓ'. -/
alias finite_cover_balls_of_compact ← IsCompact.finite_cover_balls
#align is_compact.finite_cover_balls IsCompact.finite_cover_balls

end Compact

section ProperSpace

open Metric

#print ProperSpace /-
/-- A pseudometric space is proper if all closed balls are compact. -/
class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)
#align proper_space ProperSpace
-/

export ProperSpace (isCompact_closedBall)

#print isCompact_sphere /-
/-- In a proper pseudometric space, all spheres are compact. -/
theorem isCompact_sphere {α : Type _} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    IsCompact (sphere x r) :=
  isCompact_of_isClosed_subset (isCompact_closedBall x r) isClosed_sphere sphere_subset_closedBall
#align is_compact_sphere isCompact_sphere
-/

/-- In a proper pseudometric space, any sphere is a `compact_space` when considered as a subtype. -/
instance {α : Type _} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

#print secondCountable_of_proper /-
-- see Note [lower instance priority]
/-- A proper pseudo metric space is sigma compact, and therefore second countable. -/
instance (priority := 100) secondCountable_of_proper [ProperSpace α] : SecondCountableTopology α :=
  by
  -- We already have `sigma_compact_space_of_locally_compact_second_countable`, so we don't
  -- add an instance for `sigma_compact_space`.
  suffices SigmaCompactSpace α by exact EMetric.secondCountable_of_sigmaCompact α
  rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closed_ball x n, fun n => is_compact_closed_ball _ _, Union_closed_ball_nat _⟩⟩
  · exact ⟨⟨fun n => ∅, fun n => isCompact_empty, Union_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩
#align second_countable_of_proper secondCountable_of_proper
-/

#print tendsto_dist_right_cocompact_atTop /-
theorem tendsto_dist_right_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (fun y => dist y x) (cocompact α) atTop :=
  (hasBasis_cocompact.tendsto_iffₓ atTop_basis).2 fun r hr =>
    ⟨closedBall x r, isCompact_closedBall x r, fun y hy => (not_le.1 <| mt mem_closedBall.2 hy).le⟩
#align tendsto_dist_right_cocompact_at_top tendsto_dist_right_cocompact_atTop
-/

#print tendsto_dist_left_cocompact_atTop /-
theorem tendsto_dist_left_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist x) (cocompact α) atTop := by
  simpa only [dist_comm] using tendsto_dist_right_cocompact_atTop x
#align tendsto_dist_left_cocompact_at_top tendsto_dist_left_cocompact_atTop
-/

/- warning: proper_space_of_compact_closed_ball_of_le -> properSpace_of_compact_closedBall_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (R : Real), (forall (x : α) (r : Real), (LE.le.{0} Real Real.hasLe R r) -> (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Metric.closedBall.{u1} α _inst_1 x r))) -> (ProperSpace.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (R : Real), (forall (x : α) (r : Real), (LE.le.{0} Real Real.instLEReal R r) -> (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Metric.closedBall.{u1} α _inst_1 x r))) -> (ProperSpace.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align proper_space_of_compact_closed_ball_of_le properSpace_of_compact_closedBall_of_leₓ'. -/
/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
theorem properSpace_of_compact_closedBall_of_le (R : ℝ)
    (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨by
    intro x r
    by_cases hr : R ≤ r
    · exact h x r hr
    · have : closed_ball x r = closed_ball x R ∩ closed_ball x r :=
        by
        symm
        apply inter_eq_self_of_subset_right
        exact closed_ball_subset_closed_ball (le_of_lt (not_le.1 hr))
      rw [this]
      exact (h x R le_rfl).inter_right is_closed_ball⟩
#align proper_space_of_compact_closed_ball_of_le properSpace_of_compact_closedBall_of_le

#print proper_of_compact /-
-- A compact pseudometric space is proper 
-- see Note [lower instance priority]
instance (priority := 100) proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun x r => isClosed_ball.IsCompact⟩
#align proper_of_compact proper_of_compact
-/

#print locally_compact_of_proper /-
-- see Note [lower instance priority]
/-- A proper space is locally compact -/
instance (priority := 100) locally_compact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  locallyCompactSpace_of_hasBasis (fun x => nhds_basis_closedBall) fun x ε ε0 =>
    isCompact_closedBall _ _
#align locally_compact_of_proper locally_compact_of_proper
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » t) -/
#print complete_of_proper /-
-- see Note [lower instance priority]
/-- A proper space is complete -/
instance (priority := 100) complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨by
    intro f hf
    /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
      ball (therefore compact by properness) where it is nontrivial. -/
    obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ (x) (_ : x ∈ t) (y) (_ : y ∈ t), dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closed_ball x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases(isCompact_iff_totallyBounded_isComplete.1 (is_compact_closed_ball x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩
#align complete_of_proper complete_of_proper
-/

#print prod_properSpace /-
/-- A binary product of proper spaces is proper. -/
instance prod_properSpace {α : Type _} {β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [ProperSpace α] [ProperSpace β] : ProperSpace (α × β)
    where isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    apply (is_compact_closed_ball x r).Prod (is_compact_closed_ball y r)
#align prod_proper_space prod_properSpace
-/

#print pi_properSpace /-
/-- A finite product of proper spaces is proper. -/
instance pi_properSpace {π : β → Type _} [Fintype β] [∀ b, PseudoMetricSpace (π b)]
    [h : ∀ b, ProperSpace (π b)] : ProperSpace (∀ b, π b) :=
  by
  refine' properSpace_of_compact_closedBall_of_le 0 fun x r hr => _
  rw [closedBall_pi _ hr]
  apply isCompact_univ_pi fun b => _
  apply (h b).isCompact_closedBall
#align pi_proper_space pi_properSpace
-/

variable [ProperSpace α] {x : α} {r : ℝ} {s : Set α}

/- warning: exists_pos_lt_subset_ball -> exists_pos_lt_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] {x : α} {r : Real} {s : Set.{u1} α}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Metric.ball.{u1} α _inst_1 x r)) -> (Exists.{1} Real (fun (r' : Real) => Exists.{0} (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) r' (Set.Ioo.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) r' (Set.Ioo.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Metric.ball.{u1} α _inst_1 x r'))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] {x : α} {r : Real} {s : Set.{u1} α}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Metric.ball.{u1} α _inst_1 x r)) -> (Exists.{1} Real (fun (r' : Real) => And (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) r' (Set.Ioo.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Metric.ball.{u1} α _inst_1 x r'))))
Case conversion may be inaccurate. Consider using '#align exists_pos_lt_subset_ball exists_pos_lt_subset_ballₓ'. -/
/-- If a nonempty ball in a proper space includes a closed set `s`, then there exists a nonempty
ball with the same center and a strictly smaller radius that includes `s`. -/
theorem exists_pos_lt_subset_ball (hr : 0 < r) (hs : IsClosed s) (h : s ⊆ ball x r) :
    ∃ r' ∈ Ioo 0 r, s ⊆ ball x r' :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    isCompact_of_isClosed_subset (is_compact_closed_ball x r) hs
      (subset.trans h ball_subset_closed_ball)
  obtain ⟨y, hys, hy⟩ : ∃ y ∈ s, s ⊆ closed_ball x (dist y x)
  exact this.exists_forall_ge hne (continuous_id.dist continuous_const).ContinuousOn
  have hyr : dist y x < r := h hys
  rcases exists_between hyr with ⟨r', hyr', hrr'⟩
  exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, subset.trans hy <| closed_ball_subset_ball hyr'⟩
#align exists_pos_lt_subset_ball exists_pos_lt_subset_ball

/- warning: exists_lt_subset_ball -> exists_lt_subset_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] {x : α} {r : Real} {s : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Metric.ball.{u1} α _inst_1 x r)) -> (Exists.{1} Real (fun (r' : Real) => Exists.{0} (LT.lt.{0} Real Real.hasLt r' r) (fun (H : LT.lt.{0} Real Real.hasLt r' r) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Metric.ball.{u1} α _inst_1 x r'))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] {x : α} {r : Real} {s : Set.{u1} α}, (IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Metric.ball.{u1} α _inst_1 x r)) -> (Exists.{1} Real (fun (r' : Real) => And (LT.lt.{0} Real Real.instLTReal r' r) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Metric.ball.{u1} α _inst_1 x r'))))
Case conversion may be inaccurate. Consider using '#align exists_lt_subset_ball exists_lt_subset_ballₓ'. -/
/-- If a ball in a proper space includes a closed set `s`, then there exists a ball with the same
center and a strictly smaller radius that includes `s`. -/
theorem exists_lt_subset_ball (hs : IsClosed s) (h : s ⊆ ball x r) : ∃ r' < r, s ⊆ ball x r' :=
  by
  cases' le_or_lt r 0 with hr hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.fst.2, hr'.snd⟩
#align exists_lt_subset_ball exists_lt_subset_ball

end ProperSpace

#print IsCompact.isSeparable /-
theorem IsCompact.isSeparable {s : Set α} (hs : IsCompact s) : IsSeparable s :=
  haveI : CompactSpace s := is_compact_iff_compact_space.mp hs
  is_separable_of_separable_space_subtype s
#align is_compact.is_separable IsCompact.isSeparable
-/

namespace Metric

section SecondCountable

open TopologicalSpace

/- warning: metric.second_countable_of_almost_dense_set -> Metric.secondCountable_of_almost_dense_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Set.Countable.{u1} α s) (forall (x : α), Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) ε)))))) -> (TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Set.Countable.{u1} α s) (forall (x : α), Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) ε)))))) -> (TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align metric.second_countable_of_almost_dense_set Metric.secondCountable_of_almost_dense_setₓ'. -/
/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
theorem secondCountable_of_almost_dense_set
    (H : ∀ ε > (0 : ℝ), ∃ s : Set α, s.Countable ∧ ∀ x, ∃ y ∈ s, dist x y ≤ ε) :
    SecondCountableTopology α :=
  by
  refine' EMetric.secondCountable_of_almost_dense_set fun ε ε0 => _
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩
  choose s hsc y hys hyx using H ε' (by exact_mod_cast ε'0)
  refine' ⟨s, hsc, Union₂_eq_univ_iff.2 fun x => ⟨y x, hys _, le_trans _ ε'ε.le⟩⟩
  exact_mod_cast hyx x
#align metric.second_countable_of_almost_dense_set Metric.secondCountable_of_almost_dense_set

end SecondCountable

end Metric

/- warning: lebesgue_number_lemma_of_metric -> lebesgue_number_lemma_of_metric is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {c : ι -> (Set.{u1} α)}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall (i : ι), IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (c i)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.iUnion.{u1, u2} α ι (fun (i : ι) => c i))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x δ) (c i))))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {s : Set.{u2} α} {ι : Sort.{u1}} {c : ι -> (Set.{u2} α)}, (IsCompact.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) s) -> (forall (i : ι), IsOpen.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (c i)) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.iUnion.{u2, u1} α ι (fun (i : ι) => c i))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Exists.{u1} ι (fun (i : ι) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Metric.ball.{u2} α _inst_1 x δ) (c i))))))
Case conversion may be inaccurate. Consider using '#align lebesgue_number_lemma_of_metric lebesgue_number_lemma_of_metricₓ'. -/
theorem lebesgue_number_lemma_of_metric {s : Set α} {ι} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
  let ⟨n, en, hn⟩ := lebesgue_number_lemma hs hc₁ hc₂
  let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 en
  ⟨δ, δ0, fun x hx =>
    let ⟨i, hi⟩ := hn x hx
    ⟨i, fun y hy => hi (hδ (mem_ball'.mp hy))⟩⟩
#align lebesgue_number_lemma_of_metric lebesgue_number_lemma_of_metric

/- warning: lebesgue_number_lemma_of_metric_sUnion -> lebesgue_number_lemma_of_metric_sUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {c : Set.{u1} (Set.{u1} α)}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall (t : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t c) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) t)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.sUnion.{u1} α c)) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t c) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) t c) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Metric.ball.{u1} α _inst_1 x δ) t))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {c : Set.{u1} (Set.{u1} α)}, (IsCompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) s) -> (forall (t : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t c) -> (IsOpen.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) t)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Set.sUnion.{u1} α c)) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) t c) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Metric.ball.{u1} α _inst_1 x δ) t))))))
Case conversion may be inaccurate. Consider using '#align lebesgue_number_lemma_of_metric_sUnion lebesgue_number_lemma_of_metric_sUnionₓ'. -/
theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t := by
  rw [sUnion_eq_Union] at hc₂ <;> simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂
#align lebesgue_number_lemma_of_metric_sUnion lebesgue_number_lemma_of_metric_sUnion

namespace Metric

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Metric.Bounded /-
/-- Boundedness of a subset of a pseudometric space. We formulate the definition to work
even in the empty space. -/
def Bounded (s : Set α) : Prop :=
  ∃ C, ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), dist x y ≤ C
#align metric.bounded Metric.Bounded
-/

section Bounded

variable {x : α} {s t : Set α} {r : ℝ}

#print Metric.bounded_iff_isBounded /-
theorem bounded_iff_isBounded (s : Set α) : Bounded s ↔ IsBounded s :=
  by
  change bounded s ↔ sᶜ ∈ (cobounded α).sets
  simp [PseudoMetricSpace.cobounded_sets, Metric.Bounded]
#align metric.bounded_iff_is_bounded Metric.bounded_iff_isBounded
-/

#print Metric.bounded_empty /-
@[simp]
theorem bounded_empty : Bounded (∅ : Set α) :=
  ⟨0, by simp⟩
#align metric.bounded_empty Metric.bounded_empty
-/

#print Metric.bounded_iff_mem_bounded /-
theorem bounded_iff_mem_bounded : Bounded s ↔ ∀ x ∈ s, Bounded s :=
  ⟨fun h _ _ => h, fun H =>
    s.eq_empty_or_nonempty.elim (fun hs => hs.symm ▸ bounded_empty) fun ⟨x, hx⟩ => H x hx⟩
#align metric.bounded_iff_mem_bounded Metric.bounded_iff_mem_bounded
-/

#print Metric.Bounded.mono /-
/-- Subsets of a bounded set are also bounded -/
theorem Bounded.mono (incl : s ⊆ t) : Bounded t → Bounded s :=
  Exists.imp fun C hC x hx y hy => hC x (incl hx) y (incl hy)
#align metric.bounded.mono Metric.Bounded.mono
-/

#print Metric.bounded_closedBall /-
/-- Closed balls are bounded -/
theorem bounded_closedBall : Bounded (closedBall x r) :=
  ⟨r + r, fun y hy z hz => by
    simp only [mem_closed_ball] at *
    calc
      dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add hy hz
      ⟩
#align metric.bounded_closed_ball Metric.bounded_closedBall
-/

#print Metric.bounded_ball /-
/-- Open balls are bounded -/
theorem bounded_ball : Bounded (ball x r) :=
  bounded_closedBall.mono ball_subset_closedBall
#align metric.bounded_ball Metric.bounded_ball
-/

#print Metric.bounded_sphere /-
/-- Spheres are bounded -/
theorem bounded_sphere : Bounded (sphere x r) :=
  bounded_closedBall.mono sphere_subset_closedBall
#align metric.bounded_sphere Metric.bounded_sphere
-/

#print Metric.bounded_iff_subset_ball /-
/-- Given a point, a bounded subset is included in some ball around this point -/
theorem bounded_iff_subset_ball (c : α) : Bounded s ↔ ∃ r, s ⊆ closedBall c r :=
  by
  constructor <;> rintro ⟨C, hC⟩
  · cases' s.eq_empty_or_nonempty with h h
    · subst s
      exact ⟨0, by simp⟩
    · rcases h with ⟨x, hx⟩
      exact
        ⟨C + dist x c, fun y hy =>
          calc
            dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
            _ ≤ C + dist x c := add_le_add_right (hC y hy x hx) _
            ⟩
  · exact bounded_closed_ball.mono hC
#align metric.bounded_iff_subset_ball Metric.bounded_iff_subset_ball
-/

#print Metric.Bounded.subset_ball /-
theorem Bounded.subset_ball (h : Bounded s) (c : α) : ∃ r, s ⊆ closedBall c r :=
  (bounded_iff_subset_ball c).1 h
#align metric.bounded.subset_ball Metric.Bounded.subset_ball
-/

/- warning: metric.bounded.subset_ball_lt -> Metric.Bounded.subset_ball_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Metric.Bounded.{u1} α _inst_1 s) -> (forall (a : Real) (c : α), Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.hasLt a r) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Metric.closedBall.{u1} α _inst_1 c r))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Metric.Bounded.{u1} α _inst_1 s) -> (forall (a : Real) (c : α), Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.instLTReal a r) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Metric.closedBall.{u1} α _inst_1 c r))))
Case conversion may be inaccurate. Consider using '#align metric.bounded.subset_ball_lt Metric.Bounded.subset_ball_ltₓ'. -/
theorem Bounded.subset_ball_lt (h : Bounded s) (a : ℝ) (c : α) : ∃ r, a < r ∧ s ⊆ closedBall c r :=
  by
  rcases h.subset_ball c with ⟨r, hr⟩
  refine' ⟨max r (a + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _), _⟩
  exact subset.trans hr (closed_ball_subset_closed_ball (le_max_left _ _))
#align metric.bounded.subset_ball_lt Metric.Bounded.subset_ball_lt

#print Metric.bounded_closure_of_bounded /-
theorem bounded_closure_of_bounded (h : Bounded s) : Bounded (closure s) :=
  let ⟨C, h⟩ := h
  ⟨C, fun a ha b hb => (isClosed_le' C).closure_subset <| map_mem_closure₂ continuous_dist ha hb h⟩
#align metric.bounded_closure_of_bounded Metric.bounded_closure_of_bounded
-/

alias bounded_closure_of_bounded ← bounded.closure
#align metric.bounded.closure Metric.Bounded.closure

#print Metric.bounded_closure_iff /-
@[simp]
theorem bounded_closure_iff : Bounded (closure s) ↔ Bounded s :=
  ⟨fun h => h.mono subset_closure, fun h => h.closure⟩
#align metric.bounded_closure_iff Metric.bounded_closure_iff
-/

/- warning: metric.bounded.union -> Metric.Bounded.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Metric.Bounded.{u1} α _inst_1 t) -> (Metric.Bounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Metric.Bounded.{u1} α _inst_1 t) -> (Metric.Bounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align metric.bounded.union Metric.Bounded.unionₓ'. -/
/-- The union of two bounded sets is bounded. -/
theorem Bounded.union (hs : Bounded s) (ht : Bounded t) : Bounded (s ∪ t) :=
  by
  refine' bounded_iff_mem_bounded.2 fun x _ => _
  rw [bounded_iff_subset_ball x] at hs ht⊢
  rcases hs with ⟨Cs, hCs⟩; rcases ht with ⟨Ct, hCt⟩
  exact
    ⟨max Cs Ct,
      union_subset (subset.trans hCs <| closed_ball_subset_closed_ball <| le_max_left _ _)
        (subset.trans hCt <| closed_ball_subset_closed_ball <| le_max_right _ _)⟩
#align metric.bounded.union Metric.Bounded.union

/- warning: metric.bounded_union -> Metric.bounded_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Metric.Bounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (And (Metric.Bounded.{u1} α _inst_1 s) (Metric.Bounded.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Metric.Bounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (And (Metric.Bounded.{u1} α _inst_1 s) (Metric.Bounded.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align metric.bounded_union Metric.bounded_unionₓ'. -/
/-- The union of two sets is bounded iff each of the sets is bounded. -/
@[simp]
theorem bounded_union : Bounded (s ∪ t) ↔ Bounded s ∧ Bounded t :=
  ⟨fun h => ⟨h.mono (by simp), h.mono (by simp)⟩, fun h => h.1.union h.2⟩
#align metric.bounded_union Metric.bounded_union

#print Metric.bounded_biUnion /-
/-- A finite union of bounded sets is bounded -/
theorem bounded_biUnion {I : Set β} {s : β → Set α} (H : I.Finite) :
    Bounded (⋃ i ∈ I, s i) ↔ ∀ i ∈ I, Bounded (s i) :=
  Finite.induction_on H (by simp) fun x I _ _ IH => by simp [or_imp, forall_and, IH]
#align metric.bounded_bUnion Metric.bounded_biUnion
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Metric.Bounded.prod /-
protected theorem Bounded.prod [PseudoMetricSpace β] {s : Set α} {t : Set β} (hs : Bounded s)
    (ht : Bounded t) : Bounded (s ×ˢ t) :=
  by
  refine' bounded_iff_mem_bounded.mpr fun x hx => _
  rcases hs.subset_ball x.1 with ⟨rs, hrs⟩
  rcases ht.subset_ball x.2 with ⟨rt, hrt⟩
  suffices : s ×ˢ t ⊆ closed_ball x (max rs rt)
  exact bounded_closed_ball.mono this
  rw [← @Prod.mk.eta _ _ x, ← closedBall_prod_same]
  exact
    prod_mono (hrs.trans <| closed_ball_subset_closed_ball <| le_max_left _ _)
      (hrt.trans <| closed_ball_subset_closed_ball <| le_max_right _ _)
#align metric.bounded.prod Metric.Bounded.prod
-/

#print TotallyBounded.bounded /-
/-- A totally bounded set is bounded -/
theorem TotallyBounded.bounded {s : Set α} (h : TotallyBounded s) : Bounded s :=
  let-- We cover the totally bounded set by finitely many balls of radius 1,
    -- and then argue that a finite union of bounded sets is bounded
    ⟨t, fint, subs⟩ :=
    (totallyBounded_iff.mp h) 1 zero_lt_one
  Bounded.mono subs <| (bounded_biUnion fint).2 fun i hi => bounded_ball
#align totally_bounded.bounded TotallyBounded.bounded
-/

#print IsCompact.bounded /-
/-- A compact set is bounded -/
theorem IsCompact.bounded {s : Set α} (h : IsCompact s) : Bounded s :=
  -- A compact set is totally bounded, thus bounded
      h.TotallyBounded.Bounded
#align is_compact.bounded IsCompact.bounded
-/

#print Metric.bounded_of_finite /-
/-- A finite set is bounded -/
theorem bounded_of_finite {s : Set α} (h : s.Finite) : Bounded s :=
  h.IsCompact.Bounded
#align metric.bounded_of_finite Metric.bounded_of_finite
-/

alias bounded_of_finite ← _root_.set.finite.bounded
#align set.finite.bounded Set.Finite.bounded

#print Metric.bounded_singleton /-
/-- A singleton is bounded -/
theorem bounded_singleton {x : α} : Bounded ({x} : Set α) :=
  bounded_of_finite <| finite_singleton _
#align metric.bounded_singleton Metric.bounded_singleton
-/

/- warning: metric.bounded_range_iff -> Metric.bounded_range_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α}, Iff (Metric.Bounded.{u1} α _inst_1 (Set.range.{u1, succ u2} α β f)) (Exists.{1} Real (fun (C : Real) => forall (x : β) (y : β), LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (f y)) C))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] {f : β -> α}, Iff (Metric.Bounded.{u1} α _inst_1 (Set.range.{u1, succ u2} α β f)) (Exists.{1} Real (fun (C : Real) => forall (x : β) (y : β), LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) (f x) (f y)) C))
Case conversion may be inaccurate. Consider using '#align metric.bounded_range_iff Metric.bounded_range_iffₓ'. -/
/-- Characterization of the boundedness of the range of a function -/
theorem bounded_range_iff {f : β → α} : Bounded (range f) ↔ ∃ C, ∀ x y, dist (f x) (f y) ≤ C :=
  exists_congr fun C =>
    ⟨fun H x y => H _ ⟨x, rfl⟩ _ ⟨y, rfl⟩, by rintro H _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ <;> exact H x y⟩
#align metric.bounded_range_iff Metric.bounded_range_iff

#print Metric.bounded_range_of_tendsto_cofinite_uniformity /-
theorem bounded_range_of_tendsto_cofinite_uniformity {f : β → α}
    (hf : Tendsto (Prod.map f f) (cofinite ×ᶠ cofinite) (𝓤 α)) : Bounded (range f) :=
  by
  rcases(has_basis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one with
    ⟨s, hsf, hs1⟩
  rw [← image_univ, ← union_compl_self s, image_union, bounded_union]
  use (hsf.image f).Bounded, 1
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)
#align metric.bounded_range_of_tendsto_cofinite_uniformity Metric.bounded_range_of_tendsto_cofinite_uniformity
-/

#print Metric.bounded_range_of_cauchy_map_cofinite /-
theorem bounded_range_of_cauchy_map_cofinite {f : β → α} (hf : Cauchy (map f cofinite)) :
    Bounded (range f) :=
  bounded_range_of_tendsto_cofinite_uniformity <| (cauchy_map_iff.1 hf).2
#align metric.bounded_range_of_cauchy_map_cofinite Metric.bounded_range_of_cauchy_map_cofinite
-/

#print CauchySeq.bounded_range /-
theorem CauchySeq.bounded_range {f : ℕ → α} (hf : CauchySeq f) : Bounded (range f) :=
  bounded_range_of_cauchy_map_cofinite <| by rwa [Nat.cofinite_eq_atTop]
#align cauchy_seq.bounded_range CauchySeq.bounded_range
-/

#print Metric.bounded_range_of_tendsto_cofinite /-
theorem bounded_range_of_tendsto_cofinite {f : β → α} {a : α} (hf : Tendsto f cofinite (𝓝 a)) :
    Bounded (range f) :=
  bounded_range_of_tendsto_cofinite_uniformity <|
    (hf.Prod_map hf).mono_right <| nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)
#align metric.bounded_range_of_tendsto_cofinite Metric.bounded_range_of_tendsto_cofinite
-/

#print Metric.bounded_of_compactSpace /-
/-- In a compact space, all sets are bounded -/
theorem bounded_of_compactSpace [CompactSpace α] : Bounded s :=
  isCompact_univ.Bounded.mono (subset_univ _)
#align metric.bounded_of_compact_space Metric.bounded_of_compactSpace
-/

#print Metric.bounded_range_of_tendsto /-
theorem bounded_range_of_tendsto (u : ℕ → α) {x : α} (hu : Tendsto u atTop (𝓝 x)) :
    Bounded (range u) :=
  hu.CauchySeq.bounded_range
#align metric.bounded_range_of_tendsto Metric.bounded_range_of_tendsto
-/

/- warning: metric.exists_is_open_bounded_image_inter_of_is_compact_of_forall_continuous_within_at -> Metric.exists_isOpen_bounded_image_inter_of_isCompact_of_forall_continuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {k : Set.{u2} β} {s : Set.{u2} β} {f : β -> α}, (IsCompact.{u2} β _inst_2 k) -> (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x k) -> (ContinuousWithinAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s x)) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) k t) (And (IsOpen.{u2} β _inst_2 t) (Metric.Bounded.{u1} α _inst_1 (Set.image.{u2, u1} β α f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t s))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {k : Set.{u2} β} {s : Set.{u2} β} {f : β -> α}, (IsCompact.{u2} β _inst_2 k) -> (forall (x : β), (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x k) -> (ContinuousWithinAt.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s x)) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) k t) (And (IsOpen.{u2} β _inst_2 t) (Metric.Bounded.{u1} α _inst_1 (Set.image.{u2, u1} β α f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) t s))))))
Case conversion may be inaccurate. Consider using '#align metric.exists_is_open_bounded_image_inter_of_is_compact_of_forall_continuous_within_at Metric.exists_isOpen_bounded_image_inter_of_isCompact_of_forall_continuousWithinAtₓ'. -/
/-- If a function is continuous within a set `s` at every point of a compact set `k`, then it is
bounded on some open neighborhood of `k` in `s`. -/
theorem exists_isOpen_bounded_image_inter_of_isCompact_of_forall_continuousWithinAt
    [TopologicalSpace β] {k s : Set β} {f : β → α} (hk : IsCompact k)
    (hf : ∀ x ∈ k, ContinuousWithinAt f s x) : ∃ t, k ⊆ t ∧ IsOpen t ∧ Bounded (f '' (t ∩ s)) :=
  by
  apply hk.induction_on
  · exact ⟨∅, subset.refl _, isOpen_empty, by simp only [image_empty, bounded_empty, empty_inter]⟩
  · rintro s s' hss' ⟨t, s't, t_open, t_bounded⟩
    exact ⟨t, hss'.trans s't, t_open, t_bounded⟩
  · rintro s s' ⟨t, st, t_open, t_bounded⟩ ⟨t', s't', t'_open, t'_bounded⟩
    refine' ⟨t ∪ t', union_subset_union st s't', t_open.union t'_open, _⟩
    rw [union_inter_distrib_right, image_union]
    exact t_bounded.union t'_bounded
  · intro x hx
    have A : ball (f x) 1 ∈ 𝓝 (f x) := ball_mem_nhds _ zero_lt_one
    have B : f ⁻¹' ball (f x) 1 ∈ 𝓝[s] x := hf x hx A
    obtain ⟨u, u_open, xu, uf⟩ : ∃ u : Set β, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' ball (f x) 1
    exact _root_.mem_nhds_within.1 B
    refine' ⟨u, _, u, subset.refl _, u_open, _⟩
    · apply nhdsWithin_le_nhds
      exact u_open.mem_nhds xu
    · apply bounded.mono (image_subset _ uf)
      exact bounded_ball.mono (image_preimage_subset _ _)
#align metric.exists_is_open_bounded_image_inter_of_is_compact_of_forall_continuous_within_at Metric.exists_isOpen_bounded_image_inter_of_isCompact_of_forall_continuousWithinAt

#print Metric.exists_isOpen_bounded_image_of_isCompact_of_forall_continuousAt /-
/-- If a function is continuous at every point of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
theorem exists_isOpen_bounded_image_of_isCompact_of_forall_continuousAt [TopologicalSpace β]
    {k : Set β} {f : β → α} (hk : IsCompact k) (hf : ∀ x ∈ k, ContinuousAt f x) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ Bounded (f '' t) :=
  by
  simp_rw [← continuousWithinAt_univ] at hf
  simpa only [inter_univ] using
    exists_is_open_bounded_image_inter_of_is_compact_of_forall_continuous_within_at hk hf
#align metric.exists_is_open_bounded_image_of_is_compact_of_forall_continuous_at Metric.exists_isOpen_bounded_image_of_isCompact_of_forall_continuousAt
-/

/- warning: metric.exists_is_open_bounded_image_inter_of_is_compact_of_continuous_on -> Metric.exists_isOpen_bounded_image_inter_of_isCompact_of_continuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {k : Set.{u2} β} {s : Set.{u2} β} {f : β -> α}, (IsCompact.{u2} β _inst_2 k) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) k s) -> (ContinuousOn.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) k t) (And (IsOpen.{u2} β _inst_2 t) (Metric.Bounded.{u1} α _inst_1 (Set.image.{u2, u1} β α f (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t s))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {k : Set.{u2} β} {s : Set.{u2} β} {f : β -> α}, (IsCompact.{u2} β _inst_2 k) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) k s) -> (ContinuousOn.{u2, u1} β α _inst_2 (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) f s) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) k t) (And (IsOpen.{u2} β _inst_2 t) (Metric.Bounded.{u1} α _inst_1 (Set.image.{u2, u1} β α f (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) t s))))))
Case conversion may be inaccurate. Consider using '#align metric.exists_is_open_bounded_image_inter_of_is_compact_of_continuous_on Metric.exists_isOpen_bounded_image_inter_of_isCompact_of_continuousOnₓ'. -/
/-- If a function is continuous on a set `s` containing a compact set `k`, then it is bounded on
some open neighborhood of `k` in `s`. -/
theorem exists_isOpen_bounded_image_inter_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β → α} (hk : IsCompact k) (hks : k ⊆ s) (hf : ContinuousOn f s) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ Bounded (f '' (t ∩ s)) :=
  exists_isOpen_bounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk fun x hx =>
    hf x (hks hx)
#align metric.exists_is_open_bounded_image_inter_of_is_compact_of_continuous_on Metric.exists_isOpen_bounded_image_inter_of_isCompact_of_continuousOn

#print Metric.exists_isOpen_bounded_image_of_isCompact_of_continuousOn /-
/-- If a function is continuous on a neighborhood of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
theorem exists_isOpen_bounded_image_of_isCompact_of_continuousOn [TopologicalSpace β] {k s : Set β}
    {f : β → α} (hk : IsCompact k) (hs : IsOpen s) (hks : k ⊆ s) (hf : ContinuousOn f s) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ Bounded (f '' t) :=
  exists_isOpen_bounded_image_of_isCompact_of_forall_continuousAt hk fun x hx =>
    hf.ContinuousAt (hs.mem_nhds (hks hx))
#align metric.exists_is_open_bounded_image_of_is_compact_of_continuous_on Metric.exists_isOpen_bounded_image_of_isCompact_of_continuousOn
-/

#print Metric.isCompact_of_isClosed_bounded /-
/-- The **Heine–Borel theorem**: In a proper space, a closed bounded set is compact. -/
theorem isCompact_of_isClosed_bounded [ProperSpace α] (hc : IsClosed s) (hb : Bounded s) :
    IsCompact s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  · exact isCompact_empty
  · rcases hb.subset_ball x with ⟨r, hr⟩
    exact isCompact_of_isClosed_subset (is_compact_closed_ball x r) hc hr
#align metric.is_compact_of_is_closed_bounded Metric.isCompact_of_isClosed_bounded
-/

#print Metric.Bounded.isCompact_closure /-
/-- The **Heine–Borel theorem**: In a proper space, the closure of a bounded set is compact. -/
theorem Bounded.isCompact_closure [ProperSpace α] (h : Bounded s) : IsCompact (closure s) :=
  isCompact_of_isClosed_bounded isClosed_closure h.closure
#align metric.bounded.is_compact_closure Metric.Bounded.isCompact_closure
-/

#print Metric.isCompact_iff_isClosed_bounded /-
/-- The **Heine–Borel theorem**:
In a proper Hausdorff space, a set is compact if and only if it is closed and bounded. -/
theorem isCompact_iff_isClosed_bounded [T2Space α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ Bounded s :=
  ⟨fun h => ⟨h.IsClosed, h.Bounded⟩, fun h => isCompact_of_isClosed_bounded h.1 h.2⟩
#align metric.is_compact_iff_is_closed_bounded Metric.isCompact_iff_isClosed_bounded
-/

#print Metric.compactSpace_iff_bounded_univ /-
theorem compactSpace_iff_bounded_univ [ProperSpace α] : CompactSpace α ↔ Bounded (univ : Set α) :=
  ⟨@bounded_of_compactSpace α _ _, fun hb => ⟨isCompact_of_isClosed_bounded isClosed_univ hb⟩⟩
#align metric.compact_space_iff_bounded_univ Metric.compactSpace_iff_bounded_univ
-/

section ConditionallyCompleteLinearOrder

variable [Preorder α] [CompactIccSpace α]

#print Metric.bounded_Icc /-
theorem bounded_Icc (a b : α) : Bounded (Icc a b) :=
  (totallyBounded_Icc a b).Bounded
#align metric.bounded_Icc Metric.bounded_Icc
-/

#print Metric.bounded_Ico /-
theorem bounded_Ico (a b : α) : Bounded (Ico a b) :=
  (totallyBounded_Ico a b).Bounded
#align metric.bounded_Ico Metric.bounded_Ico
-/

#print Metric.bounded_Ioc /-
theorem bounded_Ioc (a b : α) : Bounded (Ioc a b) :=
  (totallyBounded_Ioc a b).Bounded
#align metric.bounded_Ioc Metric.bounded_Ioc
-/

#print Metric.bounded_Ioo /-
theorem bounded_Ioo (a b : α) : Bounded (Ioo a b) :=
  (totallyBounded_Ioo a b).Bounded
#align metric.bounded_Ioo Metric.bounded_Ioo
-/

#print Metric.bounded_of_bddAbove_of_bddBelow /-
/-- In a pseudo metric space with a conditionally complete linear order such that the order and the
    metric structure give the same topology, any order-bounded set is metric-bounded. -/
theorem bounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) :
    Bounded s :=
  let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  Bounded.mono (fun x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩) (bounded_Icc l u)
#align metric.bounded_of_bdd_above_of_bdd_below Metric.bounded_of_bddAbove_of_bddBelow
-/

end ConditionallyCompleteLinearOrder

end Bounded

section Diam

variable {s : Set α} {x y z : α}

#print Metric.diam /-
/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the emetric.diameter -/
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (EMetric.diam s)
#align metric.diam Metric.diam
-/

/- warning: metric.diam_nonneg -> Metric.diam_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Metric.diam.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Metric.diam.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align metric.diam_nonneg Metric.diam_nonnegₓ'. -/
/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg : 0 ≤ diam s :=
  ENNReal.toReal_nonneg
#align metric.diam_nonneg Metric.diam_nonneg

/- warning: metric.diam_subsingleton -> Metric.diam_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} Real (Metric.diam.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Subsingleton.{u1} α s) -> (Eq.{1} Real (Metric.diam.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.diam_subsingleton Metric.diam_subsingletonₓ'. -/
theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 := by
  simp only [diam, EMetric.diam_subsingleton hs, ENNReal.zero_toReal]
#align metric.diam_subsingleton Metric.diam_subsingleton

/- warning: metric.diam_empty -> Metric.diam_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Eq.{1} Real (Metric.diam.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α], Eq.{1} Real (Metric.diam.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.diam_empty Metric.diam_emptyₓ'. -/
/-- The empty set has zero diameter -/
@[simp]
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty
#align metric.diam_empty Metric.diam_empty

/- warning: metric.diam_singleton -> Metric.diam_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Eq.{1} Real (Metric.diam.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α}, Eq.{1} Real (Metric.diam.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.diam_singleton Metric.diam_singletonₓ'. -/
/-- A singleton has zero diameter -/
@[simp]
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton
#align metric.diam_singleton Metric.diam_singleton

#print Metric.diam_pair /-
-- Does not work as a simp-lemma, since {x, y} reduces to (insert y {x})
theorem diam_pair : diam ({x, y} : Set α) = dist x y := by
  simp only [diam, EMetric.diam_pair, dist_edist]
#align metric.diam_pair Metric.diam_pair
-/

/- warning: metric.diam_triple -> Metric.diam_triple is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {z : α}, Eq.{1} Real (Metric.diam.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) z)))) (LinearOrder.max.{0} Real Real.linearOrder (LinearOrder.max.{0} Real Real.linearOrder (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x z)) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y z))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {y : α} {z : α}, Eq.{1} Real (Metric.diam.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) y (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) z)))) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x z)) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z))
Case conversion may be inaccurate. Consider using '#align metric.diam_triple Metric.diam_tripleₓ'. -/
-- Does not work as a simp-lemma, since {x, y, z} reduces to (insert z (insert y {x}))
theorem diam_triple :
    Metric.diam ({x, y, z} : Set α) = max (max (dist x y) (dist x z)) (dist y z) :=
  by
  simp only [Metric.diam, EMetric.diam_triple, dist_edist]
  rw [ENNReal.toReal_max, ENNReal.toReal_max] <;> apply_rules [ne_of_lt, edist_lt_top, max_lt]
#align metric.diam_triple Metric.diam_triple

/- warning: metric.ediam_le_of_forall_dist_le -> Metric.ediam_le_of_forall_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {C : Real}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) C))) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (ENNReal.ofReal C))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {C : Real}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) C))) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (ENNReal.ofReal C))
Case conversion may be inaccurate. Consider using '#align metric.ediam_le_of_forall_dist_le Metric.ediam_le_of_forall_dist_leₓ'. -/
/-- If the distance between any two points in a set is bounded by some constant `C`,
then `ennreal.of_real C`  bounds the emetric diameter of this set. -/
theorem ediam_le_of_forall_dist_le {C : ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) :
    EMetric.diam s ≤ ENNReal.ofReal C :=
  EMetric.diam_le fun x hx y hy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy)
#align metric.ediam_le_of_forall_dist_le Metric.ediam_le_of_forall_dist_le

/- warning: metric.diam_le_of_forall_dist_le -> Metric.diam_le_of_forall_dist_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {C : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) C) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) C))) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 s) C)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {C : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) C) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) C))) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 s) C)
Case conversion may be inaccurate. Consider using '#align metric.diam_le_of_forall_dist_le Metric.diam_le_of_forall_dist_leₓ'. -/
/-- If the distance between any two points in a set is bounded by some non-negative constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le {C : ℝ} (h₀ : 0 ≤ C) (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) :
    diam s ≤ C :=
  ENNReal.toReal_le_of_le_ofReal h₀ (ediam_le_of_forall_dist_le h)
#align metric.diam_le_of_forall_dist_le Metric.diam_le_of_forall_dist_le

/- warning: metric.diam_le_of_forall_dist_le_of_nonempty -> Metric.diam_le_of_forall_dist_le_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {C : Real}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) C))) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 s) C))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall {C : Real}, (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) C))) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 s) C))
Case conversion may be inaccurate. Consider using '#align metric.diam_le_of_forall_dist_le_of_nonempty Metric.diam_le_of_forall_dist_le_of_nonemptyₓ'. -/
/-- If the distance between any two points in a nonempty set is bounded by some constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le_of_nonempty (hs : s.Nonempty) {C : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) : diam s ≤ C :=
  have h₀ : 0 ≤ C :=
    let ⟨x, hx⟩ := hs
    le_trans dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h
#align metric.diam_le_of_forall_dist_le_of_nonempty Metric.diam_le_of_forall_dist_le_of_nonempty

/- warning: metric.dist_le_diam_of_mem' -> Metric.dist_le_diam_of_mem' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Ne.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Metric.diam.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Ne.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Metric.diam.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align metric.dist_le_diam_of_mem' Metric.dist_le_diam_of_mem'ₓ'. -/
/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem' (h : EMetric.diam s ≠ ⊤) (hx : x ∈ s) (hy : y ∈ s) :
    dist x y ≤ diam s := by
  rw [diam, dist_edist]
  rw [ENNReal.toReal_le_toReal (edist_ne_top _ _) h]
  exact EMetric.edist_le_diam_of_mem hx hy
#align metric.dist_le_diam_of_mem' Metric.dist_le_diam_of_mem'

/- warning: metric.bounded_iff_ediam_ne_top -> Metric.bounded_iff_ediam_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Metric.Bounded.{u1} α _inst_1 s) (Ne.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, Iff (Metric.Bounded.{u1} α _inst_1 s) (Ne.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align metric.bounded_iff_ediam_ne_top Metric.bounded_iff_ediam_ne_topₓ'. -/
/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
theorem bounded_iff_ediam_ne_top : Bounded s ↔ EMetric.diam s ≠ ⊤ :=
  Iff.intro
    (fun ⟨C, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top <| ediam_le_of_forall_dist_le hC)
    fun h => ⟨diam s, fun x hx y hy => dist_le_diam_of_mem' h hx hy⟩
#align metric.bounded_iff_ediam_ne_top Metric.bounded_iff_ediam_ne_top

/- warning: metric.bounded.ediam_ne_top -> Metric.Bounded.ediam_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Ne.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Ne.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align metric.bounded.ediam_ne_top Metric.Bounded.ediam_ne_topₓ'. -/
theorem Bounded.ediam_ne_top (h : Bounded s) : EMetric.diam s ≠ ⊤ :=
  bounded_iff_ediam_ne_top.1 h
#align metric.bounded.ediam_ne_top Metric.Bounded.ediam_ne_top

/- warning: metric.ediam_univ_eq_top_iff_noncompact -> Metric.ediam_univ_eq_top_iff_noncompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1], Iff (Eq.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (Set.univ.{u1} α)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (NoncompactSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1], Iff (Eq.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (Set.univ.{u1} α)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (NoncompactSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align metric.ediam_univ_eq_top_iff_noncompact Metric.ediam_univ_eq_top_iff_noncompactₓ'. -/
theorem ediam_univ_eq_top_iff_noncompact [ProperSpace α] :
    EMetric.diam (univ : Set α) = ∞ ↔ NoncompactSpace α := by
  rw [← not_compactSpace_iff, compact_space_iff_bounded_univ, bounded_iff_ediam_ne_top,
    Classical.not_not]
#align metric.ediam_univ_eq_top_iff_noncompact Metric.ediam_univ_eq_top_iff_noncompact

/- warning: metric.ediam_univ_of_noncompact -> Metric.ediam_univ_of_noncompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] [_inst_3 : NoncompactSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))], Eq.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (Set.univ.{u1} α)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] [_inst_3 : NoncompactSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))], Eq.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) (Set.univ.{u1} α)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align metric.ediam_univ_of_noncompact Metric.ediam_univ_of_noncompactₓ'. -/
@[simp]
theorem ediam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] :
    EMetric.diam (univ : Set α) = ∞ :=
  ediam_univ_eq_top_iff_noncompact.mpr ‹_›
#align metric.ediam_univ_of_noncompact Metric.ediam_univ_of_noncompact

/- warning: metric.diam_univ_of_noncompact -> Metric.diam_univ_of_noncompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] [_inst_3 : NoncompactSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))], Eq.{1} Real (Metric.diam.{u1} α _inst_1 (Set.univ.{u1} α)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] [_inst_3 : NoncompactSpace.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1))], Eq.{1} Real (Metric.diam.{u1} α _inst_1 (Set.univ.{u1} α)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align metric.diam_univ_of_noncompact Metric.diam_univ_of_noncompactₓ'. -/
@[simp]
theorem diam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : diam (univ : Set α) = 0 := by
  simp [diam]
#align metric.diam_univ_of_noncompact Metric.diam_univ_of_noncompact

/- warning: metric.dist_le_diam_of_mem -> Metric.dist_le_diam_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y) (Metric.diam.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, (Metric.Bounded.{u1} α _inst_1 s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y) (Metric.diam.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align metric.dist_le_diam_of_mem Metric.dist_le_diam_of_memₓ'. -/
/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem (h : Bounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
  dist_le_diam_of_mem' h.ediam_ne_top hx hy
#align metric.dist_le_diam_of_mem Metric.dist_le_diam_of_mem

/- warning: metric.ediam_of_unbounded -> Metric.ediam_of_unbounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Not (Metric.Bounded.{u1} α _inst_1 s)) -> (Eq.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Not (Metric.Bounded.{u1} α _inst_1 s)) -> (Eq.{1} ENNReal (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_1) s) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align metric.ediam_of_unbounded Metric.ediam_of_unboundedₓ'. -/
theorem ediam_of_unbounded (h : ¬Bounded s) : EMetric.diam s = ∞ := by
  rwa [bounded_iff_ediam_ne_top, Classical.not_not] at h
#align metric.ediam_of_unbounded Metric.ediam_of_unbounded

/- warning: metric.diam_eq_zero_of_unbounded -> Metric.diam_eq_zero_of_unbounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Not (Metric.Bounded.{u1} α _inst_1 s)) -> (Eq.{1} Real (Metric.diam.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α}, (Not (Metric.Bounded.{u1} α _inst_1 s)) -> (Eq.{1} Real (Metric.diam.{u1} α _inst_1 s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align metric.diam_eq_zero_of_unbounded Metric.diam_eq_zero_of_unboundedₓ'. -/
/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `emetric.diam`.
This lemma makes it possible to avoid side conditions in some situations -/
theorem diam_eq_zero_of_unbounded (h : ¬Bounded s) : diam s = 0 := by
  rw [diam, ediam_of_unbounded h, ENNReal.top_toReal]
#align metric.diam_eq_zero_of_unbounded Metric.diam_eq_zero_of_unbounded

/- warning: metric.diam_mono -> Metric.diam_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Metric.Bounded.{u1} α _inst_1 t) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 s) (Metric.diam.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Metric.Bounded.{u1} α _inst_1 t) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 s) (Metric.diam.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align metric.diam_mono Metric.diam_monoₓ'. -/
/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
theorem diam_mono {s t : Set α} (h : s ⊆ t) (ht : Bounded t) : diam s ≤ diam t :=
  by
  unfold diam
  rw [ENNReal.toReal_le_toReal (bounded.mono h ht).ediam_ne_top ht.ediam_ne_top]
  exact EMetric.diam_mono h
#align metric.diam_mono Metric.diam_mono

/- warning: metric.diam_union -> Metric.diam_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.diam.{u1} α _inst_1 s) (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x y)) (Metric.diam.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {y : α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.diam.{u1} α _inst_1 s) (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x y)) (Metric.diam.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align metric.diam_union Metric.diam_unionₓ'. -/
/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
theorem diam_union {t : Set α} (xs : x ∈ s) (yt : y ∈ t) :
    diam (s ∪ t) ≤ diam s + dist x y + diam t :=
  by
  by_cases H : bounded (s ∪ t)
  · have hs : bounded s := H.mono (subset_union_left _ _)
    have ht : bounded t := H.mono (subset_union_right _ _)
    rw [bounded_iff_ediam_ne_top] at H hs ht
    rw [dist_edist, diam, diam, diam, ← ENNReal.toReal_add, ← ENNReal.toReal_add,
            ENNReal.toReal_le_toReal] <;>
          repeat' apply ENNReal.add_ne_top.2 <;> constructor <;>
        try assumption <;>
      try apply edist_ne_top
    exact EMetric.diam_union xs yt
  · rw [diam_eq_zero_of_unbounded H]
    apply_rules [add_nonneg, diam_nonneg, dist_nonneg]
#align metric.diam_union Metric.diam_union

/- warning: metric.diam_union' -> Metric.diam_union' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Metric.diam.{u1} α _inst_1 s) (Metric.diam.{u1} α _inst_1 t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Metric.diam.{u1} α _inst_1 s) (Metric.diam.{u1} α _inst_1 t)))
Case conversion may be inaccurate. Consider using '#align metric.diam_union' Metric.diam_union'ₓ'. -/
/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s + diam t :=
  by
  rcases h with ⟨x, ⟨xs, xt⟩⟩
  simpa using diam_union xs xt
#align metric.diam_union' Metric.diam_union'

/- warning: metric.diam_le_of_subset_closed_ball -> Metric.diam_le_of_subset_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Metric.closedBall.{u1} α _inst_1 x r)) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) r))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Set.{u1} α} {x : α} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Metric.closedBall.{u1} α _inst_1 x r)) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 s) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) r))
Case conversion may be inaccurate. Consider using '#align metric.diam_le_of_subset_closed_ball Metric.diam_le_of_subset_closedBallₓ'. -/
theorem diam_le_of_subset_closedBall {r : ℝ} (hr : 0 ≤ r) (h : s ⊆ closedBall x r) :
    diam s ≤ 2 * r :=
  diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b ≤ dist a x + dist b x := dist_triangle_right _ _ _
      _ ≤ r + r := (add_le_add (h ha) (h hb))
      _ = 2 * r := by simp [mul_two, mul_comm]
      
#align metric.diam_le_of_subset_closed_ball Metric.diam_le_of_subset_closedBall

/- warning: metric.diam_closed_ball -> Metric.diam_closedBall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 (Metric.closedBall.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) r))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 (Metric.closedBall.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) r))
Case conversion may be inaccurate. Consider using '#align metric.diam_closed_ball Metric.diam_closedBallₓ'. -/
/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
theorem diam_closedBall {r : ℝ} (h : 0 ≤ r) : diam (closedBall x r) ≤ 2 * r :=
  diam_le_of_subset_closedBall h Subset.rfl
#align metric.diam_closed_ball Metric.diam_closedBall

/- warning: metric.diam_ball -> Metric.diam_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LE.le.{0} Real Real.hasLe (Metric.diam.{u1} α _inst_1 (Metric.ball.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) r))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {x : α} {r : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LE.le.{0} Real Real.instLEReal (Metric.diam.{u1} α _inst_1 (Metric.ball.{u1} α _inst_1 x r)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) r))
Case conversion may be inaccurate. Consider using '#align metric.diam_ball Metric.diam_ballₓ'. -/
/-- The diameter of a ball of radius `r` is at most `2 r`. -/
theorem diam_ball {r : ℝ} (h : 0 ≤ r) : diam (ball x r) ≤ 2 * r :=
  diam_le_of_subset_closedBall h ball_subset_closedBall
#align metric.diam_ball Metric.diam_ball

/- warning: is_complete.nonempty_Inter_of_nonempty_bInter -> IsComplete.nonempty_iInter_of_nonempty_biInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Nat -> (Set.{u1} α)}, (IsComplete.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (s (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) -> (forall (n : Nat), IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (s n)) -> (forall (n : Nat), Metric.Bounded.{u1} α _inst_1 (s n)) -> (forall (N : Nat), Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => Set.iInter.{u1, 0} α (LE.le.{0} Nat Nat.hasLe n N) (fun (H : LE.le.{0} Nat Nat.hasLe n N) => s n)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Metric.diam.{u1} α _inst_1 (s n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => s n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {s : Nat -> (Set.{u1} α)}, (IsComplete.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) (s (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) -> (forall (n : Nat), IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (s n)) -> (forall (n : Nat), Metric.Bounded.{u1} α _inst_1 (s n)) -> (forall (N : Nat), Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => Set.iInter.{u1, 0} α (LE.le.{0} Nat instLENat n N) (fun (H : LE.le.{0} Nat instLENat n N) => s n)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Metric.diam.{u1} α _inst_1 (s n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => s n)))
Case conversion may be inaccurate. Consider using '#align is_complete.nonempty_Inter_of_nonempty_bInter IsComplete.nonempty_iInter_of_nonempty_biInterₓ'. -/
/-- If a family of complete sets with diameter tending to `0` is such that each finite intersection
is nonempty, then the total intersection is also nonempty. -/
theorem IsComplete.nonempty_iInter_of_nonempty_biInter {s : ℕ → Set α} (h0 : IsComplete (s 0))
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, Bounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  by
  let u N := (h N).some
  have I : ∀ n N, n ≤ N → u N ∈ s n := by
    intro n N hn
    apply mem_of_subset_of_mem _ (h N).choose_spec
    intro x hx
    simp only [mem_Inter] at hx
    exact hx n hn
  have : ∀ n, u n ∈ s 0 := fun n => I 0 n (zero_le _)
  have : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 _ _ h'
    intro m n N hm hn
    exact dist_le_diam_of_mem (h's N) (I _ _ hm) (I _ _ hn)
  obtain ⟨x, hx, xlim⟩ : ∃ (x : α)(H : x ∈ s 0), tendsto (fun n : ℕ => u n) at_top (𝓝 x) :=
    cauchySeq_tendsto_of_isComplete h0 (fun n => I 0 n (zero_le _)) this
  refine' ⟨x, mem_Inter.2 fun n => _⟩
  apply (hs n).mem_of_tendsto xlim
  filter_upwards [Ici_mem_at_top n]with p hp
  exact I n p hp
#align is_complete.nonempty_Inter_of_nonempty_bInter IsComplete.nonempty_iInter_of_nonempty_biInter

/- warning: metric.nonempty_Inter_of_nonempty_bInter -> Metric.nonempty_iInter_of_nonempty_biInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)] {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (s n)) -> (forall (n : Nat), Metric.Bounded.{u1} α _inst_1 (s n)) -> (forall (N : Nat), Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => Set.iInter.{u1, 0} α (LE.le.{0} Nat Nat.hasLe n N) (fun (H : LE.le.{0} Nat Nat.hasLe n N) => s n)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Metric.diam.{u1} α _inst_1 (s n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => s n)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)] {s : Nat -> (Set.{u1} α)}, (forall (n : Nat), IsClosed.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (s n)) -> (forall (n : Nat), Metric.Bounded.{u1} α _inst_1 (s n)) -> (forall (N : Nat), Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => Set.iInter.{u1, 0} α (LE.le.{0} Nat instLENat n N) (fun (H : LE.le.{0} Nat instLENat n N) => s n)))) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Metric.diam.{u1} α _inst_1 (s n)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Set.Nonempty.{u1} α (Set.iInter.{u1, 1} α Nat (fun (n : Nat) => s n)))
Case conversion may be inaccurate. Consider using '#align metric.nonempty_Inter_of_nonempty_bInter Metric.nonempty_iInter_of_nonempty_biInterₓ'. -/
/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, Bounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).IsComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'
#align metric.nonempty_Inter_of_nonempty_bInter Metric.nonempty_iInter_of_nonempty_biInter

end Diam

/- warning: metric.exists_local_min_mem_ball -> Metric.exists_local_min_mem_ball is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : ConditionallyCompleteLinearOrder.{u2} β] [_inst_5 : OrderTopology.{u2} β _inst_3 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_4)))))] {f : α -> β} {a : α} {z : α} {r : Real}, (ContinuousOn.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) _inst_3 f (Metric.closedBall.{u1} α _inst_1 a r)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (Metric.closedBall.{u1} α _inst_1 a r)) -> (forall (z' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z' (Metric.sphere.{u1} α _inst_1 a r)) -> (LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_4)))))) (f z) (f z'))) -> (Exists.{succ u1} α (fun (z : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (Metric.ball.{u1} α _inst_1 a r)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (Metric.ball.{u1} α _inst_1 a r)) => IsLocalMin.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_4))))) f z)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : ProperSpace.{u1} α _inst_1] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : ConditionallyCompleteLinearOrder.{u2} β] [_inst_5 : OrderTopology.{u2} β _inst_3 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_4)))))] {f : α -> β} {a : α} {z : α} {r : Real}, (ContinuousOn.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) _inst_3 f (Metric.closedBall.{u1} α _inst_1 a r)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (Metric.closedBall.{u1} α _inst_1 a r)) -> (forall (z' : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z' (Metric.sphere.{u1} α _inst_1 a r)) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_4)))))) (f z) (f z'))) -> (Exists.{succ u1} α (fun (z : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (Metric.ball.{u1} α _inst_1 a r)) (IsLocalMin.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (ConditionallyCompleteLattice.toLattice.{u2} β (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} β _inst_4))))) f z)))
Case conversion may be inaccurate. Consider using '#align metric.exists_local_min_mem_ball Metric.exists_local_min_mem_ballₓ'. -/
theorem exists_local_min_mem_ball [ProperSpace α] [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a z : α} {r : ℝ}
    (hf : ContinuousOn f (closedBall a r)) (hz : z ∈ closedBall a r)
    (hf1 : ∀ z' ∈ sphere a r, f z < f z') : ∃ z ∈ ball a r, IsLocalMin f z :=
  by
  simp_rw [← closed_ball_diff_ball] at hf1
  exact
    (is_compact_closed_ball a r).exists_local_min_mem_open ball_subset_closed_ball hf hz hf1
      is_open_ball
#align metric.exists_local_min_mem_ball Metric.exists_local_min_mem_ball

end Metric

namespace Tactic

open Positivity

/-- Extension for the `positivity` tactic: the diameter of a set is always nonnegative. -/
@[positivity]
unsafe def positivity_diam : expr → tactic strictness
  | q(Metric.diam $(s)) => nonnegative <$> mk_app `` Metric.diam_nonneg [s]
  | e => pp e >>= fail ∘ format.bracket "The expression " " is not of the form `metric.diam s`"
#align tactic.positivity_diam tactic.positivity_diam

end Tactic

/- warning: comap_dist_right_at_top_le_cocompact -> comap_dist_right_atTop_le_cocompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.comap.{u1, 0} α Real (fun (y : α) => Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) y x) (Filter.atTop.{0} Real Real.preorder)) (Filter.cocompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.comap.{u1, 0} α Real (fun (y : α) => Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y x) (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.cocompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align comap_dist_right_at_top_le_cocompact comap_dist_right_atTop_le_cocompactₓ'. -/
theorem comap_dist_right_atTop_le_cocompact (x : α) :
    comap (fun y => dist y x) atTop ≤ cocompact α :=
  by
  refine' filter.has_basis_cocompact.ge_iff.2 fun s hs => mem_comap.2 _
  rcases hs.bounded.subset_ball x with ⟨r, hr⟩
  exact ⟨Ioi r, Ioi_mem_at_top r, fun y hy hys => (mem_closed_ball.1 <| hr hys).not_lt hy⟩
#align comap_dist_right_at_top_le_cocompact comap_dist_right_atTop_le_cocompact

/- warning: comap_dist_left_at_top_le_cocompact -> comap_dist_left_atTop_le_cocompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.comap.{u1, 0} α Real (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) x) (Filter.atTop.{0} Real Real.preorder)) (Filter.cocompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] (x : α), LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.comap.{u1, 0} α Real (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) x) (Filter.atTop.{0} Real Real.instPreorderReal)) (Filter.cocompact.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align comap_dist_left_at_top_le_cocompact comap_dist_left_atTop_le_cocompactₓ'. -/
theorem comap_dist_left_atTop_le_cocompact (x : α) : comap (dist x) atTop ≤ cocompact α := by
  simpa only [dist_comm _ x] using comap_dist_right_atTop_le_cocompact x
#align comap_dist_left_at_top_le_cocompact comap_dist_left_atTop_le_cocompact

#print comap_dist_right_atTop_eq_cocompact /-
theorem comap_dist_right_atTop_eq_cocompact [ProperSpace α] (x : α) :
    comap (fun y => dist y x) atTop = cocompact α :=
  (comap_dist_right_atTop_le_cocompact x).antisymm <|
    (tendsto_dist_right_cocompact_atTop x).le_comap
#align comap_dist_right_at_top_eq_cocompact comap_dist_right_atTop_eq_cocompact
-/

#print comap_dist_left_atTop_eq_cocompact /-
theorem comap_dist_left_atTop_eq_cocompact [ProperSpace α] (x : α) :
    comap (dist x) atTop = cocompact α :=
  (comap_dist_left_atTop_le_cocompact x).antisymm <| (tendsto_dist_left_cocompact_atTop x).le_comap
#align comap_dist_left_at_top_eq_cocompact comap_dist_left_atTop_eq_cocompact
-/

#print tendsto_cocompact_of_tendsto_dist_comp_atTop /-
theorem tendsto_cocompact_of_tendsto_dist_comp_atTop {f : β → α} {l : Filter β} (x : α)
    (h : Tendsto (fun y => dist (f y) x) l atTop) : Tendsto f l (cocompact α) :=
  by
  refine' tendsto.mono_right _ (comap_dist_right_atTop_le_cocompact x)
  rwa [tendsto_comap_iff]
#align tendsto_cocompact_of_tendsto_dist_comp_at_top tendsto_cocompact_of_tendsto_dist_comp_atTop
-/

#print MetricSpace /-
/-- We now define `metric_space`, extending `pseudo_metric_space`. -/
class MetricSpace (α : Type u) extends PseudoMetricSpace α : Type u where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
#align metric_space MetricSpace
-/

#print MetricSpace.ext /-
/-- Two metric space structures with the same distance coincide. -/
@[ext]
theorem MetricSpace.ext {α : Type _} {m m' : MetricSpace α} (h : m.toHasDist = m'.toHasDist) :
    m = m' :=
  by
  have h' : m.to_pseudo_metric_space = m'.to_pseudo_metric_space := PseudoMetricSpace.ext h
  rcases m with ⟨⟩
  rcases m' with ⟨⟩
  dsimp at h'
  subst h'
#align metric_space.ext MetricSpace.ext
-/

/- warning: metric_space.of_dist_topology -> MetricSpace.ofDistTopology is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α), Eq.{1} Real (dist x x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (dist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (dist x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (dist x y) (dist y z))) -> (forall (s : Set.{u1} α), Iff (IsOpen.{u1} α _inst_2 s) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall (y : α), (LT.lt.{0} Real Real.hasLt (dist x y) ε) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s)))))) -> (forall (x : α) (y : α), (Eq.{1} Real (dist x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{succ u1} α x y)) -> (MetricSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α), Eq.{1} Real (dist x x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (dist y x)) -> (forall (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (dist x z) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (dist x y) (dist y z))) -> (forall (s : Set.{u1} α), Iff (IsOpen.{u1} α _inst_2 s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (y : α), (LT.lt.{0} Real Real.instLTReal (dist x y) ε) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s)))))) -> (forall (x : α) (y : α), (Eq.{1} Real (dist x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{succ u1} α x y)) -> (MetricSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align metric_space.of_dist_topology MetricSpace.ofDistTopologyₓ'. -/
/-- Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero }
#align metric_space.of_dist_topology MetricSpace.ofDistTopology

variable {γ : Type w} [MetricSpace γ]

/- warning: eq_of_dist_eq_zero -> eq_of_dist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, (Eq.{1} Real (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, (Eq.{1} Real (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align eq_of_dist_eq_zero eq_of_dist_eq_zeroₓ'. -/
theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y :=
  MetricSpace.eq_of_dist_eq_zero
#align eq_of_dist_eq_zero eq_of_dist_eq_zero

/- warning: dist_eq_zero -> dist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} Real (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} Real (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align dist_eq_zero dist_eq_zeroₓ'. -/
@[simp]
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
  Iff.intro eq_of_dist_eq_zero fun this : x = y => this ▸ dist_self _
#align dist_eq_zero dist_eq_zero

/- warning: zero_eq_dist -> zero_eq_dist is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} Real (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y)) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} Real (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y)) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align zero_eq_dist zero_eq_distₓ'. -/
@[simp]
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y := by rw [eq_comm, dist_eq_zero]
#align zero_eq_dist zero_eq_dist

/- warning: dist_ne_zero -> dist_ne_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Ne.{1} Real (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Ne.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Ne.{1} Real (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Ne.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align dist_ne_zero dist_ne_zeroₓ'. -/
theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y := by
  simpa only [not_iff_not] using dist_eq_zero
#align dist_ne_zero dist_ne_zero

/- warning: dist_le_zero -> dist_le_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align dist_le_zero dist_le_zeroₓ'. -/
@[simp]
theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y := by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y
#align dist_le_zero dist_le_zero

/- warning: dist_pos -> dist_pos is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y)) (Ne.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y)) (Ne.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align dist_pos dist_posₓ'. -/
@[simp]
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y := by
  simpa only [not_le] using not_congr dist_le_zero
#align dist_pos dist_pos

/- warning: eq_of_forall_dist_le -> eq_of_forall_dist_le is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) ε)) -> (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) ε)) -> (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align eq_of_forall_dist_le eq_of_forall_dist_leₓ'. -/
theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε > 0, dist x y ≤ ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)
#align eq_of_forall_dist_le eq_of_forall_dist_le

/- warning: eq_of_nndist_eq_zero -> eq_of_nndist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, (Eq.{1} NNReal (NNDist.nndist.{u1} γ (PseudoMetricSpace.toNNDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, (Eq.{1} NNReal (NNDist.nndist.{u1} γ (PseudoMetricSpace.toNNDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align eq_of_nndist_eq_zero eq_of_nndist_eq_zeroₓ'. -/
/-- Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 → x = y := by
  simp only [← NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]
#align eq_of_nndist_eq_zero eq_of_nndist_eq_zero

/- warning: nndist_eq_zero -> nndist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} NNReal (NNDist.nndist.{u1} γ (PseudoMetricSpace.toNNDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} NNReal (NNDist.nndist.{u1} γ (PseudoMetricSpace.toNNDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align nndist_eq_zero nndist_eq_zeroₓ'. -/
/-- Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp]
theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y := by
  simp only [← NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]
#align nndist_eq_zero nndist_eq_zero

/- warning: zero_eq_nndist -> zero_eq_nndist is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} NNReal (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (NNDist.nndist.{u1} γ (PseudoMetricSpace.toNNDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y)) (Eq.{succ u1} γ x y)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ} {y : γ}, Iff (Eq.{1} NNReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (NNDist.nndist.{u1} γ (PseudoMetricSpace.toNNDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y)) (Eq.{succ u1} γ x y)
Case conversion may be inaccurate. Consider using '#align zero_eq_nndist zero_eq_nndistₓ'. -/
@[simp]
theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y := by
  simp only [← NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, zero_eq_dist]
#align zero_eq_nndist zero_eq_nndist

namespace Metric

variable {x : γ} {s : Set γ}

/- warning: metric.closed_ball_zero -> Metric.closedBall_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ}, Eq.{succ u1} (Set.{u1} γ) (Metric.closedBall.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.hasSingleton.{u1} γ) x)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ}, Eq.{succ u1} (Set.{u1} γ) (Metric.closedBall.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.instSingletonSet.{u1} γ) x)
Case conversion may be inaccurate. Consider using '#align metric.closed_ball_zero Metric.closedBall_zeroₓ'. -/
@[simp]
theorem closedBall_zero : closedBall x 0 = {x} :=
  Set.ext fun y => dist_le_zero
#align metric.closed_ball_zero Metric.closedBall_zero

/- warning: metric.sphere_zero -> Metric.sphere_zero is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ}, Eq.{succ u1} (Set.{u1} γ) (Metric.sphere.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.hasSingleton.{u1} γ) x)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {x : γ}, Eq.{succ u1} (Set.{u1} γ) (Metric.sphere.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Singleton.singleton.{u1, u1} γ (Set.{u1} γ) (Set.instSingletonSet.{u1} γ) x)
Case conversion may be inaccurate. Consider using '#align metric.sphere_zero Metric.sphere_zeroₓ'. -/
@[simp]
theorem sphere_zero : sphere x 0 = {x} :=
  Set.ext fun y => dist_eq_zero
#align metric.sphere_zero Metric.sphere_zero

/- warning: metric.subsingleton_closed_ball -> Metric.subsingleton_closedBall is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] (x : γ) {r : Real}, (LE.le.{0} Real Real.hasLe r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Set.Subsingleton.{u1} γ (Metric.closedBall.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x r))
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] (x : γ) {r : Real}, (LE.le.{0} Real Real.instLEReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Set.Subsingleton.{u1} γ (Metric.closedBall.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x r))
Case conversion may be inaccurate. Consider using '#align metric.subsingleton_closed_ball Metric.subsingleton_closedBallₓ'. -/
theorem subsingleton_closedBall (x : γ) {r : ℝ} (hr : r ≤ 0) : (closedBall x r).Subsingleton :=
  by
  rcases hr.lt_or_eq with (hr | rfl)
  · rw [closed_ball_eq_empty.2 hr]
    exact subsingleton_empty
  · rw [closed_ball_zero]
    exact subsingleton_singleton
#align metric.subsingleton_closed_ball Metric.subsingleton_closedBall

/- warning: metric.subsingleton_sphere -> Metric.subsingleton_sphere is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] (x : γ) {r : Real}, (LE.le.{0} Real Real.hasLe r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Set.Subsingleton.{u1} γ (Metric.sphere.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x r))
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] (x : γ) {r : Real}, (LE.le.{0} Real Real.instLEReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Set.Subsingleton.{u1} γ (Metric.sphere.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2) x r))
Case conversion may be inaccurate. Consider using '#align metric.subsingleton_sphere Metric.subsingleton_sphereₓ'. -/
theorem subsingleton_sphere (x : γ) {r : ℝ} (hr : r ≤ 0) : (sphere x r).Subsingleton :=
  (subsingleton_closedBall x hr).anti sphere_subset_closedBall
#align metric.subsingleton_sphere Metric.subsingleton_sphere

#print MetricSpace.to_separated /-
-- see Note [lower instance priority]
instance (priority := 100) MetricSpace.to_separated : SeparatedSpace γ :=
  separated_def.2 fun x y h =>
    eq_of_forall_dist_le fun ε ε0 => le_of_lt (h _ (dist_mem_uniformity ε0))
#align metric_space.to_separated MetricSpace.to_separated
-/

/- warning: metric.uniform_embedding_iff' -> Metric.uniformEmbedding_iff' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : MetricSpace.{u2} γ] [_inst_3 : MetricSpace.{u1} β] {f : γ -> β}, Iff (UniformEmbedding.{u2, u1} γ β (PseudoMetricSpace.toUniformSpace.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_3)) f) (And (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (δ : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : γ} {b : γ}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} γ (PseudoMetricSpace.toHasDist.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) a b) δ) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} β (PseudoMetricSpace.toHasDist.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_3)) (f a) (f b)) ε))))) (forall (δ : Real), (GT.gt.{0} Real Real.hasLt δ (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (ε : Real) => Exists.{0} (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (fun (H : GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) => forall {a : γ} {b : γ}, (LT.lt.{0} Real Real.hasLt (Dist.dist.{u1} β (PseudoMetricSpace.toHasDist.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_3)) (f a) (f b)) ε) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} γ (PseudoMetricSpace.toHasDist.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) a b) δ))))))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_2 : MetricSpace.{u2} γ] [_inst_3 : MetricSpace.{u1} β] {f : γ -> β}, Iff (UniformEmbedding.{u2, u1} γ β (PseudoMetricSpace.toUniformSpace.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) (PseudoMetricSpace.toUniformSpace.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_3)) f) (And (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (δ : Real) => And (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : γ} {b : γ}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} γ (PseudoMetricSpace.toDist.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) a b) δ) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_3)) (f a) (f b)) ε))))) (forall (δ : Real), (GT.gt.{0} Real Real.instLTReal δ (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (ε : Real) => And (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall {a : γ} {b : γ}, (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β (MetricSpace.toPseudoMetricSpace.{u1} β _inst_3)) (f a) (f b)) ε) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} γ (PseudoMetricSpace.toDist.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) a b) δ))))))
Case conversion may be inaccurate. Consider using '#align metric.uniform_embedding_iff' Metric.uniformEmbedding_iff'ₓ'. -/
/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniformEmbedding_iff' [MetricSpace β] {f : γ → β} :
    UniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ :=
  by
  simp only [uniformEmbedding_iff_uniformInducing,
    uniformity_basis_dist.uniform_inducing_iff uniformity_basis_dist, exists_prop]
  rfl
#align metric.uniform_embedding_iff' Metric.uniformEmbedding_iff'

#print MetricSpace.ofT0PseudoMetricSpace /-
/-- If a `pseudo_metric_space` is a T₀ space, then it is a `metric_space`. -/
def MetricSpace.ofT0PseudoMetricSpace (α : Type _) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α :=
  { ‹PseudoMetricSpace α› with
    eq_of_dist_eq_zero := fun x y hdist => Inseparable.eq <| Metric.inseparable_iff.2 hdist }
#align metric_space.of_t0_pseudo_metric_space MetricSpace.ofT0PseudoMetricSpace
-/

#print MetricSpace.toEMetricSpace /-
-- see Note [lower instance priority]
/-- A metric space induces an emetric space -/
instance (priority := 100) MetricSpace.toEMetricSpace : EMetricSpace γ :=
  EMetricSpace.ofT0PseudoEMetricSpace γ
#align metric_space.to_emetric_space MetricSpace.toEMetricSpace
-/

/- warning: metric.is_closed_of_pairwise_le_dist -> Metric.isClosed_of_pairwise_le_dist is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {s : Set.{u1} γ} {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Set.Pairwise.{u1} γ s (fun (x : γ) (y : γ) => LE.le.{0} Real Real.hasLe ε (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y))) -> (IsClosed.{u1} γ (UniformSpace.toTopologicalSpace.{u1} γ (PseudoMetricSpace.toUniformSpace.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2))) s)
but is expected to have type
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {s : Set.{u1} γ} {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Set.Pairwise.{u1} γ s (fun (x : γ) (y : γ) => LE.le.{0} Real Real.instLEReal ε (Dist.dist.{u1} γ (PseudoMetricSpace.toDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) x y))) -> (IsClosed.{u1} γ (UniformSpace.toTopologicalSpace.{u1} γ (PseudoMetricSpace.toUniformSpace.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2))) s)
Case conversion may be inaccurate. Consider using '#align metric.is_closed_of_pairwise_le_dist Metric.isClosed_of_pairwise_le_distₓ'. -/
theorem isClosed_of_pairwise_le_dist {s : Set γ} {ε : ℝ} (hε : 0 < ε)
    (hs : s.Pairwise fun x y => ε ≤ dist x y) : IsClosed s :=
  isClosed_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hs
#align metric.is_closed_of_pairwise_le_dist Metric.isClosed_of_pairwise_le_dist

/- warning: metric.closed_embedding_of_pairwise_le_dist -> Metric.closedEmbedding_of_pairwise_le_dist is a dubious translation:
lean 3 declaration is
  forall {γ : Type.{u1}} [_inst_2 : MetricSpace.{u1} γ] {α : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : DiscreteTopology.{u2} α _inst_3] {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall {f : α -> γ}, (Pairwise.{u2} α (fun (x : α) (y : α) => LE.le.{0} Real Real.hasLe ε (Dist.dist.{u1} γ (PseudoMetricSpace.toHasDist.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2)) (f x) (f y)))) -> (ClosedEmbedding.{u2, u1} α γ _inst_3 (UniformSpace.toTopologicalSpace.{u1} γ (PseudoMetricSpace.toUniformSpace.{u1} γ (MetricSpace.toPseudoMetricSpace.{u1} γ _inst_2))) f))
but is expected to have type
  forall {γ : Type.{u2}} [_inst_2 : MetricSpace.{u2} γ] {α : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : DiscreteTopology.{u1} α _inst_3] {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall {f : α -> γ}, (Pairwise.{u1} α (fun (x : α) (y : α) => LE.le.{0} Real Real.instLEReal ε (Dist.dist.{u2} γ (PseudoMetricSpace.toDist.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2)) (f x) (f y)))) -> (ClosedEmbedding.{u1, u2} α γ _inst_3 (UniformSpace.toTopologicalSpace.{u2} γ (PseudoMetricSpace.toUniformSpace.{u2} γ (MetricSpace.toPseudoMetricSpace.{u2} γ _inst_2))) f))
Case conversion may be inaccurate. Consider using '#align metric.closed_embedding_of_pairwise_le_dist Metric.closedEmbedding_of_pairwise_le_distₓ'. -/
theorem closedEmbedding_of_pairwise_le_dist {α : Type _} [TopologicalSpace α] [DiscreteTopology α]
    {ε : ℝ} (hε : 0 < ε) {f : α → γ} (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    ClosedEmbedding f :=
  closedEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf
#align metric.closed_embedding_of_pairwise_le_dist Metric.closedEmbedding_of_pairwise_le_dist

/- warning: metric.uniform_embedding_bot_of_pairwise_le_dist -> Metric.uniformEmbedding_bot_of_pairwise_le_dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PseudoMetricSpace.{u1} α] {β : Type.{u2}} {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall {f : β -> α}, (Pairwise.{u2} β (fun (x : β) (y : β) => LE.le.{0} Real Real.hasLe ε (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α _inst_1) (f x) (f y)))) -> (UniformEmbedding.{u2, u1} β α (Bot.bot.{u2} (UniformSpace.{u2} β) (UniformSpace.hasBot.{u2} β)) (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1) f))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : PseudoMetricSpace.{u2} α] {β : Type.{u1}} {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall {f : β -> α}, (Pairwise.{u1} β (fun (x : β) (y : β) => LE.le.{0} Real Real.instLEReal ε (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α _inst_1) (f x) (f y)))) -> (UniformEmbedding.{u1, u2} β α (Bot.bot.{u1} (UniformSpace.{u1} β) (instBotUniformSpace.{u1} β)) (inferInstance.{succ u2} (UniformSpace.{u2} α) (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) f))
Case conversion may be inaccurate. Consider using '#align metric.uniform_embedding_bot_of_pairwise_le_dist Metric.uniformEmbedding_bot_of_pairwise_le_distₓ'. -/
/-- If `f : β → α` sends any two distinct points to points at distance at least `ε > 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`. -/
theorem uniformEmbedding_bot_of_pairwise_le_dist {β : Type _} {ε : ℝ} (hε : 0 < ε) {f : β → α}
    (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    @UniformEmbedding _ _ ⊥ (by infer_instance) f :=
  uniformEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf
#align metric.uniform_embedding_bot_of_pairwise_le_dist Metric.uniformEmbedding_bot_of_pairwise_le_dist

end Metric

#print MetricSpace.replaceUniformity /-
/-- Build a new metric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ :=
  { PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H with
    eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _ }
#align metric_space.replace_uniformity MetricSpace.replaceUniformity
-/

#print MetricSpace.replaceUniformity_eq /-
theorem MetricSpace.replaceUniformity_eq {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m :=
  by
  ext
  rfl
#align metric_space.replace_uniformity_eq MetricSpace.replaceUniformity_eq
-/

#print MetricSpace.replaceTopology /-
/-- Build a new metric space from an old one where the bundled topological structure is provably
(but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible]
def MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl
#align metric_space.replace_topology MetricSpace.replaceTopology
-/

#print MetricSpace.replaceTopology_eq /-
theorem MetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : m.replaceTopology H = m :=
  by
  ext
  rfl
#align metric_space.replace_topology_eq MetricSpace.replaceTopology_eq
-/

/- warning: emetric_space.to_metric_space_of_dist -> EMetricSpace.toMetricSpaceOfDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [e : EMetricSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α e)) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (ENNReal.toReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α e)) x y))) -> (MetricSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [e : EMetricSpace.{u1} α] (dist : α -> α -> Real), (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α e)) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (forall (x : α) (y : α), Eq.{1} Real (dist x y) (ENNReal.toReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α e)) x y))) -> (MetricSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align emetric_space.to_metric_space_of_dist EMetricSpace.toMetricSpaceOfDistₓ'. -/
/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
def EMetricSpace.toMetricSpaceOfDist {α : Type u} [e : EMetricSpace α] (dist : α → α → ℝ)
    (edist_ne_top : ∀ x y : α, edist x y ≠ ⊤) (h : ∀ x y, dist x y = ENNReal.toReal (edist x y)) :
    MetricSpace α :=
  @MetricSpace.ofT0PseudoMetricSpace α
    (PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist edist_ne_top h) _
#align emetric_space.to_metric_space_of_dist EMetricSpace.toMetricSpaceOfDist

/- warning: emetric_space.to_metric_space -> EMetricSpace.toMetricSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : EMetricSpace.{u1} α], (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toHasEdist.{u1} α (EMetricSpace.toPseudoEmetricSpace.{u1} α _inst_3)) x y) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) -> (MetricSpace.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : EMetricSpace.{u1} α], (forall (x : α) (y : α), Ne.{1} ENNReal (EDist.edist.{u1} α (PseudoEMetricSpace.toEDist.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α _inst_3)) x y) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) -> (MetricSpace.{u1} α)
Case conversion may be inaccurate. Consider using '#align emetric_space.to_metric_space EMetricSpace.toMetricSpaceₓ'. -/
/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
def EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (fun x y => ENNReal.toReal (edist x y)) h fun x y => rfl
#align emetric_space.to_metric_space EMetricSpace.toMetricSpace

#print MetricSpace.replaceBornology /-
/-- Build a new metric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
def MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }
#align metric_space.replace_bornology MetricSpace.replaceBornology
-/

#print MetricSpace.replaceBornology_eq /-
theorem MetricSpace.replaceBornology_eq {α} [m : MetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    MetricSpace.replaceBornology _ H = m := by
  ext
  rfl
#align metric_space.replace_bornology_eq MetricSpace.replaceBornology_eq
-/

#print MetricSpace.induced /-
/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
def MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun x y h => hf (dist_eq_zero.1 h) }
#align metric_space.induced MetricSpace.induced
-/

#print UniformEmbedding.comapMetricSpace /-
/-- Pull back a metric space structure by a uniform embedding. This is a version of
`metric_space.induced` useful in case if the domain already has a `uniform_space` structure. -/
@[reducible]
def UniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [MetricSpace β] (f : α → β)
    (h : UniformEmbedding f) : MetricSpace α :=
  (MetricSpace.induced f h.inj ‹_›).replaceUniformity h.comap_uniformity.symm
#align uniform_embedding.comap_metric_space UniformEmbedding.comapMetricSpace
-/

#print Embedding.comapMetricSpace /-
/-- Pull back a metric space structure by an embedding. This is a version of
`metric_space.induced` useful in case if the domain already has a `topological_space` structure. -/
@[reducible]
def Embedding.comapMetricSpace {α β} [TopologicalSpace α] [MetricSpace β] (f : α → β)
    (h : Embedding f) : MetricSpace α :=
  letI : UniformSpace α := Embedding.comapUniformSpace f h
  UniformEmbedding.comapMetricSpace f (h.to_uniform_embedding f)
#align embedding.comap_metric_space Embedding.comapMetricSpace
-/

#print Subtype.metricSpace /-
instance Subtype.metricSpace {α : Type _} {p : α → Prop} [MetricSpace α] :
    MetricSpace (Subtype p) :=
  MetricSpace.induced coe Subtype.coe_injective ‹_›
#align subtype.metric_space Subtype.metricSpace
-/

@[to_additive]
instance {α : Type _} [MetricSpace α] : MetricSpace αᵐᵒᵖ :=
  MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance : MetricSpace Empty where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ _ _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := Empty.uniformSpace
  uniformity_dist := Subsingleton.elim _ _

instance : MetricSpace PUnit.{u + 1} where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ _ _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := PUnit.uniformSpace
  uniformity_dist := by
    simp only
    have : ne_bot (⨅ ε > (0 : ℝ), 𝓟 { p : PUnit.{u + 1} × PUnit.{u + 1} | 0 < ε }) :=
      @uniformity.neBot _
        (UniformSpace.ofDist (fun _ _ => 0) (fun _ => rfl) (fun _ _ => rfl) fun _ _ _ => by
          rw [zero_add])
        _
    refine' (eq_top_of_ne_bot _).trans (eq_top_of_ne_bot _).symm

section Real

#print Real.metricSpace /-
/-- Instantiate the reals as a metric space. -/
instance Real.metricSpace : MetricSpace ℝ :=
  { Real.pseudoMetricSpace with
    eq_of_dist_eq_zero := fun x y h => by simpa [dist, sub_eq_zero] using h }
#align real.metric_space Real.metricSpace
-/

end Real

section NNReal

instance : MetricSpace ℝ≥0 :=
  Subtype.metricSpace

end NNReal

instance [MetricSpace β] : MetricSpace (ULift β) :=
  MetricSpace.induced ULift.down ULift.down_injective ‹_›

section Prod

#print Prod.metricSpaceMax /-
instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) :=
  { Prod.pseudoMetricSpaceMax with
    eq_of_dist_eq_zero := fun x y h =>
      by
      cases' max_le_iff.1 (le_of_eq h) with h₁ h₂
      exact Prod.ext_iff.2 ⟨dist_le_zero.1 h₁, dist_le_zero.1 h₂⟩ }
#align prod.metric_space_max Prod.metricSpaceMax
-/

end Prod

section Pi

open Finset

variable {π : β → Type _} [Fintype β] [∀ b, MetricSpace (π b)]

#print metricSpacePi /-
/-- A finite product of metric spaces is a metric space, with the sup distance. -/
instance metricSpacePi : MetricSpace (∀ b, π b) :=
  {/- we construct the instance from the emetric space instance to avoid checking again that the
      uniformity is the same as the product uniformity, but we register nevertheless a nice formula
      for the distance -/
    pseudoMetricSpacePi with
    eq_of_dist_eq_zero := fun f g eq0 =>
      by
      have eq1 : edist f g = 0 := by simp only [edist_dist, eq0, ENNReal.ofReal_zero]
      have eq2 : (sup univ fun b : β => edist (f b) (g b)) ≤ 0 := le_of_eq eq1
      simp only [Finset.sup_le_iff] at eq2
      exact funext fun b => edist_le_zero.1 <| eq2 b <| mem_univ b }
#align metric_space_pi metricSpacePi
-/

end Pi

namespace Metric

section SecondCountable

open TopologicalSpace

/- warning: metric.second_countable_of_countable_discretization -> Metric.secondCountable_of_countable_discretization is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : MetricSpace.{u1} α], (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{succ (succ u2)} Type.{u2} (fun (β : Type.{u2}) => Exists.{succ u2} (Encodable.{u2} β) (fun (_x : Encodable.{u2} β) => Exists.{max (succ u1) (succ u2)} (α -> β) (fun (F : α -> β) => forall (x : α) (y : α), (Eq.{succ u2} β (F x) (F y)) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u1} α (PseudoMetricSpace.toHasDist.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_3)) x y) ε)))))) -> (TopologicalSpace.SecondCountableTopology.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_3))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_3 : MetricSpace.{u2} α], (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{succ (succ u1)} Type.{u1} (fun (β : Type.{u1}) => Exists.{succ u1} (Encodable.{u1} β) (fun (_x : Encodable.{u1} β) => Exists.{max (succ u2) (succ u1)} (α -> β) (fun (F : α -> β) => forall (x : α) (y : α), (Eq.{succ u1} β (F x) (F y)) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} α (PseudoMetricSpace.toDist.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_3)) x y) ε)))))) -> (TopologicalSpace.SecondCountableTopology.{u2} α (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α (MetricSpace.toPseudoMetricSpace.{u2} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align metric.second_countable_of_countable_discretization Metric.secondCountable_of_countable_discretizationₓ'. -/
/-- A metric space is second countable if one can reconstruct up to any `ε>0` any element of the
space from countably many data. -/
theorem secondCountable_of_countable_discretization {α : Type u} [MetricSpace α]
    (H :
      ∀ ε > (0 : ℝ), ∃ (β : Type _)(_ : Encodable β)(F : α → β), ∀ x y, F x = F y → dist x y ≤ ε) :
    SecondCountableTopology α :=
  by
  cases' (univ : Set α).eq_empty_or_nonempty with hs hs
  · haveI : CompactSpace α := ⟨by rw [hs] <;> exact isCompact_empty⟩
    · infer_instance
  rcases hs with ⟨x0, hx0⟩
  letI : Inhabited α := ⟨x0⟩
  refine' second_countable_of_almost_dense_set fun ε ε0 => _
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  skip
  let Finv := Function.invFun F
  refine' ⟨range Finv, ⟨countable_range _, fun x => _⟩⟩
  let x' := Finv (F x)
  have : F x' = F x := Function.invFun_eq ⟨x, rfl⟩
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩
#align metric.second_countable_of_countable_discretization Metric.secondCountable_of_countable_discretization

end SecondCountable

end Metric

section EqRel

instance {α : Type u} [PseudoMetricSpace α] : Dist (UniformSpace.SeparationQuotient α)
    where dist p q :=
    Quotient.liftOn₂' p q dist fun x y x' y' hx hy => by
      rw [dist_edist, dist_edist, ← UniformSpace.SeparationQuotient.edist_mk x, ←
        UniformSpace.SeparationQuotient.edist_mk x', Quot.sound hx, Quot.sound hy]

#print UniformSpace.SeparationQuotient.dist_mk /-
theorem UniformSpace.SeparationQuotient.dist_mk {α : Type u} [PseudoMetricSpace α] (p q : α) :
    @dist (UniformSpace.SeparationQuotient α) _ (Quot.mk _ p) (Quot.mk _ q) = dist p q :=
  rfl
#align uniform_space.separation_quotient.dist_mk UniformSpace.SeparationQuotient.dist_mk
-/

instance {α : Type u} [PseudoMetricSpace α] : MetricSpace (UniformSpace.SeparationQuotient α) :=
  EMetricSpace.toMetricSpaceOfDist dist (fun x y => Quotient.inductionOn₂' x y edist_ne_top)
    fun x y => Quotient.inductionOn₂' x y dist_edist

end EqRel

/-!
### `additive`, `multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [Dist X]

instance : Dist (Additive X) :=
  ‹Dist X›

instance : Dist (Multiplicative X) :=
  ‹Dist X›

#print dist_ofMul /-
@[simp]
theorem dist_ofMul (a b : X) : dist (ofMul a) (ofMul b) = dist a b :=
  rfl
#align dist_of_mul dist_ofMul
-/

#print dist_ofAdd /-
@[simp]
theorem dist_ofAdd (a b : X) : dist (ofAdd a) (ofAdd b) = dist a b :=
  rfl
#align dist_of_add dist_ofAdd
-/

#print dist_toMul /-
@[simp]
theorem dist_toMul (a b : Additive X) : dist (toMul a) (toMul b) = dist a b :=
  rfl
#align dist_to_mul dist_toMul
-/

#print dist_toAdd /-
@[simp]
theorem dist_toAdd (a b : Multiplicative X) : dist (toAdd a) (toAdd b) = dist a b :=
  rfl
#align dist_to_add dist_toAdd
-/

end

section

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace (Additive X) :=
  ‹PseudoMetricSpace X›

instance : PseudoMetricSpace (Multiplicative X) :=
  ‹PseudoMetricSpace X›

#print nndist_ofMul /-
@[simp]
theorem nndist_ofMul (a b : X) : nndist (ofMul a) (ofMul b) = nndist a b :=
  rfl
#align nndist_of_mul nndist_ofMul
-/

#print nndist_ofAdd /-
@[simp]
theorem nndist_ofAdd (a b : X) : nndist (ofAdd a) (ofAdd b) = nndist a b :=
  rfl
#align nndist_of_add nndist_ofAdd
-/

#print nndist_toMul /-
@[simp]
theorem nndist_toMul (a b : Additive X) : nndist (toMul a) (toMul b) = nndist a b :=
  rfl
#align nndist_to_mul nndist_toMul
-/

#print nndist_toAdd /-
@[simp]
theorem nndist_toAdd (a b : Multiplicative X) : nndist (toAdd a) (toAdd b) = nndist a b :=
  rfl
#align nndist_to_add nndist_toAdd
-/

end

instance [MetricSpace X] : MetricSpace (Additive X) :=
  ‹MetricSpace X›

instance [MetricSpace X] : MetricSpace (Multiplicative X) :=
  ‹MetricSpace X›

instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Additive X) :=
  ‹ProperSpace X›

instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Multiplicative X) :=
  ‹ProperSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/


open OrderDual

section

variable [Dist X]

instance : Dist Xᵒᵈ :=
  ‹Dist X›

#print dist_toDual /-
@[simp]
theorem dist_toDual (a b : X) : dist (toDual a) (toDual b) = dist a b :=
  rfl
#align dist_to_dual dist_toDual
-/

#print dist_ofDual /-
@[simp]
theorem dist_ofDual (a b : Xᵒᵈ) : dist (ofDual a) (ofDual b) = dist a b :=
  rfl
#align dist_of_dual dist_ofDual
-/

end

section

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace Xᵒᵈ :=
  ‹PseudoMetricSpace X›

#print nndist_toDual /-
@[simp]
theorem nndist_toDual (a b : X) : nndist (toDual a) (toDual b) = nndist a b :=
  rfl
#align nndist_to_dual nndist_toDual
-/

#print nndist_ofDual /-
@[simp]
theorem nndist_ofDual (a b : Xᵒᵈ) : nndist (ofDual a) (ofDual b) = nndist a b :=
  rfl
#align nndist_of_dual nndist_ofDual
-/

end

instance [MetricSpace X] : MetricSpace Xᵒᵈ :=
  ‹MetricSpace X›

instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace Xᵒᵈ :=
  ‹ProperSpace X›

